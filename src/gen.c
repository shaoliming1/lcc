#include "c.h"

static char rcsid[] = "$Id$";

#define readsreg(p) \
	(generic((p)->op)==INDIR && (p)->kids[0]->op==VREG+P)
#define setsrc(d) ((d) && (d)->x.regnode && \
	(d)->x.regnode->set == src->x.regnode->set && \
	(d)->x.regnode->mask&src->x.regnode->mask)

#define relink(a, b) ((b)->x.prev = (a), (a)->x.next = (b))

static Symbol   askfixedreg(Symbol);
static Symbol   askreg(Symbol, unsigned*);
static void     blkunroll(int, int, int, int, int, int, int[]);
static void     docall(Node);
static void     dumpcover(Node, int, int);
static void     dumpregs(char *, char *, char *);
static void     dumprule(int);
static void     dumptree(Node);
static void     genreload(Node, Symbol, int);
static void     genspill(Symbol, Node, Symbol);
static Symbol   getreg(Symbol, unsigned*, Node);
static int      getrule(Node, int);
static void     linearize(Node, Node);
static int      moveself(Node);
static void     prelabel(Node);
static Node*    prune(Node, Node*);
static void     putreg(Symbol);
static void     ralloc(Node);
static void     reduce(Node, int);
static int      reprune(Node*, int, int, Node);
static int      requate(Node);
static Node     reuse(Node, int);
static void     rewrite(Node);
static Symbol   spillee(Symbol, unsigned mask[], Node);
static void     spillr(Symbol, Node);
static int      uses(Node, Regnode);

// offset就是最后一个自动变量的栈偏移的绝对值
int offset;

int maxoffset;

// 接口过程function设置framesize的值等于或者大于maxoffset, 以留出空间来存储诸如被调用程序必须保存的
// 寄存器之类的数据, 他还会生成过程头和过程尾代码, 这些代码根据framesize调整栈指针, 以分配或者释放该程序
// 的栈空间.
int framesize;
int argoffset;

int maxargoffset;

int dalign, salign;
int bflag = 0;  /* omit */
int dflag = 0;

int swap;

unsigned (*emitter)(Node, int) = emitasm;
// NeedsReg测试把具有副作用的节点与那些需要寄存器存放结果的节点区分开来.
// NeedsReg按照通用操作码索引, 并标记产生值的操作码.
static char NeedsReg[] = {
	0,                      /* unused */
	1,                      /* CNST */
	0, 0,                   /* ARG ASGN */
	1,                      /* INDIR  */
	0, 0, 1, 1,             /*  -  - CVF CVI */
	1, 0, 1, 1,             /* CVP - CVU NEG */
	1,                      /* CALL */
	1,                      /* LOAD */
	0,                      /* RET */
	1, 1, 1,                /* ADDRG ADDRF ADDRL */
	1, 1, 1, 1, 1,          /* ADD SUB LSH MOD RSH */
	1, 1, 1, 1,             /* BAND BCOM BOR BXOR */
	1, 1,                   /* DIV MUL */
	0, 0, 0, 0, 0, 0,       /* EQ GE GT LE LT NE */
	0, 0                   /* JUMP LABEL   */
};
Node head;

unsigned freemask[2];
unsigned usedmask[2];
// tmask表示用于临时变量的寄存器
unsigned tmask[2];
// vmask表示分配给寄存器变量的寄存器
unsigned vmask[2];
// mkreg创建初始化寄存器符号
Symbol mkreg(char *fmt, int n, int mask, int set) {
	Symbol p;

	NEW0(p, PERM);
	p->name = p->x.name = stringf(fmt, n);
	NEW0(p->x.regnode, PERM);
	p->x.regnode->number = n;
	p->x.regnode->mask = mask<<n;
	p->x.regnode->set = set;
	return p;
}
Symbol mkwildcard(Symbol *syms) {
	Symbol p;

	NEW0(p, PERM);
	p->name = p->x.name = "wildcard";
	p->x.wildcard = syms;
	return p;
}
// mkauto函数将栈空间进行对齐, 以便安排下一帧
void mkauto(Symbol p) {
	assert(p->sclass == AUTO);
	offset = roundup(offset + p->type->size, p->type->align);
	p->x.offset = -offset;
	p->x.name = stringd(-offset);
}
// 在每一个块的开始, 编译前端都调用blockbeg来保存当前栈的偏移量以及每一个寄存器的分配状态
void blockbeg(Env *e) {
	e->offset = offset;
	e->freemask[IREG] = freemask[IREG];
	e->freemask[FREG] = freemask[FREG];
}
void blockend(Env *e) {
	if (offset > maxoffset)
		maxoffset = offset;
	offset = e->offset;
	freemask[IREG] = e->freemask[IREG];
	freemask[FREG] = e->freemask[FREG];
}
int mkactual(int align, int size) {
	int n = roundup(argoffset, align);

	argoffset = n + size;
	return n;
}
// 处理每一个参数列表结束的CALL节点时都要调用docall函数.
// 该函数为下一个参数集合清除argoffset值, 计算出最大的
// 输出参数块的大小并存于maxargoffset中.
static void docall(Node p) {
	p->syms[1] = p->syms[0];
	// docall函数将当前调用参数块的大小记录在p->syms[0]中
	// 因此必要时调用者可以将它弹出栈.X86代码生成器就使用了这种
	// 机制
	p->syms[0] = intconst(argoffset);
	if (argoffset > maxargoffset)
		maxargoffset = argoffset;
	argoffset = 0;
}
// blkcopy函数是块复制代码生成器的入口
// 它与目标机器无关
// 与blkloop的参数相同
void blkcopy(int dreg, int doff, int sreg, int soff, int size, int tmp[]) {
	assert(size >= 0);
	if (size == 0)
		return;
	else if (size <= 2)
		blkunroll(size, dreg, doff, sreg, soff, size, tmp);
	else if (size == 3) {
		blkunroll(2, dreg, doff,   sreg, soff,   2, tmp);
		blkunroll(1, dreg, doff+2, sreg, soff+2, 1, tmp);
	}
	else if (size <= 16) {
		blkunroll(4, dreg, doff, sreg, soff, size&~3, tmp);
		blkcopy(dreg, doff+(size&~3),
	                sreg, soff+(size&~3), size&3, tmp);
	}
	else
		(*IR->x.blkloop)(dreg, doff, sreg, soff, size, tmp);
}
/***
 * @k
 */
static void blkunroll(int k, int dreg, int doff, int sreg, int soff, int size, int tmp[]) {
	int i;

	assert(IR->x.max_unaligned_load);
	if (k > IR->x.max_unaligned_load
	&& (k > salign || k > dalign))
		k = IR->x.max_unaligned_load;
	for (i = 0; i+k < size; i += 2*k) {
		(*IR->x.blkfetch)(k, soff+i,   sreg, tmp[0]);
		(*IR->x.blkfetch)(k, soff+i+k, sreg, tmp[1]);
		(*IR->x.blkstore)(k, doff+i,   dreg, tmp[0]);
		(*IR->x.blkstore)(k, doff+i+k, dreg, tmp[1]);
	}
	if (i < size) {
		(*IR->x.blkfetch)(k, i+soff, sreg, tmp[0]);
		(*IR->x.blkstore)(k, i+doff, dreg, tmp[0]);
	}
}
void parseflags(int argc, char *argv[]) {
	int i;

	for (i = 0; i < argc; i++)
		if (strcmp(argv[i], "-d") == 0)
			dflag = 1;
		else if (strcmp(argv[i], "-b") == 0)	/* omit */
			bflag = 1;			/* omit */
}
// lcc has three reducers. One identifes the nodes that need registers, another emits code, and a third prints a tree cover to help during debugging. They all use getrule, which wraps _rule in some assertions and encapsulates the indirection through IR;
static int getrule(Node p, int nt) {
	int rulenum;

	assert(p);
	rulenum = (*IR->x._rule)(p->x.state, nt);
	if (!rulenum) {
		fprint(stderr, "(%x->op=%s at %w is corrupt.)\n", p, opname(p->op), &src);
		assert(0);
	}
	return rulenum;
}
// lburg flags in x.isinstruction rules that emit instructions, in constrast to those that 
// emit subinstructions like addressing modes;it does so by examining the assembler template,
// which Section 14.6 explains
static void reduce(Node p, int nt) {
	int rulenum, i;
	short *nts;
	Node kids[10];

	p = reuse(p, nt);
	rulenum = getrule(p, nt);
	nts = IR->x._nts[rulenum];
	(*IR->x._kids)(p, rulenum, kids);
	for (i = 0; nts[i]; i++)
		reduce(kids[i], nts[i]);
	if (IR->x._isinstruction[rulenum]) {
		// x.inst is more than just a flags;it also indentifies the nonterminal
		// responsible for the mark. The register allocator linearizes
		// the instruction tree, and the emitter reduces each instruction 
		// in isolation, so the emitter needs a record of the nonterminal used
		// in the instruction's reduction.
		assert(p->x.inst == 0 || p->x.inst == nt);
		p->x.inst = nt;
		if (p->syms[RX] && p->syms[RX]->temporary) {
			debug(fprint(stderr, "(using %s)\n", p->syms[RX]->name));
			p->syms[RX]->x.usecount++;
		}
	}
}
static Node reuse(Node p, int nt) {
	struct _state {
		short cost[1];
	};
	Symbol r = p->syms[RX];

	// cse stand for "common subexpressions"
	//
	if (generic(p->op) == INDIR && p->kids[0]->op == VREG+P
	&& r->u.t.cse && p->x.mayrecalc
	&& ((struct _state*)r->u.t.cse->x.state)->cost[nt] == 0)
		return r->u.t.cse;
	else
		return p;
}

// 即使其中一个输入改变了,公共子表达式也不能重新计算
// 在允许一个额外的匹配名额之前, labeller调用mayrecalc进一步证实
// 该公共子表达式可以被重新计算,并把结果记录在x.mayrecalc中
int mayrecalc(Node p) {
	int op;

	assert(p && p->syms[RX]);
	// 如果节点不表示公共子表达式, mayrelcalc就会返回假
	if (p->syms[RX]->u.t.cse == NULL)
		return 0;
	op = generic(p->syms[RX]->u.t.cse->op);
	if (op == CNST || op == ADDRF || op == ADDRG || op == ADDRL) {
		p->x.mayrecalc = 1;
		return 1;
	} else
		return 0;
}
// reduce及其辅助程序执行完毕后, gen调用prune.
// prune使用x.inst 标记在x.kids域中构建一棵树
// prune的参数
//	p 指向需要prune的树
//	pp points to an element of some node's x.kids vector, namely the next element to fill in;
// 返回值: 下一个要fill in 的kids元素的pointer 	
static Node *prune(Node p, Node pp[]) {
	if (p == NULL)
		return pp;
	p->x.kids[0] = p->x.kids[1] = p->x.kids[2] = NULL;
	if (p->x.inst == 0)
		return prune(p->kids[1], prune(p->kids[0], pp));
	else if (p->syms[RX] && p->syms[RX]->temporary
	&& p->syms[RX]->x.usecount < 2) {
		p->x.inst = 0;
		debug(fprint(stderr, "(clobbering %s)\n", p->syms[RX]->name));
		return prune(p->kids[1], prune(p->kids[0], pp));
	}
	else {
		prune(p->kids[1], prune(p->kids[0], &p->x.kids[0]));
		*pp = p;
		return pp + 1;
	}
}

#define ck(i) return (i) ? 0 : LBURG_MAX

int range(Node p, int lo, int hi) {
	Symbol s = p->syms[0];

	switch (specific(p->op)) {
	case ADDRF+P:
	case ADDRL+P: ck(s->x.offset >= lo && s->x.offset <= hi);
	case CNST+I:  ck(s->u.c.v.i  >= lo && s->u.c.v.i  <= hi);
	case CNST+U:  ck(s->u.c.v.u  >= lo && s->u.c.v.u  <= hi);
	case CNST+P:  ck(s->u.c.v.p  == 0  && lo <= 0 && hi >= 0);
	}
	return LBURG_MAX;
}
// dump打印操作符和所有子树
static void dumptree(Node p) {
	if (p->op == VREG+P && p->syms[0]) {
		fprint(stderr, "VREGP(%s)", p->syms[0]->name);
		return;
	} else if (generic(p->op) == LOAD) {
		fprint(stderr, "LOAD(");
		dumptree(p->kids[0]);
		fprint(stderr, ")");
		return;
	}
	fprint(stderr, "%s(", opname(p->op));
	switch (generic(p->op)) {
	case CNST: case LABEL:
	case ADDRG: case ADDRF: case ADDRL:
		if (p->syms[0])
			fprint(stderr, "%s", p->syms[0]->name);
		break;
	case RET:
		if (p->kids[0])
			dumptree(p->kids[0]);
		break;
	case CVF: case CVI: case CVP: case CVU: case JUMP: 
	case ARG: case BCOM: case NEG: case INDIR:
		dumptree(p->kids[0]);
		break;
	case CALL:
		if (optype(p->op) != B) {
			dumptree(p->kids[0]);
			break;
		}
		/* else fall thru */
	case EQ: case NE: case GT: case GE: case LE: case LT:
	case ASGN: case BOR: case BAND: case BXOR: case RSH: case LSH:
	case ADD: case SUB:  case DIV: case MUL: case MOD:
		dumptree(p->kids[0]);
		fprint(stderr, ", ");
		dumptree(p->kids[1]);
		break;
	default: assert(0);
	}
	fprint(stderr, ")");
}
static void dumpcover(Node p, int nt, int in) {
	int rulenum, i;
	short *nts;
	Node kids[10];

	p = reuse(p, nt);
	rulenum = getrule(p, nt);
	nts = IR->x._nts[rulenum];
	fprint(stderr, "dumpcover(%x) = ", p);
	for (i = 0; i < in; i++)
		fprint(stderr, " ");
	dumprule(rulenum);
	(*IR->x._kids)(p, rulenum, kids);
	for (i = 0; nts[i]; i++)
		dumpcover(kids[i], nts[i], in+1);
}

static void dumprule(int rulenum) {
	assert(rulenum);
	fprint(stderr, "%s / %s", IR->x._string[rulenum],
		IR->x._templates[rulenum]);
	if (!IR->x._isinstruction[rulenum])
		fprint(stderr, "\n");
}
//
unsigned emitasm(Node p, int nt) {
	int rulenum;
	short *nts;
	char *fmt;
	Node kids[10];

	p = reuse(p, nt);
	rulenum = getrule(p, nt);
	nts = IR->x._nts[rulenum];
	fmt = IR->x._templates[rulenum];
	assert(fmt);
	if (IR->x._isinstruction[rulenum] && p->x.emitted)
		print("%s", p->syms[RX]->x.name);
	else if (*fmt == '#')
		(*IR->x.emit2)(p);
	else {
		if (*fmt == '?') {
			fmt++;
			assert(p->kids[0]);
			if (p->syms[RX] == p->x.kids[0]->syms[RX])
				while (*fmt++ != '\n')
					;
		}
		for ((*IR->x._kids)(p, rulenum, kids); *fmt; fmt++)
			if (*fmt != '%')
				(void)putchar(*fmt);
			else if (*++fmt == 'F')
				print("%d", framesize);
			else if (*fmt >= '0' && *fmt <= '9')
				emitasm(kids[*fmt - '0'], nts[*fmt - '0']);
			else if (*fmt >= 'a' && *fmt < 'a' + NELEMS(p->syms))
				fputs(p->syms[*fmt - 'a']->x.name, stdout);
			else
				(void)putchar(*fmt);
	}
	return 0;
}
void emit(Node p) {
	for (; p; p = p->x.next) {
		assert(p->x.registered);
		if (p->x.equatable && requate(p) || moveself(p))
			;
		else
			(*emitter)(p, p->x.inst);
		p->x.emitted = 1;
	}
}
static int moveself(Node p) {
	return p->x.copy
	&& p->syms[RX]->x.name == p->x.kids[0]->syms[RX]->x.name;
}
int move(Node p) {
	p->x.copy = 1;
	return 1;
}
static int requate(Node q) {
	Symbol src = q->x.kids[0]->syms[RX];
	Symbol tmp = q->syms[RX];
	Node p;
	int n = 0;

	debug(fprint(stderr, "(requate(%x): tmp=%s src=%s)\n", q, tmp->x.name, src->x.name));
	for (p = q->x.next; p; p = p->x.next)
		if (p->x.copy && p->syms[RX] == src
		&&  p->x.kids[0]->syms[RX] == tmp)
			debug(fprint(stderr, "(requate arm 0 at %x)\n", p)),
			p->syms[RX] = tmp;
		else if (setsrc(p->syms[RX]) && !moveself(p) && !readsreg(p))
			return 0;
		else if (p->x.spills)
			return 0;
		else if (generic(p->op) == CALL && p->x.next)
			return 0;
		else if (p->op == LABEL+V && p->x.next)
			return 0;
		else if (p->syms[RX] == tmp && readsreg(p))
			debug(fprint(stderr, "(requate arm 5 at %x)\n", p)),
			n++;
		else if (p->syms[RX] == tmp)
			break;
	debug(fprint(stderr, "(requate arm 7 at %x)\n", p));
	assert(n > 0);
	for (p = q->x.next; p; p = p->x.next)
		if (p->syms[RX] == tmp && readsreg(p)) {
			p->syms[RX] = src;
			if (--n <= 0)
				break;
		}
	return 1;
}
static void prelabel(Node p) {
	if (p == NULL)
		return;
	// 先序遍历
	prelabel(p->kids[0]);
	prelabel(p->kids[1]);
	if (NeedsReg[opindex(p->op)])
		setreg(p, (*IR->x.rmap)(opkind(p->op)));
	switch (generic(p->op)) {
	case ADDRF: case ADDRL:
		if (p->syms[0]->sclass == REGISTER)
			p->op = VREG+P;
		break;
	case INDIR:
		if (p->kids[0]->op == VREG+P)
			setreg(p, p->kids[0]->syms[0]);
		break;
	case ASGN:
		if (p->kids[0]->op == VREG+P)
			rtarget(p, 1, p->kids[0]->syms[0]);
		break;
	case CVI: case CVU: case CVP:
		if (optype(p->op) != F
		&&  opsize(p->op) <= p->syms[0]->u.c.v.i)
			p->op = LOAD + opkind(p->op);
		break;
	}
	(IR->x.target)(p);
}
// setreg在节点中记录了来自rmap的值, 以支持寄存器定位(register target)和分配
// prelabel调用setreg, 为所有带有相同类型后缀的操作码指派相同的通配符.
void setreg(Node p, Symbol r) {
	p->syms[RX] = r;
}
// rtarget(p,n,r)保证直接计算p->kids[n]的结果并保存到寄存器r中
void rtarget(Node p, int n, Symbol r) {
	Node q = p->kids[n];

	assert(q);
	assert(r);
	assert(r->sclass == REGISTER || !r->x.wildcard);
	assert(q->syms[RX]);
	// 如果子节点已被定位到另外一个寄存器变量或者 `返回寄存器`(the return register)
	// 之类的特殊寄存器, 那么rtarget在树的父节点和子节点之间插入一个LOAD节点, 并定位LOAD节点(而不是原来的节点)
	if (r != q->syms[RX] && !q->syms[RX]->x.wildcard) {
		q = newnode(LOAD + opkind(q->op),
			q, NULL, q->syms[0]);
		// note: Symbol-table entries for temporaries that hold common subexpressions
		// are identified as such by having nonnull u.t.cse fields.
		if (r->u.t.cse == p->kids[n])
			r->u.t.cse = q;
		p->kids[n] = p->x.kids[n] = q;
		q->x.kids[0] = q->kids[0];
	}
	setreg(q, r);
	debug(fprint(stderr, "(targeting %x->x.kids[%d]=%x to %s)\n", p, n, p->kids[n], r->x.name));
}
// rewrite完成单稞树的寄存器定位和指令选择
static void rewrite(Node p) {
	assert(p->x.inst == 0);
	prelabel(p);
	debug(dumptree(p));
	debug(fprint(stderr, "\n"));
	(*IR->x._label)(p);
	debug(dumpcover(p, 1, 0));
	reduce(p, 1);
}
// 接口函数gen从前端接收森林, 然后对这些树进行多次遍历
// 第一次遍历: 调用rewrite选择指令,对列出的节点进行标记
// 第二次遍历: 从树中删除子指令
Node gen(Node forest) {
	int i;
	struct node sentinel;
	Node dummy, p;

	head = forest;
	// 第一次遍历为参数和过程调用完成了与目标机器相关的处理.
	// 例如: 按照调用约定使用寄存器传递参数.
	for (p = forest; p; p = p->link) {
		assert(p->count == 0);
		// 如果调用没有返回值或者忽略返回值,那么调用本身就出现在森林中,下面的if语句来识别这种模式
		if (generic(p->op) == CALL)
			docall(p);
		// 调用指令将出现在对一个临时变量赋值的指令下面, 该临时变量用于以后需要返回值的地方.
		// 第二个if语句用来识别这种模式.
		else if (generic(p->op) == ASGN
		&& generic(p->kids[1]->op) == CALL)
			docall(p->kids[1]);
		else if (generic(p->op) == ARG)
			//只有doarg是目标机器相关的
			(*IR->x.doarg)(p);
		rewrite(p);
		// 对列出的节点进行标记
		p->x.listed = 1;
	}
	for (p = forest; p; p = p->link)
		prune(p, &dummy);
	relink(&sentinel, &sentinel);
	for (p = forest; p; p = p->link)
		linearize(p, &sentinel);
	forest = sentinel.x.next;
	assert(forest);
	sentinel.x.next->x.prev = NULL;
	sentinel.x.prev->x.next = NULL;
	for (p = forest; p; p = p->x.next)
		for (i = 0; i < NELEMS(p->x.kids) && p->x.kids[i]; i++) {
			assert(p->x.kids[i]->syms[RX]);
			if (p->x.kids[i]->syms[RX]->temporary) {
				p->x.kids[i]->x.prevuse =
					p->x.kids[i]->syms[RX]->x.lastuse;
				p->x.kids[i]->syms[RX]->x.lastuse = p->x.kids[i];
			}
		}
	// 最后一遍扫描森林为每个节点分配一个寄存器.rmap是一个以类型后缀进行索引的向量,
	// 它的每个元素都是一个表示寄存器组的寄存器通配符.这些寄存器组适合具有相应类型的
	// 未定位节点
	for (p = forest; p; p = p->x.next) {
		ralloc(p);
		if (p->x.listed && NeedsReg[opindex(p->op)]
		&& (*IR->x.rmap)(opkind(p->op))) {
			assert(generic(p->op) == CALL || generic(p->op) == LOAD);
			putreg(p->syms[RX]);
		}
	}
	return forest;
}
int notarget(Node p) {
	return p->syms[RX]->x.wildcard ? 0 : LBURG_MAX;
}
static void putreg(Symbol r) {
	assert(r && r->x.regnode);
	freemask[r->x.regnode->set] |= r->x.regnode->mask;
	debug(dumpregs("(freeing %s)\n", r->x.name, NULL));
}
static Symbol askfixedreg(Symbol s) {
	Regnode r = s->x.regnode;
	int n = r->set;

	if (r->mask&~freemask[n])
		return NULL;
	else {
		freemask[n] &= ~r->mask;
		usedmask[n] |=  r->mask;
		return s;
	}
}
static Symbol askreg(Symbol rs, unsigned rmask[]) {
	int i;

	if (rs->x.wildcard == NULL)
		return askfixedreg(rs);
	for (i = 31; i >= 0; i--) {
		Symbol r = rs->x.wildcard[i];
		if (r != NULL
		&& !(r->x.regnode->mask&~rmask[r->x.regnode->set])
		&& askfixedreg(r))
			return r;
	}
	return NULL;
}

static Symbol getreg(Symbol s, unsigned mask[], Node p) {
	Symbol r = askreg(s, mask);
	if (r == NULL) {
		r = spillee(s, mask, p);
		assert(r && r->x.regnode);
		spill(r->x.regnode->mask, r->x.regnode->set, p);
		r = askreg(s, mask);
	}
	assert(r && r->x.regnode);
	r->x.regnode->vbl = NULL;
	return r;
}
// askregvar 试图为一个局部变量或者形式参数分配寄存器. 如果分配成功就返回1, 否则返回0
int askregvar(Symbol p, Symbol regs) {
	Symbol r;

	assert(p);
	if (p->sclass != REGISTER)
		return 0;
	else if (!isscalar(p->type)) {
		p->sclass = AUTO;
		return 0;
	}
	else if (p->temporary) {
		p->x.name = "?";
		return 1;
	}
	else if ((r = askreg(regs, vmask)) != NULL) {
		p->x.regnode = r->x.regnode;
		p->x.regnode->vbl = p;
		p->x.name = r->x.name;
		debug(dumpregs("(allocating %s to symbol %s)\n", p->x.name, p->name));
		return 1;
	}
	else {
		p->sclass = AUTO;
		return 0;
	}
}
static void linearize(Node p, Node next) {
	int i;

	for (i = 0; i < NELEMS(p->x.kids) && p->x.kids[i]; i++)
		linearize(p->x.kids[i], next);
	relink(next->x.prev, p);
	relink(p, next);
	debug(fprint(stderr, "(listing %x)\n", p));
}
// ralloc(p) 释放了所有p的子节点不再需要的寄存器, 然后, 如果p需要一个寄存器,
// 且之前未被处理, 就给p分配一个寄存器.
static void ralloc(Node p) {
	int i;
	unsigned mask[2];

	mask[0] = tmask[0];
	mask[1] = tmask[1];
	assert(p);
	debug(fprint(stderr, "(rallocing %x)\n", p));
	for (i = 0; i < NELEMS(p->x.kids) && p->x.kids[i]; i++) {
		Node kid = p->x.kids[i];
		Symbol r = kid->syms[RX];
		assert(r && kid->x.registered);
		if (r->sclass != REGISTER && r->x.lastuse == kid)
			putreg(r);
	}
	if (!p->x.registered && NeedsReg[opindex(p->op)]
	&& (*IR->x.rmap)(opkind(p->op))) {
		Symbol sym = p->syms[RX], set = sym;
		assert(sym);
		if (sym->temporary)
			set = (*IR->x.rmap)(opkind(p->op));
		assert(set);
		if (set->sclass != REGISTER) {
			Symbol r;
			if (*IR->x._templates[getrule(p, p->x.inst)] == '?')
				for (i = 1; i < NELEMS(p->x.kids) && p->x.kids[i]; i++) {
					Symbol r = p->x.kids[i]->syms[RX];
					assert(p->x.kids[i]->x.registered);
					assert(r && r->x.regnode);
					assert(sym->x.wildcard || sym != r);
					mask[r->x.regnode->set] &= ~r->x.regnode->mask;
				}
			r = getreg(set, mask, p);
			if (sym->temporary) {
				Node q;
				r->x.lastuse = sym->x.lastuse;
				for (q = sym->x.lastuse; q; q = q->x.prevuse) {
					q->syms[RX] = r;
					q->x.registered = 1;
					if (sym->u.t.cse && q->x.copy)
						q->x.equatable = 1;
				}
			} else {
				p->syms[RX] = r;
				r->x.lastuse = p;
			}
			debug(dumpregs("(allocating %s to node %x)\n", r->x.name, (char *) p));
		}
	}
	p->x.registered = 1;
	// 最后, ralloc调用目标机器的clobber, 溢出所有因这个节点而被溢出的寄存器.
	(*IR->x.clobber)(p);
}
// 在set中寻找使用点离here最远的寄存器
static Symbol spillee(Symbol set, unsigned mask[], Node here) {
	Symbol bestreg = NULL;
	int bestdist = -1, i;

	assert(set);
	// 如果不是寄存器通配符
	if (!set->x.wildcard)
		bestreg = set;
	else {
		for (i = 31; i >= 0; i--) {
			Symbol ri = set->x.wildcard[i];
			if (
				ri != NULL &&
				ri->x.lastuse &&
				(ri->x.regnode->mask&tmask[ri->x.regnode->set]&mask[ri->x.regnode->set])
			) {
				Regnode rn = ri->x.regnode;
				Node q = here;
				int dist = 0;
				// 从here节点开始往指令序列后面找
				for (; q && !uses(q, rn); q = q->x.next)
					dist++;
				if (q && dist > bestdist) {
					bestdist = dist;
					bestreg = ri;
				}
			}
		}
	}
	assert(bestreg); /* Must be able to spill something. Reconfigure the register allocator
		to ensure that we can allocate a register for all nodes without spilling
		the node's necessary input regs. */	
	assert(bestreg->x.regnode->vbl == NULL); /* Can't spill register variables because
		the reload site might be in other blocks. Reconfigure the register allocator
		to ensure that this register is never allocated to a variable. */
	return bestreg;
}
// use 检查节点p是否读取了一个给定的寄存器
static int uses(Node p, Regnode rn) {
	int i;

	for (i = 0; i < NELEMS(p->x.kids); i++)
		if (
			p->x.kids[i] &&
			p->x.kids[i]->x.registered &&
			rn->set == p->x.kids[i]->syms[RX]->x.regnode->set &&
			(rn->mask&p->x.kids[i]->syms[RX]->x.regnode->mask)
		)
			return 1;
	return 0;
}
// spillr(r, here) 溢出寄存器r, 并且把here之后r的每个使用都替换成一个重取操作
static void spillr(Symbol r, Node here) {
	int i;
	Symbol tmp;
	Node p = r->x.lastuse;
	assert(p);
	while (p->x.prevuse)
		assert(r == p->syms[RX]),
		p = p->x.prevuse;
	assert(p->x.registered && !readsreg(p));
	tmp = newtemp(AUTO, optype(p->op), opsize(p->op));
	genspill(r, p, tmp);
	// spillr 将所有剩余的读取r的节点改成从溢出单元取值;最后是释放r
	for (p = here->x.next; p; p = p->x.next)
		for (i = 0; i < NELEMS(p->x.kids) && p->x.kids[i]; i++) {
			Node k = p->x.kids[i];
			if (k->x.registered && k->syms[RX] == r)
				genreload(p, tmp, i);
		}
	putreg(r);
}
static void genspill(Symbol r, Node last, Symbol tmp) {
	Node p, q;
	Symbol s;
	unsigned ty;

	debug(fprint(stderr, "(spilling %s to local %s)\n", r->x.name, tmp->x.name));
	debug(fprint(stderr, "(genspill: "));
	debug(dumptree(last));
	debug(fprint(stderr, ")\n"));
	ty = opkind(last->op);
	NEW0(s, FUNC);
	s->sclass = REGISTER;
	s->name = s->x.name = r->x.name;
	s->x.regnode = r->x.regnode;
	q = newnode(ADDRL+P + sizeop(IR->ptrmetric.size), NULL, NULL, s);
	q = newnode(INDIR + ty, q, NULL, NULL);
	p = newnode(ADDRL+P + sizeop(IR->ptrmetric.size), NULL, NULL, tmp);
	p = newnode(ASGN + ty, p, q, NULL);
	p->x.spills = 1;
	rewrite(p);
	prune(p, &q);
	q = last->x.next;
	linearize(p, q);
	for (p = last->x.next; p != q; p = p->x.next) {
		ralloc(p);
		assert(!p->x.listed || !NeedsReg[opindex(p->op)] || !(*IR->x.rmap)(opkind(p->op)));
	}
}

static void genreload(Node p, Symbol tmp, int i) {
	Node q;
	int ty;

	debug(fprint(stderr, "(replacing %x with a reload from %s)\n", p->x.kids[i], tmp->x.name));
	debug(fprint(stderr, "(genreload: "));
	debug(dumptree(p->x.kids[i]));
	debug(fprint(stderr, ")\n"));
	ty = opkind(p->x.kids[i]->op);
	q = newnode(ADDRL+P + sizeop(IR->ptrmetric.size), NULL, NULL, tmp);
	p->x.kids[i] = newnode(INDIR + ty, q, NULL, NULL);
	rewrite(p->x.kids[i]);
	prune(p->x.kids[i], &q);
	reprune(&p->kids[1], reprune(&p->kids[0], 0, i, p), i, p);
	prune(p, &q);
	linearize(p->x.kids[i], p);
}
static int reprune(Node *pp, int k, int n, Node p) {
	struct node x, *q = *pp;

	if (q == NULL || k > n)
		return k;
	else if (q->x.inst == 0)
		return reprune(&q->kids[1],
			reprune(&q->kids[0], k, n, p), n, p);
	if (k == n) {
		debug(fprint(stderr, "(reprune changes %x from %x to %x)\n", pp, *pp, p->x.kids[n]));
		*pp = p->x.kids[n];
		x = *p;
		(IR->x.target)(&x);
	}
	return k + 1;
}
void spill(unsigned mask, int n, Node here) {
	int i;
	Node p;

	here->x.spills = 1;
	usedmask[n] |= mask;
	if (mask&~freemask[n]) {

		assert( /* It makes no sense for a node to clobber() its target. */
			here->x.registered == 0 || /* call isn't coming through clobber() */
			here->syms[RX] == NULL ||
			here->syms[RX]->x.regnode == NULL ||
			here->syms[RX]->x.regnode->set != n ||
			(here->syms[RX]->x.regnode->mask&mask) == 0
		);

		for (p = here; p; p = p->x.next)
			for (i = 0; i < NELEMS(p->x.kids) && p->x.kids[i]; i++) {
				Symbol r = p->x.kids[i]->syms[RX];
				assert(r);
				if (p->x.kids[i]->x.registered && r->x.regnode->set == n
				&& r->x.regnode->mask&mask)
					spillr(r, here);
			}
	}
}
static void dumpregs(char *msg, char *a, char *b) {
	fprint(stderr, msg, a, b);
	fprint(stderr, "(free[0]=%x)\n", freemask[0]);
	fprint(stderr, "(free[1]=%x)\n", freemask[1]);
}

int getregnum(Node p) {
	assert(p && p->syms[RX] && p->syms[RX]->x.regnode);
	return p->syms[RX]->x.regnode->number;
}


unsigned regloc(Symbol p) {
	assert(p && p->sclass == REGISTER && p->sclass == REGISTER && p->x.regnode);
	return p->x.regnode->set<<8 | p->x.regnode->number;
}

