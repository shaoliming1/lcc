/* $Id$ */
// 收集了所有与机器相关的数据和例程
// 这些数据和函数都是编译后端的与目标
// 无关的部分生成代码时所需要的
// 对于编译后端来说,该类型对于目标无关的意义,
// 就如同interface对于编译前端的意义一样.
typedef struct {
	// max_unaligined_load给出了目标机器按非对齐方式可以存取的最大字节数
	//
	unsigned char max_unaligned_load;
	Symbol (*rmap)(int);

	// blkfetch从给定单元取数到寄存器的代码
	// blkfetch产生的代码首先将寄存器reg的值与
	// 偏移常量off相加到一个地址，然后从该地址
	// 单元中取出size字节的数据，载入寄存器tmp中。
	void (*blkfetch)(int size, int off, int reg, int tmp);
	// blkstore产生代码, 将某个寄存器数据存储到给定单元
	// blkstore产生的代码将size字节的数据从寄存器tmp中存储到给定单元
	// , 单元地址由寄存器reg与偏移量off相加得到.
	void (*blkstore)(int size, int off, int reg, int tmp);
	// blkloop产生一个循环复制内存中size字节的数据.
	// 源地址为寄存器sreg于偏移量soff相加之和, 
	// 目标地址为寄存器dreg与偏移量doff相加之和
	// tmp是一个由三个整数组成的数组, 表示实现该循环可用
	// 的寄存器
	void (*blkloop)(int dreg, int doff,
	                 int sreg, int soff,
	                 int size, int tmps[]);
	void (*_label)(Node);
	int (*_rule)(void*, int);
	short **_nts;
	void (*_kids)(Node, int, Node*);
	char **_string;
	char **_templates;
	char *_isinstruction;
	char **_ntname;
	// emit2产生那些不能通过产生简单的指令模板来处理的指令,
	// 每种机器以及许多调用约定(calling convention), 都包含一些没有emit2的转义
	// 子句就很难处理的特性.
	void (*emit2)(Node);
	// doarg计算分配给下一个参数的寄存器或者栈单元
	// 编译后端要对树组成的森林进行多次扫描.第一遍扫描时, 每遇到ARG节点就调用x.doarg
	// lcc需要doarg来产生符合复杂的调用约定的代码
	void (*doarg)(Node);
	// target标记那些必须送到特定寄存器中计算的树节点
	// 例如:返回值必须存放到返回寄存器中, 还有一些机器需要把除数及余数送到固定寄存器中,对于这些节点的标记
	// 是通过对节点的sysms[RX]赋值来实现的,sysms[RX]登记了存放该节点的计算结果的寄存器.
	void (*target)(Node);
	// 使被某条给定指令破坏的所有寄存器溢出到存储器, 在以后需要这些值的时候重新加载
	// 该过程通常根据节点的操作码进行分别处理. 每种情况都要调用spill, spill是一个与机器无关的过程,它保存
	// 或者恢复指定的寄存器集合
	void (*clobber)(Node);
} Xinterface;
extern int     askregvar(Symbol, Symbol);
extern void    blkcopy(int, int, int, int, int, int[]);
extern unsigned emitasm(Node, int);
extern int     getregnum(Node);
extern int     mayrecalc(Node);
extern int     mkactual(int, int);
extern void    mkauto(Symbol);
extern Symbol  mkreg(char *, int, int, int);
extern Symbol  mkwildcard(Symbol *);
extern int     move(Node);
extern int     notarget(Node);
extern void    parseflags(int, char **);
extern int     range(Node, int, int);
extern unsigned regloc(Symbol);  /* omit */
extern void    rtarget(Node, int, Symbol);
extern void    setreg(Node, Symbol);
// 保存或者恢复指定的寄存器集合
extern void    spill(unsigned, int, Node);
extern int     widens(Node);

extern int      argoffset, maxargoffset;
extern int      bflag, dflag;
extern int      dalign, salign;
extern int      framesize;
extern unsigned freemask[], usedmask[];
extern int      offset, maxoffset;
extern int      swap;
extern unsigned tmask[], vmask[];
// 节点扩张
// 代码生成器的主要操作就是对编译器前端的节点进行注释扩展
// 注释记录了诸如指令选择和寄存器分配数据.
// 在node结构体中扩展的域被命名为x并具有Xnode类型
typedef struct {
	unsigned listed:1;
	unsigned registered:1;
	unsigned emitted:1;
	unsigned copy:1;
	unsigned equatable:1;
	unsigned spills:1;
	unsigned mayrecalc:1;
	// 指令选择器标识了可以实现该节点的指令和寻址模式, 并且使用x.state来记录结果
	// 第14章将详细介绍x.state域指向的结构体所表示的信息
	void *state;
	// 由于指令的实现需要寄存器,但是那些通过地址分配实现的节点则不需要寄存器,
	// 所以区分这两种类型十分有用, 指令选择器必须标识他们.编译后端使用x.inst来标识通过指令实现的节点
	// 如果节点是通过指令实现的, 则x.inst非零, 该值可以帮助标识指令.
	short inst;
	// kids域存放编译后端实现的指令树
	Node kids[3];
	Node prev, next;
	// 寄存器分配器使用x.prevuse来链接读写相同的临时单元的节点
	Node prevuse;
	// argno域中记录参数的数目处理参数传递
	short argno;
} Xnode;
typedef struct {
	Symbol vbl;
	short set;
	short number;
	unsigned mask;
} *Regnode;
enum { IREG=0, FREG=1 };
typedef struct {
	char *name;
	unsigned int eaddr;  /* omit */
	int offset;
	Node lastuse;
	int usecount;
	Regnode regnode;
	Symbol *wildcard;
} Xsymbol;
enum { RX=2 };
typedef struct {
	int offset;
	unsigned freemask[2];
} Env;

#define LBURG_MAX SHRT_MAX

enum { VREG=(44<<4) };

/* Exported for the front end */
extern void             blockbeg(Env *);
extern void             blockend(Env *);
extern void             emit(Node);
extern Node             gen(Node);

extern unsigned         emitbin(Node, int);

#ifdef NDEBUG
#define debug(x) (void)0
#else
#define debug(x) (void)(dflag&&((x),0))
#endif
