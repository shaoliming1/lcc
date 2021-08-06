//
// Created by bytedance on 2021/8/4.
//
#include "c.h"


static void defsymbol(Symbol p) {
    if (p->scope >= LOCAL && p->sclass == STATIC)
        p->x.name = stringf("%s.%d", p->name, genlabel(1));
    else if (p->generated)
        p->x.name = stringf(".LC%s", p->name);
    else if (p->scope == GLOBAL || p->sclass == EXTERN)
        p->x.name = stringf("%s", p->name);
    else
        p->x.name = p->name;
}

static void function(Symbol f, Symbol caller[], Symbol callee[], int n){
    if(f->u.f.ncalls){
        // 非leaf函数会比leaf函数多保存一个leaf函数
        print("push {r11, lr}\n");
        print("add r11, sp, #0\n");
        print("sub sp, sp, #16");
    }else{
        print("push {r11}\n");
        print("add r11, sp, #0\n");
        print("sub sp sp #12\n");
    }
}