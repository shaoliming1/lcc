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