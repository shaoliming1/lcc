cmake_minimum_required(VERSION 3.16)
# set the projec t name and version number
project(rcc C )

set(CMAKE_C_STANDARD 99)
include_directories (${rcc_SOURCE_DIR}/src)
add_executable(rcc
        ${rcc_SOURCE_DIR}/src/main.c
        ${rcc_SOURCE_DIR}/src/alloc.c
        ${rcc_SOURCE_DIR}/src/bind.c
        ${rcc_SOURCE_DIR}/src/bytecode.c
        ${rcc_SOURCE_DIR}/src/dag.c
        ${rcc_SOURCE_DIR}/src/decl.c
        ${rcc_SOURCE_DIR}/src/enode.c
        ${rcc_SOURCE_DIR}/src/error.c
        ${rcc_SOURCE_DIR}/src/event.c
        ${rcc_SOURCE_DIR}/src/expr.c
        ${rcc_SOURCE_DIR}/src/gen.c
        ${rcc_SOURCE_DIR}/src/init.c
        ${rcc_SOURCE_DIR}/src/inits.c
        ${rcc_SOURCE_DIR}/src/input.c
        ${rcc_SOURCE_DIR}/src/lex.c
        ${rcc_SOURCE_DIR}/src/list.c
        ${rcc_SOURCE_DIR}/src/main.c
        ${rcc_SOURCE_DIR}/src/null.c
        ${rcc_SOURCE_DIR}/src/output.c
        ${rcc_SOURCE_DIR}/src/prof.c
        ${rcc_SOURCE_DIR}/src/profio.c
        ${rcc_SOURCE_DIR}/src/simp.c
        ${rcc_SOURCE_DIR}/src/stab.c
        ${rcc_SOURCE_DIR}/src/stmt.c
        ${rcc_SOURCE_DIR}/src/string.c
        ${rcc_SOURCE_DIR}/src/sym.c
        ${rcc_SOURCE_DIR}/src/symbolic.c
        ${rcc_SOURCE_DIR}/src/trace.c
        ${rcc_SOURCE_DIR}/src/tree.c
        ${rcc_SOURCE_DIR}/src/types.c
        ${rcc_SOURCE_DIR}/src/alpha.c
        ${rcc_SOURCE_DIR}/src/mips.c
        ${rcc_SOURCE_DIR}/src/dagcheck.c
        ${rcc_SOURCE_DIR}/src/sparc.c
        ${rcc_SOURCE_DIR}/src/x86.c
        ${rcc_SOURCE_DIR}/src/x86linux.c
        )

add_executable(ops
        ${rcc_SOURCE_DIR}/etc/ops.c
        )