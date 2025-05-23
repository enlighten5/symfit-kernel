/* SPDX-License-Identifier: GPL-2.0-or-later */
/*
 * Helper file for declaring TCG helper functions.
 * This one expands generation functions for tcg opcodes.
 * Define HELPER_H for the header file to be expanded,
 * and static inline to change from global file scope.
 */

#include "tcg/tcg.h"
#include "tcg/helper-info.h"
#include "exec/helper-head.h"

#define DEF_HELPER_FLAGS_0(name, flags, ret)                            \
extern TCGHelperInfo glue(helper_info_, name);                          \
static inline void glue(gen_helper_, name)(dh_retvar_decl0(ret))        \
{                                                                       \
    tcg_gen_call0(&glue(helper_info_, name), dh_retvar(ret));           \
}

#define DEF_HELPER_FLAGS_1(name, flags, ret, t1)                        \
extern TCGHelperInfo glue(helper_info_, name);                          \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)          \
    dh_arg_decl(t1, 1))                                                 \
{                                                                       \
    tcg_gen_call1(&glue(helper_info_, name), dh_retvar(ret),            \
                  dh_arg(t1, 1));                                       \
}

#define DEF_HELPER_FLAGS_2(name, flags, ret, t1, t2)                    \
extern TCGHelperInfo glue(helper_info_, name);                          \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)          \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2))                             \
{                                                                       \
    tcg_gen_call2(&glue(helper_info_, name), dh_retvar(ret),            \
                  dh_arg(t1, 1), dh_arg(t2, 2));                        \
}

#define DEF_HELPER_FLAGS_3(name, flags, ret, t1, t2, t3)                \
extern TCGHelperInfo glue(helper_info_, name);                          \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)          \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2), dh_arg_decl(t3, 3))         \
{                                                                       \
    tcg_gen_call3(&glue(helper_info_, name), dh_retvar(ret),            \
                  dh_arg(t1, 1), dh_arg(t2, 2), dh_arg(t3, 3));         \
}

#define DEF_HELPER_FLAGS_4(name, flags, ret, t1, t2, t3, t4)            \
extern TCGHelperInfo glue(helper_info_, name);                          \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)          \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2),                             \
    dh_arg_decl(t3, 3), dh_arg_decl(t4, 4))                             \
{                                                                       \
    tcg_gen_call4(&glue(helper_info_, name), dh_retvar(ret),            \
                  dh_arg(t1, 1), dh_arg(t2, 2),                         \
                  dh_arg(t3, 3), dh_arg(t4, 4));                        \
}

#define DEF_HELPER_FLAGS_5(name, flags, ret, t1, t2, t3, t4, t5)        \
extern TCGHelperInfo glue(helper_info_, name);                          \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)          \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2), dh_arg_decl(t3, 3),         \
    dh_arg_decl(t4, 4), dh_arg_decl(t5, 5))                             \
{                                                                       \
    tcg_gen_call5(&glue(helper_info_, name), dh_retvar(ret),            \
                  dh_arg(t1, 1), dh_arg(t2, 2), dh_arg(t3, 3),          \
                  dh_arg(t4, 4), dh_arg(t5, 5));                        \
}

#define DEF_HELPER_FLAGS_6(name, flags, ret, t1, t2, t3, t4, t5, t6)    \
extern TCGHelperInfo glue(helper_info_, name);                          \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)          \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2), dh_arg_decl(t3, 3),         \
    dh_arg_decl(t4, 4), dh_arg_decl(t5, 5), dh_arg_decl(t6, 6))         \
{                                                                       \
    tcg_gen_call6(&glue(helper_info_, name), dh_retvar(ret),            \
                  dh_arg(t1, 1), dh_arg(t2, 2), dh_arg(t3, 3),          \
                  dh_arg(t4, 4), dh_arg(t5, 5), dh_arg(t6, 6));         \
}

#define DEF_HELPER_FLAGS_7(name, flags, ret, t1, t2, t3, t4, t5, t6, t7)\
extern TCGHelperInfo glue(helper_info_, name);                          \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)          \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2), dh_arg_decl(t3, 3),         \
    dh_arg_decl(t4, 4), dh_arg_decl(t5, 5), dh_arg_decl(t6, 6),         \
    dh_arg_decl(t7, 7))                                                 \
{                                                                       \
    tcg_gen_call7(&glue(helper_info_, name), dh_retvar(ret),            \
                  dh_arg(t1, 1), dh_arg(t2, 2), dh_arg(t3, 3),          \
                  dh_arg(t4, 4), dh_arg(t5, 5), dh_arg(t6, 6),          \
                  dh_arg(t7, 7));                                       \
}

#define DEF_HELPER_FLAGS_8(name, flags, ret, t1, t2, t3, t4, t5, t6, t7, \
                           t8)                                           \
extern TCGHelperInfo glue(helper_info_, name);                           \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)           \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2), dh_arg_decl(t3, 3),          \
    dh_arg_decl(t4, 4), dh_arg_decl(t5, 5), dh_arg_decl(t6, 6),          \
    dh_arg_decl(t7, 7), dh_arg_decl(t8, 8))                              \
{                                                                        \
    tcg_gen_call8(&glue(helper_info_, name), dh_retvar(ret),             \
                  dh_arg(t1, 1), dh_arg(t2, 2), dh_arg(t3, 3),           \
                  dh_arg(t4, 4), dh_arg(t5, 5), dh_arg(t6, 6),           \
                  dh_arg(t7, 7), dh_arg(t8, 8));                         \
}

#define DEF_HELPER_FLAGS_9(name, flags, ret, t1, t2, t3, t4, t5, t6, t7, \
                           t8, t9)                                       \
extern TCGHelperInfo glue(helper_info_, name);                           \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)           \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2), dh_arg_decl(t3, 3),          \
    dh_arg_decl(t4, 4), dh_arg_decl(t5, 5), dh_arg_decl(t6, 6),          \
    dh_arg_decl(t7, 7), dh_arg_decl(t8, 8), dh_arg_decl(t9, 9))          \
{                                                                        \
    tcg_gen_call9(&glue(helper_info_, name), dh_retvar(ret),             \
                  dh_arg(t1, 1), dh_arg(t2, 2), dh_arg(t3, 3),           \
                  dh_arg(t4, 4), dh_arg(t5, 5), dh_arg(t6, 6),           \
                  dh_arg(t7, 7), dh_arg(t8, 8), dh_arg(t9, 9));          \
}

#define DEF_HELPER_FLAGS_10(name, flags, ret, t1, t2, t3, t4, t5, t6, t7, \
                           t8, t9, t10)                                   \
extern TCGHelperInfo glue(helper_info_, name);                            \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)            \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2), dh_arg_decl(t3, 3),           \
    dh_arg_decl(t4, 4), dh_arg_decl(t5, 5), dh_arg_decl(t6, 6),           \
    dh_arg_decl(t7, 7), dh_arg_decl(t8, 8), dh_arg_decl(t9, 9),           \
    dh_arg_decl(t10, 10))                                                 \
{                                                                         \
    tcg_gen_call10(&glue(helper_info_, name), dh_retvar(ret),             \
                  dh_arg(t1, 1), dh_arg(t2, 2), dh_arg(t3, 3),            \
                  dh_arg(t4, 4), dh_arg(t5, 5), dh_arg(t6, 6),            \
                  dh_arg(t7, 7), dh_arg(t8, 8), dh_arg(t9, 9),            \
                  dh_arg(t10, 10));                                       \
}

#define DEF_HELPER_FLAGS_11(name, flags, ret, t1, t2, t3, t4, t5, t6, t7, \
                           t8, t9, t10, t11)                              \
extern TCGHelperInfo glue(helper_info_, name);                            \
static inline void glue(gen_helper_, name)(dh_retvar_decl(ret)            \
    dh_arg_decl(t1, 1), dh_arg_decl(t2, 2), dh_arg_decl(t3, 3),           \
    dh_arg_decl(t4, 4), dh_arg_decl(t5, 5), dh_arg_decl(t6, 6),           \
    dh_arg_decl(t7, 7), dh_arg_decl(t8, 8), dh_arg_decl(t9, 9),           \
    dh_arg_decl(t10, 10), dh_arg_decl(t11, 11))                           \
{                                                                         \
    tcg_gen_call11(&glue(helper_info_, name), dh_retvar(ret),             \
                  dh_arg(t1, 1), dh_arg(t2, 2), dh_arg(t3, 3),            \
                  dh_arg(t4, 4), dh_arg(t5, 5), dh_arg(t6, 6),            \
                  dh_arg(t7, 7), dh_arg(t8, 8), dh_arg(t9, 9),            \
                  dh_arg(t10, 10), dh_arg(t11, 11));                      \
}

#include HELPER_H

#undef DEF_HELPER_FLAGS_0
#undef DEF_HELPER_FLAGS_1
#undef DEF_HELPER_FLAGS_2
#undef DEF_HELPER_FLAGS_3
#undef DEF_HELPER_FLAGS_4
#undef DEF_HELPER_FLAGS_5
#undef DEF_HELPER_FLAGS_6
#undef DEF_HELPER_FLAGS_7
#undef DEF_HELPER_FLAGS_8
#undef DEF_HELPER_FLAGS_9
#undef DEF_HELPER_FLAGS_10
#undef DEF_HELPER_FLAGS_11