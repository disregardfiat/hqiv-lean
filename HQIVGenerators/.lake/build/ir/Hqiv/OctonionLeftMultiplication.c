// Lean compiler output
// Module: Hqiv.OctonionLeftMultiplication
// Imports: public import Init public import Mathlib.Data.Real.Basic public import Mathlib.Data.Fin.Basic public import Mathlib.LinearAlgebra.Matrix.Defs public import Mathlib.LinearAlgebra.Matrix.Notation
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__24;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__39;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__17;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__2;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__4;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__3;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__40;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__0(lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__11;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__6;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__5;
lean_object* l_Fin_cases___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__1;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__0;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__20;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__7;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__16;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__22;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__0;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__3;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2(lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__6;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__19;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__3;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__0;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__34;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6(lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__14;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__19;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__18;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__1;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__33;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__2;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__18;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__4;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__30;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__32;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3(lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__3;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__38;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__30;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__3;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__1___boxed(lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__12;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__23;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__23;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__34;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__37;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__29;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__5;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__43;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__36;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__13;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__7;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__4;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__0;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__1;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7(lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__9;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__3;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__0___boxed(lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__51;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__28;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5(lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__44;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__31;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__4;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__3;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__27;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__4;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__38;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__10;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__2;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__1;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__1(lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__52;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__6;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__2;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1(lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__22;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__16;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__35;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__5;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__29;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__1;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__48;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__8;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__2;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__8;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__21;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__40;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__32;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__36;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__54;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__7;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__17;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__6;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__13;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__4;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__46;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__28;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__0;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__7;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__45;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__25;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__5;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__41;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__11;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__5;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__50;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__5;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__35;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__37;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__20;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__6;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17(lean_object*, lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__7;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__47;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__5;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__14;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__42;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2(lean_object*, lean_object*, lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__21;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__0;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__6;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__2;
lean_object* lp_mathlib_Equiv_refl(lean_object*);
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__26;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__15;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__31;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__9;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__4;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__15;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__1;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__7;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__6;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__2;
static lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__10;
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__1(lean_object* x_1) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Fin_cases___redArg(x_1, x_2, x_3);
x_6 = lean_apply_1(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Fin_cases___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lp_mathlib_Equiv_refl(lean_box(0));
return x_1;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__2;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__3;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__4;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__5;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__6;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__7;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__8;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__7;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__10;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__11;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__5;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__14;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__15;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__16;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__17;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__3;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__19;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__20;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__21;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__22;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__23;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__24;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__9;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_2 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__6;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__28;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__29;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__30;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__13;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__31;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__32;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__18;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__4;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__34;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__35;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__36;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__37;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__38;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__33;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__40;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__2;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__42;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__43;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__44;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__45;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__46;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__47;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__48;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__41;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__50;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__8;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__52;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__51;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__54;
x_6 = lean_apply_3(x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__6;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__0;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__1;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__2;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__4;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__4;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__5;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__6;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__7;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__8;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__2;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__10;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__11;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__12;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__13;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__14;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__15;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__16;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__18;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__3;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__5;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__20;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__21;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__22;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__23;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__19;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__25;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__9;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__3;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__27;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__28;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__29;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__30;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__31;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__32;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__26;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__34;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__35;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__17;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__7;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__17___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__37;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__38;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__36;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__39;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__40;
x_6 = lean_apply_3(x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__18;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__0;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__2;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__3;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__4;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__5;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__6;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__31;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__7;
x_6 = lean_apply_3(x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__31;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__0;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__39;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__2;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__3;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__17;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__4;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__5;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__9;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__6;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__7;
x_6 = lean_apply_3(x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__8;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1279875089____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__0;
x_2 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__2___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__32;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__2;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__1;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__3;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__4;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__5;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__6;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__7;
x_6 = lean_apply_3(x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__18;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__0;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__3;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__2;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__3;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__4;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__17;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__5;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__6;
x_6 = lean_apply_3(x_4, x_5, x_1, x_2);
return x_6;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__0;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__1;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__1;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__2;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__3;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__3;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__4;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__5;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__6;
x_2 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49;
x_3 = lean_alloc_closure((void*)(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___lam__12___boxed), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_HQIVGenerators_Hqiv_octonionLeftMul__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__7;
x_6 = lean_apply_3(x_4, x_5, x_1, x_2);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Real_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fin_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Matrix_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Matrix_Notation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HQIVGenerators_Hqiv_OctonionLeftMultiplication(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Real_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Matrix_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Matrix_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__0);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__1);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__2 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__2();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__2);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__3 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__3();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__3);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__4 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__4();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__4);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__5 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__5();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__5);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__6 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__6();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__6);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__7 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__7();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__7);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__8 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__8();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__8);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__9 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__9();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__9);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__10 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__10();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__10);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__11 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__11();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__11);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__12);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__13 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__13();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__13);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__14 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__14();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__14);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__15 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__15();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__15);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__16 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__16();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__16);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__17 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__17();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__17);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__18 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__18();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__18);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__19 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__19();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__19);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__20 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__20();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__20);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__21 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__21();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__21);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__22 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__22();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__22);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__23 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__23();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__23);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__24 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__24();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__24);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__25);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__26);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__27);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__28 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__28();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__28);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__29 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__29();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__29);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__30 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__30();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__30);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__31 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__31();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__31);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__32 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__32();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__32);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__33 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__33();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__33);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__34 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__34();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__34);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__35 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__35();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__35);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__36 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__36();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__36);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__37 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__37();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__37);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__38 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__38();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__38);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__39);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__40 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__40();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__40);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__41 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__41();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__41);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__42 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__42();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__42);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__43 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__43();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__43);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__44 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__44();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__44);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__45 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__45();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__45);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__46 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__46();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__46);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__47 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__47();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__47);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__48 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__48();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__48);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__49);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__50 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__50();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__50);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__51 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__51();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__51);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__52 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__52();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__52);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__53);
lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__54 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__54();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__1___closed__54);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__0 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__0();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__0);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__1 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__1();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__1);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__2 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__2();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__2);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__3 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__3();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__3);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__4 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__4();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__4);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__5 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__5();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__5);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__6 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__6();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__6);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__7 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__7();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__7);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__8 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__8();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__8);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__9 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__9();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__9);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__10 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__10();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__10);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__11 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__11();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__11);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__12 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__12();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__12);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__13 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__13();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__13);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__14 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__14();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__14);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__15 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__15();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__15);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__16 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__16();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__16);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__17 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__17();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__17);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__18 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__18();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__18);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__19 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__19();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__19);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__20 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__20();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__20);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__21 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__21();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__21);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__22 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__22();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__22);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__23 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__23();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__23);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__24);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__25 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__25();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__25);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__26 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__26();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__26);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__27 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__27();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__27);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__28 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__28();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__28);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__29 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__29();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__29);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__30 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__30();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__30);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__31 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__31();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__31);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__32 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__32();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__32);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__33);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__34 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__34();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__34);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__35 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__35();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__35);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__36 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__36();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__36);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__37 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__37();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__37);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__38 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__38();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__38);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__39 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__39();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__39);
lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__40 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__40();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__2___closed__40);
lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__0 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__0();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__0);
lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__1 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__1();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__1);
lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__2 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__2();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__2);
lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__3 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__3();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__3);
lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__4 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__4();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__4);
lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__5 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__5();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__5);
lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__6 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__6();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__6);
lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__7 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__7();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__3___closed__7);
lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__0 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__0();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__0);
lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__1 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__1();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__1);
lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__2 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__2();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__2);
lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__3 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__3();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__3);
lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__4 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__4();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__4);
lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__5 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__5();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__5);
lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__6 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__6();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__6);
lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__7 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__7();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__4___closed__7);
lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__0 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__0();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__0);
lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__1 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__1();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__1);
lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__2 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__2();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__2);
lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__3 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__3();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__3);
lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__4 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__4();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__4);
lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__5 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__5();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__5);
lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__6 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__6();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__6);
lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__7 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__7();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__5___closed__7);
lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__0 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__0();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__0);
lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__1 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__1();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__1);
lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__2 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__2();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__2);
lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__3 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__3();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__3);
lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__4 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__4();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__4);
lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__5 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__5();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__5);
lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__6 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__6();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__6___closed__6);
lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__0 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__0();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__0);
lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__1 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__1();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__1);
lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__2 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__2();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__2);
lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__3 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__3();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__3);
lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__4 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__4();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__4);
lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__5 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__5();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__5);
lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__6 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__6();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__6);
lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__7 = _init_lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__7();
lean_mark_persistent(lp_HQIVGenerators_Hqiv_octonionLeftMul__7___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
