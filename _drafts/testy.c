// Lean compiler output
// Module: testy
// Imports: Init
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
LEAN_EXPORT lean_object* l_myadd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_myadd2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_myadd2(uint64_t, uint64_t);
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint64_t myadd(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_myadd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = myadd(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_myadd2(uint64_t x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; 
x_3 = lean_uint64_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_myadd2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_myadd2(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_testy(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
