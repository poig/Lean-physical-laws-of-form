// Lean compiler output
// Module: PhysicalLoF.Foundations.Existence
// Imports: public import Init public import PhysicalLoF.Foundations.Distinction public import PhysicalLoF.Foundations.Collapse
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_physical_x2dlaws_x2dof_x2dform_PhysicalLoF_Foundations_Distinction(uint8_t builtin);
lean_object* initialize_physical_x2dlaws_x2dof_x2dform_PhysicalLoF_Foundations_Collapse(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_physical_x2dlaws_x2dof_x2dform_PhysicalLoF_Foundations_Existence(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_physical_x2dlaws_x2dof_x2dform_PhysicalLoF_Foundations_Distinction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_physical_x2dlaws_x2dof_x2dform_PhysicalLoF_Foundations_Collapse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
