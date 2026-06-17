// Lean compiler output
// Module: FundamentalInequality
// Imports: public import Init public meta import Init public import Mathlib.RingTheory.Valuation.Basic public import Mathlib.RingTheory.Valuation.ValuationRing public import Mathlib.RingTheory.Valuation.Extension public import Mathlib.RingTheory.Valuation.ValuationSubring public import Mathlib.Algebra.Order.Group.Defs public import Mathlib.GroupTheory.Index public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic public import Mathlib.RingTheory.LocalRing.ResidueField.Basic public import Mathlib.FieldTheory.Tower public import Mathlib.FieldTheory.Separable public import Mathlib.LinearAlgebra.Basis.Basic public import Mathlib.LinearAlgebra.Dimension.Free public import Mathlib.LinearAlgebra.Dimension.Finrank public import Mathlib.LinearAlgebra.Dimension.Finite
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_Valuation_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_Valuation_ValuationRing(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_Valuation_Extension(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_Valuation_ValuationSubring(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Order_Group_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_GroupTheory_Index(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_IntegralClosure_IsIntegral_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_LocalRing_ResidueField_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_FieldTheory_Tower(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_FieldTheory_Separable(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Basis_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Dimension_Free(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Dimension_Finrank(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Dimension_Finite(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_FundamentalInequality_FundamentalInequality(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_Valuation_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_Valuation_ValuationRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_Valuation_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_Valuation_ValuationSubring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Order_Group_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_GroupTheory_Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_IntegralClosure_IsIntegral_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_LocalRing_ResidueField_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_FieldTheory_Tower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_FieldTheory_Separable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Basis_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Dimension_Free(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Dimension_Finrank(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Dimension_Finite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
