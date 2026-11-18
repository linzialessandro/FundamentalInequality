/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreierDefect
public import Examples.PadicSqrtP

/-!
# Axiom audit for the worked examples

This file is deliberately not a library root. It only prints axiom dependencies
and can be compiled with

```
lake env lean Examples/Audit.lean
```

It must not appear among the `Examples` library roots in `lakefile.toml`.
-/

@[expose] public section

#print axioms ValuativeExtension.ramificationIdx_mul_inertiaDeg_le_finrank
#print axioms ValuativeExtension.fundamental_inequality
#print axioms ValuativeExtension.ramificationIdx_mul_ramificationIdx
#print axioms ValuativeExtension.inertiaDeg_mul_inertiaDeg
#print axioms ValuativeExtension.comp
#print axioms ValuativeExtension.instIsLocalHomInteger
#print axioms ValuativeExtension.instIsScalarTowerInteger
#print axioms ValuativeExtension.instNormalUnitsValueGroupWithZero
#print axioms ValuativeExtension.pow_ramificationIdx_le_mul_uniformizer
#print axioms ValuativeExtension.eventually_pow_mul_uniformizer_lt
#print axioms ValuativeExtension.exists_sub_val_lt
#print axioms ValuativeExtension.span_eq_top_of_completeSpace
#print axioms ValuativeExtension.ramificationIdx_mul_inertiaDeg_eq_finrank
#print axioms ArtinSchreier.polynomial
#print axioms ArtinSchreier.eval_polynomial
#print axioms ArtinSchreier.derivative_polynomial
#print axioms ArtinSchreier.separable
#print axioms ArtinSchreier.natDegree_polynomial
#print axioms ArtinSchreier.monic
#print axioms ArtinSchreier.primeCast
#print axioms ArtinSchreier.primeCast_pow
#print axioms ArtinSchreier.translated_root
#print axioms ArtinSchreier.translate_injective
#print axioms ArtinSchreier.roots_eq
#print axioms ArtinSchreier.splits_of_root
#print axioms ArtinSchreier.isRoot_iff
#print axioms ArtinSchreier.factorisation
#print axioms ArtinSchreier.irreducible_of_not_isRoot
#print axioms ArtinSchreierBridge.localInertiaDeg
#print axioms ArtinSchreierBridge.local_map_eq_algebraMap
#print axioms ArtinSchreierBridge.isLocalHom_of_compatible
#print axioms ArtinSchreierBridge.residueField_map_eq_of_local_map
#print axioms ArtinSchreierBridge.inertiaDeg_eq_of_local_map
#print axioms ValuativeRel.IsRankLeOne.of_finiteDimensional
#print axioms ValuativeRel.IsNontrivial.of_valuativeExtension
#print axioms ArtinSchreierBridge.absoluteValue_rpow
#print axioms ArtinSchreierBridge.absoluteValue_rpow_apply
#print axioms ArtinSchreierBridge.unique_valuativeRel_of_complete
#print axioms ArtinSchreierBridge.Extensions
#print axioms ArtinSchreierBridge.extensionWeight
#print axioms ArtinSchreierBridge.sum_eq_of_unique
#print axioms ArtinSchreierBridge.sum_le_finrank_of_unique
#print axioms ArtinSchreierBridge.sum_strict_of_unique_immediate
#print axioms ArtinSchreierBridge.extensionFintype_of_unique
#print axioms ArtinSchreierDefect.Base
#print axioms ArtinSchreierDefect.baseCharP
#print axioms ArtinSchreierDefect.Hull
#print axioms ArtinSchreierDefect.inverseT
#print axioms ArtinSchreierDefect.standardPolynomial
#print axioms ArtinSchreierDefect.baseValuativeRel
#print axioms ArtinSchreierDefect.inverseT_value
#print axioms ArtinSchreierDefect.exp_one_not_pth_power
#print axioms ArtinSchreierDefect.base_no_root
#print axioms ArtinSchreierDefect.hull_no_root
#print axioms ArtinSchreierDefect.standardPolynomial_irreducible
#print axioms ArtinSchreierDefect.extension_degree
#print axioms ArtinSchreierDefect.root_equation
#print axioms ArtinSchreierDefect.General.ramificationIdx_eq_one_of_pow_surjective
#print axioms ArtinSchreierDefect.General.concrete_ramificationIdx
#print axioms ArtinSchreierDefect.General.unique_extension
#print axioms ArtinSchreierDefect.General.extension_eq_spectral
#print axioms ArtinSchreierDefect.General.exists_levelOne_pow_polynomial
#print axioms ArtinSchreierDefect.General.integral_levelOne_polynomial_cong
#print axioms ArtinSchreierDefect.General.concrete_inertiaDeg
#print axioms ArtinSchreierDefect.General.sum_strict
#print axioms ArtinSchreierDefect.General.defect_quotient
#print axioms ArtinSchreierDefect.quadratic_irreducible
#print axioms ArtinSchreierDefect.QuadraticExtension
#print axioms ArtinSchreierDefect.quadratic_degree
#print axioms ArtinSchreierDefect.quadratic_root_equation
#print axioms ArtinSchreierDefect.finrankQuotient
#print axioms ArtinSchreierDefect.defect_of_immediate
#print axioms ArtinSchreierDefect.quadratic_defect_quotient
#print axioms ArtinSchreierDefect.Quadratic.Base
#print axioms ArtinSchreierDefect.Quadratic.Hull
#print axioms ArtinSchreierDefect.Quadratic.Extension
#print axioms ArtinSchreierDefect.Quadratic.inverseT
#print axioms ArtinSchreierDefect.Quadratic.baseRankOne
#print axioms ArtinSchreierDefect.Quadratic.baseNorm
#print axioms ArtinSchreierDefect.Quadratic.spectralValuation
#print axioms ArtinSchreierDefect.Quadratic.hullValuativeRel
#print axioms ArtinSchreierDefect.Quadratic.baseHullValuativeExtension
#print axioms ArtinSchreierDefect.Quadratic.extensionAlgebraic
#print axioms ArtinSchreierDefect.Quadratic.extensionValuativeRel
#print axioms ArtinSchreierDefect.Quadratic.hullExtensionValuativeExtension
#print axioms ArtinSchreierDefect.Quadratic.baseExtensionValuativeExtension
#print axioms ArtinSchreierDefect.Quadratic.ramificationIdx_eq_one_of_square_surjective
#print axioms ArtinSchreierDefect.Quadratic.extensionCharP
#print axioms ArtinSchreierDefect.Quadratic.extensionPerfect
#print axioms ArtinSchreierDefect.Quadratic.concrete_ramificationIdx
#print axioms ArtinSchreierDefect.Quadratic.pow_vle_pow_iff
#print axioms ArtinSchreierDefect.Quadratic.purelyInseparable_unique
#print axioms ArtinSchreierDefect.Quadratic.hullCharP
#print axioms ArtinSchreierDefect.Quadratic.hull_isPerfectClosure
#print axioms ArtinSchreierDefect.Quadratic.hull_unique
#print axioms ArtinSchreierDefect.Quadratic.instScalarTowerBaseHullExtension
#print axioms ArtinSchreierDefect.Quadratic.hullCompatible
#print axioms ArtinSchreierDefect.Quadratic.hullIsRankLeOne
#print axioms ArtinSchreierDefect.Quadratic.exp_one_ne_one
#print axioms ArtinSchreierDefect.Quadratic.baseIsNontrivial
#print axioms ArtinSchreierDefect.Quadratic.base_vle_iff_norm
#print axioms ArtinSchreierDefect.Quadratic.unique_extension
#print axioms ArtinSchreierDefect.Quadratic.exp_one_ne_one
#print axioms ArtinSchreierDefect.Quadratic.baseIsNontrivial
#print axioms ArtinSchreierDefect.Quadratic.base_vle_iff_norm
#print axioms ArtinSchreierDefect.Quadratic.extension_eq_spectral
#print axioms ArtinSchreierDefect.Quadratic.baseCompatible
#print axioms ArtinSchreierDefect.Quadratic.extensionCompatible
#print axioms ArtinSchreierDefect.Quadratic.hullPerfect
#print axioms ArtinSchreierDefect.Quadratic.IsLevelOne
#print axioms ArtinSchreierDefect.Quadratic.isLevelOne_zero
#print axioms ArtinSchreierDefect.Quadratic.isLevelOne_one
#print axioms ArtinSchreierDefect.Quadratic.isLevelOne_algebraMap
#print axioms ArtinSchreierDefect.Quadratic.isLevelOne_add
#print axioms ArtinSchreierDefect.Quadratic.isLevelOne_mul
#print axioms ArtinSchreierDefect.Quadratic.isLevelOne_inv
#print axioms ArtinSchreierDefect.Quadratic.exists_sqPow_in_base
#print axioms ArtinSchreierDefect.Quadratic.one_vlt_inverseT_base
#print axioms ArtinSchreierDefect.Quadratic.not_sq_veq_inverseT
#print axioms ArtinSchreierDefect.Quadratic.exists_invTRoot
#print axioms ArtinSchreierDefect.Quadratic.invTRoot
#print axioms ArtinSchreierDefect.Quadratic.invTRoot_sq
#print axioms ArtinSchreierDefect.Quadratic.isLevelOne_invTRoot
#print axioms ArtinSchreierDefect.Quadratic.invTRoot_ne_zero
#print axioms ArtinSchreierDefect.Quadratic.one_vlt_inverseT_hull
#print axioms ArtinSchreierDefect.Quadratic.one_vlt_invTRoot
#print axioms ArtinSchreierDefect.Quadratic.asRoot
#print axioms ArtinSchreierDefect.Quadratic.invTRootE
#print axioms ArtinSchreierDefect.Quadratic.invTRootE_ne_zero
#print axioms ArtinSchreierDefect.Quadratic.invTRootE_sq
#print axioms ArtinSchreierDefect.Quadratic.one_vlt_invTRootE
#print axioms ArtinSchreierDefect.Quadratic.root_sub_eq_invTRootE_sq
#print axioms ArtinSchreierDefect.Quadratic.asRoot_veq_invTRootE
#print axioms ArtinSchreierDefect.Quadratic.unitGen
#print axioms ArtinSchreierDefect.Quadratic.unitGen_mul_invTRootE
#print axioms ArtinSchreierDefect.Quadratic.unitGen_veq_one
#print axioms ArtinSchreierDefect.Quadratic.unitGen_sq_sub_one
#print axioms ArtinSchreierDefect.Quadratic.one_eq_neg_one_extension
#print axioms ArtinSchreierDefect.Quadratic.unitGen_sub_one_sq
#print axioms ArtinSchreierDefect.Quadratic.unitGen_sub_one_vlt_one
#print axioms ArtinSchreierDefect.Quadratic.veq_of_algebraMap_base
#print axioms ArtinSchreierDefect.Quadratic.veq_of_algebraMap_hull
#print axioms ArtinSchreierDefect.Quadratic.not_pow4_veq_inverseT_of_levelOne
#print axioms ArtinSchreierDefect.Quadratic.not_veq_unitGen_sub_one_of_levelOne
#print axioms ArtinSchreierDefect.Quadratic.not_mul_unitGen_sub_one_veq_one
#print axioms ArtinSchreierDefect.Quadratic.exists_root_coords
#print axioms ArtinSchreierDefect.Quadratic.exists_unitGen_coords
#print axioms ArtinSchreierDefect.Quadratic.unitGen_pow_levelOne
#print axioms ArtinSchreierDefect.Quadratic.exists_levelOne_pow_coords
#print axioms ArtinSchreierDefect.Quadratic.vle_one_of_algebraMap
#print axioms ArtinSchreierDefect.Quadratic.integral_levelOne_cong
#print axioms ArtinSchreierDefect.Quadratic.exists_pow_root_of_perfect
#print axioms ArtinSchreierDefect.Quadratic.hullIntegerCharP
#print axioms ArtinSchreierDefect.Quadratic.extensionIntegerCharP
#print axioms ArtinSchreierDefect.Quadratic.residueCharP_of_charP
#print axioms ArtinSchreierDefect.Quadratic.hullResidueCharP
#print axioms ArtinSchreierDefect.Quadratic.extensionResidueCharP
#print axioms ArtinSchreierDefect.Quadratic.hullResiduePerfect
#print axioms ArtinSchreierDefect.Quadratic.concrete_inertiaDeg
#print axioms ArtinSchreierDefect.Quadratic.quadratic_sum_strict
#print axioms PadicSqrtP.integerPolynomial_isEisenstein
#print axioms PadicSqrtP.polynomial_irreducible
#print axioms PadicSqrtP.finrank_eq_two
#print axioms PadicSqrtP.root_sq
#print axioms PadicSqrtP.baseExtensionValuativeExtension
#print axioms PadicSqrtP.unique_extension
#print axioms PadicSqrtP.extension_eq_spectral
#print axioms PadicSqrtP.sqrtP_value_not_mem_range
#print axioms PadicSqrtP.ramificationIdx_eq_two
#print axioms PadicSqrtP.inertiaDeg_eq_one
#print axioms PadicSqrtP.ramificationIdx_mul_inertiaDeg_eq_finrank
#print axioms PadicSqrtP.stage3_ramificationIdx_mul_inertiaDeg_eq_finrank
#print axioms PadicSqrtP.inertiaDeg_eq_one_from_stage3
