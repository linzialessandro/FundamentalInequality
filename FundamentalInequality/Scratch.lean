import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

open Valuation

section Scratch

variable {K : Type*} [Field K] {ΓK : Type*} [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK)
variable {L : Type*} [Field L] {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL]
    (vL : Valuation L ΓL)
variable [Algebra K L] [vK.HasExtension vL]

variable [FiniteDimensional K L]

noncomputable def e := Valuation.ramificationIndex vK vL
noncomputable def f := Valuation.residueDegree vK vL

variable (Kv := IsLocalRing.ResidueField vK.valuationSubring)
variable (Lv := IsLocalRing.ResidueField vL.valuationSubring)

lemma test_residue_map (x : vK.valuationSubring) (x_L : vL.valuationSubring)
    (h : (x_L : L) = algebraMap K L (x : K)) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring) x_L =
    algebraMap (IsLocalRing.ResidueField vK.valuationSubring) (IsLocalRing.ResidueField vL.valuationSubring)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal vK.valuationSubring) x) := by
  sorry

end Scratch
