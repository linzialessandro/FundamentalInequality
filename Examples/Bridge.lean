/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import FundamentalInequality

/-!
# Compatibility of local residue-field maps with Linzi's residue degree

This file compares an explicitly supplied compatible local map of valuation rings
with the canonical structure map used by `ValuativeExtension.residueDegree`.
The ramification index is not redefined: later example files use
`ValuativeExtension.ramificationIndex` directly.
-/

@[expose] public section
noncomputable section
open ValuativeRel
open scoped ValuativeRel

namespace ArtinSchreierBridge

/-- Residue degree computed from an arbitrary compatible local map of valuation rings. -/
def localResidueDegree {K L : Type*} [Field K] [Field L]
    [ValuativeRel K] [ValuativeRel L]
    (ι : 𝒪[K] →+* 𝒪[L]) [IsLocalHom ι] : ℕ :=
  letI := (IsLocalRing.ResidueField.map ι).toAlgebra
  Module.finrank (IsLocalRing.ResidueField 𝒪[K])
    (IsLocalRing.ResidueField 𝒪[L])

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [ValuativeExtension K L]

/-- Compatibility means equality with the field embedding after inclusion of
valuation rings. The ambient `ValuativeExtension` supplies valuation compatibility. -/
theorem local_map_eq_algebraMap (ι : 𝒪[K] →+* 𝒪[L])
    (hι : ∀ x : 𝒪[K], (ι x : L) = algebraMap K L (x : K)) :
    ι = algebraMap 𝒪[K] 𝒪[L] := by
  ext x
  exact hι x

/-- Locality follows from the restriction condition; it need not be an extra axiom. -/
theorem isLocalHom_of_compatible (ι : 𝒪[K] →+* 𝒪[L])
    (hι : ∀ x : 𝒪[K], (ι x : L) = algebraMap K L (x : K)) :
    IsLocalHom ι := by
  rw [local_map_eq_algebraMap ι hι]
  exact ValuativeExtension.instIsLocalHom_integer K L

/-- The actual residue-field maps agree, including their induced scalar actions. -/
theorem residueField_map_eq_of_local_map (ι : 𝒪[K] →+* 𝒪[L])
    [IsLocalHom ι]
    (hι : ∀ x : 𝒪[K], (ι x : L) = algebraMap K L (x : K)) :
    IsLocalRing.ResidueField.map ι = algebraMap 𝓀[K] 𝓀[L] := by
  have h := local_map_eq_algebraMap ι hι
  subst ι
  rfl

/-- The previous finrank via a compatible local map is Linzi's residue degree. -/
theorem residueDegree_eq_of_local_map (ι : 𝒪[K] →+* 𝒪[L])
    [IsLocalHom ι]
    (hι : ∀ x : 𝒪[K], (ι x : L) = algebraMap K L (x : K)) :
    localResidueDegree ι = ValuativeExtension.residueDegree K L := by
  have h := local_map_eq_algebraMap ι hι
  subst ι
  unfold localResidueDegree ValuativeExtension.residueDegree
  congr 1
  apply Module.ext'
  intro r x
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  simp only [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_residue, ← map_mul]
  change IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[L])
      (IsLocalRing.residue 𝒪[K] r) * IsLocalRing.residue 𝒪[L] x = _
  rw [IsLocalRing.ResidueField.map_residue, ← map_mul]

end ArtinSchreierBridge
