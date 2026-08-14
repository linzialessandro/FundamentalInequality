/-
Copyright (c) 2026 Alessandro Linzi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Linzi
-/
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Ramification index, residue degree, and the fundamental inequality

This file defines the ramification index `e(w/v)` and residue degree `f(w/v)` of an
extension of valued fields `(L | K, w | v)`, and proves the simple fundamental
inequality

\[
  [L : K] \ge e(w/v)\, f(w/v)
\]

for a finite extension, including finiteness of `e` and `f`.

This is the single-extension form (Kuhlmann, Lemma 6.13). The Ostrowski sum over
all extensions of `v` to `L`, the characterisation of vs-defectless extensions
(`n = e f`), and the comparison with `Ideal.ramificationIdx` / `Ideal.inertiaDeg`
are left to later work.

## Main definitions

* `Valuation.residueDegree` : the inertia / residue degree `f(w/v) = [Lw : Kv]`.
* `Valuation.ramificationIndex` : the ramification index `e(w/v) = (wL : vK)`.

Both are `ℕ`, with the same convention as `Module.finrank` and `Subgroup.relIndex`:
an infinite value is recorded as `0`. Separate lemmas show they are positive
under `FiniteDimensional K L`.

## Main results

* `Valuation.residueDegree_self`, `Valuation.ramificationIndex_self` :
  the identity extension has `e = f = 1`.
* `Valuation.residueDegree_mul`, `Valuation.ramificationIndex_mul` :
  multiplicativity in towers (Kuhlmann, Lemma 6.16).
* `Valuation.residueDegree_pos`, `Valuation.ramificationIndex_ne_zero` :
  finiteness of `f` and `e` for a finite extension.
* `Valuation.exists_max_val_mul` : Kuhlmann, Lemma 6.12 (valuation independence).
* `Valuation.valuation_independence` : the same products are `K`-linearly independent.
* `Valuation.fundamental_inequality` : Kuhlmann, Lemma 6.13.

## Implementation notes

`HasExtension vK vL` only gives `vK.IsEquiv (vL.comap (algebraMap K L))`.
Equivalent valuations have isomorphic value groups and the same valuation ring,
but not definitionally the same `Γ`. The ramification index is therefore
computed entirely inside `Γ_Lˣ`:

```
valueGroup (vL.comap (algebraMap K L))   -- = vL(Kˣ) ≤ ΓLˣ
  |>.relIndex
    (valueGroup vL)                      -- = vL(Lˣ) ≤ ΓLˣ
```

Residue degree is the `finrank` of the residue fields of the two
`valuationSubring`s. `HasExtension` already supplies the algebra instances.

In the residue argument of Lemma 6.12, several scaled coefficients may have
nonzero residue. That is intended: the distinguished coordinate is `1`, so
residue-linear independence still implies that the combination is a unit.

## References

* F.-V. Kuhlmann, *Valued Fields*, Chapter 6, §6.3, Lemmas 6.12–6.13 and 6.16.
* N. Bourbaki, *Algèbre commutative*, Chapter VI.

## Tags

valuation, ramification index, residue degree, inertia degree,
fundamental inequality, valued field
-/

open Valuation Cardinal

noncomputable section

variable {K : Type*} [Field K] {ΓK : Type*} [LinearOrderedCommGroupWithZero ΓK]
  (vK : Valuation K ΓK)
variable {L : Type*} [Field L] {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL]
  (vL : Valuation L ΓL)
variable [Algebra K L]

/-! ### Definitions -/

/-- The residue degree (inertia degree) `f(w/v) = [Lw : Kv]` of an extension of
valued fields. This is `0` if the residue-field extension is infinite, matching
the `Module.finrank` convention. -/
def Valuation.residueDegree [vK.HasExtension vL] : ℕ :=
  Module.finrank
    (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

/-- The ramification index `e(w/v) = (wL : vK)` of an extension of valued fields.
It is the relative index of `vL(Kˣ)` in `vL(Lˣ)`, computed in `Γ_Lˣ` via
`comap` so that the definition is well-typed under `HasExtension` (equivalence
of valuations, not equality). This is `0` if the index is infinite, matching
the `Subgroup.relIndex` convention. -/
def Valuation.ramificationIndex [vK.HasExtension vL] : ℕ :=
  MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L)) |>.relIndex
    (MonoidWithZeroHom.valueGroup vL)

/-! ### Identity extension -/

/-- The residue degree of a valued field over itself is `1`. -/
theorem Valuation.residueDegree_self (v : Valuation K ΓK) :
    residueDegree v v = 1 :=
  CommSemiring.finrank_self _

/-- The ramification index of a valued field over itself is `1`. -/
theorem Valuation.ramificationIndex_self (v : Valuation K ΓK) :
    ramificationIndex v v = 1 := by
  unfold ramificationIndex
  simp only [Algebra.algebraMap_self, comap_id]
  exact Subgroup.relIndex_self _

/-- Restriction of a valuation along `K → L` is `HasExtension`-compatible. -/
instance Valuation.comap_hasExtension_self :
    (vL.comap (algebraMap K L)).HasExtension vL where
  val_isEquiv_comap := IsEquiv.refl

/-- `e(w/v)` depends only on `w` and the algebra map `K → L`, not on the
choice of representative of `v` in its `IsEquiv`-class. -/
theorem Valuation.ramificationIndex_eq_comap [vK.HasExtension vL] :
    ramificationIndex vK vL =
      ramificationIndex (vL.comap (algebraMap K L)) vL :=
  rfl

/-! ### Tower multiplicativity -/

variable {F : Type*} [Field F] {ΓF : Type*} [LinearOrderedCommGroupWithZero ΓF]
  (vF : Valuation F ΓF)
variable [Algebra K F] [Algebra F L] [IsScalarTower K F L]

/-- The two-step comap along `K → F → L` is `HasExtension`-compatible. -/
instance Valuation.comap_hasExtension_comap :
    (vL.comap (algebraMap K L)).HasExtension (vL.comap (algebraMap F L)) where
  val_isEquiv_comap := by
    -- `vL.comap (F → L)` is a valuation on `F`, so the `HasExtension` comap
    -- is along `algebraMap K F`.
    rw [← comap_comp, IsScalarTower.algebraMap_eq K F L]
    exact IsEquiv.refl

/-- The value group of a comap along a smaller field sits inside the value group
of the comap along a larger intermediate field. -/
lemma Valuation.valueGroup_comap_le_valueGroup_comap :
    MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L)) ≤
      MonoidWithZeroHom.valueGroup (vL.comap (algebraMap F L)) := by
  intro γ hγ
  have hmem : (γ : ΓL) ∈ Set.range (vL.comap (algebraMap K L)) \ {0} := by
    have := Set.mem_image_of_mem Units.val hγ
    rwa [MonoidWithZeroHom.valueGroup_eq_range] at this
  obtain ⟨x, hx⟩ := hmem.1
  have hx' : vL (algebraMap F L (algebraMap K F x)) = (γ : ΓL) := by
    rw [← IsScalarTower.algebraMap_apply, ← hx]
    rfl
  have hγ_ne : (γ : ΓL) ≠ 0 := hmem.2
  have hrange : (γ : ΓL) ∈ Set.range (vL.comap (algebraMap F L)) \ {0} :=
    ⟨⟨algebraMap K F x, hx'⟩, hγ_ne⟩
  have : (γ : ΓL) ∈ Units.val ''
      (MonoidWithZeroHom.valueGroup (vL.comap (algebraMap F L)) : Set ΓLˣ) := by
    rwa [MonoidWithZeroHom.valueGroup_eq_range]
  obtain ⟨δ, hδ, hval⟩ := this
  exact (Units.ext hval).symm ▸ hδ

/-- The value group of a comap sits inside the value group of the original
valuation. -/
lemma Valuation.valueGroup_comap_le_valueGroup :
    MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L)) ≤
      MonoidWithZeroHom.valueGroup vL := by
  intro γ hγ
  have hmem : (γ : ΓL) ∈ Set.range (vL.comap (algebraMap K L)) \ {0} := by
    have := Set.mem_image_of_mem Units.val hγ
    rwa [MonoidWithZeroHom.valueGroup_eq_range] at this
  obtain ⟨x, hx⟩ := hmem.1
  have hγ_ne : (γ : ΓL) ≠ 0 := hmem.2
  have hrange : (γ : ΓL) ∈ Set.range vL \ {0} := ⟨⟨algebraMap K L x, hx⟩, hγ_ne⟩
  have : (γ : ΓL) ∈ Units.val ''
      (MonoidWithZeroHom.valueGroup vL : Set ΓLˣ) := by
    rwa [MonoidWithZeroHom.valueGroup_eq_range]
  obtain ⟨δ, hδ, hval⟩ := this
  exact (Units.ext hval).symm ▸ hδ

/-- Ramification index is multiplicative in towers when computed from a single
valuation on the top field (Kuhlmann, Lemma 6.16). This is the book's setting:
one valuation on `L`, restricted to the subfields. -/
theorem Valuation.ramificationIndex_mul :
    ramificationIndex (vL.comap (algebraMap K L)) vL =
      ramificationIndex (vL.comap (algebraMap K L)) (vL.comap (algebraMap F L)) *
        ramificationIndex (vL.comap (algebraMap F L)) vL := by
  have hcomap :
      (vL.comap (algebraMap F L)).comap (algebraMap K F) =
        vL.comap (algebraMap K L) := by
    rw [← comap_comp, IsScalarTower.algebraMap_eq K F L]
  set A := MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L))
  set C := MonoidWithZeroHom.valueGroup (vL.comap (algebraMap F L))
  set B := MonoidWithZeroHom.valueGroup vL
  have hAC : A ≤ C := valueGroup_comap_le_valueGroup_comap (F := F) vL
  have hCB : C ≤ B := valueGroup_comap_le_valueGroup (K := F) vL
  unfold ramificationIndex
  rw [hcomap]
  exact (Subgroup.relIndex_mul_relIndex A C B hAC hCB).symm

/-- In the two-valuation API, `e(w/v) = e(w/u) · [w(Fˣ) : w(Kˣ)]`. The second
factor is `e(u/v)` computed inside `Γ_L` (see `ramificationIndex_eq_comap`). -/
theorem Valuation.ramificationIndex_mul_hasExtension
    [vK.HasExtension vF] [vF.HasExtension vL] [vK.HasExtension vL] :
    ramificationIndex vK vL =
      ramificationIndex (vL.comap (algebraMap K L)) (vL.comap (algebraMap F L)) *
        ramificationIndex vF vL := by
  simpa [ramificationIndex_eq_comap vK vL, ramificationIndex_eq_comap vF vL] using
    ramificationIndex_mul (K := K) (F := F) (L := L) vL

/-- Residue-field algebras along a tower of valued fields form a scalar tower. -/
instance Valuation.isScalarTower_valuationSubring
    [vK.HasExtension vF] [vF.HasExtension vL] [vK.HasExtension vL] :
    IsScalarTower vK.valuationSubring vF.valuationSubring vL.valuationSubring :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    ext
    simp only [HasExtension.coe_algebraMap_valuationSubring_eq]
    exact IsScalarTower.algebraMap_apply K F L _

/-- Residue degree is multiplicative in towers (Kuhlmann, Lemma 6.16). The
identity holds with the usual `finrank` convention that an infinite factor
makes both sides `0`. -/
theorem Valuation.residueDegree_mul
    [vK.HasExtension vF] [vF.HasExtension vL] [vK.HasExtension vL] :
    residueDegree vK vF * residueDegree vF vL = residueDegree vK vL := by
  unfold residueDegree
  exact Module.finrank_mul_finrank
    (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vF.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

/-! ### Valuation of finite sums -/

variable [vK.HasExtension vL]

/-- A finite sum of nonzero terms with pairwise distinct valuations cannot be
zero. Equivalently: if such a sum vanishes, two terms share a valuation. -/
lemma Valuation.exists_eq_val_of_sum_eq_zero
    {I : Type*} [Fintype I] [Nonempty I] (f : I → L)
    (h_sum : ∑ i, f i = 0) (h_nz : ∀ i, f i ≠ 0) :
    ∃ i j, i ≠ j ∧ vL (f i) = vL (f j) := by
  classical
  by_contra h_dist
  push Not at h_dist
  obtain ⟨j, hj, hj_max⟩ :=
    Finset.exists_max_image Finset.univ (fun i ↦ vL (f i)) Finset.univ_nonempty
  have h_strict : ∀ i ∈ Finset.univ \ {j}, vL (f i) < vL (f j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact lt_of_le_of_ne (hj_max i (Finset.mem_univ i)) (h_dist i j hi.2)
  have h_val := Valuation.map_sum_eq_of_lt vL hj h_strict
  rw [h_sum, Valuation.map_zero] at h_val
  have h_val_nz : vL (f j) ≠ 0 := by
    intro h_zero
    exact h_nz j (vL.zero_iff.mp h_zero)
  exact h_val_nz h_val.symm

/-- Elements whose valuations lie in pairwise distinct cosets of `vL(Kˣ)` are
linearly independent over `K`. This is the `J = 1` case of Lemma 6.12. -/
theorem Valuation.linearIndependent_of_val_distinct_coset
    {I : Type*} [Nonempty I] (z : I → L) (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i j, i ≠ j → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      vL (algebraMap K L c * z i) ≠ vL (algebraMap K L d * z j)) :
    LinearIndependent K z := by
  rw [linearIndependent_iff']
  intro s g hg
  by_contra h_not_zero
  push Not at h_not_zero
  classical
  set s_nz := s.filter (fun i ↦ g i ≠ 0) with hs_nz
  have h_snz_nonempty : s_nz.Nonempty := by
    obtain ⟨x, hx, hgx⟩ := h_not_zero
    exact ⟨x, by rw [hs_nz, Finset.mem_filter]; exact ⟨hx, hgx⟩⟩
  haveI : Nonempty s_nz := h_snz_nonempty.to_subtype
  let f : s_nz → L := fun ⟨i, _⟩ ↦ algebraMap K L (g i) * z i
  have hf_sum : ∑ i : s_nz, f i = 0 := by
    have h1 : ∑ i : s_nz, f i =
        ∑ i ∈ s_nz, algebraMap K L (g i) * z i :=
      Finset.sum_attach s_nz (fun i ↦ algebraMap K L (g i) * z i)
    rw [h1]
    have h2 : ∑ i ∈ s_nz, algebraMap K L (g i) * z i =
        ∑ i ∈ s, algebraMap K L (g i) * z i := by
      apply Finset.sum_subset
      · rw [hs_nz]; exact Finset.filter_subset _ _
      · intro i hi his_nz
        rw [hs_nz, Finset.mem_filter, not_and] at his_nz
        have hgi : g i = 0 := by
          by_contra h_ne
          exact his_nz hi h_ne
        rw [hgi, map_zero, zero_mul]
    rw [h2]
    have h3 : ∑ i ∈ s, algebraMap K L (g i) * z i = ∑ i ∈ s, g i • z i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (Algebra.smul_def (g i) (z i)).symm
    rw [h3]
    exact hg
  have hf_nz : ∀ i : s_nz, f i ≠ 0 := by
    intro ⟨i, hi⟩
    have hi_prop : i ∈ s_nz := hi
    rw [hs_nz, Finset.mem_filter] at hi_prop
    have h_alg_nz : algebraMap K L (g i) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr hi_prop.2
    exact mul_ne_zero h_alg_nz (hz_nz i)
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hval⟩ :=
    exists_eq_val_of_sum_eq_zero vL f hf_sum hf_nz
  have hij' : i ≠ j := fun h ↦ hij (Subtype.ext h)
  have hi_prop : i ∈ s_nz := hi
  have hj_prop : j ∈ s_nz := hj
  rw [hs_nz, Finset.mem_filter] at hi_prop hj_prop
  exact hz_dist i j hij' (g i) (g j) hi_prop.2 hj_prop.2 hval

/-! ### Residue lifts of units of valuation one -/

/-- An element of the valuation ring whose residue is nonzero is a unit, hence
has valuation `1`. -/
lemma Valuation.val_eq_one_of_residue_ne_zero {u : vL.valuationSubring}
    (h : Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring) u ≠ 0) :
    vL (u : L) = 1 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, not_not] at h
  have h_val := ValuationSubring.valuation_eq_one_iff vL.valuationSubring u
  rw [h_val] at h
  exact (Valuation.isEquiv_valuation_valuationSubring vL).eq_one_iff_eq_one.mpr h

/-- The residue of an element of valuation `1`. -/
def Valuation.residueOfValOne {u : L} (hu : vL u = 1) :
    IsLocalRing.ResidueField vL.valuationSubring :=
  Ideal.Quotient.mk _ ⟨u, (mem_valuationSubring_iff vL u).mpr hu.le⟩

/-- Lift a family of residues to elements of `L` of valuation `1` whenever the
residues are nonzero (in particular, whenever they are linearly independent). -/
lemma Valuation.exists_lifts_of_residue
    {J : Type*} (x : J → IsLocalRing.ResidueField vL.valuationSubring) :
    ∃ u : J → vL.valuationSubring,
      ∀ j, Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring) (u j) =
        x j :=
  ⟨fun j ↦ Classical.choose (Ideal.Quotient.mk_surjective (x j)),
    fun j ↦ Classical.choose_spec (Ideal.Quotient.mk_surjective (x j))⟩

/-! ### Residue independence implies the no-cancellation property -/

/-- If the residues of units `u j` are linearly independent over `Kv`, then a
nontrivial `K`-linear combination of the `u j` has the same valuation as one
of its terms of maximal valuation (Kuhlmann's residue argument). -/
lemma Valuation.exists_max_val_of_residueIndependent
    {J : Type*} [Fintype J]
    (u : J → L) (hu_val_one : ∀ j, vL (u j) = 1)
    (hu_indep : LinearIndependent
      (IsLocalRing.ResidueField vK.valuationSubring)
      (fun j ↦ residueOfValOne vL (hu_val_one j)))
    (d : J → K) (hd : ∃ j, d j ≠ 0) :
    ∃ j0, vL (∑ j, algebraMap K L (d j) * u j) =
        vL (algebraMap K L (d j0) * u j0) ∧
      ∀ j, vL (algebraMap K L (d j) * u j) ≤
        vL (algebraMap K L (d j0) * u j0) := by
  let Kv := IsLocalRing.ResidueField vK.valuationSubring
  let Lv := IsLocalRing.ResidueField vL.valuationSubring
  haveI : Nonempty J := ⟨hd.choose⟩
  obtain ⟨j0, hj0_max⟩ :=
    Finset.exists_max_image Finset.univ (fun j ↦ vK (d j)) Finset.univ_nonempty
  have hd_j0_nz : d j0 ≠ 0 := by
    obtain ⟨j_nz, hd_nz_val⟩ := hd
    have h_le := hj0_max.2 j_nz (Finset.mem_univ _)
    have h_pos : 0 < vK (d j_nz) :=
      lt_of_le_of_ne zero_le (Ne.symm ((Valuation.zero_iff vK).not.mpr hd_nz_val))
    exact (Valuation.zero_iff vK).not.mp (Ne.symm (ne_of_lt (lt_of_lt_of_le h_pos h_le)))
  refine ⟨j0, ?_, ?_⟩
  · have h_alg_nz : algebraMap K L (d j0) ≠ 0 :=
      (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hd_j0_nz
    have h_sum_fact :
        (∑ j, algebraMap K L (d j) * u j) =
          algebraMap K L (d j0) *
            ∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j := by
      rw [Finset.mul_sum]
      refine (Finset.sum_congr rfl fun j _ ↦ ?_).symm
      calc algebraMap K L (d j0) * (algebraMap K L (d j * (d j0)⁻¹) * u j)
          _ = algebraMap K L (d j0) *
              (algebraMap K L (d j) * algebraMap K L (d j0)⁻¹ * u j) := by
                rw [map_mul]
          _ = (algebraMap K L (d j0) * algebraMap K L (d j0)⁻¹) *
              algebraMap K L (d j) * u j := by ring
          _ = algebraMap K L (d j0 * (d j0)⁻¹) * algebraMap K L (d j) * u j := by
                rw [← map_mul]
          _ = algebraMap K L 1 * algebraMap K L (d j) * u j := by
                rw [mul_inv_cancel₀ hd_j0_nz]
          _ = algebraMap K L (d j) * u j := by rw [map_one, one_mul]
    have h_c_le_one : ∀ j, vK (d j * (d j0)⁻¹) ≤ 1 := by
      intro j
      have h_le : vK (d j) ≤ vK (d j0) := hj0_max.2 j (Finset.mem_univ _)
      have hd_j0_pos : 0 < vK (d j0) :=
        lt_of_le_of_ne zero_le (Ne.symm ((Valuation.zero_iff vK).not.mpr hd_j0_nz))
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ hd_j0_pos).mpr (by rwa [one_mul])
    have h_c_vL_le_one : ∀ j, vL (algebraMap K L (d j * (d j0)⁻¹)) ≤ 1 :=
      fun j ↦ (HasExtension.val_map_le_one_iff vK vL _).mpr (h_c_le_one j)
    have h_sum_subring_val :
        vL (∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j) = 1 := by
      have h_c_vK_le_one : ∀ j, d j * (d j0)⁻¹ ∈ vK.valuationSubring :=
        fun j ↦ (mem_valuationSubring_iff vK _).mpr (h_c_le_one j)
      let c_sub_K : J → vK.valuationSubring :=
        fun j ↦ ⟨d j * (d j0)⁻¹, h_c_vK_le_one j⟩
      have h_c_sub_K_j0 : c_sub_K j0 = 1 := by
        ext
        exact mul_inv_cancel₀ hd_j0_nz
      let c_res : J → Kv := fun j ↦
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal vK.valuationSubring) (c_sub_K j)
      have h_c_res_j0 : c_res j0 = 1 := by
        change Ideal.Quotient.mk _ (c_sub_K j0) = 1
        rw [h_c_sub_K_j0, map_one]
      have h_c_sub : ∀ j, algebraMap K L (d j * (d j0)⁻¹) ∈ vL.valuationSubring :=
        fun j ↦ (mem_valuationSubring_iff vL _).mpr (h_c_vL_le_one j)
      let c_sub : J → vL.valuationSubring :=
        fun j ↦ ⟨algebraMap K L (d j * (d j0)⁻¹), h_c_sub j⟩
      let u_sub : J → vL.valuationSubring :=
        fun j ↦ ⟨u j, (mem_valuationSubring_iff vL _).mpr (hu_val_one j).le⟩
      have h_sum_eq_coe :
          (∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j) =
            (↑(∑ j : J, c_sub j * u_sub j) : L) := by
        rw [AddSubmonoidClass.coe_finsetSum]
        rfl
      have h_res_sum :
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring)
              (∑ j : J, c_sub j * u_sub j) =
            ∑ j : J, c_res j • residueOfValOne vL (hu_val_one j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        have h_mul :
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring)
                (c_sub j * u_sub j) =
              Ideal.Quotient.mk _ (c_sub j) * Ideal.Quotient.mk _ (u_sub j) :=
          map_mul _ _ _
        rw [h_mul]
        have h_c_sub_map :
            Ideal.Quotient.mk _ (c_sub j) = algebraMap Kv Lv (c_res j) := by
          have h_eq : c_sub j =
              algebraMap vK.valuationSubring vL.valuationSubring (c_sub_K j) := by
            ext; rfl
          rw [h_eq]
          change IsLocalRing.residue _
              (algebraMap vK.valuationSubring vL.valuationSubring (c_sub_K j)) =
            algebraMap Kv Lv (IsLocalRing.residue _ (c_sub_K j))
          rw [IsLocalRing.ResidueField.algebraMap_residue]
        rw [h_c_sub_map]
        exact (Algebra.smul_def (c_res j) (residueOfValOne vL (hu_val_one j))).symm
      have h_lin_comb_nz : ∑ j : J, c_res j • residueOfValOne vL (hu_val_one j) ≠ 0 := by
        intro h_zero
        rw [Fintype.linearIndependent_iff] at hu_indep
        have h_j0_zero := hu_indep c_res h_zero j0
        rw [h_c_res_j0] at h_j0_zero
        exact one_ne_zero h_j0_zero
      have h_sum_unit : IsUnit (∑ j : J, c_sub j * u_sub j) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, IsLocalRing.residue_def]
        rw [h_res_sum]
        exact h_lin_comb_nz
      rw [h_sum_eq_coe]
      have h_val_sub :=
        ValuationSubring.valuation_eq_one_iff vL.valuationSubring
          (∑ j : J, c_sub j * u_sub j)
      rw [h_val_sub] at h_sum_unit
      exact (isEquiv_valuation_valuationSubring vL).eq_one_iff_eq_one.mpr h_sum_unit
    rw [h_sum_fact, Valuation.map_mul, h_sum_subring_val, mul_one]
    rw [Valuation.map_mul, hu_val_one j0, mul_one]
  · intro j
    rw [Valuation.map_mul, hu_val_one j, mul_one, Valuation.map_mul, hu_val_one j0,
      mul_one]
    have h_c_le_one : vK (d j * (d j0)⁻¹) ≤ 1 := by
      have h_le : vK (d j) ≤ vK (d j0) := hj0_max.2 j (Finset.mem_univ _)
      have hd_j0_pos : 0 < vK (d j0) :=
        lt_of_le_of_ne zero_le (Ne.symm ((Valuation.zero_iff vK).not.mpr hd_j0_nz))
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ hd_j0_pos).mpr (by rwa [one_mul])
    have h_le_one : vL (algebraMap K L (d j * (d j0)⁻¹)) ≤ 1 :=
      (HasExtension.val_map_le_one_iff vK vL _).mpr h_c_le_one
    have h_alg_nz : algebraMap K L (d j0) ≠ 0 :=
      (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hd_j0_nz
    have hd_j0_alg_pos : 0 < vL (algebraMap K L (d j0)) :=
      lt_of_le_of_ne zero_le (Ne.symm ((Valuation.zero_iff vL).not.mpr h_alg_nz))
    have h_le_one' :
        vL (algebraMap K L (d j)) * (vL (algebraMap K L (d j0)))⁻¹ ≤ 1 := by
      rw [← map_inv₀, ← map_mul, ← map_inv₀ (algebraMap K L),
        ← map_mul (algebraMap K L)]
      exact h_le_one
    have h_le_one'' := (mul_inv_le_iff₀ hd_j0_alg_pos).mp h_le_one'
    rwa [one_mul] at h_le_one''

/-! ### Lemma 6.12 -/

/-- For each \(i\) in the support, the \(u\)-block has a distinguished coefficient
of maximal valuation, necessarily nonzero. -/
private lemma exists_block_max_coeff
    {I J : Type*} [Fintype J]
    (u : J → L) (hu_val_one : ∀ j, vL (u j) = 1)
    (hu_indep : LinearIndependent
      (IsLocalRing.ResidueField vK.valuationSubring)
      (fun j ↦ residueOfValOne vL (hu_val_one j)))
    (c : I × J → K) (i : I) (hi : ∃ j, c (i, j) ≠ 0) :
    ∃ j0, c (i, j0) ≠ 0 ∧
      vL (∑ j, algebraMap K L (c (i, j)) * u j) =
        vL (algebraMap K L (c (i, j0))) ∧
      ∀ j, vL (algebraMap K L (c (i, j)) * u j) ≤
        vL (algebraMap K L (c (i, j0)) * u j0) := by
  obtain ⟨j0, hj0_eq, hj0_le⟩ :=
    exists_max_val_of_residueIndependent vK vL u hu_val_one hu_indep
      (fun j ↦ c (i, j)) hi
  have h_val_g :
      vL (∑ j, algebraMap K L (c (i, j)) * u j) =
        vL (algebraMap K L (c (i, j0))) := by
    rw [hj0_eq, Valuation.map_mul, hu_val_one j0, mul_one]
  refine ⟨j0, ?_, h_val_g, hj0_le⟩
  intro hc_zero
  obtain ⟨j_ex, hc_ex⟩ := hi
  have h_ex_le := hj0_le j_ex
  rw [hc_zero, map_zero, zero_mul, Valuation.map_zero] at h_ex_le
  have h_ex_val_zero := le_antisymm h_ex_le zero_le
  have h_ex_mul_zero := vL.zero_iff.mp h_ex_val_zero
  cases mul_eq_zero.mp h_ex_mul_zero with
  | inl h_alg =>
    exact hc_ex ((map_eq_zero_iff _ (algebraMap K L).injective).mp h_alg)
  | inr h_u =>
    have h_val_u := hu_val_one j_ex
    rw [h_u, Valuation.map_zero] at h_val_u
    exact zero_ne_one h_val_u

/-- Valuation independence of the products `z i * u j` (Kuhlmann, Lemma 6.12).

If the values `vL (z i)` lie in distinct cosets of `vL(Kˣ)` and the residues of
the units `u j` are linearly independent over `Kv`, then a nontrivial
`K`-linear combination of the products has the same valuation as one of its
terms of maximal valuation (multiplicative notation). -/
theorem Valuation.exists_max_val_mul
    {I J : Type*} [Fintype I] [Fintype J]
    (z : I → L) (u : J → L)
    (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i i', i ≠ i' → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      vL (algebraMap K L c * z i) ≠ vL (algebraMap K L d * z i'))
    (hu_val_one : ∀ j, vL (u j) = 1)
    (hu_indep : LinearIndependent
      (IsLocalRing.ResidueField vK.valuationSubring)
      (fun j ↦ residueOfValOne vL (hu_val_one j)))
    (c : I × J → K) (hc : ∃ p, c p ≠ 0) :
    ∃ p0, c p0 ≠ 0 ∧
      vL (∑ p, algebraMap K L (c p) * (z p.1 * u p.2)) =
        vL (algebraMap K L (c p0) * (z p0.1 * u p0.2)) ∧
      ∀ p, vL (algebraMap K L (c p) * (z p.1 * u p.2)) ≤
        vL (algebraMap K L (c p0) * (z p0.1 * u p0.2)) := by
  classical
  let g : I → L := fun i ↦ ∑ j, algebraMap K L (c (i, j)) * u j
  have h_sum :
      ∑ p : I × J, algebraMap K L (c p) * (z p.1 * u p.2) = ∑ i, z i * g i := by
    have h2 : ∑ p : I × J, algebraMap K L (c p) * (z p.1 * u p.2) =
        ∑ i, ∑ j, algebraMap K L (c (i, j)) * (z i * u j) :=
      Fintype.sum_prod_type fun p : I × J ↦
        algebraMap K L (c p) * (z p.1 * u p.2)
    rw [h2]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h4 : ∑ j, algebraMap K L (c (i, j)) * (z i * u j) =
        ∑ j, z i * (algebraMap K L (c (i, j)) * u j) :=
      Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _
    rw [h4, ← Finset.mul_sum]
  set sI := Finset.univ.filter (fun i ↦ ∃ j, c (i, j) ≠ 0) with hsI
  obtain ⟨⟨i_nz, j_nz⟩, hc_nz⟩ := hc
  have hsI_nonempty : sI.Nonempty := by
    refine ⟨i_nz, ?_⟩
    rw [hsI, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨j_nz, hc_nz⟩⟩
  have h_g_data : ∀ i ∈ sI, ∃ j0, c (i, j0) ≠ 0 ∧
      vL (g i) = vL (algebraMap K L (c (i, j0))) ∧
      ∀ j, vL (algebraMap K L (c (i, j)) * u j) ≤
        vL (algebraMap K L (c (i, j0)) * u j0) := by
    intro i hi
    rw [hsI, Finset.mem_filter] at hi
    exact exists_block_max_coeff vK vL u hu_val_one hu_indep c i hi.2
  have h_g_nz : ∀ i ∈ sI, g i ≠ 0 := by
    intro i hi
    obtain ⟨j0, hj0_nz, hval, _⟩ := h_g_data i hi
    intro hg0
    have : vL (g i) = 0 := by rw [hg0, Valuation.map_zero]
    rw [this] at hval
    exact hj0_nz ((map_eq_zero_iff _ (algebraMap K L).injective).mp
      (vL.zero_iff.mp hval.symm))
  have val_term (i : I) (j : J) :
      vL (algebraMap K L (c (i, j)) * (z i * u j)) =
        vL (algebraMap K L (c (i, j)) * z i) := by
    rw [← mul_assoc, Valuation.map_mul, hu_val_one j, mul_one]
  have val_coeff_of_le {i : I} {j j' : J}
      (hle : vL (algebraMap K L (c (i, j)) * u j) ≤
        vL (algebraMap K L (c (i, j')) * u j')) :
      vL (algebraMap K L (c (i, j))) ≤ vL (algebraMap K L (c (i, j'))) := by
    rw [Valuation.map_mul, Valuation.map_mul, hu_val_one j, hu_val_one j',
      mul_one, mul_one] at hle
    exact hle
  have h_block_val : ∀ i ∈ sI, ∀ j0,
      c (i, j0) ≠ 0 →
        (∀ j, vL (algebraMap K L (c (i, j)) * u j) ≤
          vL (algebraMap K L (c (i, j0)) * u j0)) →
        vL (z i * g i) = vL (algebraMap K L (c (i, j0)) * (z i * u j0)) := by
    intro i hi j0 _hj0_nz hj0_le
    obtain ⟨j1, _hj1_nz, hval, hj1_le⟩ := h_g_data i hi
    have hzi : vL (z i * g i) = vL (algebraMap K L (c (i, j1)) * z i) := by
      rw [Valuation.map_mul, hval, mul_comm (vL (z i)), ← Valuation.map_mul]
    have h_eq_coeff :
        vL (algebraMap K L (c (i, j0))) = vL (algebraMap K L (c (i, j1))) :=
      le_antisymm (val_coeff_of_le (hj1_le j0)) (val_coeff_of_le (hj0_le j1))
    rw [hzi, val_term, Valuation.map_mul, Valuation.map_mul, h_eq_coeff]
  obtain ⟨i0, hi0_mem, hi0_max⟩ :=
    Finset.exists_max_image sI (fun i ↦ vL (z i * g i)) hsI_nonempty
  obtain ⟨j0, hj0_nz, hval_i0, hj0_le⟩ := h_g_data i0 hi0_mem
  have h_max_pos : 0 < vL (z i0 * g i0) := by
    have hnz : z i0 * g i0 ≠ 0 := mul_ne_zero (hz_nz i0) (h_g_nz i0 hi0_mem)
    exact lt_of_le_of_ne zero_le (Ne.symm ((Valuation.zero_iff vL).not.mpr hnz))
  have h_strict : ∀ i ∈ Finset.univ \ {i0},
      vL (z i * g i) < vL (z i0 * g i0) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    by_cases hsup : i ∈ sI
    · have hle := hi0_max i hsup
      have hne : vL (z i * g i) ≠ vL (z i0 * g i0) := by
        obtain ⟨ji, hji_nz, hval_i, hji_le⟩ := h_g_data i hsup
        have hi_eq := h_block_val i hsup ji hji_nz hji_le
        have hi0_eq := h_block_val i0 hi0_mem j0 hj0_nz hj0_le
        rw [hi_eq, hi0_eq, val_term, val_term]
        exact hz_dist i i0 hi.2 (c (i, ji)) (c (i0, j0)) hji_nz hj0_nz
      exact lt_of_le_of_ne hle hne
    · have hgi : g i = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have : c (i, j) = 0 := by
          rw [hsI, Finset.mem_filter, not_and, not_exists] at hsup
          have h_no := hsup (Finset.mem_univ i)
          push Not at h_no
          exact h_no j
        rw [this, map_zero, zero_mul]
      rw [hgi, mul_zero, Valuation.map_zero]
      exact h_max_pos
  have h_val_sum :
      vL (∑ p, algebraMap K L (c p) * (z p.1 * u p.2)) = vL (z i0 * g i0) := by
    rw [h_sum]
    exact Valuation.map_sum_eq_of_lt vL (Finset.mem_univ i0) h_strict
  refine ⟨(i0, j0), hj0_nz, ?_, ?_⟩
  · rw [h_val_sum]
    exact h_block_val i0 hi0_mem j0 hj0_nz hj0_le
  · intro p
    have hp_le_block :
        vL (algebraMap K L (c p) * (z p.1 * u p.2)) ≤ vL (z p.1 * g p.1) := by
      by_cases hpz : c p = 0
      · rw [hpz, map_zero, zero_mul, Valuation.map_zero]
        exact zero_le
      · have hp_mem : p.1 ∈ sI := by
          rw [hsI, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ⟨p.2, hpz⟩⟩
        obtain ⟨ji, hji_nz, hval_i, hji_le⟩ := h_g_data p.1 hp_mem
        have hle := val_coeff_of_le (hji_le p.2)
        calc vL (algebraMap K L (c p) * (z p.1 * u p.2))
            _ = vL (algebraMap K L (c (p.1, p.2)) * z p.1) := val_term p.1 p.2
            _ = vL (algebraMap K L (c (p.1, p.2))) * vL (z p.1) :=
                  Valuation.map_mul _ _ _
            _ ≤ vL (algebraMap K L (c (p.1, ji))) * vL (z p.1) :=
                  mul_le_mul_of_nonneg_right hle zero_le
            _ = vL (g p.1) * vL (z p.1) := by rw [hval_i]
            _ = vL (z p.1 * g p.1) := by rw [mul_comm, ← Valuation.map_mul]
    have h_block_le : vL (z p.1 * g p.1) ≤ vL (z i0 * g i0) := by
      by_cases hsup : p.1 ∈ sI
      · exact hi0_max p.1 hsup
      · have hgi : g p.1 = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          have : c (p.1, j) = 0 := by
            rw [hsI, Finset.mem_filter, not_and, not_exists] at hsup
            have h_no := hsup (Finset.mem_univ p.1)
            push Not at h_no
            exact h_no j
          rw [this, map_zero, zero_mul]
        rw [hgi, mul_zero, Valuation.map_zero]
        exact zero_le
    have hi0_eq := h_block_val i0 hi0_mem j0 hj0_nz hj0_le
    calc vL (algebraMap K L (c p) * (z p.1 * u p.2))
        _ ≤ vL (z p.1 * g p.1) := hp_le_block
        _ ≤ vL (z i0 * g i0) := h_block_le
        _ = vL (algebraMap K L (c (i0, j0)) * (z i0 * u j0)) := hi0_eq

/-- Linear independence of the products `z i * u j` (corollary of Lemma 6.12). -/
theorem Valuation.valuation_independence
    {I J : Type*} [Finite I] [Finite J]
    (z : I → L) (u : J → L)
    (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i i', i ≠ i' → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      vL (algebraMap K L c * z i) ≠ vL (algebraMap K L d * z i'))
    (hu_val_one : ∀ j, vL (u j) = 1)
    (hu_indep : LinearIndependent
      (IsLocalRing.ResidueField vK.valuationSubring)
      (fun j ↦ residueOfValOne vL (hu_val_one j))) :
    LinearIndependent K (fun p : I × J ↦ z p.1 * u p.2) := by
  letI := Fintype.ofFinite I
  letI := Fintype.ofFinite J
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra h_not_zero
  push Not at h_not_zero
  obtain ⟨p0, hp0_nz, hp0_eq, hp0_le⟩ :=
    exists_max_val_mul vK vL z u hz_nz hz_dist hu_val_one hu_indep c h_not_zero
  have h_sum : ∑ p, algebraMap K L (c p) * (z p.1 * u p.2) = 0 := by
    have h_smul : ∑ p, algebraMap K L (c p) * (z p.1 * u p.2) =
        ∑ p, c p • (z p.1 * u p.2) :=
      Finset.sum_congr rfl fun p _ ↦ (Algebra.smul_def (c p) (z p.1 * u p.2)).symm
    rw [h_smul, hc]
  rw [h_sum, Valuation.map_zero] at hp0_eq
  have h_term_zero :
      vL (algebraMap K L (c p0) * (z p0.1 * u p0.2)) = 0 := by
    exact le_antisymm (hp0_eq ▸ hp0_le p0) zero_le
  have h_mul_zero := vL.zero_iff.mp h_term_zero
  rcases (mul_eq_zero.mp h_mul_zero) with h_alg | h_zu
  · exact hp0_nz ((map_eq_zero_iff _ (algebraMap K L).injective).mp h_alg)
  · rcases (mul_eq_zero.mp h_zu) with h_z | h_u
    · exact hz_nz p0.1 h_z
    · have h1 := hu_val_one p0.2
      rw [h_u, Valuation.map_zero] at h1
      exact zero_ne_one h1

/-! ### Coset representatives and residue bases -/

/-- Coset representatives taken as `Quotient.out` have pairwise distinct
value-cosets. -/
lemma Valuation.distinct_cosets_of_quotient_out
    {e : ℕ} (_he : e ≠ 0)
    (A : Subgroup ΓLˣ) (B : Subgroup ΓLˣ)
    (hA : A = MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L)))
    (hB : B = MonoidWithZeroHom.valueGroup vL)
    (eqv : B ⧸ A.comap B.subtype ≃ Fin e)
    (z : Fin e → L)
    (hz : ∀ i, vL (z i) = ((Quotient.out (eqv.symm i)).val : ΓL))
    (_hz_nz : ∀ i, z i ≠ 0) :
    ∀ i j, i ≠ j → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      vL (algebraMap K L c * z i) ≠ vL (algebraMap K L d * z j) := by
  intro i j hij c d hc hd h_eq
  have hc_alg_nz : algebraMap K L c ≠ 0 :=
    (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hc
  have hd_alg_nz : algebraMap K L d ≠ 0 :=
    (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hd
  rw [Valuation.map_mul, Valuation.map_mul, hz i, hz j] at h_eq
  have h_vc : vL (algebraMap K L c) ≠ 0 := fun h ↦ hc_alg_nz (vL.zero_iff.mp h)
  have h_vd : vL (algebraMap K L d) ≠ 0 := fun h ↦ hd_alg_nz (vL.zero_iff.mp h)
  have h_c_unit : IsUnit (vL (algebraMap K L c)) := IsUnit.mk0 _ h_vc
  have h_d_unit : IsUnit (vL (algebraMap K L d)) := IsUnit.mk0 _ h_vd
  have h_eq_unit :
      h_c_unit.unit * (Quotient.out (eqv.symm i) : B).val =
        h_d_unit.unit * (Quotient.out (eqv.symm j) : B).val := by
    ext
    exact h_eq
  have hd_mem : h_d_unit.unit ∈ B := by
    subst hB
    exact MonoidWithZeroHom.mem_valueGroup _ ⟨algebraMap K L d, rfl⟩
  have hc_mem : h_c_unit.unit ∈ B := by
    subst hB
    exact MonoidWithZeroHom.mem_valueGroup _ ⟨algebraMap K L c, rfl⟩
  have h_ratio_val :
      ((Quotient.out (eqv.symm i) : B)⁻¹ * (Quotient.out (eqv.symm j) : B)).val =
        (⟨h_c_unit.unit, hc_mem⟩ : B).val * (⟨h_d_unit.unit, hd_mem⟩ : B)⁻¹.val := by
    change ((Quotient.out (eqv.symm i)).val)⁻¹ * (Quotient.out (eqv.symm j)).val =
      h_c_unit.unit * (h_d_unit.unit)⁻¹
    apply mul_left_cancel (a := (Quotient.out (eqv.symm i)).val * h_d_unit.unit)
    have h_lhs :
        (Quotient.out (eqv.symm i)).val * h_d_unit.unit *
            (((Quotient.out (eqv.symm i)).val)⁻¹ * (Quotient.out (eqv.symm j)).val) =
          h_d_unit.unit * (Quotient.out (eqv.symm j)).val := by
      calc (Quotient.out (eqv.symm i)).val * h_d_unit.unit *
            (((Quotient.out (eqv.symm i)).val)⁻¹ * (Quotient.out (eqv.symm j)).val)
          _ = (Quotient.out (eqv.symm i)).val *
              ((Quotient.out (eqv.symm i)).val)⁻¹ * h_d_unit.unit *
              (Quotient.out (eqv.symm j)).val := by ac_rfl
          _ = 1 * h_d_unit.unit * (Quotient.out (eqv.symm j)).val := by
                rw [mul_inv_cancel (Quotient.out (eqv.symm i)).val]
          _ = h_d_unit.unit * (Quotient.out (eqv.symm j)).val := by rw [one_mul]
    have h_rhs :
        (Quotient.out (eqv.symm i)).val * h_d_unit.unit *
            (h_c_unit.unit * (h_d_unit.unit)⁻¹) =
          h_c_unit.unit * (Quotient.out (eqv.symm i)).val := by
      calc (Quotient.out (eqv.symm i)).val * h_d_unit.unit *
            (h_c_unit.unit * (h_d_unit.unit)⁻¹)
          _ = h_d_unit.unit * (h_d_unit.unit)⁻¹ * h_c_unit.unit *
              (Quotient.out (eqv.symm i)).val := by ac_rfl
          _ = 1 * h_c_unit.unit * (Quotient.out (eqv.symm i)).val := by
                rw [mul_inv_cancel h_d_unit.unit]
          _ = h_c_unit.unit * (Quotient.out (eqv.symm i)).val := by rw [one_mul]
    rw [h_lhs, h_rhs]
    exact h_eq_unit.symm
  have h_z_ratio_in_A :
      ((Quotient.out (eqv.symm i) : B)⁻¹ * (Quotient.out (eqv.symm j) : B)) ∈
        A.comap B.subtype := by
    rw [Subgroup.mem_comap]
    change ((Quotient.out (eqv.symm i) : B)⁻¹ *
      (Quotient.out (eqv.symm j) : B)).val ∈ A
    rw [h_ratio_val]
    have h_d_in_A : h_d_unit.unit ∈ A := by
      subst hA
      exact MonoidWithZeroHom.mem_valueGroup _ ⟨d, rfl⟩
    have h_c_in_A : h_c_unit.unit ∈ A := by
      subst hA
      exact MonoidWithZeroHom.mem_valueGroup _ ⟨c, rfl⟩
    exact Subgroup.mul_mem A h_c_in_A (Subgroup.inv_mem A h_d_in_A)
  have h_eq_out :
      (Quotient.mk _ (Quotient.out (eqv.symm i)) : B ⧸ A.comap B.subtype) =
        Quotient.mk _ (Quotient.out (eqv.symm j)) :=
    QuotientGroup.eq.mpr h_z_ratio_in_A
  rw [Quotient.out_eq, Quotient.out_eq] at h_eq_out
  exact hij (eqv.symm.injective h_eq_out)

/-! ### Finiteness of `e` and `f` -/

/-- A finite linearly independent family of residues lifts to a `K`-linearly
independent family in `L` of the same cardinality. -/
lemma Valuation.fintype_card_le_finrank_of_residueIndependent
    {J : Type*} [Fintype J]
    (u : J → L) (hu_val_one : ∀ j, vL (u j) = 1)
    (hu_indep : LinearIndependent
      (IsLocalRing.ResidueField vK.valuationSubring)
      (fun j ↦ residueOfValOne vL (hu_val_one j)))
    [FiniteDimensional K L] :
    Fintype.card J ≤ Module.finrank K L := by
  have hli := valuation_independence vK vL
    (fun _ : Unit ↦ (1 : L)) u
    (fun _ ↦ one_ne_zero)
    (fun i i' h ↦ (h (Subsingleton.elim i i')).elim)
    hu_val_one hu_indep
  have hcard := LinearIndependent.fintype_card_le_finrank hli
  simpa [Fintype.card_prod, Fintype.card_unique] using hcard

/-- For a finite extension, the residue-field extension is finite
(Kuhlmann, Lemma 6.13). -/
theorem Valuation.finite_residueField_extension [FiniteDimensional K L] :
    Module.Finite
      (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring) := by
  let Kv := IsLocalRing.ResidueField vK.valuationSubring
  let Lv := IsLocalRing.ResidueField vL.valuationSubring
  by_contra hinf
  have hrank : ℵ₀ ≤ Module.rank Kv Lv := by
    rw [← not_lt, Module.rank_lt_aleph0_iff]
    exact hinf
  let n := Module.finrank K L + 1
  have hn : (n : Cardinal) ≤ Module.rank Kv Lv :=
    natCast_lt_aleph0.le.trans hrank
  let b := Module.Free.chooseBasis Kv Lv
  have hInf : Infinite (Module.Free.ChooseBasisIndex Kv Lv) := by
    rw [← not_finite_iff_infinite]
    intro hfin
    exact hinf (Module.Finite.of_basis b)
  obtain ⟨t, ht⟩ := Infinite.exists_subset_card_eq
    (Module.Free.ChooseBasisIndex Kv Lv) n
  let b_t : t → Lv := fun i ↦ b i.1
  have hb_t : LinearIndependent Kv b_t :=
    b.linearIndependent.comp _ Subtype.val_injective
  obtain ⟨u_sub, hu_sub⟩ := exists_lifts_of_residue vL b_t
  have hu_val : ∀ j : t, vL (u_sub j : L) = 1 := fun j ↦
    val_eq_one_of_residue_ne_zero vL (by
      rw [hu_sub]
      exact hb_t.ne_zero j)
  have hu_indep :
      LinearIndependent Kv (fun j ↦ residueOfValOne vL (hu_val j)) := by
    have h_eq : (fun j ↦ residueOfValOne vL (hu_val j)) = b_t := by
      funext j
      simp only [residueOfValOne]
      rw [Subtype.coe_eta]
      exact hu_sub j
    rwa [h_eq]
  have hle :=
    fintype_card_le_finrank_of_residueIndependent vK vL
      (fun j ↦ (u_sub j : L)) hu_val hu_indep
  have : n ≤ Module.finrank K L := by
    convert hle
    simp [n, Fintype.card_coe, ht]
  exact (Nat.not_succ_le_self (Module.finrank K L)) this

/-- The residue degree of a finite extension is positive
(Kuhlmann, Lemma 6.13: `Lv | Kv` is finite, and residue fields are nonzero). -/
theorem Valuation.residueDegree_pos [FiniteDimensional K L] :
    0 < residueDegree vK vL := by
  haveI := finite_residueField_extension vK vL
  exact Module.finrank_pos

/-- For a finite extension, the value-group quotient is finite
(Kuhlmann, Lemma 6.13). -/
theorem Valuation.finite_valueGroup_quotient [FiniteDimensional K L] :
    Finite
      (MonoidWithZeroHom.valueGroup vL ⧸
        (MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L))).comap
          (MonoidWithZeroHom.valueGroup vL).subtype) := by
  set A := MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L))
  set B := MonoidWithZeroHom.valueGroup vL
  set Q := B ⧸ A.comap B.subtype
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  let n := Module.finrank K L + 1
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq Q n
  let z_sub : s → B := fun i ↦ Quotient.out (i : Q)
  have hz_val : ∀ i : s, ((z_sub i).val : ΓL) ∈ Set.range vL := fun i ↦ by
    have h_eq : Units.val '' (B : Set ΓLˣ) = Set.range vL \ {0} :=
      MonoidWithZeroHom.valueGroup_eq_range vL
    have h_in : ((z_sub i).val : ΓL) ∈ Units.val '' (B : Set ΓLˣ) :=
      Set.mem_image_of_mem _ (z_sub i).property
    rw [h_eq] at h_in
    exact h_in.1
  choose z hz using hz_val
  have hz_nz : ∀ i : s, z i ≠ 0 := fun i ↦ by
    intro hz0
    have h_eq := hz i
    rw [hz0, Valuation.map_zero] at h_eq
    exact Units.ne_zero (z_sub i).val h_eq.symm
  have hz_dist : ∀ i j : s, i ≠ j → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      vL (algebraMap K L c * z i) ≠ vL (algebraMap K L d * z j) := by
    intro i j hij c d hc hd h_eq
    -- Reduce to the `Quotient.out` criterion on the ambient quotient `Q`.
    have hc_alg_nz : algebraMap K L c ≠ 0 :=
      (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hc
    have hd_alg_nz : algebraMap K L d ≠ 0 :=
      (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hd
    rw [Valuation.map_mul, Valuation.map_mul, hz i, hz j] at h_eq
    have h_vc : vL (algebraMap K L c) ≠ 0 := fun h ↦ hc_alg_nz (vL.zero_iff.mp h)
    have h_vd : vL (algebraMap K L d) ≠ 0 := fun h ↦ hd_alg_nz (vL.zero_iff.mp h)
    have h_c_unit : IsUnit (vL (algebraMap K L c)) := IsUnit.mk0 _ h_vc
    have h_d_unit : IsUnit (vL (algebraMap K L d)) := IsUnit.mk0 _ h_vd
    have h_eq_unit :
        h_c_unit.unit * (z_sub i).val = h_d_unit.unit * (z_sub j).val := by
      ext; exact h_eq
    have hd_mem : h_d_unit.unit ∈ B :=
      MonoidWithZeroHom.mem_valueGroup _ ⟨algebraMap K L d, rfl⟩
    have hc_mem : h_c_unit.unit ∈ B :=
      MonoidWithZeroHom.mem_valueGroup _ ⟨algebraMap K L c, rfl⟩
    have h_ratio_val :
        ((z_sub i : B)⁻¹ * (z_sub j : B)).val =
          (⟨h_c_unit.unit, hc_mem⟩ : B).val *
            (⟨h_d_unit.unit, hd_mem⟩ : B)⁻¹.val := by
      change ((z_sub i).val)⁻¹ * (z_sub j).val = h_c_unit.unit * (h_d_unit.unit)⁻¹
      apply mul_left_cancel (a := (z_sub i).val * h_d_unit.unit)
      have h_lhs : (z_sub i).val * h_d_unit.unit *
          (((z_sub i).val)⁻¹ * (z_sub j).val) =
            h_d_unit.unit * (z_sub j).val := by
        calc (z_sub i).val * h_d_unit.unit * (((z_sub i).val)⁻¹ * (z_sub j).val)
            _ = (z_sub i).val * ((z_sub i).val)⁻¹ * h_d_unit.unit *
                (z_sub j).val := by ac_rfl
            _ = 1 * h_d_unit.unit * (z_sub j).val := by
                  rw [mul_inv_cancel (z_sub i).val]
            _ = h_d_unit.unit * (z_sub j).val := by rw [one_mul]
      have h_rhs : (z_sub i).val * h_d_unit.unit *
          (h_c_unit.unit * (h_d_unit.unit)⁻¹) =
            h_c_unit.unit * (z_sub i).val := by
        calc (z_sub i).val * h_d_unit.unit * (h_c_unit.unit * (h_d_unit.unit)⁻¹)
            _ = h_d_unit.unit * (h_d_unit.unit)⁻¹ * h_c_unit.unit *
                (z_sub i).val := by ac_rfl
            _ = 1 * h_c_unit.unit * (z_sub i).val := by
                  rw [mul_inv_cancel h_d_unit.unit]
            _ = h_c_unit.unit * (z_sub i).val := by rw [one_mul]
      rw [h_lhs, h_rhs]
      exact h_eq_unit.symm
    have h_z_ratio_in_A : ((z_sub i : B)⁻¹ * (z_sub j : B)) ∈ A.comap B.subtype := by
      rw [Subgroup.mem_comap]
      change ((z_sub i : B)⁻¹ * (z_sub j : B)).val ∈ A
      rw [h_ratio_val]
      have h_d_in_A : h_d_unit.unit ∈ A :=
        MonoidWithZeroHom.mem_valueGroup _ ⟨d, rfl⟩
      have h_c_in_A : h_c_unit.unit ∈ A :=
        MonoidWithZeroHom.mem_valueGroup _ ⟨c, rfl⟩
      exact Subgroup.mul_mem A h_c_in_A (Subgroup.inv_mem A h_d_in_A)
    have h_eq_out : (Quotient.mk _ (z_sub i) : Q) = Quotient.mk _ (z_sub j) :=
      QuotientGroup.eq.mpr h_z_ratio_in_A
    have hi : (Quotient.mk _ (z_sub i) : Q) = (i : Q) := Quotient.out_eq _
    have hj : (Quotient.mk _ (z_sub j) : Q) = (j : Q) := Quotient.out_eq _
    rw [hi, hj] at h_eq_out
    exact hij (Subtype.ext h_eq_out)
  have hs_ne : s.Nonempty :=
    Finset.card_pos.mp (by rw [hs]; exact Nat.succ_pos _)
  haveI : Nonempty s := hs_ne.to_subtype
  have hli :=
    linearIndependent_of_val_distinct_coset vL z hz_nz hz_dist
  have hcard := LinearIndependent.fintype_card_le_finrank hli
  have : n ≤ Module.finrank K L := by
    simpa [Fintype.card_coe, hs] using hcard
  exact (Nat.not_succ_le_self (Module.finrank K L)) this

/-- The ramification index of a finite extension is nonzero
(Kuhlmann, Lemma 6.13: `vL / vK` is finite, and the quotient is nonempty). -/
theorem Valuation.ramificationIndex_ne_zero [FiniteDimensional K L] :
    ramificationIndex vK vL ≠ 0 := by
  haveI := finite_valueGroup_quotient (K := K) vL
  rw [ramificationIndex, Subgroup.relIndex, Subgroup.index, Subgroup.subgroupOf]
  exact Finite.card_pos.ne'

/-- The ramification index of a finite extension is at least `1`. -/
theorem Valuation.one_le_ramificationIndex [FiniteDimensional K L] :
    1 ≤ ramificationIndex vK vL :=
  Nat.one_le_iff_ne_zero.mpr (ramificationIndex_ne_zero vK vL)

/-! ### Lemma 6.13 -/

/-- The fundamental inequality for a finite extension of valued fields
(Kuhlmann, Lemma 6.13):

\[
  e(w/v)\, f(w/v) \le [L : K].
\]

Finiteness of `e` and `f` is included: both are positive, so the product is
not the vacuous `0` of the `ℕ` convention for infinite cardinals. -/
theorem Valuation.fundamental_inequality [FiniteDimensional K L] :
    ramificationIndex vK vL * residueDegree vK vL ≤ Module.finrank K L := by
  let e := ramificationIndex vK vL
  let f := residueDegree vK vL
  change e * f ≤ _
  have he : e ≠ 0 := ramificationIndex_ne_zero vK vL
  have hf : 0 < f := residueDegree_pos vK vL
  haveI : Nonempty (Fin e) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero he)
  haveI : Nonempty (Fin f) := Fin.pos_iff_nonempty.mp hf
  haveI : Module.Finite
      (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring) :=
    finite_residueField_extension vK vL
  let Kv := IsLocalRing.ResidueField vK.valuationSubring
  let Lv := IsLocalRing.ResidueField vL.valuationSubring
  let b_res := Module.finBasis Kv Lv
  obtain ⟨u_sub, hu_sub⟩ := exists_lifts_of_residue vL b_res
  let u : Fin f → L := fun j ↦ (u_sub j : L)
  have hu_val_one : ∀ j, vL (u j) = 1 := fun j ↦
    val_eq_one_of_residue_ne_zero vL (by
      rw [hu_sub]
      exact (Module.finBasis Kv Lv).linearIndependent.ne_zero j)
  have hu_indep :
      LinearIndependent Kv (fun j ↦ residueOfValOne vL (hu_val_one j)) := by
    have h_eq : (fun j ↦ residueOfValOne vL (hu_val_one j)) = b_res := by
      funext j
      simp only [residueOfValOne]
      rw [Subtype.coe_eta]
      exact hu_sub j
    rw [h_eq]
    exact (Module.finBasis Kv Lv).linearIndependent
  let A := MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L))
  let B := MonoidWithZeroHom.valueGroup vL
  let Q := B ⧸ A.comap B.subtype
  haveI : Finite Q := finite_valueGroup_quotient (K := K) vL
  haveI : Fintype Q := Fintype.ofFinite Q
  have h_card' : Fintype.card Q = e := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  let eqv : Q ≃ Fin e := Fintype.equivFinOfCardEq h_card'
  let z_sub : Fin e → B := fun i ↦ Quotient.out (eqv.symm i)
  have hz_val : ∀ i, ((z_sub i).val : ΓL) ∈ Set.range vL := fun i ↦ by
    have h_eq : Units.val '' (B : Set ΓLˣ) = Set.range vL \ {0} :=
      MonoidWithZeroHom.valueGroup_eq_range vL
    have h_in : ((z_sub i).val : ΓL) ∈ Units.val '' (B : Set ΓLˣ) :=
      Set.mem_image_of_mem _ (z_sub i).property
    rw [h_eq] at h_in
    exact h_in.1
  choose z hz using hz_val
  have hz_nz : ∀ i, z i ≠ 0 := fun i ↦ by
    intro hz0
    have h_eq := hz i
    rw [hz0, Valuation.map_zero] at h_eq
    exact Units.ne_zero (z_sub i).val h_eq.symm
  have hz_dist :=
    distinct_cosets_of_quotient_out vL he A B rfl rfl eqv z hz hz_nz
  have h_indep :=
    valuation_independence vK vL z u hz_nz hz_dist hu_val_one hu_indep
  have h_card := LinearIndependent.fintype_card_le_finrank h_indep
  have h_card_prod : Fintype.card (Fin e × Fin f) = e * f := by simp
  rwa [h_card_prod] at h_card

/-- Alias matching the previous declaration name. -/
theorem Valuation.fundamentalInequality [FiniteDimensional K L] :
    ramificationIndex vK vL * residueDegree vK vL ≤ Module.finrank K L :=
  fundamental_inequality vK vL

end
