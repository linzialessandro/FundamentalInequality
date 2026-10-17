/-
Copyright (c) 2026 Alessandro Linzi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Linzi
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.FieldTheory.Tower
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Ramification index, residue degree, and the fundamental inequality

This file defines the ramification index and residue degree of a valuative field
extension, and proves the simple fundamental inequality

\[
  e(L/K)\, f(L/K) \le [L : K]
\]

for a finite extension, including finiteness of both invariants.

## Main definitions

* `ValuativeExtension.residueDegree` : the residue degree `f(L/K) = [𝓀[L] : 𝓀[K]]`.
* `ValuativeExtension.ramificationIndex` : the ramification index `e(L/K)`, the index
  of the image of `(ValueGroupWithZero K)ˣ` under `mapValueGroupWithZero`.
* `ValuativeExtension.IsImmediate` : the value-group map and the residue-field map
  are both surjective.

Both numerical invariants are `ℕ`, with the same convention as `Module.finrank` and
`Subgroup.index`: an infinite value is recorded as `0`.

## Main results

* `residueDegree_self`, `ramificationIndex_self` : the identity extension has `e = f = 1`.
* `residueDegree_mul`, `ramificationIndex_mul` : multiplicativity in towers.
  The middle factor of `ramificationIndex_mul` is `ramificationIndex K F`, the index
  computed in `ValueGroupWithZero F` and transported along `mapValueGroupWithZero F L`.
* `residueDegree_pos`, `ramificationIndex_ne_zero` : finiteness for a finite extension.
* `exists_max_val_mul` : the valuation form of valuation independence.
* `valuation_independence` : the same products are `K`-linearly independent.
* `fundamental_inequality`.
* `isImmediate_iff_ramificationIndex_eq_one_and_residueDegree_eq_one`.

## Implementation notes

`ValuativeExtension K L` says that the valuative relation on `K` is the one induced by `L`.
The canonical valuations are then related by `HasExtension`, which supplies the algebra
`𝒪[K] → 𝒪[L]` and, after the local-homomorphism instance proved here, the algebra
`𝓀[K] → 𝓀[L]`.

The ramification index is the subgroup index of

```
(Units.map (mapValueGroupWithZero K L)).range    ≤    (ValueGroupWithZero L)ˣ
```

`mapValueGroupWithZero` is strictly monotone, so the induced map on units is injective.
Multiplicativity in a tower is `Subgroup.index_map_of_injective` applied to that map:
the factor `e(F/K)` is moved from `ValueGroupWithZero F` into `ValueGroupWithZero L`
along `mapValueGroupWithZero F L`.

## References

* [F.-V. Kuhlmann, *Valuation Theory*][kuhlmannValuation], book in preparation,
  <https://www.fvkuhlmann.de/Fvkbook.htm>, Chapter 6, §6.3, Lemmas 6.12, 6.13 and 6.16,
  and Chapter 6, Definition 6.1 for immediate extensions.
* [N. Bourbaki, *Commutative Algebra*][bourbaki1989b], Chapter VI.

## Tags

valuation, ramification index, residue degree, fundamental inequality, valued field
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

open IsLocalRing ValuativeRel Valuation Valuation.HasExtension

namespace ValuativeExtension

variable {K L : Type*}

/-- Subgroups of the unit group of a value group are normal. -/
instance subgroup_normal (K : Type*) [Field K] [ValuativeRel K]
    (H : Subgroup (ValueGroupWithZero K)ˣ) : H.Normal where
  conj_mem n hn g := by
    rwa [mul_comm g n, mul_inv_cancel_right]

/-- A ring with its own valuative relation is a valuative extension of itself. -/
instance (K : Type*) [CommRing K] [ValuativeRel K] : ValuativeExtension K K where
  vle_iff_vle _ _ := by simp

section Field

variable [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- The canonical valuations of a valuative field extension form a `HasExtension`. -/
instance valuation_hasExtension (K L : Type*) [Field K] [Field L] [ValuativeRel K]
    [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] :
    (valuation K).HasExtension (valuation L) where
  val_isEquiv_comap := fun x y ↦ by
    simp only [Valuation.comap_apply]
    rw [← Compatible.vle_iff_le (v := valuation L), vle_iff_vle,
      Compatible.vle_iff_le (v := valuation K)]

/-- The structure map of valuation rings in a valuative field extension is local. -/
instance instIsLocalHom_integer (K L : Type*) [Field K] [Field L] [ValuativeRel K]
    [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] :
    IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) where
  map_nonunit x hx := by
    have hx1 : valuation L (algebraMap 𝒪[K] 𝒪[L] x : L) = 1 :=
      (integer.integers (valuation L)).isUnit_iff_valuation_eq_one.mp hx
    rw [val_algebraMap] at hx1
    rw [(integer.integers (valuation K)).isUnit_iff_valuation_eq_one]
    exact (val_map_eq_one_iff (valuation K) (valuation L) (x : K)).mp hx1

/-! ### Definitions -/

/-- The residue degree `f(L/K) = [𝓀[L] : 𝓀[K]]`.

This is `0` when the residue-field extension is infinite, matching `Module.finrank`. -/
def residueDegree (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : ℕ :=
  Module.finrank 𝓀[K] 𝓀[L]

/-- The ramification index `e(L/K)`.

It is the index of the image of `(ValueGroupWithZero K)ˣ` in `(ValueGroupWithZero L)ˣ`
under `mapValueGroupWithZero`. This is `0` when the index is infinite, matching
`Subgroup.index`. -/
def ramificationIndex (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : ℕ :=
  (Units.map (mapValueGroupWithZero K L).toMonoidHom).range.index

/-- Value-group units of `L`, modulo the image of the value-group units of `K`. -/
abbrev valueGroupQuotient (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] :=
  (ValueGroupWithZero L)ˣ ⧸ (Units.map (mapValueGroupWithZero K L).toMonoidHom).range

/-- A valuative extension is immediate when neither the value group nor the residue
field grows. This is Kuhlmann's Definition 6.1. -/
def IsImmediate (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : Prop :=
  Function.Surjective (mapValueGroupWithZero K L) ∧
    Function.Surjective (algebraMap 𝓀[K] 𝓀[L])

/-! ### Identity extension -/

/-- `mapValueGroupWithZero` along the identity algebra is the identity. -/
@[simp]
theorem mapValueGroupWithZero_self (K : Type*) [Field K] [ValuativeRel K] :
    mapValueGroupWithZero K K = .id _ := by
  ext x
  obtain ⟨a, rfl⟩ := valuation_surjective (K := K) x
  simp

/-- The residue degree of the identity extension is `1`. -/
@[simp]
theorem residueDegree_self (K : Type*) [Field K] [ValuativeRel K] :
    residueDegree K K = 1 := by
  unfold residueDegree
  exact Module.finrank_self 𝓀[K]

/-- The ramification index of the identity extension is `1`. -/
@[simp]
theorem ramificationIndex_self (K : Type*) [Field K] [ValuativeRel K] :
    ramificationIndex K K = 1 := by
  rw [ramificationIndex, mapValueGroupWithZero_self]
  have hid : Units.map (MonoidWithZeroHom.id (ValueGroupWithZero K)).toMonoidHom =
      MonoidHom.id _ := by
    ext u
    simp
  rw [hid, MonoidHom.range_eq_top_of_surjective _ fun u ↦ ⟨u, rfl⟩, Subgroup.index_top]

/-! ### Tower multiplicativity -/

variable {F : Type*} [Field F] [ValuativeRel F] [Algebra K F] [Algebra F L]
  [IsScalarTower K F L]

omit [ValuativeExtension K L] in
/-- A tower of valuative extensions is a valuative extension. -/
theorem tower [ValuativeExtension K F] [ValuativeExtension F L] : ValuativeExtension K L where
  vle_iff_vle a b := by
    rw [IsScalarTower.algebraMap_apply K F L, IsScalarTower.algebraMap_apply K F L,
      vle_iff_vle (A := F) (B := L), vle_iff_vle (A := K) (B := F)]

/-- `mapValueGroupWithZero` is functorial in towers of valuative extensions. -/
theorem mapValueGroupWithZero_comp [ValuativeExtension K F] [ValuativeExtension F L] :
    (mapValueGroupWithZero F L).comp (mapValueGroupWithZero K F) =
      mapValueGroupWithZero K L := by
  ext γ
  obtain ⟨x, rfl⟩ := valuation_surjective (K := K) γ
  simp only [MonoidWithZeroHom.comp_apply, mapValueGroupWithZero_valuation]
  rw [← IsScalarTower.algebraMap_apply K F L]

/-- The valuation rings of a tower of valuative extensions form a scalar tower. -/
instance instIsScalarTower_integer [ValuativeExtension K F] [ValuativeExtension F L] :
    IsScalarTower 𝒪[K] 𝒪[F] 𝒪[L] := by
  refine .of_algebraMap_eq fun x ↦ ?_
  apply Subtype.ext
  simp only [val_algebraMap]
  exact IsScalarTower.algebraMap_apply K F L (x : K)

/-- Residue degree is multiplicative in towers (Kuhlmann, Lemma 6.16). -/
theorem residueDegree_mul [ValuativeExtension K F] [ValuativeExtension F L] :
    residueDegree K F * residueDegree F L = residueDegree K L := by
  simpa [residueDegree] using
    Module.finrank_mul_finrank (F := 𝓀[K]) (K := 𝓀[F]) (A := 𝓀[L])

/-- Ramification index is multiplicative in towers (Kuhlmann, Lemma 6.16).

The factor `ramificationIndex K F` is the index in `(ValueGroupWithZero F)ˣ`.
Injectivity of `mapValueGroupWithZero F L` transports it into `(ValueGroupWithZero L)ˣ`,
where it multiplies `ramificationIndex F L`. -/
theorem ramificationIndex_mul [ValuativeExtension K F] [ValuativeExtension F L] :
    ramificationIndex K F * ramificationIndex F L = ramificationIndex K L := by
  have hcomp := mapValueGroupWithZero_comp (K := K) (F := F) (L := L)
  have hunits : Units.map (mapValueGroupWithZero K L).toMonoidHom =
      (Units.map (mapValueGroupWithZero F L).toMonoidHom).comp
        (Units.map (mapValueGroupWithZero K F).toMonoidHom) := by
    ext u
    simpa [MonoidWithZeroHom.comp_apply] using (congr($hcomp (u : _))).symm
  have hinj : Function.Injective (Units.map (mapValueGroupWithZero F L).toMonoidHom) :=
    Units.map_injective (mapValueGroupWithZero_strictMono (A := F) (B := L)).injective
  rw [ramificationIndex, ramificationIndex, ramificationIndex, hunits, MonoidHom.range_comp,
    ← Subgroup.index_map_of_injective
      (Units.map (mapValueGroupWithZero K F).toMonoidHom).range hinj]

/-! ### Immediate extensions -/

/-- `e(L/K) = 1` if and only if `mapValueGroupWithZero K L` is surjective. -/
theorem ramificationIndex_eq_one_iff :
    ramificationIndex K L = 1 ↔ Function.Surjective (mapValueGroupWithZero K L) := by
  classical
  rw [ramificationIndex, Subgroup.index_eq_one, MonoidHom.range_eq_top]
  constructor
  · intro h γ
    by_cases hγ : γ = 0
    · exact ⟨0, by simp [hγ]⟩
    · obtain ⟨u, hu⟩ := h (Units.mk0 γ hγ)
      refine ⟨(u : ValueGroupWithZero K), ?_⟩
      simpa [Units.ext_iff] using hu
  · intro h u
    obtain ⟨γ, hγ⟩ := h (u : ValueGroupWithZero L)
    have hγ0 : γ ≠ 0 := by
      intro h0
      exact u.ne_zero (by simpa [h0] using hγ.symm)
    refine ⟨Units.mk0 γ hγ0, ?_⟩
    ext
    simpa using hγ

/-- `f(L/K) = 1` if and only if the residue-field algebra map is surjective. -/
theorem residueDegree_eq_one_iff :
    residueDegree K L = 1 ↔ Function.Surjective (algebraMap 𝓀[K] 𝓀[L]) := by
  rw [residueDegree, Algebra.finrank_eq_one_iff_bijective_algebraMap]
  exact ⟨And.right, fun h ↦ ⟨RingHom.injective _, h⟩⟩

/-- An extension is immediate if and only if `e(L/K) = f(L/K) = 1`. -/
theorem isImmediate_iff_ramificationIndex_eq_one_and_residueDegree_eq_one :
    IsImmediate K L ↔ ramificationIndex K L = 1 ∧ residueDegree K L = 1 := by
  rw [IsImmediate, ramificationIndex_eq_one_iff, residueDegree_eq_one_iff]

/-! ### Cosets of the value group -/

/-- If `v(c z₁) = v(d z₂)`, then `v(z₁)` and `v(z₂)` lie in the same coset of the image
of `(ValueGroupWithZero K)ˣ`. -/
lemma quotientMk_eq_of_val_mul_eq {c d : K} {z₁ z₂ : L}
    (hc : c ≠ 0) (hd : d ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (h : valuation L (algebraMap K L c * z₁) = valuation L (algebraMap K L d * z₂)) :
    (Units.mk0 (valuation L z₁) ((valuation L).ne_zero_iff.mpr hz₁) : valueGroupQuotient K L) =
      Units.mk0 (valuation L z₂) ((valuation L).ne_zero_iff.mpr hz₂) := by
  set φ := (mapValueGroupWithZero K L).toMonoidHom
  set u₁ := Units.mk0 (valuation L z₁) ((valuation L).ne_zero_iff.mpr hz₁)
  set u₂ := Units.mk0 (valuation L z₂) ((valuation L).ne_zero_iff.mpr hz₂)
  set uc := Units.mk0 (valuation K c) ((valuation K).ne_zero_iff.mpr hc)
  set ud := Units.mk0 (valuation K d) ((valuation K).ne_zero_iff.mpr hd)
  rw [QuotientGroup.eq_iff_div_mem]
  refine ⟨uc⁻¹ * ud, ?_⟩
  apply Units.ext
  simp only [div_eq_mul_inv, Units.val_inv_eq_inv_val, Units.val_mul, Units.coe_map,
    MonoidHom.map_mul, MonoidHom.map_inv, uc, ud, u₁, u₂, φ, Units.val_mk0]
  symm
  have h' : valuation L (algebraMap K L c) * valuation L z₁ =
      valuation L (algebraMap K L d) * valuation L z₂ := by
    simpa [Valuation.map_mul] using h
  calc
    valuation L z₁ * (valuation L z₂)⁻¹
      = (valuation L (algebraMap K L c))⁻¹ *
          (valuation L (algebraMap K L c) * valuation L z₁) * (valuation L z₂)⁻¹ := by
        rw [← mul_assoc, inv_mul_cancel₀ ((valuation L).ne_zero_iff.mpr
          ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hc)), one_mul]
    _ = (valuation L (algebraMap K L c))⁻¹ *
          (valuation L (algebraMap K L d) * valuation L z₂) * (valuation L z₂)⁻¹ := by
        rw [h']
    _ = (valuation L (algebraMap K L c))⁻¹ * valuation L (algebraMap K L d) := by
        rw [mul_assoc, mul_assoc, mul_inv_cancel₀ ((valuation L).ne_zero_iff.mpr hz₂), mul_one]
    _ = (mapValueGroupWithZero K L (valuation K c))⁻¹ *
          mapValueGroupWithZero K L (valuation K d) := by
        rw [← mapValueGroupWithZero_valuation, ← mapValueGroupWithZero_valuation]

/-! ### Valuation of finite sums -/

/-- A finite sum of nonzero terms with pairwise distinct valuations cannot vanish. -/
lemma exists_eq_val_of_sum_eq_zero {I : Type*} [Fintype I] [Nonempty I] (f : I → L)
    (h_sum : ∑ i, f i = 0) (h_nz : ∀ i, f i ≠ 0) :
    ∃ i j, i ≠ j ∧ valuation L (f i) = valuation L (f j) := by
  classical
  by_contra h_dist
  push Not at h_dist
  obtain ⟨j, hj, hj_max⟩ :=
    Finset.exists_max_image Finset.univ (fun i ↦ valuation L (f i)) Finset.univ_nonempty
  have h_strict : ∀ i ∈ Finset.univ \ {j}, valuation L (f i) < valuation L (f j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact lt_of_le_of_ne (hj_max i (Finset.mem_univ i)) (h_dist i j hi.2)
  have h_val := map_sum_eq_of_lt (valuation L) hj h_strict
  rw [h_sum, map_zero] at h_val
  exact ((valuation L).ne_zero_iff.mpr (h_nz j)) h_val.symm

omit [ValuativeRel K] [ValuativeExtension K L] in
/-- Elements whose valuations lie in pairwise distinct cosets of `v(Kˣ)` are linearly
independent over `K`. This is the one-unit case of Kuhlmann's Lemma 6.12. -/
theorem linearIndependent_of_val_distinct_coset {I : Type*} (z : I → L)
    (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i j, i ≠ j → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      valuation L (algebraMap K L c * z i) ≠ valuation L (algebraMap K L d * z j)) :
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
  have : Nonempty s_nz := h_snz_nonempty.to_subtype
  let f : s_nz → L := fun ⟨i, _⟩ ↦ algebraMap K L (g i) * z i
  have hf_sum : ∑ i : s_nz, f i = 0 := by
    have h1 : ∑ i : s_nz, f i = ∑ i ∈ s_nz, algebraMap K L (g i) * z i :=
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
    rw [h3, hg]
  have hf_nz : ∀ i : s_nz, f i ≠ 0 := by
    intro ⟨i, hi⟩
    rw [hs_nz, Finset.mem_filter] at hi
    exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hi.2) (hz_nz i)
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hval⟩ :=
    exists_eq_val_of_sum_eq_zero f hf_sum hf_nz
  have hij' : i ≠ j := fun h ↦ hij (Subtype.ext h)
  rw [hs_nz, Finset.mem_filter] at hi hj
  exact hz_dist i j hij' (g i) (g j) hi.2 hj.2 hval

/-! ### Residue lifts -/

/-- The residue of an element of valuation `1`. -/
def residueOfValOne {u : L} (hu : valuation L u = 1) : 𝓀[L] :=
  residue 𝒪[L] ⟨u, (mem_integer_iff _ _).mpr hu.le⟩

/-- An element of the valuation ring with nonzero residue is a unit, hence has valuation `1`. -/
lemma val_eq_one_of_residue_ne_zero {u : 𝒪[L]} (h : residue 𝒪[L] u ≠ 0) :
    valuation L (u : L) = 1 :=
  (integer.integers (valuation L)).isUnit_iff_valuation_eq_one.mp
    ((residue_ne_zero_iff_isUnit u).mp h)

/-- Lift a family of residues to the valuation ring. -/
lemma exists_residue_lift {J : Type*} (x : J → 𝓀[L]) :
    ∃ u : J → 𝒪[L], ∀ j, residue 𝒪[L] (u j) = x j :=
  ⟨fun j ↦ (residue_surjective (x j)).choose,
    fun j ↦ (residue_surjective (x j)).choose_spec⟩

/-! ### Scaling step -/

/-- A nontrivial finite family of coefficients has one of maximal valuation, and that
coefficient is nonzero. -/
lemma exists_max_val_coeff {J : Type*} [Finite J] (d : J → K) (hd : ∃ j, d j ≠ 0) :
    ∃ j0, d j0 ≠ 0 ∧ ∀ j, valuation K (d j) ≤ valuation K (d j0) := by
  have : Fintype J := Fintype.ofFinite J
  have : Nonempty J := ⟨hd.choose⟩
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j ↦ valuation K (d j))
    Finset.univ_nonempty
  refine ⟨j0, ?_, fun j ↦ hj0 j (Finset.mem_univ _)⟩
  obtain ⟨j, hj⟩ := hd
  have hle := hj0 j (Finset.mem_univ _)
  exact (valuation K).ne_zero_iff.mp <| ne_of_gt <|
    lt_of_lt_of_le (lt_of_le_of_ne zero_le ((valuation K).ne_zero_iff.mpr hj).symm) hle

omit [ValuativeRel K] [ValuativeRel L] [ValuativeExtension K L] in
/-- Factor a linear combination through the coefficient of maximal valuation. -/
lemma sum_eq_coeff_mul_scaled {J : Type*} [Fintype J] (u : J → L) (d : J → K) {j0 : J}
    (hd0 : d j0 ≠ 0) :
    ∑ j, algebraMap K L (d j) * u j =
      algebraMap K L (d j0) * ∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j := by
  rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun j _ ↦ ?_).symm
  rw [← mul_assoc, ← map_mul]
  congr 1
  field_simp [hd0]

/-! ### Residue combination -/

/-- After scaling so that one coefficient has valuation `1` and the others have valuation
at most `1`, the combination lies in `𝒪[L]` and is a unit. The distinguished residue is `1`,
so residue-linear independence keeps the combination nonzero. -/
lemma val_scaledSum_eq_one {J : Type*} [Fintype J] (u : J → L)
    (hu : ∀ j, valuation L (u j) = 1)
    (hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j)))
    (d : J → K) (j0 : J) (hd0 : d j0 ≠ 0)
    (hmax : ∀ j, valuation K (d j) ≤ valuation K (d j0)) :
    valuation L (∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j) = 1 := by
  have hle (j : J) : valuation K (d j * (d j0)⁻¹) ≤ 1 := by
    have hpos : 0 < valuation K (d j0) :=
      lt_of_le_of_ne zero_le ((valuation K).ne_zero_iff.mpr hd0).symm
    rw [map_mul, map_inv₀]
    exact (mul_inv_le_iff₀ hpos).mpr (by simpa using hmax j)
  have hleL (j : J) : valuation L (algebraMap K L (d j * (d j0)⁻¹)) ≤ 1 :=
    (val_map_le_one_iff (valuation K) (valuation L) _).mpr (hle j)
  let cK (j : J) : 𝒪[K] := ⟨d j * (d j0)⁻¹, (mem_integer_iff _ _).mpr (hle j)⟩
  have hcK1 : cK j0 = 1 := by
    ext
    exact mul_inv_cancel₀ hd0
  let cL (j : J) : 𝒪[L] :=
    ⟨algebraMap K L (d j * (d j0)⁻¹), (mem_integer_iff _ _).mpr (hleL j)⟩
  let uO (j : J) : 𝒪[L] := ⟨u j, (mem_integer_iff _ _).mpr (hu j).le⟩
  have hc_map (j : J) : cL j = algebraMap 𝒪[K] 𝒪[L] (cK j) := by
    ext
    simp [cL, cK, val_algebraMap]
  have hsum_coe : ((∑ j, cL j * uO j : 𝒪[L]) : L) =
      ∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j := by
    rw [← Subring.coe_subtype, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, Subring.coe_subtype]
  have hres : residue 𝒪[L] (∑ j, cL j * uO j) =
      ∑ j, residue 𝒪[K] (cK j) • residueOfValOne (hu j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, Algebra.smul_def]
    have hc : residue 𝒪[L] (cL j) =
        algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] (cK j)) := by
      rw [hc_map, ResidueField.algebraMap_residue]
    have huO : residue 𝒪[L] (uO j) = residueOfValOne (hu j) := by
      simp [residueOfValOne, uO]
    rw [hc, huO]
  have hnz : ∑ j, residue 𝒪[K] (cK j) • residueOfValOne (hu j) ≠ 0 := by
    intro hz
    have hzero := (Fintype.linearIndependent_iff.mp hindep)
      (fun j ↦ residue 𝒪[K] (cK j)) hz j0
    have h1 : residue 𝒪[K] (cK j0) = 1 := by rw [hcK1, map_one]
    exact one_ne_zero (h1 ▸ hzero)
  have hunit : IsUnit (∑ j, cL j * uO j) :=
    (residue_ne_zero_iff_isUnit _).mp (by rwa [hres])
  have hval :=
    (integer.integers (valuation L)).isUnit_iff_valuation_eq_one.mp hunit
  rw [← hsum_coe]
  exact hval

/-- A nontrivial `K`-linear combination of valuation-one elements with `𝓀[K]`-linearly
independent residues has the valuation of one of its maximal terms. -/
lemma exists_max_val_of_residueIndependent {J : Type*} [Fintype J] (u : J → L)
    (hu : ∀ j, valuation L (u j) = 1)
    (hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j)))
    (d : J → K) (hd : ∃ j, d j ≠ 0) :
    ∃ j0, valuation L (∑ j, algebraMap K L (d j) * u j) =
        valuation L (algebraMap K L (d j0) * u j0) ∧
      ∀ j, valuation L (algebraMap K L (d j) * u j) ≤
        valuation L (algebraMap K L (d j0) * u j0) := by
  obtain ⟨j0, hd0, hmax⟩ := exists_max_val_coeff d hd
  refine ⟨j0, ?_, ?_⟩
  · rw [sum_eq_coeff_mul_scaled u d hd0, map_mul,
      val_scaledSum_eq_one u hu hindep d j0 hd0 hmax, mul_one, map_mul, hu j0, mul_one]
  · intro j
    rw [map_mul, map_mul, hu j, hu j0, mul_one, mul_one]
    exact (val_map_le_iff (valuation K) (valuation L) (d j) (d j0)).mpr (hmax j)

/-! ### Distinct-coset sum (Kuhlmann, Lemma 6.12) -/

/-- For each index in the support, the corresponding `u`-block has a nonzero coefficient
of maximal valuation, and the block valuation equals that coefficient's valuation. -/
private lemma exists_block_max_coeff {I J : Type*} [Fintype J] (u : J → L)
    (hu : ∀ j, valuation L (u j) = 1)
    (hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j)))
    (c : I × J → K) (i : I) (hi : ∃ j, c (i, j) ≠ 0) :
    ∃ j0, c (i, j0) ≠ 0 ∧
      valuation L (∑ j, algebraMap K L (c (i, j)) * u j) =
        valuation L (algebraMap K L (c (i, j0))) ∧
      ∀ j, valuation L (algebraMap K L (c (i, j)) * u j) ≤
        valuation L (algebraMap K L (c (i, j0)) * u j0) := by
  obtain ⟨j0, hj_eq, hj_le⟩ :=
    exists_max_val_of_residueIndependent u hu hindep (fun j ↦ c (i, j)) hi
  refine ⟨j0, ?_, by rw [hj_eq, map_mul, hu j0, mul_one], hj_le⟩
  intro hc0
  obtain ⟨j, hj⟩ := hi
  have hle := hj_le j
  rw [hc0, map_zero, zero_mul, map_zero] at hle
  rcases mul_eq_zero.mp ((valuation L).zero_iff.mp (le_antisymm hle zero_le)) with h | h
  · exact hj ((map_eq_zero_iff _ (algebraMap K L).injective).mp h)
  · have hv := hu j
    rw [h, map_zero] at hv
    exact zero_ne_one hv

/-- Valuation independence of the products `z i * u j` (Kuhlmann, Lemma 6.12).

If the values `v(z i)` lie in distinct cosets of `v(Kˣ)` and the residues of the units
`u j` are linearly independent over `𝓀[K]`, then a nontrivial `K`-linear combination of
the products has the valuation of one of its maximal terms. -/
theorem exists_max_val_mul {I J : Type*} [Fintype I] [Fintype J]
    (z : I → L) (u : J → L) (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i i', i ≠ i' → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      valuation L (algebraMap K L c * z i) ≠ valuation L (algebraMap K L d * z i'))
    (hu : ∀ j, valuation L (u j) = 1)
    (hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j)))
    (c : I × J → K) (hc : ∃ p, c p ≠ 0) :
    ∃ p0, c p0 ≠ 0 ∧
      valuation L (∑ p, algebraMap K L (c p) * (z p.1 * u p.2)) =
        valuation L (algebraMap K L (c p0) * (z p0.1 * u p0.2)) ∧
      ∀ p, valuation L (algebraMap K L (c p) * (z p.1 * u p.2)) ≤
        valuation L (algebraMap K L (c p0) * (z p0.1 * u p0.2)) := by
  classical
  let g : I → L := fun i ↦ ∑ j, algebraMap K L (c (i, j)) * u j
  have h_sum : ∑ p : I × J, algebraMap K L (c p) * (z p.1 * u p.2) = ∑ i, z i * g i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hterm (j : J) : algebraMap K L (c (i, j)) * (z i * u j) =
        z i * (algebraMap K L (c (i, j)) * u j) := by
      rw [mul_left_comm]
    simp_rw [hterm, ← Finset.mul_sum]
    rfl
  set sI := Finset.univ.filter (fun i ↦ ∃ j, c (i, j) ≠ 0) with hsI
  obtain ⟨⟨i_nz, j_nz⟩, hc_nz⟩ := hc
  have hsI_nonempty : sI.Nonempty := by
    refine ⟨i_nz, ?_⟩
    rw [hsI, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨j_nz, hc_nz⟩⟩
  have h_g (i : I) (hi : i ∈ sI) :
      ∃ j0, c (i, j0) ≠ 0 ∧
        valuation L (g i) = valuation L (algebraMap K L (c (i, j0))) ∧
        ∀ j, valuation L (algebraMap K L (c (i, j)) * u j) ≤
          valuation L (algebraMap K L (c (i, j0)) * u j0) := by
    rw [hsI, Finset.mem_filter] at hi
    exact exists_block_max_coeff u hu hindep c i hi.2
  have h_g_nz (i : I) (hi : i ∈ sI) : g i ≠ 0 := by
    intro hg
    obtain ⟨j0, hj0, hval, _⟩ := h_g i hi
    exact hj0 ((map_eq_zero_iff _ (algebraMap K L).injective).mp
      ((valuation L).zero_iff.mp (by simpa [hg] using hval.symm)))
  have val_term (i : I) (j : J) :
      valuation L (algebraMap K L (c (i, j)) * (z i * u j)) =
        valuation L (algebraMap K L (c (i, j)) * z i) := by
    rw [← mul_assoc, map_mul, hu j, mul_one]
  have val_coeff_of_le {i : I} {j j' : J}
      (hle : valuation L (algebraMap K L (c (i, j)) * u j) ≤
        valuation L (algebraMap K L (c (i, j')) * u j')) :
      valuation L (algebraMap K L (c (i, j))) ≤
        valuation L (algebraMap K L (c (i, j'))) := by
    simpa [map_mul, hu j, hu j', mul_one] using hle
  have h_block (i : I) (hi : i ∈ sI) (j0 : J) (_hj0 : c (i, j0) ≠ 0)
      (hj0_le : ∀ j, valuation L (algebraMap K L (c (i, j)) * u j) ≤
        valuation L (algebraMap K L (c (i, j0)) * u j0)) :
      valuation L (z i * g i) =
        valuation L (algebraMap K L (c (i, j0)) * (z i * u j0)) := by
    obtain ⟨j1, _, hval, hj1_le⟩ := h_g i hi
    have h_eq_coeff : valuation L (algebraMap K L (c (i, j0))) =
        valuation L (algebraMap K L (c (i, j1))) :=
      le_antisymm (val_coeff_of_le (hj1_le j0)) (val_coeff_of_le (hj0_le j1))
    rw [map_mul, hval, mul_comm, ← map_mul, val_term, map_mul, map_mul, h_eq_coeff]
  obtain ⟨i0, hi0_mem, hi0_max⟩ :=
    Finset.exists_max_image sI (fun i ↦ valuation L (z i * g i)) hsI_nonempty
  obtain ⟨j0, hj0_nz, -, hj0_le⟩ := h_g i0 hi0_mem
  have h_max_pos : 0 < valuation L (z i0 * g i0) :=
    lt_of_le_of_ne zero_le ((valuation L).ne_zero_iff.mpr
      (mul_ne_zero (hz_nz i0) (h_g_nz i0 hi0_mem))).symm
  have h_strict : ∀ i ∈ Finset.univ \ {i0},
      valuation L (z i * g i) < valuation L (z i0 * g i0) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    by_cases hsup : i ∈ sI
    · have hne : valuation L (z i * g i) ≠ valuation L (z i0 * g i0) := by
        obtain ⟨ji, hji, -, hji_le⟩ := h_g i hsup
        rw [h_block i hsup ji hji hji_le, h_block i0 hi0_mem j0 hj0_nz hj0_le,
          val_term, val_term]
        exact hz_dist i i0 hi.2 (c (i, ji)) (c (i0, j0)) hji hj0_nz
      exact lt_of_le_of_ne (hi0_max i hsup) hne
    · have hgi : g i = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hc0 : c (i, j) = 0 := by
          rw [hsI, Finset.mem_filter, not_and, not_exists] at hsup
          push Not at hsup
          exact hsup (Finset.mem_univ i) j
        simp [hc0]
      rw [hgi, mul_zero, map_zero]
      exact h_max_pos
  have h_val_sum : valuation L (∑ p, algebraMap K L (c p) * (z p.1 * u p.2)) =
      valuation L (z i0 * g i0) := by
    rw [h_sum]
    exact map_sum_eq_of_lt (valuation L) (Finset.mem_univ i0) h_strict
  refine ⟨(i0, j0), hj0_nz, ?_, ?_⟩
  · rw [h_val_sum, h_block i0 hi0_mem j0 hj0_nz hj0_le]
  · intro p
    have hp_le_block : valuation L (algebraMap K L (c p) * (z p.1 * u p.2)) ≤
        valuation L (z p.1 * g p.1) := by
      by_cases hpz : c p = 0
      · simp [hpz]
      · have hp_mem : p.1 ∈ sI := by
          rw [hsI, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ⟨p.2, hpz⟩⟩
        obtain ⟨ji, -, hval_i, hji_le⟩ := h_g p.1 hp_mem
        calc valuation L (algebraMap K L (c p) * (z p.1 * u p.2))
            _ = valuation L (algebraMap K L (c p) * z p.1) := val_term _ _
            _ = valuation L (algebraMap K L (c p)) * valuation L (z p.1) := map_mul _ _ _
            _ ≤ valuation L (algebraMap K L (c (p.1, ji))) * valuation L (z p.1) :=
                mul_le_mul_of_nonneg_right (val_coeff_of_le (hji_le p.2)) zero_le
            _ = valuation L (g p.1) * valuation L (z p.1) := by rw [hval_i]
            _ = valuation L (z p.1 * g p.1) := by rw [mul_comm, ← map_mul]
    have h_block_le : valuation L (z p.1 * g p.1) ≤ valuation L (z i0 * g i0) := by
      by_cases hsup : p.1 ∈ sI
      · exact hi0_max p.1 hsup
      · have hgi : g p.1 = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          have hc0 : c (p.1, j) = 0 := by
            rw [hsI, Finset.mem_filter, not_and, not_exists] at hsup
            push Not at hsup
            exact hsup (Finset.mem_univ p.1) j
          simp [hc0]
        rw [hgi, mul_zero, map_zero]
        exact zero_le
    calc valuation L (algebraMap K L (c p) * (z p.1 * u p.2))
        _ ≤ valuation L (z p.1 * g p.1) := hp_le_block
        _ ≤ valuation L (z i0 * g i0) := h_block_le
        _ = valuation L (algebraMap K L (c (i0, j0)) * (z i0 * u j0)) :=
            h_block i0 hi0_mem j0 hj0_nz hj0_le

/-- Linear independence of the products `z i * u j`. -/
theorem valuation_independence {I J : Type*} [Finite I] [Finite J]
    (z : I → L) (u : J → L) (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i i', i ≠ i' → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      valuation L (algebraMap K L c * z i) ≠ valuation L (algebraMap K L d * z i'))
    (hu : ∀ j, valuation L (u j) = 1)
    (hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j))) :
    LinearIndependent K (fun p : I × J ↦ z p.1 * u p.2) := by
  have : Fintype I := Fintype.ofFinite I
  have : Fintype J := Fintype.ofFinite J
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra h_not_zero
  push Not at h_not_zero
  obtain ⟨p0, hp0_nz, hp0_eq, hp0_le⟩ :=
    exists_max_val_mul z u hz_nz hz_dist hu hindep c h_not_zero
  have h_sum : ∑ p, algebraMap K L (c p) * (z p.1 * u p.2) = 0 := by
    rw [show ∑ p, algebraMap K L (c p) * (z p.1 * u p.2) = ∑ p, c p • (z p.1 * u p.2) by
      refine Finset.sum_congr rfl fun p _ ↦ (Algebra.smul_def _ _).symm, hc]
  rw [h_sum, map_zero] at hp0_eq
  have h_term_zero : valuation L (algebraMap K L (c p0) * (z p0.1 * u p0.2)) = 0 :=
    le_antisymm (hp0_eq ▸ hp0_le p0) zero_le
  rcases mul_eq_zero.mp ((valuation L).zero_iff.mp h_term_zero) with h_alg | h_zu
  · exact hp0_nz ((map_eq_zero_iff _ (algebraMap K L).injective).mp h_alg)
  · rcases mul_eq_zero.mp h_zu with h_z | h_u
    · exact hz_nz p0.1 h_z
    · have hv := hu p0.2
      rw [h_u, map_zero] at hv
      exact zero_ne_one hv

/-! ### Finiteness of `e` and `f` -/

/-- A finite `𝓀[K]`-linearly independent family of residues gives a `K`-linearly independent
family in `L` of the same cardinality. -/
lemma fintype_card_le_finrank_of_residueIndependent {J : Type*} [Fintype J]
    (u : J → L) (hu : ∀ j, valuation L (u j) = 1)
    (hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j)))
    [FiniteDimensional K L] :
    Fintype.card J ≤ Module.finrank K L := by
  have hli := valuation_independence (fun _ : Unit ↦ (1 : L)) u (fun _ ↦ one_ne_zero)
    (fun i i' h ↦ (h (Subsingleton.elim i i')).elim) hu hindep
  simpa [Fintype.card_prod, Fintype.card_unique] using hli.fintype_card_le_finrank

/-- For a finite extension, the residue-field extension is finite (Kuhlmann, Lemma 6.13). -/
theorem finite_residueField_extension [FiniteDimensional K L] : Module.Finite 𝓀[K] 𝓀[L] := by
  by_contra hinf
  let n := Module.finrank K L + 1
  let b := Module.Free.chooseBasis 𝓀[K] 𝓀[L]
  have hInf : Infinite (Module.Free.ChooseBasisIndex 𝓀[K] 𝓀[L]) := by
    rw [← not_finite_iff_infinite]
    intro hfin
    exact hinf (Module.Finite.of_basis b)
  obtain ⟨t, ht⟩ := Infinite.exists_subset_card_eq
    (Module.Free.ChooseBasisIndex 𝓀[K] 𝓀[L]) n
  let b_t : t → 𝓀[L] := fun i ↦ b i.1
  have hb_t : LinearIndependent 𝓀[K] b_t :=
    b.linearIndependent.comp _ Subtype.val_injective
  obtain ⟨u_sub, hu_sub⟩ := exists_residue_lift b_t
  have hu : ∀ j : t, valuation L (u_sub j : L) = 1 := fun j ↦
    val_eq_one_of_residue_ne_zero (by rw [hu_sub]; exact hb_t.ne_zero j)
  have hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j)) := by
    have h_eq : (fun j ↦ residueOfValOne (hu j)) = b_t := by
      funext j
      simp only [residueOfValOne]
      rw [show (⟨(u_sub j : L), _⟩ : 𝒪[L]) = u_sub j by ext; rfl, hu_sub]
    rwa [h_eq]
  have hle := fintype_card_le_finrank_of_residueIndependent
    (fun j ↦ (u_sub j : L)) hu hindep
  have : n ≤ Module.finrank K L := by
    convert hle
    simp [n, Fintype.card_coe, ht]
  exact Nat.not_succ_le_self _ this

/-- The residue degree of a finite extension is positive (Kuhlmann, Lemma 6.13). -/
theorem residueDegree_pos [FiniteDimensional K L] : 0 < residueDegree K L := by
  have : Module.Finite 𝓀[K] 𝓀[L] := finite_residueField_extension (K := K) (L := L)
  simpa [residueDegree] using Module.finrank_pos (R := 𝓀[K]) (M := 𝓀[L])

/-- For a finite extension, the value-group quotient is finite (Kuhlmann, Lemma 6.13). -/
theorem finite_valueGroup_quotient [FiniteDimensional K L] :
    Finite (valueGroupQuotient K L) := by
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  let n := Module.finrank K L + 1
  let Q := valueGroupQuotient K L
  obtain ⟨t, ht⟩ := Infinite.exists_subset_card_eq Q n
  have hz_ex : ∀ i : t, ∃ z : L, z ≠ 0 ∧
      valuation L z = ((i : Q).out : ValueGroupWithZero L) := by
    intro i
    obtain ⟨z, hz⟩ := valuation_surjective (K := L)
      ((i : Q).out : ValueGroupWithZero L)
    refine ⟨z, ?_, hz⟩
    intro hz0
    exact ((i : Q).out).ne_zero (by simpa [hz0] using hz.symm)
  choose z hz_nz hz using hz_ex
  have hz_dist : ∀ i j : t, i ≠ j → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      valuation L (algebraMap K L c * z i) ≠ valuation L (algebraMap K L d * z j) := by
    intro i j hij c d hc hd h_eq
    have hcoset := quotientMk_eq_of_val_mul_eq hc hd (hz_nz i) (hz_nz j) h_eq
    have hi : (Units.mk0 (valuation L (z i)) ((valuation L).ne_zero_iff.mpr (hz_nz i)) : Q) =
        (i : Q) := by
      rw [show Units.mk0 (valuation L (z i)) _ = (i : Q).out by
        ext; simpa using hz i, QuotientGroup.out_eq']
    have hj : (Units.mk0 (valuation L (z j)) ((valuation L).ne_zero_iff.mpr (hz_nz j)) : Q) =
        (j : Q) := by
      rw [show Units.mk0 (valuation L (z j)) _ = (j : Q).out by
        ext; simpa using hz j, QuotientGroup.out_eq']
    exact hij (Subtype.ext (hi.symm.trans (hcoset.trans hj)))
  have hs_ne : t.Nonempty := Finset.card_pos.mp (by rw [ht]; exact Nat.succ_pos _)
  have : Nonempty t := hs_ne.to_subtype
  have hli := linearIndependent_of_val_distinct_coset z hz_nz hz_dist
  have : n ≤ Module.finrank K L := by
    simpa [Fintype.card_coe, ht] using hli.fintype_card_le_finrank
  exact Nat.not_succ_le_self _ this

/-- The ramification index of a finite extension is nonzero (Kuhlmann, Lemma 6.13). -/
theorem ramificationIndex_ne_zero [FiniteDimensional K L] : ramificationIndex K L ≠ 0 := by
  have : Finite (valueGroupQuotient K L) := finite_valueGroup_quotient (K := K) (L := L)
  rw [ramificationIndex, Subgroup.index_eq_card]
  exact Finite.card_pos.ne'

/-- The ramification index of a finite extension is at least `1`. -/
theorem one_le_ramificationIndex [FiniteDimensional K L] : 1 ≤ ramificationIndex K L :=
  Nat.one_le_iff_ne_zero.mpr (ramificationIndex_ne_zero (K := K) (L := L))

/-! ### The fundamental inequality -/

/-- The fundamental inequality for a finite extension of valued fields
(Kuhlmann, Lemma 6.13): `e(L/K) * f(L/K) ≤ [L:K]`.

Both factors are positive, so the product is not the `0` recorded for an infinite
cardinal. -/
theorem fundamental_inequality [FiniteDimensional K L] :
    ramificationIndex K L * residueDegree K L ≤ Module.finrank K L := by
  let e := ramificationIndex K L
  let f := residueDegree K L
  have he : e ≠ 0 := ramificationIndex_ne_zero (K := K) (L := L)
  have hf : 0 < f := residueDegree_pos (K := K) (L := L)
  have : Nonempty (Fin e) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero he)
  have : Nonempty (Fin f) := Fin.pos_iff_nonempty.mp hf
  have : Module.Finite 𝓀[K] 𝓀[L] := finite_residueField_extension (K := K) (L := L)
  have hf_rank : Module.finrank 𝓀[K] 𝓀[L] = f := by
    simp [f, residueDegree]
  let b := Module.finBasisOfFinrankEq 𝓀[K] 𝓀[L] hf_rank
  obtain ⟨u_sub, hu_sub⟩ := exists_residue_lift b
  let u : Fin f → L := fun j ↦ (u_sub j : L)
  have hu : ∀ j, valuation L (u j) = 1 := fun j ↦
    val_eq_one_of_residue_ne_zero (by rw [hu_sub]; exact b.linearIndependent.ne_zero j)
  have hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j)) := by
    have h_eq : (fun j ↦ residueOfValOne (hu j)) = (b : Fin f → 𝓀[L]) := by
      funext j
      simp only [residueOfValOne]
      rw [show (⟨u j, _⟩ : 𝒪[L]) = u_sub j by ext; rfl, hu_sub]
    simpa [h_eq] using b.linearIndependent
  let Q := valueGroupQuotient K L
  have : Finite Q := finite_valueGroup_quotient (K := K) (L := L)
  have : Fintype Q := Fintype.ofFinite Q
  have h_card : Fintype.card Q = e := by
    unfold e
    rw [ramificationIndex, Subgroup.index_eq_card, ← Nat.card_eq_fintype_card]
  let eqv : Q ≃ Fin e := Fintype.equivFinOfCardEq h_card
  have hz_ex : ∀ i : Fin e, ∃ z : L, z ≠ 0 ∧
      valuation L z = ((eqv.symm i).out : ValueGroupWithZero L) := by
    intro i
    obtain ⟨z, hz⟩ := valuation_surjective (K := L)
      ((eqv.symm i).out : ValueGroupWithZero L)
    refine ⟨z, ?_, hz⟩
    intro hz0
    exact ((eqv.symm i).out).ne_zero (by simpa [hz0] using hz.symm)
  choose z hz_nz hz using hz_ex
  have hz_dist : ∀ i j : Fin e, i ≠ j → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      valuation L (algebraMap K L c * z i) ≠ valuation L (algebraMap K L d * z j) := by
    intro i j hij c d hc hd h_eq
    have hcoset := quotientMk_eq_of_val_mul_eq hc hd (hz_nz i) (hz_nz j) h_eq
    have hi : (Units.mk0 (valuation L (z i)) ((valuation L).ne_zero_iff.mpr (hz_nz i)) : Q) =
        eqv.symm i := by
      rw [show Units.mk0 (valuation L (z i)) _ = (eqv.symm i).out by
        ext; simpa using hz i, QuotientGroup.out_eq']
    have hj : (Units.mk0 (valuation L (z j)) ((valuation L).ne_zero_iff.mpr (hz_nz j)) : Q) =
        eqv.symm j := by
      rw [show Units.mk0 (valuation L (z j)) _ = (eqv.symm j).out by
        ext; simpa using hz j, QuotientGroup.out_eq']
    exact hij ((eqv.symm).injective (hi.symm.trans (hcoset.trans hj)))
  have h_indep := valuation_independence z u hz_nz hz_dist hu hindep
  have hcard := h_indep.fintype_card_le_finrank
  simpa [Fintype.card_prod, e, f] using hcard

end Field

end ValuativeExtension
