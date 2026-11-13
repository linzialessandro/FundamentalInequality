/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.Bridge
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Completeness uniqueness and the Ostrowski sum

Rank at most one lifts along a finite valuative extension. Over a complete
nonarchimedean base, a compatible rank-at-most-one valuative relation is
represented by the spectral norm. The Ostrowski sum then reduces to a single
term when uniqueness is known.

This file does not re-prove transitivity of `ValuativeExtension`: callers
use `ValuativeExtension.tower`.
-/

@[expose] public section

noncomputable section

open ValuativeRel ValuativeExtension
open scoped ValuativeRel BigOperators NNReal

/-! ### Rank lifting, uniqueness from completeness, and the Ostrowski sum -/

namespace ArtinSchreierBridge

open ValuativeRel ValuativeExtension

/-- Rank at most one lifts along a finite valuative extension: the image of the
value group has finite index, and a finite-index extension of a mul-archimedean
group remains mul-archimedean. -/
theorem isRankLeOne_of_finite
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [ValuativeExtension K L]
    [FiniteDimensional K L] [IsRankLeOne K] : IsRankLeOne L := by
  rw [ValuativeRel.isRankLeOne_iff_mulArchimedean] at *
  refine ⟨fun x {y} hy => ?_⟩
  have he : ramificationIndex K L ≠ 0 := ramificationIndex_ne_zero (K := K) (L := L)
  have hepos : 0 < ramificationIndex K L := Nat.pos_of_ne_zero he
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨1, zero_le⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact not_lt_zero hy
  have hy_pow_lt : 1 < y ^ ramificationIndex K L :=
    one_lt_pow₀ hy hepos.ne.symm
  let H := (Units.map (mapValueGroupWithZero K L).toMonoidHom).range
  have hxe : (Units.mk0 x hx) ^ ramificationIndex K L ∈ H := Subgroup.pow_index_mem H _
  have hye : (Units.mk0 y hy0) ^ ramificationIndex K L ∈ H := Subgroup.pow_index_mem H _
  obtain ⟨v, hv⟩ := hye
  have hv1 : 1 < (v : ValueGroupWithZero K) := by
    have hv' : mapValueGroupWithZero K L (v : ValueGroupWithZero K) =
        y ^ ramificationIndex K L := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hv
    have hlt : mapValueGroupWithZero K L (1 : ValueGroupWithZero K) <
        mapValueGroupWithZero K L (v : ValueGroupWithZero K) := by
      simpa [map_one, hv'] using hy_pow_lt
    exact (mapValueGroupWithZero_strictMono (A := K) (B := L)).lt_iff_lt.mp hlt
  obtain ⟨u, hu⟩ := hxe
  obtain ⟨n, hn⟩ := MulArchimedean.arch (u : ValueGroupWithZero K) hv1
  have hx_le' : x ^ ramificationIndex K L ≤ (y ^ n) ^ ramificationIndex K L := by
    have hφ : mapValueGroupWithZero K L (u : ValueGroupWithZero K) ≤
        mapValueGroupWithZero K L ((v : ValueGroupWithZero K) ^ n) :=
      (mapValueGroupWithZero_strictMono (A := K) (B := L)).le_iff_le.mpr hn
    have hu' : mapValueGroupWithZero K L (u : ValueGroupWithZero K) =
        x ^ ramificationIndex K L := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hu
    have hv' : mapValueGroupWithZero K L (v : ValueGroupWithZero K) =
        y ^ ramificationIndex K L := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hv
    have : x ^ ramificationIndex K L ≤ (y ^ ramificationIndex K L) ^ n := by
      simpa [hu', hv', map_pow] using hφ
    simpa [← pow_mul, mul_comm n] using this
  refine ⟨n, ?_⟩
  by_contra h
  have hlt : y ^ n < x := lt_of_not_ge h
  have : (y ^ n) ^ ramificationIndex K L < x ^ ramificationIndex K L :=
    pow_lt_pow_left₀ (ha := (zero_le : 0 ≤ y ^ n)) hlt he
  exact this.not_ge hx_le'

/-- Nontriviality of the value group lifts along a valuative extension. -/
theorem isNontrivial_of_valuativeExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [ValuativeExtension K L]
    [IsNontrivial K] : IsNontrivial L := by
  obtain ⟨γ, hγ0, hγ1⟩ := IsNontrivial.condition (R := K)
  refine ⟨mapValueGroupWithZero K L γ, ?_, ?_⟩
  · intro h
    exact hγ0 ((map_eq_zero (mapValueGroupWithZero K L)).mp h)
  · intro h
    apply hγ1
    exact (mapValueGroupWithZero_strictMono (A := K) (B := L)).injective (by simpa using h)

/-- An ultrametric real absolute value remains an absolute value after raising to a
positive real power. -/
def absoluteValue_rpow {R : Type*} [Field R] (f : AbsoluteValue R ℝ) {c : ℝ} (hc : 0 < c)
    (hultra : ∀ x y : R, f (x + y) ≤ max (f x) (f y)) :
    AbsoluteValue R ℝ where
  toFun x := f x ^ c
  map_mul' x y := by
    simp [map_mul, Real.mul_rpow (f.nonneg x) (f.nonneg y)]
  nonneg' x := Real.rpow_nonneg (f.nonneg x) c
  eq_zero' x := by
    rw [Real.rpow_eq_zero_iff_of_nonneg (f.nonneg x)]
    simp [hc.ne']
  add_le' x y := by
    have h₁ : f (x + y) ^ c ≤ max (f x) (f y) ^ c :=
      Real.rpow_le_rpow (f.nonneg _) (hultra x y) hc.le
    have h₂ : max (f x) (f y) ^ c = max (f x ^ c) (f y ^ c) := by
      rcases le_total (f x) (f y) with h | h
      · simp [max_eq_right h, max_eq_right (Real.rpow_le_rpow (f.nonneg _) h hc.le)]
      · simp [max_eq_left h, max_eq_left (Real.rpow_le_rpow (f.nonneg _) h hc.le)]
    exact (h₁.trans_eq h₂).trans
      (max_le_add_of_nonneg (Real.rpow_nonneg (f.nonneg x) c)
        (Real.rpow_nonneg (f.nonneg y) c))

theorem absoluteValue_rpow_apply {R : Type*} [Field R] (f : AbsoluteValue R ℝ) {c : ℝ} (hc : 0 < c)
    (hultra : ∀ x y : R, f (x + y) ≤ max (f x) (f y)) (x : R) :
    absoluteValue_rpow f hc hultra x = f x ^ c := rfl

/-- Over a complete nonarchimedean base, any rank-at-most-one valuative relation
that extends the base valuation is represented by the spectral norm. -/
theorem unique_valuativeRel_of_complete
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [ValuativeRel K] (hK : ∀ x y : K, x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖)
    (v : ValuativeRel L) (hv : letI := v; ValuativeExtension K L)
    [letI := v; IsRankLeOne L] [letI := v; IsNontrivial L] :
    ∀ x y : L, v.vle x y ↔ spectralNorm K L x ≤ spectralNorm K L y := by
  let := v
  let := hv
  have : Valuation.RankOne (valuation L) := inferInstance
  let f : AbsoluteValue L ℝ := Valuation.absoluteValue (valuation L)
  have hultra : ∀ x y : L, f (x + y) ≤ max (f x) (f y) :=
    fun x y => Valuation.norm_add_le (valuation L) x y
  have hf_vle : ∀ x y : L, v.vle x y ↔ f x ≤ f y := by
    intro x y
    refine (Valuation.vle_iff_le (valuation L) (x := x) (y := y)).trans ?_
    rw [← (valuation L).restrict_le_iff,
      ← (Valuation.RankOne.strictMono (valuation L)).le_iff_le]
    rfl
  let fK : AbsoluteValue K ℝ := f.under K
  let nK : AbsoluteValue K ℝ :=
    { toFun := fun x => ‖x‖
      map_mul' := norm_mul
      nonneg' := norm_nonneg
      eq_zero' := fun x => norm_eq_zero
      add_le' := norm_add_le }
  have hequiv : fK.IsEquiv nK := by
    intro a b
    change f (algebraMap K L a) ≤ f (algebraMap K L b) ↔ ‖a‖ ≤ ‖b‖
    rw [← hf_vle, ValuativeExtension.vle_iff_vle, hK]
  obtain ⟨c, hc, hpow⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  let g : AbsoluteValue L ℝ := absoluteValue_rpow f hc hultra
  have hg_ext : ∀ x : K, g (algebraMap K L x) = ‖x‖ := by
    intro x
    have hx := congrFun hpow x
    have hfK : fK x = f (algebraMap K L x) := rfl
    have hnK : nK x = ‖x‖ := rfl
    rw [hfK, hnK] at hx
    simpa [g, absoluteValue_rpow_apply] using hx
  intro x y
  have hx : g x = spectralNorm K L x := spectralNorm_unique_field_norm_ext hg_ext x
  have hy : g y = spectralNorm K L y := spectralNorm_unique_field_norm_ext hg_ext y
  rw [hf_vle, ← Real.rpow_le_rpow_iff (f.nonneg x) (f.nonneg y) hc, ← hx, ← hy]
  simp [g, absoluteValue_rpow_apply]

end ArtinSchreierBridge

/-! ### The Ostrowski sum for the unique compatible valuation -/

namespace ArtinSchreierBridge

open ValuativeRel ValuativeExtension
open scoped ValuativeRel BigOperators

/-- All compatible valuation extensions, identified by their valuative relations. -/
def Extensions (K L : Type*) [Field K] [Field L] [Algebra K L] [ValuativeRel K] :=
  {v : ValuativeRel L // letI := v; ValuativeExtension K L}

def extensionWeight {K L : Type*} [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] (w : Extensions K L) : ℕ :=
  letI := w.val
  letI := w.property
  ramificationIndex K L * residueDegree K L

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [ValuativeExtension K L]

/-- Uniqueness reduces the sum over all extension relations to one term. -/
theorem sum_eq_of_unique [Fintype (Extensions K L)]
    (hunique : ∀ w : Extensions K L, w.val = (inferInstance : ValuativeRel L)) :
    (∑ w : Extensions K L, extensionWeight w) =
      ramificationIndex K L * residueDegree K L := by
  classical
  let w₀ : Extensions K L := ⟨inferInstance, inferInstance⟩
  have hw : ∀ w : Extensions K L, w = w₀ := fun w => Subtype.ext (hunique w)
  have hu : (Finset.univ : Finset (Extensions K L)) = {w₀} := by
    ext w
    simp [hw w]
  rw [hu, Finset.sum_singleton]
  rfl

theorem sum_le_finrank_of_unique [FiniteDimensional K L] [Fintype (Extensions K L)]
    (hunique : ∀ w : Extensions K L, w.val = (inferInstance : ValuativeRel L)) :
    (∑ w : Extensions K L, extensionWeight w) ≤ Module.finrank K L := by
  rw [sum_eq_of_unique K L hunique]
  exact fundamental_inequality

theorem sum_strict_of_unique_immediate [Fintype (Extensions K L)]
    (hunique : ∀ w : Extensions K L, w.val = (inferInstance : ValuativeRel L))
    (q : ℕ) (hq : 1 < q)
    (he : ramificationIndex K L = 1) (hf : residueDegree K L = 1)
    (hn : Module.finrank K L = q) :
    (∑ w : Extensions K L, extensionWeight w) = ramificationIndex K L * residueDegree K L ∧
    ramificationIndex K L * residueDegree K L = 1 ∧
    (∑ w : Extensions K L, extensionWeight w) < q ∧ q = Module.finrank K L := by
  have hs := sum_eq_of_unique K L hunique
  exact ⟨hs, by simp [he, hf], by simpa [hs, he, hf] using hq, hn.symm⟩

@[instance_reducible]
def extensionFintype_of_unique
    (hunique : ∀ w : Extensions K L, w.val = (inferInstance : ValuativeRel L)) :
    Fintype (Extensions K L) := by
  letI : Subsingleton (Extensions K L) := ⟨fun a b =>
    Subtype.ext ((hunique a).trans (hunique b).symm)⟩
  exact Fintype.ofSubsingleton ⟨inferInstance, inferInstance⟩

end ArtinSchreierBridge
