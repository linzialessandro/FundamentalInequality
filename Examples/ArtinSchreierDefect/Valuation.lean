/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreierDefect.Basic
public import Examples.Bridge.Completeness
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Spectral valuations and uniqueness for the quadratic Artin–Schreier extension

Compatible spectral valuations are constructed from Mathlib's spectral norm
over the complete Laurent series field. The ramification index of the
constructed valuation is one. Uniqueness of a compatible valuative relation
on the quadratic extension is deduced from completeness of `F₂((t))` and
`spectralNorm_unique_field_norm_ext`, after lifting rank at most one along
the finite extension of the hull. Compatibility along the tower uses
`ValuativeExtension.tower`. No general henselian uniqueness theorem is used,
and no `sorry` is introduced.
-/

@[expose] public section

noncomputable section

open Polynomial ValuativeRel ValuativeExtension
open scoped LaurentSeries WithZero ValuativeRel NNReal

namespace ArtinSchreierDefect.Quadratic

abbrev Base := ArtinSchreierDefect.Base 2
abbrev Hull := ArtinSchreierDefect.Hull 2
abbrev Extension := ArtinSchreierDefect.QuadraticExtension
abbrev inverseT := ArtinSchreierDefect.inverseT 2

instance baseRankOne : Valuation.RankOne (Valued.v : Valuation Base ℤᵐ⁰) where
  hom' := (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := (WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := by
    refine ⟨inverseT, ?_, ?_⟩ <;> rw [ArtinSchreierDefect.inverseT_value 2]
    · exact WithZero.coe_ne_zero
    · exact ne_of_gt (WithZero.exp_lt_exp.mpr (by norm_num : (0 : ℤ) < 1))

instance baseNorm : NontriviallyNormedField Base := Valued.toNontriviallyNormedField Base ℤᵐ⁰

/-- A spectral valuation over the complete Laurent-series base. -/
def spectralValuation (E : Type*) [Field E] [Algebra Base E] [Algebra.IsAlgebraic Base E] :
    Valuation E ℝ≥0 where
  toFun x := ⟨spectralNorm Base E x, spectralNorm_nonneg x⟩
  map_zero' := by ext; exact spectralNorm_zero
  map_one' := by ext; exact spectralNorm_one
  map_mul' x y := by ext; exact spectralAlgNorm_mul x y
  map_add_le_max' x y := isNonarchimedean_spectralNorm x y

instance hullValuativeRel : ValuativeRel Hull := .ofValuation (spectralValuation Hull)

instance baseHullValuativeExtension : ValuativeExtension Base Hull where
  vle_iff_vle a b := by
    change spectralNorm Base Hull (algebraMap _ _ a) ≤
      spectralNorm Base Hull (algebraMap _ _ b) ↔ Valued.v a ≤ Valued.v b
    rw [spectralNorm_extends, spectralNorm_extends]
    exact Valued.toNormedField.norm_le_iff

instance extensionAlgebraic : Algebra.IsAlgebraic Base Extension :=
  Algebra.IsAlgebraic.trans Base Hull Extension

instance extensionValuativeRel : ValuativeRel Extension :=
  .ofValuation (spectralValuation Extension)

instance hullExtensionValuativeExtension : ValuativeExtension Hull Extension where
  vle_iff_vle a b := by
    change spectralNorm Base Extension (algebraMap _ _ a) ≤
      spectralNorm Base Extension (algebraMap _ _ b) ↔
        spectralNorm Base Hull a ≤ spectralNorm Base Hull b
    rw [← spectralNorm.eq_of_tower, ← spectralNorm.eq_of_tower]

instance baseExtensionValuativeExtension : ValuativeExtension Base Extension where
  vle_iff_vle a b := by
    change spectralNorm Base Extension (algebraMap _ _ a) ≤
      spectralNorm Base Extension (algebraMap _ _ b) ↔ Valued.v a ≤ Valued.v b
    rw [spectralNorm_extends, spectralNorm_extends]
    exact Valued.toNormedField.norm_le_iff

/-- A quadratic valuative extension with surjective squaring upstairs has index one.
The hypotheses are general; the concrete application below constructs them. -/
theorem ramificationIndex_eq_one_of_square_surjective
    (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    (hsquare : Function.Surjective (fun x : L ↦ x ^ 2))
    (hdegree : Module.finrank K L = 2) : ramificationIndex K L = 1 := by
  have hepos := one_le_ramificationIndex (K := K) (L := L)
  have hfpos := residueDegree_pos (K := K) (L := L)
  have hbound := fundamental_inequality (K := K) (L := L)
  rw [hdegree] at hbound
  have hele : ramificationIndex K L ≤ 2 := by nlinarith
  by_contra hne
  have he2 : ramificationIndex K L = 2 := by omega
  have he1 : ramificationIndex K L = 1 := by
    apply ramificationIndex_eq_one_iff.mpr
    intro γ
    obtain ⟨x, rfl⟩ := valuation_surjective (K := L) γ
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    obtain ⟨y, hy⟩ := hsquare x
    have hy0 : y ≠ 0 := by intro h; simp [h] at hy; exact hx hy.symm
    have hvy : valuation L y ≠ 0 := (valuation L).ne_zero_iff.mpr hy0
    let H := (Units.map (mapValueGroupWithZero K L).toMonoidHom).range
    have hi : H.index = 2 := he2
    obtain ⟨u, hu⟩ := H.sq_mem_of_index_two hi (Units.mk0 (valuation L y) hvy)
    refine ⟨u.val, ?_⟩
    have hv := congrArg Units.val hu
    simpa [← map_pow, hy] using hv
  exact hne he1

instance extensionCharP : CharP Extension 2 :=
  charP_of_injective_algebraMap (algebraMap Base Extension).injective 2

instance extensionPerfect : PerfectField Extension := Algebra.IsAlgebraic.perfectField Hull

theorem concrete_ramificationIndex : ramificationIndex Hull Extension = 1 := by
  apply ramificationIndex_eq_one_of_square_surjective Hull Extension
  · exact surjective_frobenius Extension 2
  · exact ArtinSchreierDefect.quadratic_degree

/-- Raising both sides to a positive power preserves and reflects the valuative relation. -/
theorem pow_vle_pow_iff (L : Type*) [Field L] [ValuativeRel L]
    (x y : L) (n : ℕ) (hn : n ≠ 0) : x ^ n ≤ᵥ y ^ n ↔ x ≤ᵥ y := by
  constructor
  · intro h
    by_contra hxy
    exact (not_vle.mpr (pow_vlt_pow (not_vle.mp hxy) hn)) h
  · intro h
    exact pow_vle_pow h n

/-- Two compatible valuative relations on a purely inseparable extension agree. -/
theorem purelyInseparable_unique
    (K L : Type*) [Field K] [Field L] [Algebra K L] [ValuativeRel K]
    (q : ℕ) [ExpChar K q] [IsPurelyInseparable K L]
    (v₁ v₂ : ValuativeRel L)
    (h₁ : letI := v₁; ValuativeExtension K L)
    (h₂ : letI := v₂; ValuativeExtension K L) : v₁ = v₂ := by
  have hp : q ≠ 0 := expChar_pos K q |>.ne'
  have comparison (v : ValuativeRel L) (hv : letI := v; ValuativeExtension K L)
      (x y : L) (n : ℕ) (a b : K)
      (ha : algebraMap K L a = x ^ q ^ n) (hb : algebraMap K L b = y ^ q ^ n) :
      v.vle x y ↔ a ≤ᵥ b := by
    let := v
    let := hv
    rw [← pow_vle_pow_iff L x y (q ^ n) (pow_ne_zero _ hp), ← ha, ← hb]
    exact ValuativeExtension.vle_iff_vle a b
  ext x y
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem K q x
  obtain ⟨m, b, hb⟩ := IsPurelyInseparable.pow_mem K q y
  have ha' : algebraMap K L (a ^ q ^ m) = x ^ q ^ (n + m) := by
    rw [map_pow, ha, ← pow_mul, ← pow_add]
  have hb' : algebraMap K L (b ^ q ^ n) = y ^ q ^ (n + m) := by
    rw [map_pow, hb, ← pow_mul, ← pow_add, Nat.add_comm m n]
  exact (comparison v₁ h₁ x y (n + m) _ _ ha' hb').trans
    (comparison v₂ h₂ x y (n + m) _ _ ha' hb').symm

instance hullCharP : CharP Hull 2 :=
  charP_of_injective_algebraMap (algebraMap Base Hull).injective 2

theorem hull_isPerfectClosure : IsPerfectClosure (algebraMap Base Hull) 2 := inferInstance

theorem hull_unique (other : ValuativeRel Hull)
    (h : letI := other; ValuativeExtension Base Hull) : other = hullValuativeRel :=
  purelyInseparable_unique Base Hull 2 other hullValuativeRel h baseHullValuativeExtension

end ArtinSchreierDefect.Quadratic

namespace ArtinSchreierDefect.Quadratic

open ArtinSchreierBridge

instance instScalarTowerBaseHullExtension : IsScalarTower Base Hull Extension :=
  IsScalarTower.of_algebraMap_eq fun x => by
    -- The `Algebra Base Extension` instance comes from the tower through `Hull`.
    rfl

instance hullCompatible : (spectralValuation Hull).Compatible :=
  Valuation.Compatible.ofValuation (spectralValuation Hull)

instance hullIsRankLeOne : IsRankLeOne Hull :=
  IsRankLeOne.of_compatible_mulArchimedean (spectralValuation Hull)

theorem exp_one_ne_one : WithZero.exp (1 : ℤ) ≠ (1 : ℤᵐ⁰) := by
  intro h
  have : WithZero.exp (0 : ℤ) < WithZero.exp (1 : ℤ) :=
    WithZero.exp_lt_exp.mpr (by norm_num : (0 : ℤ) < 1)
  simp [h] at this

instance baseIsNontrivial : IsNontrivial Base := by
  have : Valuation.Compatible (Valued.v : Valuation Base ℤᵐ⁰) :=
    Valuation.Compatible.ofValuation _
  refine ⟨valuation Base inverseT, ?_, ?_⟩
  · intro h
    have : inverseT = (0 : Base) := (Valuation.zero_iff (valuation Base)).mp h
    exact (HahnSeries.single_ne_zero (by exact one_ne_zero)) this
  · intro h
    have hvle : Valued.v inverseT = 1 := by
      have hle : inverseT ≤ᵥ (1 : Base) :=
        (Valuation.vle_iff_le (valuation Base)).mpr (le_of_eq h)
      have hge : (1 : Base) ≤ᵥ inverseT :=
        (Valuation.vle_iff_le (valuation Base) (x := (1 : Base)) (y := inverseT)).mpr
          (by simpa using (le_of_eq h.symm))
      apply le_antisymm
      · simpa [map_one] using (Valuation.vle_iff_le (Valued.v : Valuation Base ℤᵐ⁰)).mp hle
      · simpa [map_one] using
          (Valuation.vle_iff_le (Valued.v : Valuation Base ℤᵐ⁰)
            (x := (1 : Base)) (y := inverseT)).mp hge
    exact exp_one_ne_one ((ArtinSchreierDefect.inverseT_value 2).symm.trans hvle)

theorem base_vle_iff_norm (x y : Base) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ :=
  Valued.toNormedField.norm_le_iff (x := x) (x' := y) |>.symm

/-- Any valuative relation on the Artin–Schreier extension that is compatible with
the hull (equivalently, with the complete Laurent base) coincides with the
spectral relation. This uses completeness of `F₂((t))`, not henselianity of the
hull's valuation ring. -/
theorem unique_extension (other : ValuativeRel Extension)
    (h : letI := other; ValuativeExtension Hull Extension) :
    other = extensionValuativeRel := by
  let := other
  let := h
  have hBase : ValuativeExtension Base Extension :=
    ValuativeExtension.tower (K := Base) (F := Hull) (L := Extension)
  have : IsRankLeOne Extension := isRankLeOne_of_finite Hull Extension
  have : IsNontrivial Extension :=
    isNontrivial_of_valuativeExtension Base Extension
  have : Algebra.IsAlgebraic Base Extension := extensionAlgebraic
  have hcmp := unique_valuativeRel_of_complete (K := Base) (L := Extension)
    base_vle_iff_norm other hBase
  refine ValuativeRel.ext ?_
  funext x y
  exact propext ((hcmp x y).trans Iff.rfl)

end ArtinSchreierDefect.Quadratic

namespace ArtinSchreierDefect.Quadratic

open ArtinSchreierBridge IsLocalRing
open scoped ValuativeRel BigOperators

/-- Every compatible valuative relation on the quadratic extension equals the
spectral one. -/
theorem unique_all (w : Extensions Hull Extension) :
    w.val = extensionValuativeRel :=
  unique_extension w.val w.property

instance baseCompatible : (Valued.v : Valuation Base ℤᵐ⁰).Compatible :=
  Valuation.Compatible.ofValuation _

instance extensionCompatible : (spectralValuation Extension).Compatible :=
  Valuation.Compatible.ofValuation _


instance hullPerfect : PerfectField Hull :=
  perfectClosure.perfectField (F := Base) (E := AlgebraicClosure Base)
end ArtinSchreierDefect.Quadratic
