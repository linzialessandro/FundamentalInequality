/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreierDefect.Valuation
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Subring
public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.Algebra.CharP.Two
public import Mathlib.FieldTheory.Perfect

/-!
# Residue degree one and the unconditional Ostrowski sum

A square root of `t⁻¹` in the perfect hull produces a unit generator of
residue `1`, and every integral element of the quadratic extension is
congruent, after a 2-power, to an integer of the first purely inseparable
layer of the hull. The residue degree of the constructed valuation is
therefore one, and the Ostrowski sum holds unconditionally:
`Σ eᵢfᵢ = ef = 1 < 2 = [L:K]`.
-/

@[expose] public section

noncomputable section

open Polynomial ValuativeRel ValuativeExtension
open scoped LaurentSeries WithZero ValuativeRel BigOperators NNReal

namespace ArtinSchreierDefect.Quadratic

open ArtinSchreierBridge

/-- Elements of the first purely inseparable layer: their square already lies in `Base`. -/
def IsLevelOne (x : Hull) : Prop := ∃ y : Base, x ^ 2 = algebraMap Base Hull y

theorem isLevelOne_zero : IsLevelOne 0 := ⟨0, by simp⟩

theorem isLevelOne_one : IsLevelOne 1 := ⟨1, by simp⟩

theorem isLevelOne_algebraMap (y : Base) : IsLevelOne (algebraMap Base Hull y) :=
  ⟨y ^ 2, by rw [← map_pow]⟩

theorem isLevelOne_add {x y : Hull} (hx : IsLevelOne x) (hy : IsLevelOne y) :
    IsLevelOne (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [add_pow_char (p := 2), ha, hb, map_add]

theorem isLevelOne_mul {x y : Hull} (hx : IsLevelOne x) (hy : IsLevelOne y) :
    IsLevelOne (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a * b, ?_⟩
  rw [mul_pow, ha, hb, map_mul]

theorem isLevelOne_inv {x : Hull} (hx : IsLevelOne x) : IsLevelOne x⁻¹ := by
  obtain ⟨a, ha⟩ := hx
  by_cases hx0 : x = 0
  · simpa [hx0] using isLevelOne_zero
  refine ⟨a⁻¹, ?_⟩
  rw [inv_pow, ha, map_inv₀]

theorem exists_sqPow_in_base (x : Hull) :
    ∃ n : ℕ, ∃ y : Base, x ^ (2 ^ n) = algebraMap Base Hull y := by
  have hx : (x : AlgebraicClosure Base) ∈
      perfectClosure Base (AlgebraicClosure Base) := x.2
  rw [mem_perfectClosure_iff_pow_mem (q := 2)] at hx
  obtain ⟨n, ⟨y, hy⟩⟩ := hx
  refine ⟨n, y, ?_⟩
  exact Subtype.ext (by simpa [map_pow] using hy.symm)

theorem one_vlt_inverseT_base : (1 : Base) <ᵥ inverseT := by
  have hval : (Valued.v : Valuation Base ℤᵐ⁰) inverseT = WithZero.exp (1 : ℤ) :=
    ArtinSchreierDefect.inverseT_value 2
  have hlt : (1 : ℤᵐ⁰) < (Valued.v : Valuation Base ℤᵐ⁰) inverseT := by
    rw [hval]
    change WithZero.exp (0 : ℤ) < WithZero.exp (1 : ℤ)
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  exact (Valuation.vlt_iff_lt (v := (Valued.v : Valuation Base ℤᵐ⁰))).mpr (by simpa using hlt)

theorem not_sq_veq_inverseT (x : Base) : ¬ x ^ 2 =ᵥ inverseT := by
  intro h
  have hv := (Valuation.veq_iff_eq (v := (Valued.v : Valuation Base ℤᵐ⁰))).mp h
  have hval : (Valued.v x) ^ 2 = WithZero.exp (1 : ℤ) := by
    rw [← map_pow, hv, ArtinSchreierDefect.inverseT_value 2]
  exact ArtinSchreierDefect.exp_one_not_pth_power 2 (Valued.v x) hval

theorem exists_invTRoot : ∃ σ : Hull, σ ^ 2 = algebraMap Base Hull inverseT :=
  surjective_frobenius Hull 2 (algebraMap Base Hull inverseT)

noncomputable def invTRoot : Hull := exists_invTRoot.choose

theorem invTRoot_sq : invTRoot ^ 2 = algebraMap Base Hull inverseT :=
  exists_invTRoot.choose_spec

theorem isLevelOne_invTRoot : IsLevelOne invTRoot := ⟨inverseT, invTRoot_sq⟩

theorem invTRoot_ne_zero : invTRoot ≠ 0 := by
  intro h
  have := invTRoot_sq
  rw [h, zero_pow (by decide)] at this
  have h0 : algebraMap Base Hull inverseT = 0 := this.symm
  have hinv : inverseT ≠ 0 :=
    HahnSeries.single_ne_zero (one_ne_zero (α := ZMod 2))
  exact hinv ((algebraMap Base Hull).injective (by simpa using h0))

theorem one_vlt_inverseT_hull : (1 : Hull) <ᵥ algebraMap Base Hull inverseT := by
  have h : ¬ algebraMap Base Hull inverseT ≤ᵥ algebraMap Base Hull (1 : Base) := by
    rw [ValuativeExtension.vle_iff_vle (A := Base) (B := Hull)]
    exact ValuativeRel.not_vle.mpr one_vlt_inverseT_base
  simpa using (ValuativeRel.not_vle.mp h)

theorem one_vlt_invTRoot : (1 : Hull) <ᵥ invTRoot := by
  have hsq : (1 : Hull) <ᵥ invTRoot ^ 2 := by
    rw [invTRoot_sq]; exact one_vlt_inverseT_hull
  by_contra hle
  have hle' : invTRoot ≤ᵥ (1 : Hull) := ValuativeRel.not_vlt.mp hle
  have : invTRoot ^ 2 ≤ᵥ (1 : Hull) ^ 2 := pow_vle_pow hle' 2
  simp only [one_pow] at this
  exact (ValuativeRel.not_vle.mpr hsq) this

noncomputable def asRoot : Extension := AdjoinRoot.root (standardPolynomial 2)

noncomputable def invTRootE : Extension := algebraMap Hull Extension invTRoot

theorem invTRootE_ne_zero : invTRootE ≠ 0 := by
  intro h
  exact invTRoot_ne_zero ((algebraMap Hull Extension).injective (by simpa [invTRootE] using h))

theorem invTRootE_sq :
    invTRootE ^ 2 = algebraMap Hull Extension (algebraMap Base Hull inverseT) := by
  rw [invTRootE, ← map_pow, invTRoot_sq]

theorem one_vlt_invTRootE : (1 : Extension) <ᵥ invTRootE := by
  have h : ¬ invTRootE ≤ᵥ algebraMap Hull Extension (1 : Hull) := by
    rw [invTRootE, ValuativeExtension.vle_iff_vle (A := Hull) (B := Extension)]
    exact ValuativeRel.not_vle.mpr one_vlt_invTRoot
  simpa using (ValuativeRel.not_vle.mp h)

theorem root_sub_eq_invTRootE_sq : asRoot ^ 2 - asRoot = invTRootE ^ 2 := by
  rw [asRoot, invTRootE_sq, ArtinSchreierDefect.quadratic_root_equation]

theorem asRoot_veq_invTRootE : asRoot =ᵥ invTRootE := by
  let v := spectralValuation Extension
  have heq : asRoot ^ 2 - asRoot = invTRootE ^ 2 := root_sub_eq_invTRootE_sq
  have hσ1 : 1 < v invTRootE := by
    have := (Valuation.vlt_iff_lt (v := v)).mp one_vlt_invTRootE
    rwa [map_one v] at this
  have hσ2 : 1 < v (invTRootE ^ 2) := by
    rw [map_pow]
    exact lt_trans hσ1 (lt_self_pow₀ hσ1 Nat.one_lt_two)
  have hα1 : 1 < v asRoot := by
    by_contra h
    have hle : v asRoot ≤ 1 := le_of_not_gt h
    have hpow : v (asRoot ^ 2) ≤ 1 := by
      rw [map_pow]; exact pow_le_one₀ bot_le hle
    have hsub : v (asRoot ^ 2 - asRoot) ≤ 1 := v.map_sub_le hpow hle
    rw [heq] at hsub
    exact (not_le_of_gt hσ2) hsub
  have hlt : v asRoot < v (asRoot ^ 2) := by
    rw [map_pow]
    exact lt_self_pow₀ hα1 Nat.one_lt_two
  have hsq : v asRoot ^ 2 = v invTRootE ^ 2 := by
    rw [← map_pow, ← v.map_sub_eq_of_lt_left hlt, heq, map_pow]
  exact (Valuation.veq_iff_eq (v := v)).mpr
    ((sq_eq_sq₀ bot_le bot_le).mp hsq)

/-- An integral generator of the quadratic extension, of valuation one. -/
noncomputable def unitGen : Extension := asRoot / invTRootE

theorem unitGen_mul_invTRootE : unitGen * invTRootE = asRoot :=
  div_mul_cancel₀ asRoot invTRootE_ne_zero

theorem unitGen_veq_one : unitGen =ᵥ (1 : Extension) := by
  let v := spectralValuation Extension
  have hv : v asRoot = v invTRootE :=
    (Valuation.veq_iff_eq (v := v)).mp asRoot_veq_invTRootE
  have hσ0 : v invTRootE ≠ 0 := (Valuation.ne_zero_iff v).mpr invTRootE_ne_zero
  have : v unitGen = v 1 := by
    simp [unitGen, map_div₀, hv, div_self hσ0, map_one]
  exact (Valuation.veq_iff_eq (v := v)).mpr this

theorem unitGen_sq_sub_one : unitGen ^ 2 - 1 = unitGen / invTRootE := by
  have hσ : invTRootE ≠ 0 := invTRootE_ne_zero
  have h : (unitGen * invTRootE) ^ 2 - unitGen * invTRootE = invTRootE ^ 2 := by
    rw [unitGen_mul_invTRootE, root_sub_eq_invTRootE_sq]
  rw [mul_pow] at h
  have h' : unitGen ^ 2 * invTRootE - unitGen = invTRootE := by
    apply mul_left_cancel₀ hσ
    calc
      invTRootE * (unitGen ^ 2 * invTRootE - unitGen)
          = unitGen ^ 2 * invTRootE ^ 2 - unitGen * invTRootE := by ring
      _ = invTRootE ^ 2 := h
      _ = invTRootE * invTRootE := by ring
  have h'' : (unitGen ^ 2 - 1) * invTRootE = unitGen := by
    linear_combination h'
  exact (eq_div_iff hσ).mpr h''

theorem one_eq_neg_one_extension : (1 : Extension) = -1 := by
  have h2 : (2 : Extension) = 0 := CharP.cast_eq_zero Extension 2
  have : (1 : Extension) + 1 = 0 := by
    have h11 : (1 : Extension) + 1 = 2 := one_add_one_eq_two
    rw [h11, h2]
  exact eq_neg_of_add_eq_zero_left this

theorem unitGen_sub_one_sq : (unitGen - 1) ^ 2 = unitGen / invTRootE := by
  have h2 : (2 : Extension) = 0 := CharP.cast_eq_zero Extension 2
  calc
    (unitGen - 1) ^ 2 = unitGen ^ 2 - 2 * unitGen + 1 := by ring
    _ = unitGen ^ 2 + 1 := by simp [h2]
    _ = unitGen ^ 2 - 1 := by rw [sub_eq_add_neg, ← one_eq_neg_one_extension]
    _ = unitGen / invTRootE := unitGen_sq_sub_one

theorem unitGen_sub_one_vlt_one : unitGen - 1 <ᵥ (1 : Extension) := by
  let v := spectralValuation Extension
  have hsq : (unitGen - 1) ^ 2 = unitGen / invTRootE := unitGen_sub_one_sq
  have hv1 : v unitGen = 1 := by
    have := (Valuation.veq_iff_eq (v := v)).mp unitGen_veq_one
    rwa [map_one v] at this
  have hσ1 : 1 < v invTRootE := by
    have := (Valuation.vlt_iff_lt (v := v)).mp one_vlt_invTRootE
    rwa [map_one v] at this
  have hright : v (unitGen / invTRootE) < 1 := by
    have hσ0 : v invTRootE ≠ 0 := (Valuation.ne_zero_iff v).mpr invTRootE_ne_zero
    rw [map_div₀, hv1, one_div]
    exact inv_lt_one_iff₀.mpr (Or.inr hσ1)
  have hpow : v ((unitGen - 1) ^ 2) < 1 := by simpa [hsq] using hright
  have : v (unitGen - 1) < v 1 := by
    have hlt : v (unitGen - 1) < 1 :=
      lt_of_pow_lt_pow_left₀ 2 bot_le (by simpa using hpow)
    rwa [map_one v]
  exact (Valuation.vlt_iff_lt (v := v)).mpr this

theorem veq_of_algebraMap_base {x y : Base}
    (h : algebraMap Base Hull x =ᵥ algebraMap Base Hull y) : x =ᵥ y :=
  ⟨(ValuativeExtension.vle_iff_vle (A := Base) (B := Hull) x y).mp h.1,
    (ValuativeExtension.vle_iff_vle (A := Base) (B := Hull) y x).mp h.2⟩

theorem veq_of_algebraMap_hull {x y : Hull}
    (h : algebraMap Hull Extension x =ᵥ algebraMap Hull Extension y) : x =ᵥ y :=
  ⟨(ValuativeExtension.vle_iff_vle (A := Hull) (B := Extension) x y).mp h.1,
    (ValuativeExtension.vle_iff_vle (A := Hull) (B := Extension) y x).mp h.2⟩

/-- A nonzero level-one element cannot satisfy `v(h)^4 = v(t⁻¹)`. -/
theorem not_pow4_veq_inverseT_of_levelOne {h : Hull} (hh : IsLevelOne h) (hnz : h ≠ 0) :
    ¬ algebraMap Hull Extension (h ^ 4) =ᵥ
        algebraMap Hull Extension (algebraMap Base Hull inverseT) := by
  intro heq
  obtain ⟨b, hb⟩ := hh
  have hb0 : b ≠ 0 := by
    intro hbz
    rw [hbz, map_zero] at hb
    exact hnz ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hb)
  have h4 : h ^ 4 = algebraMap Base Hull (b ^ 2) := by
    have : h ^ 4 = (h ^ 2) ^ 2 := by ring
    rw [this, hb, ← map_pow]
  rw [h4] at heq
  have heq' : algebraMap Base Hull (b ^ 2) =ᵥ algebraMap Base Hull inverseT := by
    -- collapse the two algebra maps on the left
    have : algebraMap Hull Extension (algebraMap Base Hull (b ^ 2)) =ᵥ
        algebraMap Hull Extension (algebraMap Base Hull inverseT) := heq
    exact veq_of_algebraMap_hull this
  exact not_sq_veq_inverseT b (veq_of_algebraMap_base heq')

/-- A nonzero level-one element cannot have the same valuation as `unitGen - 1`. -/
theorem not_veq_unitGen_sub_one_of_levelOne {h : Hull} (hh : IsLevelOne h)
    (hnz : h ≠ 0) : ¬ algebraMap Hull Extension h =ᵥ unitGen - 1 := by
  intro heq
  obtain ⟨b, hb⟩ := hh
  have hb0 : b ≠ 0 := by
    intro hbz
    rw [hbz, map_zero] at hb
    exact hnz ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hb)
  let v := spectralValuation Extension
  have hv : v (algebraMap Hull Extension h) = v (unitGen - 1) :=
    (Valuation.veq_iff_eq (v := v)).mp heq
  have h4val : v (algebraMap Hull Extension (h ^ 4)) =
      (v (algebraMap Hull Extension (algebraMap Base Hull inverseT)))⁻¹ := by
    have hvh : v (algebraMap Hull Extension (h ^ 4)) = v (unitGen - 1) ^ 4 := by
      have hpow : algebraMap Hull Extension (h ^ 4) =
          (algebraMap Hull Extension h) ^ 4 :=
        map_pow (algebraMap Hull Extension) h 4
      rw [hpow, map_pow, hv]
    have hv1 : v unitGen = 1 := by
      have := (Valuation.veq_iff_eq (v := v)).mp unitGen_veq_one
      rwa [map_one v] at this
    calc
      v (algebraMap Hull Extension (h ^ 4))
          = v (unitGen - 1) ^ 4 := hvh
      _ = (v (unitGen - 1) ^ 2) ^ 2 := by ring
      _ = v ((unitGen - 1) ^ 2) ^ 2 := by rw [map_pow]
      _ = v (unitGen / invTRootE) ^ 2 := by rw [unitGen_sub_one_sq]
      _ = (v unitGen / v invTRootE) ^ 2 := by rw [map_div₀]
      _ = (1 / v invTRootE) ^ 2 := by rw [hv1]
      _ = ((v invTRootE)⁻¹) ^ 2 := by rw [one_div]
      _ = (v (invTRootE ^ 2))⁻¹ := by rw [map_pow, inv_pow]
      _ = (v (algebraMap Hull Extension (algebraMap Base Hull inverseT)))⁻¹ := by
          rw [invTRootE_sq]
  have heq' : algebraMap Hull Extension (h ^ 4) =ᵥ
      algebraMap Hull Extension (algebraMap Base Hull inverseT)⁻¹ :=
    (Valuation.veq_iff_eq (v := v)).mpr (by simpa [map_inv₀] using h4val)
  -- transport: b^2 =ᵥ inverseT⁻¹, hence (b⁻¹)^2 =ᵥ inverseT
  have h4 : h ^ 4 = algebraMap Base Hull (b ^ 2) := by
    have : h ^ 4 = (h ^ 2) ^ 2 := by ring
    rw [this, hb, ← map_pow]
  have hdown : algebraMap Base Hull (b ^ 2) =ᵥ
      algebraMap Base Hull inverseT⁻¹ := by
    have : algebraMap Hull Extension (algebraMap Base Hull (b ^ 2)) =ᵥ
        algebraMap Hull Extension (algebraMap Base Hull inverseT⁻¹) := by
      simpa [h4, map_inv₀] using heq'
    exact veq_of_algebraMap_hull this
  have hbase : b ^ 2 =ᵥ inverseT⁻¹ := veq_of_algebraMap_base hdown
  have : (b⁻¹) ^ 2 =ᵥ inverseT := by
    have hvb := (Valuation.veq_iff_eq (v := (Valued.v : Valuation Base ℤᵐ⁰))).mp hbase
    have : Valued.v (b⁻¹ ^ 2) = Valued.v inverseT := by
      have hvb' : Valued.v (b ^ 2) = (Valued.v inverseT)⁻¹ := by
        rwa [map_inv₀] at hvb
      rw [map_pow, map_inv₀, inv_pow, ← map_pow, hvb', inv_inv]
    exact (Valuation.veq_iff_eq (v := (Valued.v : Valuation Base ℤᵐ⁰))).mpr this
  exact not_sq_veq_inverseT b⁻¹ this

/-- A nonzero level-one element cannot satisfy `v(h · (unitGen - 1)) = 1`. -/
theorem not_mul_unitGen_sub_one_veq_one {h : Hull} (hh : IsLevelOne h) (hnz : h ≠ 0) :
    ¬ algebraMap Hull Extension h * (unitGen - 1) =ᵥ (1 : Extension) := by
  intro heq
  let v := spectralValuation Extension
  have hv : v (algebraMap Hull Extension h) * v (unitGen - 1) = 1 := by
    have := (Valuation.veq_iff_eq (v := v)).mp heq
    simpa [map_mul] using this
  have hv1 : v unitGen = 1 := by
    have := (Valuation.veq_iff_eq (v := v)).mp unitGen_veq_one
    rwa [map_one v] at this
  have hβ : v (unitGen - 1) ^ 2 = (v invTRootE)⁻¹ := by
    have := congrArg v unitGen_sub_one_sq
    simp only [map_pow, map_div₀, hv1, one_div] at this
    exact this
  have h4val : v (algebraMap Hull Extension (h ^ 4)) =
      v (algebraMap Hull Extension (algebraMap Base Hull inverseT)) := by
    have hpow4 : v (algebraMap Hull Extension (h ^ 4)) =
        v (algebraMap Hull Extension h) ^ 4 := by simp [map_pow]
    have hmul' : v (algebraMap Hull Extension h) ^ 2 * v (unitGen - 1) ^ 2 = 1 := by
      rw [← mul_pow, hv, one_pow]
    have hprod : v (algebraMap Hull Extension h) ^ 4 * v (unitGen - 1) ^ 4 = 1 := by
      rw [show v (algebraMap Hull Extension h) ^ 4 =
            (v (algebraMap Hull Extension h) ^ 2) ^ 2 by ring,
        show v (unitGen - 1) ^ 4 = (v (unitGen - 1) ^ 2) ^ 2 by ring,
        ← mul_pow, hmul', one_pow]
    have hden : v (unitGen - 1) ^ 4 = (v (invTRootE ^ 2))⁻¹ := by
      rw [show v (unitGen - 1) ^ 4 = (v (unitGen - 1) ^ 2) ^ 2 by ring, hβ, inv_pow,
        map_pow]
    have hσ0 : v (invTRootE ^ 2) ≠ 0 := by
      rw [invTRootE_sq]
      exact (Valuation.ne_zero_iff v).mpr (by
        intro h0
        have hmap : algebraMap Base Hull inverseT = 0 :=
          (algebraMap Hull Extension).injective (by simpa using h0)
        have hinv : inverseT ≠ 0 :=
          HahnSeries.single_ne_zero (one_ne_zero (α := ZMod 2))
        have hmap0 : algebraMap Base Hull inverseT = algebraMap Base Hull 0 := by
          simpa using hmap
        exact hinv ((algebraMap Base Hull).injective hmap0))
    have : v (algebraMap Hull Extension h) ^ 4 = v (invTRootE ^ 2) := by
      have hprod' := hprod
      rw [hden] at hprod'
      field_simp [hσ0] at hprod'
      exact hprod'
    rw [hpow4, this, invTRootE_sq]
  exact not_pow4_veq_inverseT_of_levelOne hh hnz
    ((Valuation.veq_iff_eq (v := v)).mpr h4val)

theorem exists_root_coords (x : Extension) :
    ∃ a b : Hull, x = algebraMap Hull Extension a +
      algebraMap Hull Extension b * asRoot := by
  have hmonic : (standardPolynomial 2).Monic :=
    ArtinSchreier.monic 2 (algebraMap Base Hull inverseT)
  obtain ⟨g, hg⟩ := (AdjoinRoot.mk_surjective (g := standardPolynomial 2)) x
  let r := g %ₘ standardPolynomial 2
  have hr : AdjoinRoot.mk (standardPolynomial 2) r =
      AdjoinRoot.mk (standardPolynomial 2) g := by
    rw [AdjoinRoot.mk_eq_mk]
    have hrq := modByMonic_eq_sub_mul_div g (standardPolynomial 2)
    change standardPolynomial 2 ∣ (g %ₘ standardPolynomial 2) - g
    rw [hrq]
    have hdiff : (g - standardPolynomial 2 * (g /ₘ standardPolynomial 2)) - g =
        - (standardPolynomial 2 * (g /ₘ standardPolynomial 2)) := by ring
    rw [hdiff, dvd_neg]
    exact dvd_mul_right _ _
  have hdegf : (standardPolynomial 2).degree = 2 := by
    have hnat' : (standardPolynomial 2).natDegree = 2 :=
      ArtinSchreier.natDegree_polynomial 2 _
    rw [degree_eq_natDegree hmonic.ne_zero, hnat']
    rfl
  have hnat : r.natDegree < 2 := by
    rcases eq_or_ne r 0 with hr0 | hr0
    · simp [hr0]
    · rw [natDegree_lt_iff_degree_lt hr0]
      simpa [hdegf] using degree_modByMonic_lt g hmonic
  have hform : r = C (r.coeff 0) + C (r.coeff 1) * X := by
    ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · have : r.coeff (n + 2) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [← hg, ← hr, hform, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  simp [asRoot]

theorem exists_unitGen_coords (x : Extension) :
    ∃ c d : Hull, x = algebraMap Hull Extension c +
      algebraMap Hull Extension d * unitGen := by
  obtain ⟨a, b, hx⟩ := exists_root_coords x
  refine ⟨a, b * invTRoot, ?_⟩
  have hα : asRoot = unitGen * invTRootE := unitGen_mul_invTRootE.symm
  simp [hx, hα, invTRootE, map_mul, mul_left_comm, mul_comm]

theorem unitGen_pow_levelOne (n : ℕ) :
    ∃ P Q : Hull, IsLevelOne P ∧ IsLevelOne Q ∧
      unitGen ^ (2 ^ n) = algebraMap Hull Extension P +
        algebraMap Hull Extension Q * unitGen := by
  induction n with
  | zero =>
      refine ⟨0, 1, isLevelOne_zero, isLevelOne_one, ?_⟩
      simp
  | succ n ih =>
      obtain ⟨P, Q, hP, hQ, hform⟩ := ih
      have hP2 : IsLevelOne (P ^ 2) := by simpa [pow_two] using isLevelOne_mul hP hP
      have hQ2 : IsLevelOne (Q ^ 2) := by simpa [pow_two] using isLevelOne_mul hQ hQ
      refine ⟨P ^ 2 + Q ^ 2, Q ^ 2 * invTRoot⁻¹,
        isLevelOne_add hP2 hQ2,
        isLevelOne_mul hQ2 (isLevelOne_inv isLevelOne_invTRoot), ?_⟩
      have hsq : unitGen ^ 2 = 1 + unitGen / invTRootE :=
        sub_eq_iff_eq_add'.mp unitGen_sq_sub_one
      have hpow : unitGen ^ (2 ^ (n + 1)) = (unitGen ^ (2 ^ n)) ^ 2 := by
        rw [Nat.pow_succ, pow_mul]
      have hdiv : unitGen / invTRootE =
          algebraMap Hull Extension invTRoot⁻¹ * unitGen := by
        simp [invTRootE, div_eq_mul_inv, map_inv₀, mul_comm]
      calc
        unitGen ^ (2 ^ (n + 1))
            = (algebraMap Hull Extension P +
                algebraMap Hull Extension Q * unitGen) ^ 2 := by rw [hpow, hform]
        _ = algebraMap Hull Extension (P ^ 2) +
              algebraMap Hull Extension (Q ^ 2) * unitGen ^ 2 := by
            rw [add_pow_char (p := 2)]; simp [mul_pow]
        _ = algebraMap Hull Extension (P ^ 2) +
              algebraMap Hull Extension (Q ^ 2) * (1 + unitGen / invTRootE) := by
            rw [hsq]
        _ = algebraMap Hull Extension (P ^ 2) +
              algebraMap Hull Extension (Q ^ 2) +
                algebraMap Hull Extension (Q ^ 2) * (unitGen / invTRootE) := by
            rw [mul_add, mul_one, ← add_assoc, ← map_add]
        _ = algebraMap Hull Extension (P ^ 2 + Q ^ 2) +
              algebraMap Hull Extension (Q ^ 2 * invTRoot⁻¹) * unitGen := by
            rw [hdiv, ← mul_assoc, ← map_mul, ← map_add]

set_option maxHeartbeats 400000 in
-- The 2-power coordinate reduction is a short inductive rewrite, but the surrounding
-- field arithmetic in the quadratic extension exceeds the default heartbeat budget.
theorem exists_levelOne_pow_coords (x : Extension) :
    ∃ n : ℕ, ∃ A B : Hull, IsLevelOne A ∧ IsLevelOne B ∧
      x ^ (2 ^ n) = algebraMap Hull Extension A +
        algebraMap Hull Extension B * unitGen := by
  obtain ⟨c, d, hx⟩ := exists_unitGen_coords x
  obtain ⟨nc, yc, hc⟩ := exists_sqPow_in_base c
  obtain ⟨nd, yd, hd⟩ := exists_sqPow_in_base d
  let n := max nc nd
  have hc' : IsLevelOne (c ^ (2 ^ n)) := by
    have hpow : 2 ^ n = 2 ^ nc * 2 ^ (n - nc) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_max_left _ _)]
    rw [show c ^ (2 ^ n) = (c ^ (2 ^ nc)) ^ (2 ^ (n - nc)) by rw [hpow, pow_mul],
      hc, ← map_pow]
    exact isLevelOne_algebraMap _
  have hd' : IsLevelOne (d ^ (2 ^ n)) := by
    have hpow : 2 ^ n = 2 ^ nd * 2 ^ (n - nd) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_max_right _ _)]
    rw [show d ^ (2 ^ n) = (d ^ (2 ^ nd)) ^ (2 ^ (n - nd)) by rw [hpow, pow_mul],
      hd, ← map_pow]
    exact isLevelOne_algebraMap _
  obtain ⟨P, Q, hP, hQ, hβ⟩ := unitGen_pow_levelOne n
  refine ⟨n, c ^ (2 ^ n) + d ^ (2 ^ n) * P, d ^ (2 ^ n) * Q,
    isLevelOne_add hc' (isLevelOne_mul hd' hP), isLevelOne_mul hd' hQ, ?_⟩
  have hxpow : x ^ (2 ^ n) =
      algebraMap Hull Extension (c ^ (2 ^ n)) +
        algebraMap Hull Extension (d ^ (2 ^ n)) * unitGen ^ (2 ^ n) := by
    rw [hx, add_pow_char_pow (p := 2), mul_pow, map_pow, map_pow]
  have hmul :
      algebraMap Hull Extension (d ^ (2 ^ n)) *
        (algebraMap Hull Extension P + algebraMap Hull Extension Q * unitGen) =
        algebraMap Hull Extension (d ^ (2 ^ n) * P) +
          algebraMap Hull Extension (d ^ (2 ^ n) * Q) * unitGen := by
    rw [mul_add, ← map_mul, ← mul_assoc, ← map_mul]
  rw [hxpow, hβ, hmul, ← add_assoc, ← map_add]

theorem vle_one_of_algebraMap {y : Hull}
    (h : algebraMap Hull Extension y ≤ᵥ (1 : Extension)) : y ≤ᵥ 1 := by
  have : algebraMap Hull Extension y ≤ᵥ algebraMap Hull Extension (1 : Hull) := by
    simpa using h
  exact (ValuativeExtension.vle_iff_vle (A := Hull) (B := Extension) y 1).mp this

/-- An integral element of the form `A + B * unitGen` with level-one coordinates
is congruent, modulo the maximal ideal, to an integer of the hull. -/
theorem integral_levelOne_cong {z : Extension} {A B : Hull}
    (hA : IsLevelOne A) (hB : IsLevelOne B)
    (hz : z = algebraMap Hull Extension A + algebraMap Hull Extension B * unitGen)
    (hint : z ≤ᵥ 1) :
    ∃ y : Hull, y ≤ᵥ 1 ∧ z - algebraMap Hull Extension y <ᵥ 1 := by
  let v := spectralValuation Extension
  have hz' : z = algebraMap Hull Extension (A + B) +
      algebraMap Hull Extension B * (unitGen - 1) := by
    have hBexp : algebraMap Hull Extension B * unitGen =
        algebraMap Hull Extension B +
          algebraMap Hull Extension B * (unitGen - 1) := by
      rw [mul_sub, mul_one, add_sub_cancel]
    rw [hz, hBexp, ← add_assoc, ← map_add]
  set aE := algebraMap Hull Extension (A + B)
  set tE := algebraMap Hull Extension B * (unitGen - 1)
  have hzE : z = aE + tE := hz'
  have hdiff : z - aE = tE := by rw [hzE]; abel
  have hAB : IsLevelOne (A + B) := isLevelOne_add hA hB
  have hvle1 : v z ≤ 1 := by
    have := (Valuation.vle_iff_le (v := v)).mp hint
    rwa [map_one v] at this
  have hne_terms : v aE ≠ v tE ∨ tE = 0 := by
    by_cases hB0 : B = 0
    · right
      simp [tE, hB0]
    by_cases hS0 : A + B = 0
    · have ha0 : aE = 0 := by
        change algebraMap Hull Extension (A + B) = 0
        rw [hS0, map_zero]
      by_cases hval : v aE = v tE
      · right
        have : v tE = 0 := by simpa [ha0] using hval.symm
        exact (Valuation.zero_iff v).mp this
      · exact Or.inl hval
    · left
      intro hval
      have hquot : IsLevelOne ((A + B) * B⁻¹) :=
        isLevelOne_mul hAB (isLevelOne_inv hB)
      have hquot0 : (A + B) * B⁻¹ ≠ 0 := by
        simp [hB0, hS0]
      have hmap : algebraMap Hull Extension ((A + B) * B⁻¹) =
          aE / algebraMap Hull Extension B := by
        simp [aE, map_mul, map_inv₀, div_eq_mul_inv]
      have hBnz : algebraMap Hull Extension B ≠ 0 := by
        intro h
        have h0 : algebraMap Hull Extension B = algebraMap Hull Extension 0 := by
          simpa using h
        exact hB0 ((algebraMap Hull Extension).injective h0)
      have htval : v tE = v (algebraMap Hull Extension B) * v (unitGen - 1) := by
        simp [tE, map_mul]
      have hBval0 : v (algebraMap Hull Extension B) ≠ 0 :=
        (Valuation.ne_zero_iff v).mpr hBnz
      have hdiv : v (aE / algebraMap Hull Extension B) = v (unitGen - 1) := by
        rw [map_div₀, hval, htval, mul_div_cancel_left₀ _ hBval0]
      have : algebraMap Hull Extension ((A + B) * B⁻¹) =ᵥ unitGen - 1 := by
        rw [hmap]
        exact (Valuation.veq_iff_eq (v := v)).mpr hdiv
      exact not_veq_unitGen_sub_one_of_levelOne hquot hquot0 this
  have ht_ne_one : v tE ≠ 1 := by
    intro ht
    by_cases hB0 : B = 0
    · have ht0 : tE = 0 := by simp [tE, hB0]
      rw [ht0, map_zero] at ht
      exact zero_ne_one ht
    · have : tE =ᵥ (1 : Extension) := by
        refine (Valuation.veq_iff_eq (v := v)).mpr ?_
        rwa [map_one v]
      exact not_mul_unitGen_sub_one_veq_one hB hB0 this
  have ht_le : v tE ≤ 1 ∧ v aE ≤ 1 := by
    rcases hne_terms with hne | ht0
    · have hzval : v z = max (v aE) (v tE) := by
        rcases lt_or_gt_of_ne hne with h | h
        · rw [hzE, v.map_add_eq_of_lt_right h, max_eq_right (le_of_lt h)]
        · rw [hzE, v.map_add_eq_of_lt_left h, max_eq_left (le_of_lt h)]
      have : max (v aE) (v tE) ≤ 1 := by rwa [← hzval]
      exact ⟨le_trans (le_max_right _ _) this, le_trans (le_max_left _ _) this⟩
    · have htval0 : v tE = 0 := by rw [ht0, map_zero]
      have hzval : v z = v aE := by rw [hzE, ht0, add_zero]
      exact ⟨htval0 ▸ bot_le, hzval ▸ hvle1⟩
  have ha_le : aE ≤ᵥ 1 := by
    have : v aE ≤ v 1 := by
      have := ht_le.2
      rwa [map_one v]
    exact (Valuation.vle_iff_le (v := v)).mpr this
  refine ⟨A + B, vle_one_of_algebraMap (by simpa [aE] using ha_le), ?_⟩
  have : v (z - aE) < v 1 := by
    rw [hdiff]
    have hlt : v tE < 1 := lt_of_le_of_ne ht_le.1 ht_ne_one
    rwa [map_one v]
  exact (Valuation.vlt_iff_lt (v := v)).mpr this

theorem exists_pow_root_of_perfect {F : Type*} [Field F] [CharP F 2] [PerfectField F]
    (n : ℕ) (a : F) : ∃ b : F, b ^ (2 ^ n) = a := by
  induction n with
  | zero => exact ⟨a, by simp⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨b, hb⟩ := surjective_frobenius F 2 c
      refine ⟨b, ?_⟩
      have hb' : b ^ 2 = c := by
        rw [← frobenius_def (R := F) (p := 2)]
        exact hb
      rw [Nat.pow_succ, mul_comm, pow_mul, hb', hc]

instance hullIntegerCharP : CharP ↥𝒪[Hull] 2 :=
  CharP.subring Hull 2 (Valuation.integer (valuation Hull))

instance extensionIntegerCharP : CharP ↥𝒪[Extension] 2 :=
  CharP.subring Extension 2 (Valuation.integer (valuation Extension))

/-- The residue field of a characteristic-two valued field has characteristic two. -/
lemma residueCharP_of_charP (K : Type*) [Field K] [CharP K 2] [ValuativeRel K] :
    CharP 𝓀[K] 2 := by
  have : CharP ↥𝒪[K] 2 := CharP.subring K 2 (Valuation.integer (valuation K))
  refine CharP.quotient' (R := ↥𝒪[K]) 2 𝓂[K] ?_
  intro x hx
  have hmod : (x : ↥𝒪[K]) = ((x % 2 : ℕ) : ↥𝒪[K]) :=
    CharP.cast_eq_mod (R := ↥𝒪[K]) 2 x
  have hx01 : (x : ↥𝒪[K]) = 0 ∨ (x : ↥𝒪[K]) = 1 := by
    rw [hmod]
    rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx1
    · simp [hx0]
    · simp [hx1]
  rcases hx01 with hx0 | hx1
  · exact hx0
  · have hnu : ¬ IsUnit (x : ↥𝒪[K]) :=
      (IsLocalRing.mem_maximalIdeal (x : ↥𝒪[K])).mp hx
    exact (hnu (hx1.symm ▸ isUnit_one)).elim

instance hullResidueCharP : CharP 𝓀[Hull] 2 :=
  residueCharP_of_charP Hull

instance extensionResidueCharP : CharP 𝓀[Extension] 2 :=
  residueCharP_of_charP Extension

instance hullResiduePerfect : PerfectField 𝓀[Hull] := by
  have : ExpChar 𝓀[Hull] 2 := inferInstance
  have : PerfectRing 𝓀[Hull] 2 := by
    refine PerfectRing.ofSurjective 𝓀[Hull] 2 ?_
    intro a
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (I := 𝓂[Hull]) a
    obtain ⟨y, hy⟩ := surjective_frobenius Hull 2 (u : Hull)
    have hu1 : (u : Hull) ≤ᵥ 1 :=
      (Valuation.vle_one_iff (v := valuation Hull)).mpr
        ((Valuation.mem_integer_iff (valuation Hull) (u : Hull)).mp u.property)
    have hy2 : y ^ 2 = (u : Hull) := by
      rw [← frobenius_def (R := Hull) (p := 2)]
      exact hy
    have hyi : y ≤ᵥ (1 : Hull) :=
      (pow_vle_pow_iff Hull y 1 2 two_ne_zero).mp (by simpa [hy2, one_pow] using hu1)
    let yO : 𝒪[Hull] :=
      ⟨y, (Valuation.mem_integer_iff (valuation Hull) y).mpr
        ((Valuation.vle_one_iff (v := valuation Hull)).mp hyi)⟩
    refine ⟨IsLocalRing.residue 𝒪[Hull] yO, ?_⟩
    change (IsLocalRing.residue 𝒪[Hull] yO) ^ 2 = a
    rw [← hu, ← map_pow]
    congr 1
    exact Subtype.ext (by
      change y ^ 2 = (u : Hull)
      exact hy2)
  exact PerfectRing.toPerfectField 𝓀[Hull] 2

/-- The residue degree of the constructed valuation is one. -/
theorem concrete_residueDegree : residueDegree Hull Extension = 1 := by
  refine residueDegree_eq_one_iff.mpr ?_
  intro z
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (I := 𝓂[Extension]) z
  set x : Extension := (u : Extension)
  have hint : x ≤ᵥ 1 :=
    (Valuation.vle_one_iff (v := valuation Extension)).mpr
      ((Valuation.mem_integer_iff (valuation Extension) x).mp u.property)
  obtain ⟨n, A, B, hA, hB, hpow⟩ := exists_levelOne_pow_coords x
  have hpow_int : x ^ (2 ^ n) ≤ᵥ 1 := by
    have : x ^ (2 ^ n) ≤ᵥ (1 : Extension) ^ (2 ^ n) := pow_vle_pow hint (2 ^ n)
    simpa using this
  obtain ⟨y, hyint, hydiff⟩ := integral_levelOne_cong hA hB hpow hpow_int
  let yO : 𝒪[Hull] :=
    ⟨y, (Valuation.mem_integer_iff (valuation Hull) y).mpr
      ((Valuation.vle_one_iff (v := valuation Hull)).mp hyint)⟩
  let wO : 𝒪[Extension] := u ^ (2 ^ n)
  have hcongr : IsLocalRing.residue 𝒪[Extension] wO =
      algebraMap 𝓀[Hull] 𝓀[Extension] (IsLocalRing.residue 𝒪[Hull] yO) := by
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    have hcoe : ((wO - algebraMap 𝒪[Hull] 𝒪[Extension] yO : 𝒪[Extension]) : Extension) =
        x ^ (2 ^ n) - algebraMap Hull Extension y := by
      simp [wO, x, yO]
    have : valuation Extension
        ((wO - algebraMap 𝒪[Hull] 𝒪[Extension] yO : 𝒪[Extension]) : Extension) < 1 := by
      have := (Valuation.vlt_iff_lt (v := valuation Extension)).mp hydiff
      simpa [hcoe] using this
    exact this
  have hroot : (IsLocalRing.residue 𝒪[Extension] u) ^ (2 ^ n) =
      algebraMap 𝓀[Hull] 𝓀[Extension] (IsLocalRing.residue 𝒪[Hull] yO) := by
    simpa [wO] using hcongr
  obtain ⟨t, ht⟩ := exists_pow_root_of_perfect (F := 𝓀[Hull]) n
    (IsLocalRing.residue 𝒪[Hull] yO)
  refine ⟨t, ?_⟩
  have hsub :
      ((IsLocalRing.residue 𝒪[Extension] u) -
        algebraMap 𝓀[Hull] 𝓀[Extension] t) ^ (2 ^ n) = 0 := by
    have : CharP 𝓀[Extension] 2 := inferInstance
    have hxy :
        (IsLocalRing.residue 𝒪[Extension] u) -
            algebraMap 𝓀[Hull] 𝓀[Extension] t =
          (IsLocalRing.residue 𝒪[Extension] u) +
            algebraMap 𝓀[Hull] 𝓀[Extension] t :=
      CharTwo.sub_eq_add _ _
    rw [hxy, add_pow_expChar_pow (p := 2), hroot, ← map_pow, ht, CharTwo.add_self_eq_zero]
  have hsubz :
      (algebraMap 𝓀[Hull] 𝓀[Extension] t - z) ^ (2 ^ n) = 0 := by
    have hzres : z = IsLocalRing.residue 𝒪[Extension] u := hu.symm
    rw [hzres, CharTwo.sub_eq_add, add_comm, ← CharTwo.sub_eq_add]
    exact hsub
  exact eq_of_sub_eq_zero ((pow_eq_zero_iff (pow_ne_zero n two_ne_zero)).mp hsubz)

/-- The Ostrowski sum for the unique compatible valuation on the quadratic
Artin–Schreier extension.

Uniqueness of the valuative relation, ramification index one, and residue
degree one are all proved. Consequently `Σ eᵢfᵢ = ef = 1 < 2 = [L:K]`. -/
theorem quadratic_sum_strict :
    let := extensionFintype_of_unique Hull Extension unique_all
    (∑ w : Extensions Hull Extension, extensionWeight w) =
      ramificationIndex Hull Extension * residueDegree Hull Extension ∧
    ramificationIndex Hull Extension * residueDegree Hull Extension = 1 ∧
    (∑ w : Extensions Hull Extension, extensionWeight w) < 2 ∧
    2 = Module.finrank Hull Extension := by
  let := extensionFintype_of_unique Hull Extension unique_all
  exact sum_strict_of_unique_immediate Hull Extension unique_all 2 (by decide)
    concrete_ramificationIndex concrete_residueDegree
    ArtinSchreierDefect.quadratic_degree


end ArtinSchreierDefect.Quadratic

namespace ArtinSchreierDefect

open Quadratic
open scoped ValuativeRel

/-- A numerical quotient, not a general theorem about defect integrality. -/
def defectQuotient (n e f : ℕ) : ℕ := n / (e * f)

theorem defect_of_immediate (n e f q : ℕ) (hn : n = q) (he : e = 1) (hf : f = 1) :
    defectQuotient n e f = q ∧ n = defectQuotient n e f * e * f := by
  simp [defectQuotient, hn, he, hf]

/-- Arithmetic consequence of the proved identities `e = 1`, `f = 1`, and `[L:K] = 2`. -/
theorem quadratic_defect_quotient :
    defectQuotient (Module.finrank Quadratic.Hull Quadratic.Extension)
      (ramificationIndex Quadratic.Hull Quadratic.Extension)
      (residueDegree Quadratic.Hull Quadratic.Extension) = 2 := by
  simp [defectQuotient, quadratic_degree, Quadratic.concrete_ramificationIndex,
    Quadratic.concrete_residueDegree]

end ArtinSchreierDefect
