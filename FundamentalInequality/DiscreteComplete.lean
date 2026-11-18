/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import FundamentalInequality
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Order.Filter.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# The defectless equality over complete discretely valued fields

For a finite extension `L/K`, where `K` is complete for a discrete rank-at-most-one
valuation, this file proves

\[
  e(L/K)\, f(L/K) = [L : K].
\]

No separability, local compactness, finiteness of the residue field, uniqueness of the
extended valuation, or topology on `L` is assumed.

## Main results

* `ValuativeExtension.pow_ramificationIdx_le_mul_uniformizer` bounds every strict
  valuation decrease by the image of the base uniformizer after taking the
  ramification-index power.
* `ValuativeExtension.span_eq_top_of_completeSpace` proves that the valuation-independent
  family built from value-group representatives and residue-basis lifts spans `L`.
* `ValuativeExtension.ramificationIdx_mul_inertiaDeg_eq_finrank` is the defectless
  equality `e(L/K) f(L/K) = [L : K]`.

## Implementation notes

The proof uses direct successive approximation. At every step, a value-group coset
representative first scales the remainder to valuation one, and a lifted residue basis
cancels its residue. Discreteness supplies a uniform decrease after the
ramification-index power. Rank at most one makes the resulting geometric bounds tend to
zero, and completeness of `K` sums every coefficient sequence. Thus all convergence
takes place in `K`; no topology is put on `L`.

This is the equality only. It does not prove Ostrowski's sum over several extensions,
uniqueness of valuation extensions, henselianity, henselization results, or a comparison
with `Ideal.ramificationIdx` and `Ideal.inertiaDeg`.

## References

* [J.-P. Serre, *Local Fields*][serreLocalFields], Chapter II, §2, Proposition 3.
* [F.-V. Kuhlmann, *Valuation Theory*][kuhlmannValuation], Chapter 6, §6.3,
  Lemmas 6.12 and 6.13.
-/

@[expose] public section

noncomputable section

open Filter IsLocalRing Set ValuativeRel Valuation Valuation.HasExtension
open scoped Topology ValuativeRel

namespace ValuativeExtension

variable {K L : Type*} [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/-- A strict decrease in the extended value group is uniformly bounded, after taking the
ramification-index power, by one copy of the image of the base uniformizer. -/
theorem pow_ramificationIdx_le_mul_uniformizer [IsDiscrete K]
    {α β : ValueGroupWithZero L} (hαβ : α < β) (hβ : β ≠ 0) :
    α ^ ramificationIdx K L ≤
      β ^ ramificationIdx K L * mapValueGroupWithZero K L (uniformizer K) := by
  let e := ramificationIdx K L
  let H := (Units.map (mapValueGroupWithZero K L).toMonoidHom).range
  have he : e ≠ 0 := ramificationIdx_ne_zero (K := K) (L := L)
  rcases eq_or_ne α 0 with rfl | hα
  · change 0 ^ e ≤ _
    simp [he]
  have hβpos : 0 < β := bot_lt_iff_ne_bot.mpr hβ
  have hdiv : α / β < 1 := (div_lt_one₀ hβpos).mpr hαβ
  have hdiv0 : α / β ≠ 0 := div_ne_zero hα hβ
  let q : (ValueGroupWithZero L)ˣ := Units.mk0 (α / β) hdiv0
  have hqe : q ^ e ∈ H := Subgroup.pow_index_mem H q
  obtain ⟨δ, hδ⟩ := hqe
  have hmap : mapValueGroupWithZero K L (δ : ValueGroupWithZero K) = (α / β) ^ e := by
    simpa [q, Units.val_pow_eq_pow_val] using congrArg Units.val hδ
  have hδlt : (δ : ValueGroupWithZero K) < 1 := by
    apply (mapValueGroupWithZero_strictMono (A := K) (B := L)).lt_iff_lt.mp
    rw [hmap, map_one]
    exact pow_lt_one₀ (show 0 ≤ α / β from zero_le) hdiv he
  have hδle : (δ : ValueGroupWithZero K) ≤ uniformizer K :=
    le_uniformizer_iff.mpr hδlt
  have hmap_le : (α / β) ^ e ≤ mapValueGroupWithZero K L (uniformizer K) := by
    rw [← hmap]
    exact (mapValueGroupWithZero_strictMono (A := K) (B := L)).monotone hδle
  calc
    α ^ e = β ^ e * (α / β) ^ e := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero e hβ)]
    _ ≤ β ^ e * mapValueGroupWithZero K L (uniformizer K) :=
      mul_le_mul_of_nonneg_left hmap_le zero_le

/-- Powers of the image of the base uniformizer dominate any two nonzero values after
taking ramification-index powers. This is the geometric decay used in successive
approximation. -/
theorem eventually_pow_mul_uniformizer_lt [IsDiscrete K] [IsRankLeOne K]
    (α : ValueGroupWithZero L) {β : ValueGroupWithZero L} (hβ : β ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      α ^ ramificationIdx K L *
          mapValueGroupWithZero K L (uniformizer K) ^ n <
        β ^ ramificationIdx K L := by
  let e := ramificationIdx K L
  let H := (Units.map (mapValueGroupWithZero K L).toMonoidHom).range
  have he : e ≠ 0 := ramificationIdx_ne_zero (K := K) (L := L)
  rcases eq_or_ne α 0 with rfl | hα
  · filter_upwards with n
    change 0 ^ e * _ < β ^ e
    rw [zero_pow he, zero_mul]
    exact pow_pos (bot_lt_iff_ne_bot.mpr hβ) e
  have hαe : (Units.mk0 α hα) ^ e ∈ H := Subgroup.pow_index_mem H _
  have hβe : (Units.mk0 β hβ) ^ e ∈ H := Subgroup.pow_index_mem H _
  obtain ⟨a, ha⟩ := hαe
  obtain ⟨b, hb⟩ := hβe
  have hmapa : mapValueGroupWithZero K L (a : ValueGroupWithZero K) = α ^ e := by
    simpa [Units.val_pow_eq_pow_val] using congrArg Units.val ha
  have hmapb : mapValueGroupWithZero K L (b : ValueGroupWithZero K) = β ^ e := by
    simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hb
  rcases eq_or_ne (uniformizer K) 0 with hπ | hπ
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    change α ^ e * mapValueGroupWithZero K L (uniformizer K) ^ n < β ^ e
    rw [hπ, map_zero, zero_pow (Nat.ne_zero_of_lt hn), mul_zero]
    exact pow_pos (bot_lt_iff_ne_bot.mpr hβ) e
  · let π : (ValueGroupWithZero K)ˣ := Units.mk0 (uniformizer K) hπ
    have hπlt : π < 1 := by
      change uniformizer K < 1
      exact uniformizer_lt_one
    obtain ⟨N, hN⟩ := exists_pow_lt hπlt (b / a)
    have hNa : a * π ^ N < b := by
      rw [mul_comm]
      exact (lt_div_iff_mul_lt).mp hN
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpow : π ^ n ≤ π ^ N := pow_le_pow_right_of_le_one' hπlt.le hn
    have han : a * π ^ n < b := by
      calc
        a * π ^ n ≤ a * π ^ N := by gcongr
        _ < b := hNa
    have hmap := (mapValueGroupWithZero_strictMono (A := K) (B := L)).lt_iff_lt.mpr
      (show (a : ValueGroupWithZero K) * uniformizer K ^ n < b from by
        change (a.val * (π ^ n).val < b.val) at han
        simpa [π] using han)
    simpa [map_mul, map_pow, hmapa, hmapb] using hmap

omit [FiniteDimensional K L] in
/-- One step of successive approximation using value-group representatives and lifts of a
residue-field basis. The new remainder has strictly smaller valuation, while every term
used in the correction is no larger than the old remainder. -/
theorem exists_sub_val_lt {I J : Type*} [Fintype I] [Fintype J]
    (z : I → L) (hz_nz : ∀ i, z i ≠ 0)
    (hz_cover : ∀ r : L, r ≠ 0 → ∃ i a, a ≠ 0 ∧
      valuation L r = valuation L (algebraMap K L a * z i))
    (b : Module.Basis J 𝓀[K] 𝓀[L]) (u : J → 𝒪[L])
    (hu : ∀ j, residue 𝒪[L] (u j) = b j) (r : L) :
    ∃ c : I × J → K,
      (r = 0 → c = 0) ∧
      (∀ p, valuation L (algebraMap K L (c p) * (z p.1 * (u p.2 : L))) ≤
        valuation L r) ∧
      (r ≠ 0 → valuation L
        (r - ∑ p, algebraMap K L (c p) * (z p.1 * (u p.2 : L))) < valuation L r) := by
  classical
  rcases eq_or_ne r 0 with rfl | hr
  · refine ⟨0, fun _ ↦ rfl, ?_, fun h ↦ (h rfl).elim⟩
    intro p
    simp
  obtain ⟨i, a, ha, hra⟩ := hz_cover r hr
  let d₀ : L := algebraMap K L a * z i
  have hd₀ : d₀ ≠ 0 := mul_ne_zero
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr ha) (hz_nz i)
  let t : L := r / d₀
  have ht : valuation L t = 1 := by
    simp only [t]
    rw [Valuation.map_div, hra]
    exact div_self ((valuation L).ne_zero_iff.mpr hd₀)
  let tO : 𝒪[L] := ⟨t, (mem_integer_iff _ _).mpr ht.le⟩
  have hd_exists : ∀ j : J, ∃ d : 𝒪[K],
      residue 𝒪[K] d = b.repr (residue 𝒪[L] tO) j := fun j ↦
    residue_surjective _
  choose d hd using hd_exists
  let sO : 𝒪[L] := ∑ j, algebraMap 𝒪[K] 𝒪[L] (d j) * u j
  have hsO : residue 𝒪[L] sO = residue 𝒪[L] tO := by
    simp only [sO]
    rw [map_sum]
    calc
      ∑ j, residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (d j) * u j) =
          ∑ j, b.repr (residue 𝒪[L] tO) j • b j := by
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [_root_.map_mul, ← ResidueField.algebraMap_residue, hd, hu,
              Algebra.smul_def]
      _ = residue 𝒪[L] tO := b.sum_repr _
  have hsub_lt : valuation L ((tO - sO : 𝒪[L]) : L) < 1 := by
    apply Integer.not_isUnit_iff_valuation_lt_one.mp
    intro hunit
    have hne := (residue_ne_zero_iff_isUnit (tO - sO)).mpr hunit
    apply hne
    rw [_root_.map_sub, hsO, sub_self]
  let c : I × J → K := fun p ↦ if p.1 = i then a * (d p.2 : K) else 0
  refine ⟨c, fun h ↦ (hr h).elim, ?_, fun _ ↦ ?_⟩
  · rintro ⟨i', j⟩
    by_cases hi : i' = i
    · subst i'
      have hu_val : valuation L (u j : L) = 1 :=
        val_eq_one_of_residue_ne_zero (by rw [hu]; exact b.ne_zero j)
      have hd_le : valuation K (d j : K) ≤ 1 := (mem_integer_iff _ _).mp (d j).property
      have hdL_le : valuation L (algebraMap K L (d j : K)) ≤ 1 :=
        (val_map_le_one_iff (valuation K) (valuation L) _).mpr hd_le
      have hcij : c (i, j) = a * (d j : K) := by simp [c]
      rw [hcij]
      simp only [map_mul, hu_val, mul_one]
      calc
        valuation L (algebraMap K L a) * valuation L (algebraMap K L (d j : K)) *
            valuation L (z i) =
            valuation L (algebraMap K L a * z i) *
              valuation L (algebraMap K L (d j : K)) := by
                simp only [map_mul]
                ac_rfl
        _ ≤ valuation L (algebraMap K L a * z i) * 1 :=
          mul_le_mul_of_nonneg_left hdL_le zero_le
        _ = valuation L r := by simpa using hra.symm
    · simp [c, hi]
  · have hsum :
        (∑ p, algebraMap K L (c p) * (z p.1 * (u p.2 : L))) = d₀ * (sO : L) := by
      rw [Fintype.sum_prod_type]
      calc
        ∑ i', ∑ j, algebraMap K L (c (i', j)) * (z i' * (u j : L)) =
            ∑ j, algebraMap K L (c (i, j)) * (z i * (u j : L)) := by
              rw [Finset.sum_eq_single i]
              · intro i' _ hi
                apply Finset.sum_eq_zero
                intro j _
                simp [c, hi]
              · simp
        _ = d₀ * (sO : L) := by
          simp only [sO]
          rw [← Subring.coe_subtype, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [map_mul, Subring.coe_subtype, val_algebraMap]
          simp [c, map_mul]
          simp only [d₀]
          ring
    have hr_eq : r = d₀ * t := by
      change r = d₀ * (r / d₀)
      exact (mul_div_cancel₀ r hd₀).symm
    rw [hsum]
    calc
      valuation L (r - d₀ * (sO : L)) =
          valuation L (d₀ * ((tO - sO : 𝒪[L]) : L)) := by
        congr 1
        change r - d₀ * (sO : L) = d₀ * (t - (sO : L))
        rw [hr_eq]
        ring
      _ = valuation L d₀ * valuation L ((tO - sO : 𝒪[L]) : L) := map_mul _ _ _
      _ < valuation L d₀ * 1 :=
        mul_lt_mul_of_pos_left hsub_lt ((valuation L).pos_iff.mpr hd₀)
      _ = valuation L r := by simpa [d₀] using hra.symm

private theorem eventually_val_mul_lt_of_tendsto_zero
    [TopologicalSpace K] [IsValuativeTopology K] [IsDiscrete K] [IsRankLeOne K]
    {a : ℕ → K} (ha : Tendsto a atTop (𝓝 0)) {z : L} (hz : z ≠ 0)
    {β : ValueGroupWithZero L} (hβ : β ≠ 0) :
    ∀ᶠ n : ℕ in atTop, valuation L (algebraMap K L (a n) * z) < β := by
  rcases eq_or_ne (uniformizer K) 0 with hπ | hπ
  · have hball : {x : K | valuation K x < (1 : ValueGroupWithZero K)} ∈ 𝓝 0 :=
      (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mpr
        ⟨1, trivial, by simp⟩
    filter_upwards [ha.eventually hball] with n hn
    have hn0 : valuation K (a n) = 0 := by
      apply le_antisymm
      · simpa [hπ] using (le_uniformizer_iff.mpr hn)
      · exact zero_le
    have han : a n = 0 := (valuation K).zero_iff.mp hn0
    rw [han, map_zero, zero_mul, map_zero]
    exact bot_lt_iff_ne_bot.mpr hβ
  · let e := ramificationIdx K L
    have he : 1 ≤ e := one_le_ramificationIdx (K := K) (L := L)
    have hgeo := eventually_pow_mul_uniformizer_lt (K := K) (L := L)
      (valuation L z) hβ
    rw [eventually_atTop] at hgeo
    obtain ⟨N, hN⟩ := hgeo
    let m := max N 1
    have hNm : N ≤ m * e := (le_max_left N 1).trans <|
      Nat.le_mul_of_pos_right m (Nat.zero_lt_of_lt he)
    have hpow := hN (m * e) hNm
    change valuation L z ^ e * mapValueGroupWithZero K L (uniformizer K) ^ (m * e) <
      β ^ e at hpow
    have hsmall :
        mapValueGroupWithZero K L (uniformizer K ^ m) * valuation L z < β := by
      apply lt_of_pow_lt_pow_left₀ e zero_le
      simpa only [mul_pow, map_pow, pow_mul, mul_comm] using hpow
    have hπm : uniformizer K ^ m ≠ 0 := pow_ne_zero m hπ
    have hball : {x : K | valuation K x < uniformizer K ^ m} ∈ 𝓝 0 :=
      (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mpr
        ⟨Units.mk0 (uniformizer K ^ m) hπm, trivial, by simp⟩
    filter_upwards [ha.eventually hball] with n hn
    rw [map_mul, ← mapValueGroupWithZero_valuation]
    exact (mul_lt_mul_of_pos_right
      ((mapValueGroupWithZero_strictMono (A := K) (B := L)).lt_iff_lt.mpr hn)
      ((valuation L).pos_iff.mpr hz)).trans hsmall

/-- Over a complete discrete rank-at-most-one base, value-group representatives times
lifts of a residue-field basis span the extension. -/
theorem span_eq_top_of_completeSpace
    [UniformSpace K] [IsUniformAddGroup K] [IsValuativeTopology K] [CompleteSpace K]
    [IsDiscrete K] [IsRankLeOne K]
    {I J : Type*} [Finite I] [Finite J]
    (z : I → L) (hz_nz : ∀ i, z i ≠ 0)
    (hz_cover : ∀ r : L, r ≠ 0 → ∃ i a, a ≠ 0 ∧
      valuation L r = valuation L (algebraMap K L a * z i))
    (b : Module.Basis J 𝓀[K] 𝓀[L]) (u : J → 𝒪[L])
    (hu : ∀ j, residue 𝒪[L] (u j) = b j) :
    Submodule.span K (Set.range fun p : I × J ↦ z p.1 * (u p.2 : L)) = ⊤ := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have : Fintype J := Fintype.ofFinite J
  apply Submodule.eq_top_iff'.mpr
  intro x
  let step (r : L) := exists_sub_val_lt z hz_nz hz_cover b u hu r
  let c : L → I × J → K := fun r ↦ (step r).choose
  have hc_zero (r : L) (hr : r = 0) : c r = 0 := (step r).choose_spec.1 hr
  have hc_le (r : L) (p : I × J) :
      valuation L (algebraMap K L (c r p) * (z p.1 * (u p.2 : L))) ≤
        valuation L r := (step r).choose_spec.2.1 p
  have hc_lt (r : L) (hr : r ≠ 0) :
      valuation L (r - ∑ p, algebraMap K L (c r p) * (z p.1 * (u p.2 : L))) <
        valuation L r := (step r).choose_spec.2.2 hr
  let correction (r : L) : L :=
    ∑ p, algebraMap K L (c r p) * (z p.1 * (u p.2 : L))
  let remainder : ℕ → L := fun n ↦ Nat.rec x (fun _ r ↦ r - correction r) n
  have remainder_zero : remainder 0 = x := rfl
  have remainder_succ (n : ℕ) :
      remainder (n + 1) = remainder n - correction (remainder n) := by
    rfl
  have remainder_succ_of_eq_zero {n : ℕ} (hn : remainder n = 0) :
      remainder (n + 1) = 0 := by
    rw [remainder_succ, hn]
    simp only [correction, hc_zero 0 rfl]
    simp
  let e := ramificationIdx K L
  have he : e ≠ 0 := ramificationIdx_ne_zero (K := K) (L := L)
  have remainder_pow_le (n : ℕ) :
      valuation L (remainder n) ^ e ≤
        valuation L x ^ e * mapValueGroupWithZero K L (uniformizer K) ^ n := by
    induction n with
    | zero => simp [remainder_zero]
    | succ n hn =>
        rcases Classical.em (remainder n = 0) with hr | hr
        · rw [remainder_succ_of_eq_zero hr, map_zero, zero_pow he]
          exact zero_le
        · calc
            valuation L (remainder (n + 1)) ^ e ≤
                valuation L (remainder n) ^ e *
                  mapValueGroupWithZero K L (uniformizer K) :=
              pow_ramificationIdx_le_mul_uniformizer
                (by simpa [remainder_succ, correction] using hc_lt (remainder n) hr)
                ((valuation L).ne_zero_iff.mpr hr)
            _ ≤ (valuation L x ^ e *
                  mapValueGroupWithZero K L (uniformizer K) ^ n) *
                mapValueGroupWithZero K L (uniformizer K) := by gcongr
            _ = valuation L x ^ e *
                mapValueGroupWithZero K L (uniformizer K) ^ (n + 1) := by
              rw [pow_succ]
              ac_rfl
  have remainder_lt (β : ValueGroupWithZero L) (hβ : β ≠ 0) :
      ∀ᶠ n : ℕ in atTop, valuation L (remainder n) < β :=
    (eventually_pow_mul_uniformizer_lt (K := K) (L := L) (valuation L x) hβ).mono
      fun n hn ↦ lt_of_pow_lt_pow_left₀ e zero_le ((remainder_pow_le n).trans_lt hn)
  have u_val (j : J) : valuation L (u j : L) = 1 :=
    val_eq_one_of_residue_ne_zero (by rw [hu]; exact b.ne_zero j)
  have family_ne (p : I × J) : z p.1 * (u p.2 : L) ≠ 0 := by
    apply mul_ne_zero (hz_nz p.1)
    exact (valuation L).ne_zero_iff.mp (by rw [u_val]; exact one_ne_zero)
  have c_tendsto (p : I × J) :
      Tendsto (fun n ↦ c (remainder n) p) atTop (𝓝 0) := by
    refine (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff.mpr fun γ _ ↦ ?_
    let β := mapValueGroupWithZero K L (γ : ValueGroupWithZero K) * valuation L (z p.1)
    have hγ : mapValueGroupWithZero K L (γ : ValueGroupWithZero K) ≠ 0 :=
      (map_ne_zero (mapValueGroupWithZero K L)).mpr γ.ne_zero
    have hβ : β ≠ 0 := mul_ne_zero hγ ((valuation L).ne_zero_iff.mpr (hz_nz p.1))
    filter_upwards [remainder_lt β hβ] with n hn
    have hterm := (hc_le (remainder n) p).trans_lt hn
    have hmul :
        mapValueGroupWithZero K L (valuation K (c (remainder n) p)) *
            valuation L (z p.1) <
          mapValueGroupWithZero K L (γ : ValueGroupWithZero K) * valuation L (z p.1) := by
      simpa [β, map_mul, mapValueGroupWithZero_valuation, u_val] using hterm
    have hmap : mapValueGroupWithZero K L (valuation K (c (remainder n) p)) <
        mapValueGroupWithZero K L (γ : ValueGroupWithZero K) :=
      lt_of_mul_lt_mul_right hmul zero_le
    exact (mapValueGroupWithZero_strictMono (A := K) (B := L)).lt_iff_lt.mp hmap
  let hnonarch : NonarchimedeanRing K := by
    convert ValuativeRel.nonarchimedeanRing K
    exact (valuation K).toTopologicalSpace_eq
  let _ : NonarchimedeanRing K := hnonarch
  let _ : T2Space K := by
    refine IsTopologicalAddGroup.t2Space_of_zero_sep fun y hy ↦ ?_
    refine ⟨{k | valuation K k < valuation K y}, ?_, fun h ↦ ?_⟩
    · exact (IsValuativeTopology.hasBasis_nhds_zero K).mem_iff.mpr
        ⟨Units.mk0 (valuation K y) ((valuation K).ne_zero_iff.mpr hy), trivial, by simp⟩
    · exact (lt_irrefl (valuation K y)) h
  have c_summable (p : I × J) : Summable (fun n ↦ c (remainder n) p) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    simpa only [Nat.cofinite_eq_atTop] using c_tendsto p
  let C : I × J → K := fun p ↦ ∑' n, c (remainder n) p
  let tail : I × J → ℕ → K := fun p N ↦ ∑' n, c (remainder (n + N)) p
  have sum_add_tail (p : I × J) (N : ℕ) :
      (∑ n ∈ Finset.range N, c (remainder n) p) + tail p N = C p := by
    simpa only [tail, C] using (c_summable p).sum_add_tsum_nat_add N
  have tail_tendsto (p : I × J) : Tendsto (tail p) atTop (𝓝 0) := by
    have hpartial : Tendsto
        (fun N ↦ ∑ n ∈ Finset.range N, c (remainder n) p) atTop (𝓝 (C p)) := by
      simpa only [C] using (c_summable p).hasSum.tendsto_sum_nat
    have hdiff : Tendsto
        (fun N ↦ C p - ∑ n ∈ Finset.range N, c (remainder n) p) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ ↦ C p) atTop (𝓝 (C p)) := tendsto_const_nhds
      simpa only [sub_self] using hconst.sub hpartial
    refine (tendsto_congr' ?_).mpr hdiff
    filter_upwards with N
    rw [← sum_add_tail p N]
    ring
  have telescope (N : ℕ) :
      x = remainder N + ∑ n ∈ Finset.range N, correction (remainder n) := by
    induction N with
    | zero => simp [remainder_zero]
    | succ N hN =>
        calc
          x = remainder N + ∑ n ∈ Finset.range N, correction (remainder n) := hN
          _ = remainder (N + 1) +
              ∑ n ∈ Finset.range (N + 1), correction (remainder n) := by
            rw [remainder_succ, Finset.sum_range_succ]
            ring
  have corrections_eq (N : ℕ) :
      (∑ n ∈ Finset.range N, correction (remainder n)) =
        ∑ p, algebraMap K L (∑ n ∈ Finset.range N, c (remainder n) p) *
          (z p.1 * (u p.2 : L)) := by
    simp only [correction]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [map_sum, Finset.sum_mul]
  have total_eq (N : ℕ) :
      (∑ p, algebraMap K L (C p) * (z p.1 * (u p.2 : L))) =
        (∑ n ∈ Finset.range N, correction (remainder n)) +
          ∑ p, algebraMap K L (tail p N) * (z p.1 * (u p.2 : L)) := by
    rw [corrections_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← add_mul, ← map_add, sum_add_tail]
  have difference_eq (N : ℕ) :
      x - ∑ p, algebraMap K L (C p) * (z p.1 * (u p.2 : L)) =
        remainder N - ∑ p, algebraMap K L (tail p N) * (z p.1 * (u p.2 : L)) := by
    rw [total_eq, telescope]
    ring
  have difference_lt (β : ValueGroupWithZero L) (hβ : β ≠ 0) :
      valuation L (x - ∑ p, algebraMap K L (C p) * (z p.1 * (u p.2 : L))) < β := by
    have htail : ∀ p : I × J, ∀ᶠ N : ℕ in atTop,
        valuation L (algebraMap K L (tail p N) * (z p.1 * (u p.2 : L))) < β :=
      fun p ↦ eventually_val_mul_lt_of_tendsto_zero (tail_tendsto p) (family_ne p) hβ
    obtain ⟨N, hNr, hNt⟩ :=
      ((remainder_lt β hβ).and (Filter.eventually_all.mpr htail)).exists
    rw [difference_eq N]
    have hsum : valuation L
        (∑ p, algebraMap K L (tail p N) * (z p.1 * (u p.2 : L))) < β :=
      (valuation L).map_sum_lt hβ fun p _ ↦ hNt p
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hNr hsum)
  have difference_zero :
      x - ∑ p, algebraMap K L (C p) * (z p.1 * (u p.2 : L)) = 0 := by
    by_contra hne
    exact (lt_irrefl (valuation L
      (x - ∑ p, algebraMap K L (C p) * (z p.1 * (u p.2 : L)))))
        (difference_lt _ ((valuation L).ne_zero_iff.mpr hne))
  have hx : x = ∑ p, algebraMap K L (C p) * (z p.1 * (u p.2 : L)) :=
    sub_eq_zero.mp difference_zero
  rw [hx]
  apply Submodule.sum_mem
  intro p _
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self p))

/-- The defectless equality over a complete discretely valued field:
`e(L/K) * f(L/K) = [L:K]`.

No separability, local compactness, finite residue field, uniqueness hypothesis, or topology
on `L` is required. The trivial valuation is included; in that case its uniformizer is zero
and the first strict approximation step is already exact. -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank
    [UniformSpace K] [IsUniformAddGroup K] [IsValuativeTopology K] [CompleteSpace K]
    [IsDiscrete K] [IsRankLeOne K] :
    ramificationIdx K L * inertiaDeg K L = Module.finrank K L := by
  classical
  let e := ramificationIdx K L
  let f := inertiaDeg K L
  have he : e ≠ 0 := ramificationIdx_ne_zero (K := K) (L := L)
  have hf : 0 < f := inertiaDeg_pos (K := K) (L := L)
  have : Nonempty (Fin e) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero he)
  have : Nonempty (Fin f) := Fin.pos_iff_nonempty.mp hf
  have hfinite : Module.Finite 𝓀[K] 𝓀[L] :=
    finite_residueField_extension (K := K) (L := L)
  have hf_rank : Module.finrank 𝓀[K] 𝓀[L] = f := by
    simp [f, inertiaDeg]
  let b := Module.finBasisOfFinrankEq 𝓀[K] 𝓀[L] hf_rank
  obtain ⟨u, hu⟩ := exists_residue_lift b
  have u_val : ∀ j, valuation L (u j : L) = 1 := fun j ↦
    val_eq_one_of_residue_ne_zero (by rw [hu]; exact b.linearIndependent.ne_zero j)
  have u_indep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (u_val j)) := by
    have h_eq : (fun j ↦ residueOfValOne (u_val j)) = (b : Fin f → 𝓀[L]) := by
      funext j
      simp only [residueOfValOne]
      rw [show (⟨(u j : L), _⟩ : 𝒪[L]) = u j by ext; rfl, hu]
    simpa [h_eq] using b.linearIndependent
  let Q := valueGroupQuotient K L
  have : Finite Q := finite_valueGroup_quotient (K := K) (L := L)
  have : Fintype Q := Fintype.ofFinite Q
  have h_card : Fintype.card Q = e := by
    unfold e
    rw [ramificationIdx, Subgroup.index_eq_card, ← Nat.card_eq_fintype_card]
  let eqv : Q ≃ Fin e := Fintype.equivFinOfCardEq h_card
  have hz_exists : ∀ i : Fin e, ∃ z : L, z ≠ 0 ∧
      valuation L z = ((eqv.symm i).out : ValueGroupWithZero L) := by
    intro i
    obtain ⟨z, hz⟩ := valuation_surjective (K := L)
      ((eqv.symm i).out : ValueGroupWithZero L)
    refine ⟨z, ?_, hz⟩
    intro hz0
    exact ((eqv.symm i).out).ne_zero (by simpa [hz0] using hz.symm)
  choose z hz_nz hz using hz_exists
  have hz_quotient (i : Fin e) :
      (Units.mk0 (valuation L (z i)) ((valuation L).ne_zero_iff.mpr (hz_nz i)) : Q) =
        eqv.symm i := by
    rw [show Units.mk0 (valuation L (z i)) _ = (eqv.symm i).out by
      ext
      simpa using hz i, QuotientGroup.out_eq']
  have hz_cover : ∀ r : L, r ≠ 0 → ∃ i a, a ≠ 0 ∧
      valuation L r = valuation L (algebraMap K L a * z i) := by
    intro r hr
    let ur := Units.mk0 (valuation L r) ((valuation L).ne_zero_iff.mpr hr)
    let q : Q := (ur : Q)
    let i : Fin e := eqv q
    let uz := Units.mk0 (valuation L (z i)) ((valuation L).ne_zero_iff.mpr (hz_nz i))
    have hq : (ur : Q) = (uz : Q) := by
      calc
        (ur : Q) = q := rfl
        _ = eqv.symm i := (eqv.symm_apply_apply q).symm
        _ = (uz : Q) := (hz_quotient i).symm
    have hmem : ur / uz ∈
        (Units.map (mapValueGroupWithZero K L).toMonoidHom).range :=
      QuotientGroup.eq_iff_div_mem.mp hq
    obtain ⟨v, hv⟩ := hmem
    obtain ⟨a, ha_val⟩ := valuation_surjective (K := K) (v : ValueGroupWithZero K)
    have ha : a ≠ 0 := by
      intro ha0
      rw [ha0, map_zero] at ha_val
      exact v.ne_zero ha_val.symm
    refine ⟨i, a, ha, ?_⟩
    have hv_val := congrArg Units.val hv
    have hmap : mapValueGroupWithZero K L (v : ValueGroupWithZero K) =
        valuation L r / valuation L (z i) := by
      simpa [ur, uz] using hv_val
    calc
      valuation L r = (valuation L r / valuation L (z i)) * valuation L (z i) :=
        (div_mul_cancel₀ _ ((valuation L).ne_zero_iff.mpr (hz_nz i))).symm
      _ = mapValueGroupWithZero K L (v : ValueGroupWithZero K) * valuation L (z i) :=
        by rw [hmap]
      _ = mapValueGroupWithZero K L (valuation K a) * valuation L (z i) := by
        rw [ha_val]
      _ = valuation L (algebraMap K L a * z i) := by
        rw [map_mul, mapValueGroupWithZero_valuation]
  have hz_dist : ∀ i j : Fin e, i ≠ j → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      valuation L (algebraMap K L c * z i) ≠
        valuation L (algebraMap K L d * z j) := by
    intro i j hij c d hc hd h_eq
    have hcoset := quotientMk_eq_of_val_mul_eq hc hd (hz_nz i) (hz_nz j) h_eq
    exact hij ((eqv.symm).injective ((hz_quotient i).symm.trans
      (hcoset.trans (hz_quotient j))))
  have hspan : Submodule.span K
      (Set.range fun p : Fin e × Fin f ↦ z p.1 * (u p.2 : L)) = ⊤ :=
    span_eq_top_of_completeSpace z hz_nz hz_cover b u hu
  have h_indep : LinearIndependent K (fun p : Fin e × Fin f ↦ z p.1 * (u p.2 : L)) :=
    valuation_independence z (fun j ↦ (u j : L)) hz_nz hz_dist u_val u_indep
  let basis : Module.Basis (Fin e × Fin f) K L := Module.Basis.mk h_indep hspan.ge
  have hdegree : Module.finrank K L = e * f := by
    rw [Module.finrank_eq_card_basis basis, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
  simpa [e, f] using hdegree.symm

end ValuativeExtension
