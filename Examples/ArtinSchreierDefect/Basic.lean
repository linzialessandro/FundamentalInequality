/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreier
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Data.Int.WithZero
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Field data for the Artin–Schreier defect example

The polynomial results (separability, root translates, absence of a root in
`F_p((t))` or its perfect hull) are proved for every prime `p`. Irreducibility
and the quadratic extension are currently specialised to `p = 2`, where
`irreducible_of_degree_le_three_of_not_isRoot` applies.
-/

@[expose] public section

noncomputable section

open Polynomial ValuativeRel
open scoped LaurentSeries WithZero ValuativeRel

namespace ArtinSchreierDefect

variable (p : ℕ) [Fact p.Prime]

abbrev Base := LaurentSeries (ZMod p)

instance baseCharP : CharP (Base p) p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) (Base p)).injective p

/-- The perfect hull inside an algebraic closure, not the complete Laurent field itself. -/
abbrev Hull := ↥(perfectClosure (Base p) (AlgebraicClosure (Base p)))

/-- The Laurent monomial `t⁻¹`. -/
def inverseT : Base p := HahnSeries.single (-1) 1

def standardPolynomial : (Hull p)[X] :=
  ArtinSchreier.polynomial p (algebraMap (Base p) (Hull p) (inverseT p))

instance baseValuativeRel : ValuativeRel (Base p) :=
  .ofValuation (Valued.v : Valuation (Base p) ℤᵐ⁰)

theorem inverseT_value :
    (Valued.v : Valuation (Base p) ℤᵐ⁰) (inverseT p) = WithZero.exp (1 : ℤ) := by
  simpa [inverseT] using LaurentSeries.valuation_single_zpow (ZMod p) (-1)

theorem exp_one_not_pth_power (γ : ℤᵐ⁰) : γ ^ p ≠ WithZero.exp (1 : ℤ) := by
  intro h
  have hh := congrArg WithZero.log h
  have hp := (Fact.out : p.Prime).two_le
  have hh' : p * WithZero.log γ = 1 := by
    simpa [WithZero.log_pow] using hh
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hh' with h | h <;> omega

/-- A root would have pole order `1/p`, impossible in the Laurent field. -/
theorem base_no_root (x : Base p) : x ^ p - x ≠ inverseT p := by
  intro h
  let v : Valuation (Base p) ℤᵐ⁰ := Valued.v
  have ha : v (inverseT p) = WithZero.exp (1 : ℤ) := inverseT_value p
  have ha1 : 1 < v (inverseT p) := by
    rw [ha]
    change WithZero.exp (0 : ℤ) < WithZero.exp (1 : ℤ)
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hx : 1 < v x := by
    by_contra! hx
    have hxx : v (x ^ p) ≤ 1 := by rw [map_pow]; exact pow_le_one₀ zero_le hx
    have hh := v.map_sub_le hxx hx
    rw [h] at hh
    exact (not_le_of_gt ha1) hh
  have hlt : v x < v (x ^ p) := by
    rw [map_pow]
    exact lt_self_pow₀ hx (Fact.out : p.Prime).one_lt
  have hh : v x ^ p = WithZero.exp (1 : ℤ) := by
    rw [← map_pow, ← v.map_sub_eq_of_lt_left hlt, h, ha]
  exact exp_one_not_pth_power p (v x) hh

/-- A separable root cannot first appear in a purely inseparable perfect hull. -/
theorem hull_no_root (x : Hull p) : ¬ (standardPolynomial p).IsRoot x := by
  intro hx
  let f := ArtinSchreier.polynomial p (inverseT p)
  have heval : aeval x f = 0 := by
    simpa [f, standardPolynomial, ArtinSchreier.polynomial, IsRoot] using hx
  have hsep : IsSeparable (Base p) x :=
    (ArtinSchreier.separable p (inverseT p)).of_dvd (minpoly.dvd (Base p) x heval)
  obtain ⟨y, hy⟩ := IsPurelyInseparable.inseparable (Base p) x hsep
  apply base_no_root p y
  apply (algebraMap (Base p) (Hull p)).injective
  rw [map_sub, map_pow, hy]
  simpa [f, ArtinSchreier.polynomial, sub_eq_zero] using heval

theorem quadratic_irreducible : Irreducible (standardPolynomial 2) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [standardPolynomial, ArtinSchreier.natDegree_polynomial]
  · exact hull_no_root 2

instance : Fact (Irreducible (standardPolynomial 2)) := ⟨quadratic_irreducible⟩

abbrev QuadraticExtension := AdjoinRoot (standardPolynomial 2)

instance : FiniteDimensional (Hull 2) QuadraticExtension :=
  (ArtinSchreier.monic 2 _).finite_adjoinRoot

theorem quadratic_degree : Module.finrank (Hull 2) QuadraticExtension = 2 := by
  change Module.finrank (Hull 2) ((Hull 2)[X] ⧸ Ideal.span {standardPolynomial 2}) = 2
  rw [finrank_quotient_span_eq_natDegree]
  exact ArtinSchreier.natDegree_polynomial 2 _

theorem quadratic_root_equation :
    AdjoinRoot.root (standardPolynomial 2) ^ 2 -
        AdjoinRoot.root (standardPolynomial 2) =
      algebraMap (Hull 2) QuadraticExtension
        (algebraMap (Base 2) (Hull 2) (inverseT 2)) := by
  have h := AdjoinRoot.mk_self (f := standardPolynomial 2)
  change (AdjoinRoot.mk (standardPolynomial 2))
    (X ^ 2 - X - C (algebraMap (Base 2) (Hull 2) (inverseT 2))) = 0 at h
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

end ArtinSchreierDefect
