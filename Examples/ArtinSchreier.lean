/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.Polynomial.Splits

/-!
# The polynomial part of Artin–Schreier theory

All results in this file are proved, and they apply to an arbitrary prime `p`.
No valuation or defect assertion is imported.
-/

@[expose] public section

noncomputable section
open Polynomial

namespace ArtinSchreier

variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p]

/-- The Artin–Schreier polynomial in characteristic `p`. -/
def polynomial (a : K) : K[X] := X ^ p - X - C a

omit [Fact p.Prime] [CharP K p] in
@[simp] theorem eval_polynomial (a x : K) :
    (polynomial p a).eval x = x ^ p - x - a := by
  simp [polynomial]

omit [Fact p.Prime] in
theorem derivative_polynomial (a : K) :
    derivative (polynomial p a) = -1 := by
  simp [polynomial, derivative_sub, derivative_X_pow]

omit [Fact p.Prime] in
theorem separable (a : K) : (polynomial p a).Separable := by
  rw [separable_def', derivative_polynomial]
  exact ⟨0, -1, by simp⟩

omit [CharP K p] in
theorem natDegree_polynomial (a : K) : (polynomial p a).natDegree = p := by
  rw [polynomial, natDegree_sub_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow_sub_X (Fact.out : p.Prime).one_lt
  · rw [natDegree_C, natDegree_X_pow_sub_X (Fact.out : p.Prime).one_lt]
    exact (Fact.out : p.Prime).pos

omit [CharP K p] in
theorem monic (a : K) : (polynomial p a).Monic := by
  apply Monic.sub_of_left
  · exact (monic_X_pow p).sub_of_left (by
      simpa using (Fact.out : p.Prime).one_lt)
  · rw [degree_eq_natDegree (X_pow_sub_X_ne_zero (Fact.out : p.Prime).one_lt),
      natDegree_X_pow_sub_X (Fact.out : p.Prime).one_lt]
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (Fact.out : p.Prime).pos)

/-- The canonical embedding of the prime field. -/
abbrev primeCast : ZMod p →+* K := ZMod.castHom (dvd_refl p) K

theorem primeCast_pow (i : ZMod p) : primeCast p i ^ p = (primeCast p i : K) := by
  rw [← map_pow, ZMod.pow_card]

/-- Translating one root by any prime-field element gives another root. -/
theorem translated_root (a r : K) (hr : (polynomial p a).IsRoot r) (i : ZMod p) :
    (polynomial p a).IsRoot (r + primeCast p i) := by
  have hr' : r ^ p - r - a = 0 := by simpa [IsRoot] using hr
  simp only [IsRoot, eval_polynomial, add_pow_char, primeCast_pow]
  linear_combination hr'

/-- The `p` displayed translates are pairwise distinct. -/
theorem translate_injective (r : K) :
    Function.Injective (fun i : ZMod p => r + (primeCast p i : K)) := by
  intro i j h
  exact (primeCast p (K := K)).injective (add_left_cancel h)

/-- The full root multiset, not merely a list of candidate roots. -/
theorem roots_eq (a r : K) (hr : (polynomial p a).IsRoot r) :
    (polynomial p a).roots =
      (Finset.univ.map ⟨fun i : ZMod p => r + primeCast p i,
        translate_injective p r⟩).val := by
  apply roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact translated_root p a r hr i
  · simp [natDegree_polynomial, ZMod.card]
  · exact (separable p a).ne_zero

/-- A single root in the field implies splitting over that same field. -/
theorem splits_of_root (a r : K) (hr : (polynomial p a).IsRoot r) :
    (polynomial p a).Splits := by
  rw [splits_iff_card_roots, roots_eq p a r hr]
  simp [natDegree_polynomial, ZMod.card]

/-- A root is exactly one of the `p` translates of any fixed root. -/
theorem isRoot_iff (a r x : K) (hr : (polynomial p a).IsRoot r) :
    (polynomial p a).IsRoot x ↔ ∃ i : ZMod p, x = r + primeCast p i := by
  rw [← mem_roots (separable p a).ne_zero, roots_eq p a r hr]
  simp [eq_comm]

/-- Explicit linear factorisation indexed by `ZMod p`. -/
theorem factorisation (a r : K) (hr : (polynomial p a).IsRoot r) :
    polynomial p a = ∏ i : ZMod p, (X - C (r + primeCast p i)) := by
  rw [(splits_of_root p a r hr).eq_prod_roots_of_monic (monic p a), roots_eq p a r hr]
  simp only [← Finset.prod_eq_multiset_prod, Finset.prod_map]
  rfl

end ArtinSchreier
