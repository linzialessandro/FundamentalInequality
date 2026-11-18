/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.PadicSqrtP.Valuation
public import FundamentalInequality.DiscreteComplete

/-!
# Recovering the `ℚ_p(√p)` equality from Stage 3

The general defectless equality over complete discretely valued fields recovers the
Stage 2 computation for `ℚ_[p](√p)`. Together with the independently proved
ramification index and extension degree, it again forces the inertia degree to be one.

## Main results

* `PadicSqrtP.stage3_ramificationIdx_mul_inertiaDeg_eq_finrank` applies the general
  Stage 3 theorem.
* `PadicSqrtP.inertiaDeg_eq_one_from_stage3` is a consistency check against the
  explicit Stage 2 computation.

## Implementation notes

This file only applies the general theorem and reuses the existing Stage 2 declarations;
it introduces no new construction of the extension or its valuation.

## References

* [J.-P. Serre, *Local Fields*][serreLocalFields], Chapter II, §2, Proposition 3.
* [F.-V. Kuhlmann, *Valuation Theory*][kuhlmannValuation], Chapter 6, §6.3,
  Lemmas 6.12 and 6.13.
-/

@[expose] public section

noncomputable section

open ValuativeExtension

namespace PadicSqrtP

variable (p : ℕ) [Fact p.Prime]

/-- The general complete-discrete theorem recovers `e f = [L:K]` for `ℚ_[p](√p)`. -/
theorem stage3_ramificationIdx_mul_inertiaDeg_eq_finrank :
    ramificationIdx (Base p) (RootExtension p) *
      inertiaDeg (Base p) (RootExtension p) =
        Module.finrank (Base p) (RootExtension p) :=
  ValuativeExtension.ramificationIdx_mul_inertiaDeg_eq_finrank

/-- The Stage 3 equality, `e = 2`, and `[L:K] = 2` force `f = 1`. -/
theorem inertiaDeg_eq_one_from_stage3 :
    inertiaDeg (Base p) (RootExtension p) = 1 := by
  have h := stage3_ramificationIdx_mul_inertiaDeg_eq_finrank p
  rw [ramificationIdx_eq_two, finrank_eq_two] at h
  omega

end PadicSqrtP
