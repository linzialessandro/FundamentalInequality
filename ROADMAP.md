# Roadmap: toward a Mathlib valuation-theory submission

This file plans how the repository grows from the fundamental inequality into
a larger body of valuation theory intended for Mathlib. It is a plan, not a
record of finished work: Stages 1 and 2, and the equality part of Stage 3, are
done. The long-term target is the theory of the defect and of tame extensions,
following Kuhlmann's book.

Two rules hold for every stage.

- Everything is built on Mathlib's `ValuativeRel` / `ValuativeExtension` /
  `ValueGroupWithZero` API at the pin (Lean `v4.36.0-rc1`, Mathlib
  `7bb03b4c5313d552989ba5b1c6d3f0f436f65d73`). Nothing imports or restates
  Tau Ceti declarations. Where a Tau Ceti result covers a special case (for
  example `TauCeti.ramificationIndex_mul_inertiaDegree` for nonarchimedean local
  fields), the statement here is proved from Mathlib alone, in greater
  generality, and the overlap is noted rather than imported.
- Each stage builds on the pin, has no `sorry`, adds no axioms beyond
  `propext`, `Classical.choice` and `Quot.sound`, and leaves existing
  statements unchanged.

Declaration names follow the Mathlib-consistent names introduced in #5
(see "Naming and notation"). Until #5 merges, main uses the old names.

[`ROADMAP_NODE.md`](ROADMAP_NODE.md) remains the contract for Stage 1 (the
Tau Ceti node draft). Its scope boundary is the boundary of Stage 1; the
stages below are the work beyond it.

Paths below are relative to the Mathlib checkout at the pin. "Not found" means
a search of that checkout found no declaration with the stated content; it is
not a claim that the result is absent from every branch or open PR.

Difficulty: **S** (a few hundred lines), **M** (one substantial file),
**L** (several files, new API), **XL** (a project of its own).

## Overview

| Stage | Content | Status | Difficulty |
| --- | --- | --- | --- |
| 1 | `e`, `f`, towers, fundamental inequality; Artin–Schreier defect example for every prime | done | — |
| 2 | Contrast example `ℚ_p(√p)`: `e = 2`, `f = 1`, `e f = [L:K]` | done | M |
| 3 | Defectless equality `e f = [L:K]` over complete discretely valued fields | done (equality) | L |
| 4 | Henselian valued fields: uniqueness of extension, henselization (Kuhlmann §7.8, Ch. 9) | planned | XL |
| 5 | Ostrowski's sum `∑ eᵢ fᵢ ≤ [L:K]` over all extensions (Kuhlmann §7.9) | planned | L |
| 6 | Defect: definition, defectless extensions and fields, Lemma of Ostrowski (Kuhlmann Ch. 11) | planned | L–XL |
| 7 | Ramification theory: decomposition, inertia, ramification fields (Kuhlmann Ch. 7) | planned | XL |
| 8 | Tame and purely wild extensions, tame fields (Kuhlmann Ch. 13); long-term target | planned | XL |
| 9 | Upstreaming to Mathlib | planned, runs alongside 2–8 | — |

## Stage 1: the fundamental inequality (done)

- **Statement.** For a finite `ValuativeExtension K L` of fields,
  `ramificationIdx K L * inertiaDeg K L ≤ Module.finrank K L`
  (`ramificationIdx_mul_inertiaDeg_le_finrank`, alias `fundamental_inequality`;
  Kuhlmann, Lemma 6.13), with both invariants positive, multiplicative in
  towers (Lemma 6.16), and `e = f = 1` exactly for immediate extensions.
- **Where.** `FundamentalInequality.lean`; contract in `ROADMAP_NODE.md`.
- **Examples.** `Examples/ArtinSchreierDefect/` proves, for every prime `p`,
  that `X^p - X - t⁻¹` over the perfect hull of `𝔽_p((t))` gives an extension
  with `[L:K] = p`, a unique extension of the valuation, and `e = f = 1`: a
  defect extension with Ostrowski sum `1 < p`.
- **Bridge.** `Examples/Bridge/Completeness.lean` has
  `ValuativeRel.IsRankLeOne.of_finiteDimensional`,
  `ValuativeRel.IsNontrivial.of_valuativeExtension`,
  `unique_valuativeRel_of_complete` (over a complete nonarchimedean normed base,
  a compatible rank-at-most-one relation is the one given by the spectral norm),
  and Ostrowski-sum helpers for the unique-extension case (`Extensions`,
  `extensionWeight`, `sum_le_finrank_of_unique`).
- **Mathlib used.** `Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`
  (`ValuativeRel`, `ValuativeExtension`, `ValueGroupWithZero`,
  `mapValueGroupWithZero`, `mapValueGroupWithZero_strictMono`, `IsRankLeOne`,
  `IsNontrivial`, `IsDiscrete`), `Mathlib/RingTheory/Valuation/Extension.lean`
  (`Valuation.HasExtension`), `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`
  (`spectralNorm_unique_field_norm_ext`), `Mathlib/RingTheory/Valuation/RankOne.lean`.

## Stage 2: the contrast example `ℚ_p(√p)` (done)

- **Statement.** For `L = ℚ_p(√p)`, i.e. `ℚ_[p]` adjoined a root of `X² - p`,
  with the valuation extending the `p`-adic one: `[L:K] = 2`, `e = 2`, `f = 1`,
  so `e f = [L:K]` and the extension has no defect.
- **Proof plan.** Irreducibility of `X² - p` from Eisenstein at `p`. The
  extended valuation is unique (Stage 1 bridge, via the spectral norm). Then
  `v(√p)² = v(p)` and `v(p)` generates `v(ℚ_pˣ)`, so `v(√p)` is not in the image
  and `e ≥ 2`. The fundamental inequality gives `e f ≤ 2`, hence `e = 2` and
  `f = 1`. No general equality theorem is imported or used.
- **Mathlib found.** `Mathlib/NumberTheory/Padics/ValuativeRel.lean`
  (`ValuativeRel`-compatible `ℚ_[p]` with `IsNontrivial`, `IsRankLeOne`,
  `IsValuativeTopology`), and `IsNonarchimedeanLocalField ℚ_[p]` in
  `Mathlib/NumberTheory/Padics/LocalField.lean`; `Polynomial.IsEisensteinAt.irreducible` in
  `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean`;
  `Mathlib/RingTheory/Polynomial/Eisenstein/Criterion.lean`
  (`irreducible_of_eisenstein_criterion`); `IsDiscreteValuationRing ℤ_[p]` in
  `Mathlib/NumberTheory/Padics/PadicIntegers.lean`.
- **Implemented.** `Examples/PadicSqrtP/` builds the spectral `ValuativeRel`,
  proves uniqueness, and computes the two invariants from the fundamental
  inequality without a general equality theorem.
- **Difficulty.** M. Offered by Demetrios Chiuratto Agourakis.
- **Role.** First instance of Stage 3, and a test case that the Stage 3
  statement must reproduce.

## Stage 3: the defectless equality over complete discretely valued fields (done: equality)

- **Statement.** If `K` is complete for a discrete (rank-one, `IsDiscrete`)
  valuation and `L/K` is finite, then
  `ramificationIdx K L * inertiaDeg K L = Module.finrank K L`.
  No separability, local compactness, or finite residue field is assumed.
- **Proof plan.** The completeness argument of Serre, *Local Fields*,
  Ch. II §2: with `π` a
  uniformizer of `L` and `u₁, …, u_f` lifting a residue basis, the products
  `uⱼ πⁱ` (`0 ≤ i < e`) are linearly independent (Stage 1, Lemma 6.12) and span
  `𝒪[L]` over `𝒪[K]` by successive approximation, which uses completeness of
  `K`. Steps:
  1. The extension of the valuation to `L` is unique, and `L` is complete
     (Stage 1 bridge; spectral norm).
  2. `IsDiscrete K` and finite index give `IsDiscrete L`.
  3. Spanning by successive approximation, giving the equality.
  4. Bridge lemma: when `𝒪[K]` and `𝒪[L]` are DVRs, `ramificationIdx K L` and
     `inertiaDeg K L` agree with `Ideal.ramificationIdx` and
     `Ideal.inertiaDeg` of the maximal ideals. This connects the valuative and
     ideal-theoretic APIs.
- **Implemented.** The equality is proved in
  `FundamentalInequality/DiscreteComplete.lean`
  (`ramificationIdx_mul_inertiaDeg_eq_finrank`), by successive approximation
  over `K` without steps 1 and 2; `Examples/PadicSqrtP/Stage3.lean` checks it
  on `ℚ_p(√p)`. The bridge lemma of step 4 to `Ideal.ramificationIdx` /
  `Ideal.inertiaDeg` remains planned.
- **Mathlib found.**
  - `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`:
    `spectralNorm_unique_field_norm_ext`, `spectralNorm_extends`, and the
    `completeSpace` instance for a finite-dimensional extension.
  - `Mathlib/Topology/Algebra/Module/FiniteDimension.lean`:
    `FiniteDimensional.complete`.
  - `Mathlib/RingTheory/Valuation/Discrete/Basic.lean`:
    `Valuation.valuationSubring_isDiscreteValuationRing` (needs a cyclic value
    group); `Mathlib/RingTheory/Valuation/DiscreteValuativeRel.lean`.
  - `Mathlib/NumberTheory/LocalField/Basic.lean`: `IsNonarchimedeanLocalField`,
    with instances `IsDiscreteValuationRing 𝒪[K]`, `ValuativeRel.IsDiscrete K`,
    `CompleteSpace K`, `IsAdicComplete 𝓂[K] 𝒪[K]`, and
    `valueGroupWithZeroIsoInt`. Stage 3 specializes to local fields through
    these instances.
  - `Mathlib/RingTheory/RamificationInertia/Ramification.lean`
    (`Ideal.ramificationIdx`), `.../Inertia.lean` (`Ideal.inertiaDeg`),
    `.../Basic.lean` (`Ideal.sum_ramification_inertia_eq_finrank`: for
    `S` finite flat over a domain `R`, `∑ e f = finrank R S`).
  - `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`:
    `IsIntegralClosure.finite` and `IsIntegralClosure.isDedekindDomain`.
- **Missing.** Finiteness of `𝒪[L]` over `𝒪[K]` for an inseparable `L/K`:
  `IsIntegralClosure.finite` assumes `Algebra.IsSeparable K L`. The direct
  approximation argument avoids this. The alternative route through
  `Ideal.sum_ramification_inertia_eq_finrank` needs `Module.Finite 𝒪[K] 𝒪[L]`,
  so it covers only the separable case unless that finiteness is proved
  separately.
- **Difficulty.** L.
- **Overlap.** For local fields this is the statement of
  `TauCeti.ramificationIndex_mul_inertiaDegree`. The result here is proved from
  Mathlib alone and is more general; the comparison is a note, not a lemma.

## Kuhlmann as the guiding reference for Stages 4–8

From Stage 4 on, the order of definitions and proofs follows Kuhlmann's
*Valuation Theory*, the source already used for Lemmas 6.12, 6.13 and 6.16.
The long-term target is the theory of the defect and of tame extensions
(Kuhlmann, Chapters 11 and 13).

Chapter, section and result numbers below were checked against the chapter
files on <https://www.fvkuhlmann.de/Fvkbook.htm> (versions of July 14, 2011,
the ones linked there today). The author warns that numbering in the draft is
not final, so every citation names the result as well as its number. The
book's public table of contents (chapters used here):

| Chapter | Title | Used in |
| --- | --- | --- |
| 6 | Valued field extensions | Stage 1 (§6.3 Valuation independence) |
| 7 | Ramification theory | Stages 4, 5, 7 |
| 9 | Hensel's Lemma | Stage 4 |
| 11 | Defect | Stage 6 |
| 13 | The tame and the wild valuation theory | Stage 8 |
| 14 | Extremality, maximality, and defectless fields | beyond Stage 8 |

Kuhlmann defines the defect through the henselization (§11.1) and proves
Ostrowski's sum by passing to henselizations (§7.9). So henselian fields come
first in the order below.

## Stage 4: henselian valued fields (planned)

- **Statement.** Kuhlmann calls `K` henselian when the valuation extends
  uniquely to every algebraic extension (§7.8; Lemma 7.33 reduces this to finite
  Galois extensions). The target equivalence is with `𝒪[K]` being a henselian
  local ring. The henselization `Kʰ` is the decomposition field of `K̃/K`, and
  it is an immediate separable algebraic extension (Theorem 7.42). Complete
  rank-one fields are henselian.
- **Kuhlmann.** §7.8 "Henselian fields and henselizations"; Chapter 9
  "Hensel's Lemma", §9.1 "Equivalent forms of Hensel's Lemma", §9.2 "Henselian
  fields".
- **Mathlib found.**
  - `Mathlib/RingTheory/Henselian.lean`: `HenselianRing`, `HenselianLocalRing`,
    `HenselianLocalRing.TFAE`, `IsAdicComplete.henselianRing`.
  - `Mathlib/NumberTheory/Padics/Hensel.lean`: `hensels_lemma` for `ℤ_[p]`.
  - `Mathlib/Analysis/Normed/Field/Krasner.lean`: `IsKrasner`,
    `IsKrasner.of_completeSpace_of_normal`.
  - `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`: uniqueness of the
    extended norm over a complete base (already used in Stage 1's bridge).
  - `Mathlib/RingTheory/Valuation/RamificationGroup.lean`:
    `ValuationSubring.decompositionSubgroup`, which Kuhlmann's construction of
    the henselization as a decomposition field needs.
- **Missing.** A henselian valued-field class stated with `ValuativeRel`; the
  equivalence with unique extension for valuations of arbitrary rank; the
  henselization and its immediacy (none found).
- **Difficulty.** XL. The complete rank-one case is close to what Stage 1's
  bridge already proves and can come first.

## Stage 5: Ostrowski's sum over all extensions (planned)

- **Statement.** For a finite `L/K` and a valuation on `K`, the extensions
  `w₁, …, w_g` to `L` are finite in number and
  `∑ e(wᵢ) f(wᵢ) ≤ [L:K]` (Kuhlmann, Theorem 7.49, "the fundamental
  inequality", formula (7.26)). Equality holds, for example, when the valuation
  ring of `K` is a DVR and its integral closure in `L` is finite over it.
- **Kuhlmann.** §7.9 "The fundamental inequality": Lemma 7.46 (double cosets
  and degrees), Lemma 7.47, Corollary 7.48, Theorem 7.49. The proof lifts
  `L/K` to the henselizations, so it needs Stage 4.
- **Other route.** An approximation theorem for finitely many incomparable
  valuations gives the inequality directly, without henselizations. Mathlib
  has this only for rank one.
- **Mathlib found.**
  - `Mathlib/RingTheory/Valuation/LocalSubring.lean`:
    `LocalSubring.exists_valuationRing_of_isMax`,
    `LocalSubring.mem_of_isMax_of_isIntegral` (existence of extensions).
  - `Mathlib/RingTheory/Valuation/Integral.lean`: integrality lemmas for
    `Valuation.Integers`.
  - `Mathlib/Analysis/AbsoluteValue/Equivalence.lean`:
    `AbsoluteValue.denseRange_algebraMap_pi` (weak approximation for finitely
    many pairwise inequivalent real absolute values).
  - `Mathlib/RingTheory/RamificationInertia/Basic.lean`:
    `Ideal.sum_ramification_inertia_eq_finrank`, usable for the equality case
    once Stage 3's bridge lemma exists.
- **Missing.** A type of all extensions of a `ValuativeRel` along `K → L` with
  a `Finite` instance; an approximation theorem for valuations of arbitrary
  rank (not found). `Extensions` and `sum_le_finrank_of_unique` in
  `Examples/Bridge/Completeness.lean` cover only the unique-extension case.
- **Difficulty.** L once Stage 4 exists.

## Stage 6: the defect (planned)

- **Statement.** For a finite `L/K` with `[Lʰ : Kʰ]` finite, the defect is
  `d(L/K) = [Lʰ : Kʰ] / (e f)` (Kuhlmann, formula (11.1)). It is a positive
  integer and a power of the characteristic exponent of the residue field
  (Lemma 11.17, "Lemma of Ostrowski"). `K` is defectless in `L` when equality
  holds in Ostrowski's sum; this property is transitive in towers
  (Lemma 11.6). `K` is a defectless field when it is defectless in every finite
  extension. Every valued field of residue characteristic `0` is defectless
  (Theorem 11.23).
- **Kuhlmann.** Chapter 11: §11.1 "The (henselian) defect", §11.2 "Defectless
  extensions and defectless fields", §11.3 "The Lemma of Ostrowski", §11.5
  "Examples for non-trivial defect".
- **Mathlib found.** `Module.finrank_mul_finrank`;
  `ValuationSubring.decompositionSubgroup` and
  `ValuationSubring.inertiaSubgroup` in
  `Mathlib/RingTheory/Valuation/RamificationGroup.lean`.
- **Missing.** Any notion of defect or defectless extension or field (no match
  for `defect`, `defectless` or `henselization` in the Mathlib tree).
- **Examples.** The Artin–Schreier example has `d = p` (Kuhlmann §11.5
  discusses this family); Stage 2 has `d = 1`.
- **Difficulty.** L for the definition and towers. Ostrowski's lemma needs the
  ramification theory of Stage 7 (its proof uses the decomposition, inertia and
  ramification fields), so it is XL.

## Stage 7: ramification theory of valued fields (planned)

- **Statement.** For a normal algebraic extension of valued fields: the
  decomposition, inertia and ramification fields, with their value groups and
  residue fields. For the absolute case `Kˢᵉᵖ/K`: the absolute inertia field
  `Kⁱ` and ramification field `Kʳ`, and `Kˢᵉᵖ / Kʳ` is a `p`-extension
  (Kuhlmann cites Theorem 7.16 for this in §13.8). `Kʳ` is used throughout
  Stage 8.
- **Kuhlmann.** Chapter 7: §7.1 "Basic definitions", §7.3 "The decomposition
  field", §7.4 "The inertia field", §7.5 "The ramification field", §7.7
  "Absolute ramification theory".
- **Mathlib found.** `Mathlib/RingTheory/Valuation/RamificationGroup.lean`
  defines `ValuationSubring.decompositionSubgroup` and
  `ValuationSubring.inertiaSubgroup`, with no ramification subgroup and no
  fixed fields. Galois correspondence: `Mathlib/FieldTheory/Galois/`.
- **Missing.** The ramification group of a valuation, the three fixed fields,
  and their value groups and residue fields.
- **Difficulty.** XL.

## Stage 8: tame and purely wild extensions, tame fields (planned; long-term target)

- **Definitions** (Kuhlmann §13.1 "Tame and purely wild extensions"). Let `p`
  be the characteristic exponent of the residue field. An algebraic extension
  `L/K` of henselian fields is *tame* if every finite subextension `E/K`
  satisfies
  - (TE1) `e(E/K)` is prime to `p`, i.e. `p ∤ (vE : vK)`;
  - (TE2) the residue field extension is separable;
  - (TE3) `E/K` is defectless.

  An extension of a henselian field is *purely wild* if (PW1) `vL / vK` is a
  `p`-group and (PW2) the residue field extension is purely inseparable.
  Kuhlmann remarks (Remark 13.1) that "tame" here is stronger than "tamely
  ramified" in Endler's book: it also requires (TE3).
- **Main structure results**, as Kuhlmann states them:
  - Theorem 13.2: for henselian `K`, the absolute ramification field `Kʳ` is
    the maximal tame extension of `K`; the compositum of two tame extensions is
    tame.
  - Theorem 13.3: the absolute inertia field is the maximal tame unramified
    extension.
  - Lemma 13.4: for a tame `F/K` and a finite `L/K`, `d(L/K) = d(L.F/F)`.
  - Lemma 13.5: an algebraic `L/K` is purely wild if and only if it is
    linearly disjoint from `Kʳ/K`, if and only if `L ∩ Kʳ = K`.
- **Tame fields** (Kuhlmann §13.9 "Tame fields"). A henselian `K` is a *tame
  field* if `K̃/K` is tame, *separably tame* if `Kˢᵉᵖ/K` is tame, and *purely
  wild* if `K̃/K` is purely wild.
  - Lemma 13.33: `K` is tame iff `Kʳ = K̃`; algebraic extensions of tame fields
    are tame.
  - Lemma 13.35: every tame field is henselian, defectless and perfect.
  - Lemma 13.37: `K` is tame iff every algebraic purely wild extension is
    trivial, iff `K` is algebraically maximal, `vK` is `p`-divisible, and the
    residue field is perfect.
  - Corollary 13.38: in characteristic `p > 0`, tame means algebraically
    maximal and perfect.
  - §13.10 "Separably tame fields" and §13.11 "Kaplansky fields" come after.
- **Mathlib found.** None of these notions (no match for `IsTame`,
  `PurelyWild`, or "algebraically maximal" in the Mathlib tree).
  `Mathlib/FieldTheory/PurelyInseparable/` and `Mathlib/FieldTheory/Separable.lean`
  supply (PW2) and (TE2); `IsPGroup` (`Mathlib/GroupTheory/PGroup.lean`) and
  `Nat.Coprime` supply (PW1) and (TE1).
- **Examples.** The Artin–Schreier extension is purely wild and not tame
  (`e = f = 1`, `d = p`). Kuhlmann §13.4 "Artin-Schreier extensions of
  henselian fields" treats this family.
- **Difficulty.** XL. The definitions and the (TE1)–(TE3) characterization of
  a single finite extension can start after Stage 6. Theorem 13.2 and the tame
  field results need Stage 7.

## Stage 9: upstreaming plan (planned, alongside Stages 2–8)

Order, each step a separate Mathlib PR that depends only on earlier ones:

1. **Small general lemmas from the bridge.**
   `ValuativeRel.IsRankLeOne.of_finiteDimensional` and
   `ValuativeRel.IsNontrivial.of_valuativeExtension`, next to
   `ValuativeExtension` in `Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`.
2. **The invariants.** `ramificationIdx`, `inertiaDeg`, `IsImmediate`, towers,
   and the `ValuativeExtension` identity instance, as a new file under
   `Mathlib/RingTheory/Valuation/ValuativeRel/` (Layer 0 of `ROADMAP_NODE.md`).
3. **The fundamental inequality.** Lemmas 6.12 and 6.13 (Layers 1–2),
   `ramificationIdx_mul_inertiaDeg_le_finrank`, in the same directory.
4. **Uniqueness over complete rank-one fields.** `unique_valuativeRel_of_complete`,
   near `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean` or
   `Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`.
5. **Stage 3 and its bridge lemma** to `Ideal.ramificationIdx` /
   `Ideal.inertiaDeg`.
6. **Stages 4–8 in order.**

Worked examples (Artin–Schreier, `ℚ_p(√p)`) stay in this repository or go to
`MathlibTest/` / `Archive/`, depending on reviewer preference. They are not
library material as written.

Other work before step 2:

- **Duplication.** About 650 lines of the `p = 2` chain in
  `Examples/ArtinSchreierDefect/Residue.lean` duplicate
  `Examples/ArtinSchreierDefect/ResidueGeneral.lean` and can be removed before
  any example material is upstreamed.
- **Conventions.** Module docstrings with references, `@[simp]` only on
  normal-form lemmas, no `Examples.*` namespace in library files, and the
  `weak.linter.mathlibStandardSet` linters (already enabled in `lakefile.toml`)
  clean.
- **Deprecations at the pin.** `Mathlib/NumberTheory/RamificationInertia/Valuation.lean`
  is a deprecated module (since 2026-10-09); its content is in
  `Mathlib/RingTheory/DedekindDomain/AdicValuation/Ramification.lean`. The
  `Ideal.sum_ramification_inertia` of
  `Mathlib/NumberTheory/RamificationInertia/Basic.lean` is deprecated in favour
  of `Mathlib/RingTheory/RamificationInertia/Basic.lean`. New code should cite
  the current files.

## Naming and notation

The rule is to follow Mathlib's naming conventions
(<https://leanprover-community.github.io/contribute/naming.html>) and Mathlib's
existing names for the same objects. Renamed declarations keep their old name as
a `@[deprecated (since := …)] alias`, and statements do not change.

**Done in #5** (`mathlib-naming`; main keeps the old names until it merges):

| Old name | New name | Reason |
| --- | --- | --- |
| `ValuativeExtension.ramificationIndex` | `ValuativeExtension.ramificationIdx` | Mathlib: `Ideal.ramificationIdx` |
| `ValuativeExtension.residueDegree` | `ValuativeExtension.inertiaDeg` | Mathlib: `Ideal.inertiaDeg`; Kuhlmann's "inertia degree" |
| `ramificationIndex_self`, `residueDegree_self` | `ramificationIdx_self`, `inertiaDeg_self` | follows the definitions |
| `ramificationIndex_mul`, `residueDegree_mul` | `ramificationIdx_mul_ramificationIdx`, `inertiaDeg_mul_inertiaDeg` | the `x_mul_x` form of `Module.finrank_mul_finrank`, `Ideal.ramificationIdxIn_mul_ramificationIdxIn` |
| `ramificationIndex_eq_one_iff`, `residueDegree_eq_one_iff` | `ramificationIdx_eq_one_iff`, `inertiaDeg_eq_one_iff` | follows the definitions |
| `ramificationIndex_ne_zero`, `one_le_ramificationIndex`, `residueDegree_pos` | `ramificationIdx_ne_zero`, `one_le_ramificationIdx`, `inertiaDeg_pos` | follows the definitions |
| `isImmediate_iff_ramificationIndex_eq_one_and_residueDegree_eq_one` | `isImmediate_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one` | follows the definitions |
| `ValuativeExtension.tower` | `ValuativeExtension.comp` | Mathlib: `Valuation.HasExtension.comp` |
| Example names containing `ramificationIndex` / `residueDegree` / `ResidueDegree` (`localResidueDegree`, `residueDegree_eq_of_local_map`, `concrete_*`, `*_of_pow_surjective`, `*_of_square_surjective`) | same names with `ramificationIdx` / `inertiaDeg` / `InertiaDeg` | consistency |

`residueDegree` is also a Mathlib name (`AlgebraicGeometry.Scheme.Hom.residueDegree`,
in `Mathlib/AlgebraicGeometry/ResidueField.lean`), so the old name did not
clash with anything. The number-theoretic side uses `inertiaDeg`, and Stage 3's
bridge lemma compares the two directly.

Also done in #5, following the proposals Alessandro approved:

| Old name | New name | Reason |
| --- | --- | --- |
| `ValuativeExtension.fundamental_inequality` | `ValuativeExtension.ramificationIdx_mul_inertiaDeg_le_finrank`; `fundamental_inequality` stays as a plain alias, not deprecated | Mathlib names a theorem after its statement; the classical name is kept because README and papers cite it |
| `instIsLocalHom_integer`, `instIsScalarTower_integer` | `instIsLocalHomInteger`, `instIsScalarTowerInteger` | Mathlib instance names are `inst` + UpperCamelCase, without underscores (compare `Valuation.HasExtension.instIsScalarTowerInteger`) |
| `ValuativeExtension.subgroup_normal` (instance) | `ValuativeExtension.instNormalUnitsValueGroupWithZero` | the name Lean generates for this instance |
| `ArtinSchreierBridge.isNontrivial_of_valuativeExtension` | `ValuativeRel.IsNontrivial.of_valuativeExtension` | dot notation on the class, like Mathlib's `ValuativeRel.IsRankLeOne.of_valuativeExtension` |
| `ArtinSchreierBridge.isRankLeOne_of_finite` | `ValuativeRel.IsRankLeOne.of_finiteDimensional` | dot notation on the class; hypothesis named as in Mathlib |

None of these names exists in Mathlib at the pin.

**Agreed names for future notions** (not defined yet):

| Notion | Name | Reason |
| --- | --- | --- |
| the defect `d(L/K)` | `ValuativeExtension.defect` | `ℕ`-valued def in lowerCamelCase, like `ramificationIdx` |
| defectless / tame / purely wild extension | `ValuativeExtension.IsDefectless`, `ValuativeExtension.IsTame`, `ValuativeExtension.IsPurelyWild` | Prop-valued: `Is` + UpperCamelCase |
| defectless / tame / henselian field | `ValuativeRel.IsDefectless`, `ValuativeRel.IsTame`, `ValuativeRel.IsHenselian` (classes) | parallels `ValuativeRel.IsDiscrete`, `ValuativeRel.IsRankLeOne` |

**Notation.** Lean code uses Mathlib's notation only: `𝒪[K]`, `𝓀[K]`,
`ValueGroupWithZero K`, `valuation K`, `Module.finrank K L`; no new notation is
introduced. Docstrings write `e(L/K)`, `f(L/K)`, `d(L/K)`, `[L:K]` and `L/K`.
Kuhlmann writes `L|K`, `(vL : vK)` for `e`, `[Lv : Kv]` for `f`, and
`d(L|K, v)`. Docstrings cite Kuhlmann's form once when a definition is
introduced.

## References

- Franz-Viktor Kuhlmann, *Valuation Theory*, book in preparation, Chapters 6,
  7, 9, 11, 13 (`kuhlmannValuation`). Guiding reference from Stage 4 on.
- N. Bourbaki, *Commutative Algebra*, Chapter VI (`bourbaki1989b`).
- J.-P. Serre, *Local Fields*, Chapter II, §2 (`serreLocalFields`).
- A. J. Engler and A. Prestel, *Valued Fields* (`englerPrestel2005`), for an
  approximation-theorem route to Stage 5.
