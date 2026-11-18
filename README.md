# Fundamental inequality for valuative field extensions

Author: **Alessandro Linzi**

This repository formalizes the simple fundamental inequality for a finite
extension of valued fields in Lean 4. The inequality lives in
`FundamentalInequality.lean`; `FundamentalInequality/DiscreteComplete.lean`
proves the defectless equality over complete discretely valued fields. Both
modules use the `ValuativeExtension` namespace on top of Mathlib's
`ValuativeRel` / `ValuativeExtension` / `ValueGroupWithZero` API.

The development is a sandbox aimed at a Tau Ceti roadmap node. A draft of that
node is `ROADMAP_NODE.md`. Nothing in this repository is a pull request against
Mathlib or against Tau Ceti.

The longer-term goal is a valuation-theory submission to Mathlib built on the
same API, without Tau Ceti dependencies. The staged plan is
[`ROADMAP.md`](ROADMAP.md): the contrast example `ℚ_p(√p)`, the defectless
equality over complete discretely valued fields, then henselian fields,
Ostrowski's sum, the defect, ramification theory, and tame extensions,
following Kuhlmann's book, plus the upstreaming order and naming rules.

## Statement

For a finite extension `L/K` of fields carrying valuative relations, with
`ValuativeExtension K L`,

\[
  e(L/K)\, f(L/K) \le [L:K].
\]

Both factors are finite (recorded as positive natural numbers). Here

- `inertiaDeg K L` is `Module.finrank 𝓀[K] 𝓀[L]`,
- `ramificationIdx K L` is the subgroup index of the image of
  `(ValueGroupWithZero K)ˣ` under `mapValueGroupWithZero K L`.

An infinite index or an infinite residue extension is recorded as `0`, matching
`Subgroup.index` and `Module.finrank`.

The names follow Mathlib's `Ideal.ramificationIdx` / `Ideal.inertiaDeg` and
Mathlib's naming conventions. The earlier names (`ramificationIndex`,
`residueDegree`, `ramificationIndex_mul`, `residueDegree_mul`, `tower`,
`instIsLocalHom_integer`, `isRankLeOne_of_finite`, …) remain as deprecated
aliases (since 2026-11-16). The main theorem is
`ramificationIdx_mul_inertiaDeg_le_finrank`; `fundamental_inequality` is a
permanent alias for it.

## Main declarations

| Name | Role |
| --- | --- |
| `inertiaDeg`, `ramificationIdx` | `f(L/K)` and `e(L/K)` |
| `comp` | a tower of valuative extensions is a valuative extension |
| `IsImmediate` | value group and residue field both stay the same |
| `inertiaDeg_self`, `ramificationIdx_self` | identity extension: `e = f = 1` |
| `inertiaDeg_mul_inertiaDeg`, `ramificationIdx_mul_ramificationIdx` | multiplicativity in a tower |
| `isImmediate_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one` | immediate iff `e = f = 1` |
| `exists_max_val_mul`, `valuation_independence` | Kuhlmann's Lemma 6.12 |
| `finite_residueField_extension`, `finite_valueGroup_quotient` | finiteness |
| `ramificationIdx_mul_inertiaDeg_le_finrank` (alias `fundamental_inequality`) | Kuhlmann's Lemma 6.13 |
| `span_eq_top_of_completeSpace` | successive-approximation spanning over a complete discrete base |
| `ramificationIdx_mul_inertiaDeg_eq_finrank` | `e f = [L:K]` over a complete discrete rank-at-most-one base |

The middle factor of `ramificationIdx_mul_ramificationIdx` is `ramificationIdx K F`, the
index in `(ValueGroupWithZero F)ˣ`, transported into `(ValueGroupWithZero L)ˣ`
along `mapValueGroupWithZero F L` by `Subgroup.index_map_of_injective`.

## Scope

The library proves the inequality for one valuative extension and the equality
`e f = [L:K]` when the base is complete, discrete, and rank at most one. It does
not prove Ostrowski's sum over several extensions, henselianity or
henselization results, uniqueness of extension as a new general theorem, the
defect, or a comparison with `Ideal.ramificationIdx` and `Ideal.inertiaDeg`.
For local fields the new equality overlaps with
`TauCeti.ramificationIndex_mul_inertiaDegree`; Tau Ceti is neither imported nor
restated. The planned work beyond this scope is in [`ROADMAP.md`](ROADMAP.md).

## References

- Franz-Viktor Kuhlmann, *Valuation Theory*, book in preparation. Unfinished
  draft, available only at <https://www.fvkuhlmann.de/Fvkbook.htm>. Chapter 6,
  §6.3, Lemmas 6.12, 6.13 and 6.16, and Definition 6.1 for immediate extensions.
- N. Bourbaki, *Commutative Algebra*, Chapters 1–7, Chapter VI.
  Bibliography keys: `docs/references.bib`.

## Examples

`Examples/` holds a worked Artin–Schreier defect example (`lake build
Examples`) for every prime `p`.  For the extension
`X^p - X - t⁻¹` over the perfect hull of `F_p((t))`, it proves
irreducibility, uniqueness of the extended valuation, `e = f = 1`, and
`[L:K] = p`.  Thus the Ostrowski sum is `1 < p` and the numerical defect
quotient is `p`.  The original `p = 2` declarations remain available as a
backwards-compatible quadratic API.

`Examples/PadicSqrtP/` is the Stage 2 contrast example.  For every prime `p`,
it constructs the unique compatible spectral valuative relation on
`ℚ_[p](√p)`, proves `[ℚ_[p](√p) : ℚ_[p]] = 2`, `e = 2`, and `f = 1`, and
deduces `e f = [L : K]` directly from the fundamental inequality.  Its short
Stage 3 check also recovers the equality from the general complete-discrete
theorem and derives `f = 1` again from `e = [L : K] = 2`.

## Building

```bash
lake exe cache get
lake build
```

The toolchain is Lean `v4.36.0-rc1`. Mathlib is pinned to commit
`7bb03b4c5313d552989ba5b1c6d3f0f436f65d73`. There are no `sorry`s.

## License

Apache 2.0. See [LICENSE](LICENSE).
