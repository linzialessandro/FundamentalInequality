# Fundamental inequality for valuative field extensions

Author: **Alessandro Linzi**

This repository formalizes the simple fundamental inequality for a finite
extension of valued fields in Lean 4. The statements live in
`FundamentalInequality.lean`, in the `ValuativeExtension` namespace, on top of
Mathlib's `ValuativeRel` / `ValuativeExtension` / `ValueGroupWithZero` API.

The development is a sandbox aimed at a Tau Ceti roadmap node. A draft of that
node is `ROADMAP_NODE.md`. Nothing in this repository is a pull request against
Mathlib or against Tau Ceti.

## Statement

For a finite extension `L/K` of fields carrying valuative relations, with
`ValuativeExtension K L`,

\[
  e(L/K)\, f(L/K) \le [L:K].
\]

Both factors are finite (recorded as positive natural numbers). Here

- `residueDegree K L` is `Module.finrank 𝓀[K] 𝓀[L]`,
- `ramificationIndex K L` is the subgroup index of the image of
  `(ValueGroupWithZero K)ˣ` under `mapValueGroupWithZero K L`.

An infinite index or an infinite residue extension is recorded as `0`, matching
`Subgroup.index` and `Module.finrank`.

## Main declarations

| Name | Role |
| --- | --- |
| `residueDegree`, `ramificationIndex` | `f(L/K)` and `e(L/K)` |
| `IsImmediate` | value group and residue field both stay the same |
| `residueDegree_self`, `ramificationIndex_self` | identity extension: `e = f = 1` |
| `residueDegree_mul`, `ramificationIndex_mul` | multiplicativity in a tower |
| `isImmediate_iff_ramificationIndex_eq_one_and_residueDegree_eq_one` | immediate iff `e = f = 1` |
| `exists_max_val_mul`, `valuation_independence` | Kuhlmann's Lemma 6.12 |
| `finite_residueField_extension`, `finite_valueGroup_quotient` | finiteness |
| `fundamental_inequality` | Kuhlmann's Lemma 6.13 |

The middle factor of `ramificationIndex_mul` is `ramificationIndex K F`, the
index in `(ValueGroupWithZero F)ˣ`, transported into `(ValueGroupWithZero L)ˣ`
along `mapValueGroupWithZero F L` by `Subgroup.index_map_of_injective`.

## Scope

The file proves the inequality for one valuative extension. It does not prove
Ostrowski's sum over several extensions of one valuation, the defect, equality
in the defectless case, or a comparison with `Ideal.ramificationIdx` and
`Ideal.inertiaDeg`. The equality `e f = [L:K]` for finite extensions of
nonarchimedean local fields is `TauCeti.ramificationIndex_mul_inertiaDegree`,
owned by the local-fields roadmap, and is not restated here.

## References

- Franz-Viktor Kuhlmann, *Valuation Theory*, book in preparation. Unfinished
  draft, available only at <https://www.fvkuhlmann.de/Fvkbook.htm>. Chapter 6,
  §6.3, Lemmas 6.12, 6.13 and 6.16, and Definition 6.1 for immediate extensions.
- N. Bourbaki, *Commutative Algebra*, Chapters 1–7, Chapter VI.
  Bibliography keys: `docs/references.bib`.

## Building

```bash
lake exe cache get
lake build
```

The toolchain is Lean `v4.36.0-rc1`. Mathlib is pinned to commit
`7bb03b4c5313d552989ba5b1c6d3f0f436f65d73`. There are no `sorry`s.

## License

Apache 2.0. See [LICENSE](LICENSE).
