# Status

The Lean development in `FundamentalInequality.lean` proves the simple
fundamental inequality for one finite valuative field extension:

```lean
theorem ValuativeExtension.fundamental_inequality [FiniteDimensional K L] :
    ramificationIndex K L * residueDegree K L ≤ Module.finrank K L
```

`residueDegree K L` is `Module.finrank 𝓀[K] 𝓀[L]`. `ramificationIndex K L` is
the index of the image of `(ValueGroupWithZero K)ˣ` under
`mapValueGroupWithZero K L`. Both are positive when `L/K` is finite. The
identity extension has `e = f = 1`, both invariants multiply in a tower, and an
extension is immediate if and only if `e = f = 1`.

The file is sorry-free. Its axioms on the main theorems are `propext`,
`Classical.choice`, and `Quot.sound`.

## Pin

- Lean `v4.36.0-rc1` (`lean-toolchain`)
- Mathlib `7bb03b4c5313d552989ba5b1c6d3f0f436f65d73` (`lakefile.toml`)

## Where this belongs

The near-term home is a Tau Ceti roadmap node for general valuative extensions,
not a Mathlib pull request and not a direct paste into Tau Ceti. The draft node
is [`ROADMAP_NODE.md`](ROADMAP_NODE.md). It targets Kuhlmann's Lemmas 6.12,
6.13 and 6.16, and it does not reimplement
`TauCeti.ramificationIndex_mul_inertiaDegree`.

Mathlib already contains the ideal-theoretic theory
(`Ideal.ramificationIdx`, `Ideal.inertiaDeg`,
`Ideal.sum_ramification_inertia_eq_finrank`, and
`NumberTheory/RamificationInertia/Valuation.lean`). `ValuationSubring` inertia
and decomposition subgroups are Galois groups, not `e` and `f`. This
development does not restate those results.

## Boundary

The following are outside this development. They are boundaries of the
statement, not work items recorded here:

- Ostrowski's sum over all extensions of one valuation;
- the defect, and equality `n = e f` without a defectless or local-field
  hypothesis;
- a comparison lemma with `TauCeti.ramificationIndex` and
  `TauCeti.inertiaDegree` (it names Tau Ceti declarations; the identification
  is described in `ROADMAP_NODE.md`);
- Dedekind's equality for the ideal-theoretic invariants;
- the equality between the order of an inertia group and `e`.

## References

Franz-Viktor Kuhlmann, *Valuation Theory*, book in preparation, unfinished
draft available only at <https://www.fvkuhlmann.de/Fvkbook.htm>, Chapter 6,
§6.3, Lemmas 6.12, 6.13 and 6.16, and Definition 6.1. Bourbaki,
*Commutative Algebra*, Chapter VI (`bourbaki1989b`). See
`docs/references.bib`.
