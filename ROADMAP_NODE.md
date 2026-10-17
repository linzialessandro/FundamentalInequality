# Roadmap: the fundamental inequality for valuative extensions

This roadmap owns the ramification index and the residue degree of a general
valuative field extension, their finiteness for a finite extension,
multiplicativity in towers, and the fundamental inequality
`e(L/K) · f(L/K) ≤ [L:K]`. It stops before Ostrowski's sum over several
extensions of one valuation, before the defect, and before any equality
`n = ef` that needs a defectless or complete discretely valued hypothesis.

The boundary with local fields is sharp. `TauCetiRoadmap/LocalFieldsRamification`
owns the normalized ramification index and inertia degree of a finite extension
of nonarchimedean local fields, and the equality
`TauCeti.ramificationIndex_mul_inertiaDegree`
(`TauCeti/NumberTheory/LocalField/RamificationIndex.lean`,
`TauCeti/NumberTheory/LocalField/InertiaDegree.lean`). This roadmap does not
reimplement those declarations and does not restate that equality. Mathlib owns
the ideal-theoretic pair `Ideal.ramificationIdx` / `Ideal.inertiaDeg`, the
equality `Ideal.sum_ramification_inertia_eq_finrank`, and the valuation form in
`Mathlib/NumberTheory/RamificationInertia/Valuation.lean`. The subgroups
`ValuationSubring.decompositionSubgroup` and `ValuationSubring.inertiaSubgroup`
are Galois groups. None of those is an alias of the invariants below.

## Scope and exported contract

The exported vocabulary is one ramification index and one residue degree for a
`ValuativeExtension` of fields, together with the notion of an immediate
extension. Downstream code imports these declarations. It does not rebuild a
second index out of `Valuation.comap` or a second residue degree out of a
hand-rolled residue ring.

`residueDegree K L` is `Module.finrank 𝓀[K] 𝓀[L]`. `ramificationIndex K L` is
the index of

```
(Units.map (mapValueGroupWithZero K L).toMonoidHom).range
```

inside `(ValueGroupWithZero L)ˣ`. Both take the value `0` when the corresponding
cardinal is infinite, by the same convention as `Module.finrank` and
`Subgroup.index`. An extension is immediate when `mapValueGroupWithZero K L`
and `algebraMap 𝓀[K] 𝓀[L]` are both surjective (Kuhlmann, Definition 6.1).

For a tower `K → F → L` of valuative extensions, `ramificationIndex_mul` is

```
ramificationIndex K F * ramificationIndex F L = ramificationIndex K L.
```

The factor `ramificationIndex K F` is the index computed in
`(ValueGroupWithZero F)ˣ`. Injectivity of `mapValueGroupWithZero F L` transports
it into `(ValueGroupWithZero L)ˣ` by `Subgroup.index_map_of_injective`, where it
multiplies `ramificationIndex F L`. `residueDegree_mul` is the tower law
`Module.finrank_mul_finrank` on the residue fields.

On a finite extension both invariants are positive, and

```
ramificationIndex K L * residueDegree K L ≤ Module.finrank K L.
```

The products `z i * u j` that witness the inequality are `K`-linearly
independent when the values `v(z i)` lie in distinct cosets of `v(Kˣ)` and the
residues of the valuation-one elements `u j` are linearly independent over
`𝓀[K]` (Kuhlmann, Lemma 6.12). The inequality is Lemma 6.13. Multiplicativity
in towers is Lemma 6.16.

A finite extension of nonarchimedean local fields carries
`IsNonarchimedeanLocalField` and `ValuativeRel.valueGroupWithZeroIsoInt`, which
identifies `ValueGroupWithZero` with `ℤᵐ⁰`. Under that identification on both
sides of `ValuativeExtension K L`, the index defined here is the normalized
ramification index `TauCeti.ramificationIndex`, and the residue degree defined
here is `TauCeti.inertiaDegree`. The inequality then specializes to the
equality `TauCeti.ramificationIndex_mul_inertiaDegree`. That comparison names
Tau Ceti declarations, so it is not a lemma of a development that depends only
on Mathlib. It is the responsibility of the local-fields roadmap, which already
exports the equality, and this roadmap does not duplicate it.

The signatures below are sketches of the contract. The contract is the
mathematical statement in this section. A reviewer may change names and
argument order.

```lean
def residueDegree (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : ℕ

def ramificationIndex (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : ℕ

def IsImmediate (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : Prop

@[simp] theorem residueDegree_self (K : Type*) [Field K] [ValuativeRel K] :
    residueDegree K K = 1

@[simp] theorem ramificationIndex_self (K : Type*) [Field K] [ValuativeRel K] :
    ramificationIndex K K = 1

theorem residueDegree_mul [ValuativeExtension K F] [ValuativeExtension F L] :
    residueDegree K F * residueDegree F L = residueDegree K L

theorem ramificationIndex_mul [ValuativeExtension K F] [ValuativeExtension F L] :
    ramificationIndex K F * ramificationIndex F L = ramificationIndex K L

theorem finite_residueField_extension [FiniteDimensional K L] :
    Module.Finite 𝓀[K] 𝓀[L]

theorem finite_valueGroup_quotient [FiniteDimensional K L] :
    Finite (valueGroupQuotient K L)

theorem residueDegree_pos [FiniteDimensional K L] : 0 < residueDegree K L

theorem ramificationIndex_ne_zero [FiniteDimensional K L] :
    ramificationIndex K L ≠ 0

theorem exists_max_val_mul {I J : Type*} [Fintype I] [Fintype J]
    (z : I → L) (u : J → L) (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i i', i ≠ i' → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      valuation L (algebraMap K L c * z i) ≠ valuation L (algebraMap K L d * z i'))
    (hu : ∀ j, valuation L (u j) = 1)
    (hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j)))
    (c : I × J → K) (hc : ∃ p, c p ≠ 0) :
    ∃ p0, c p0 ≠ 0 ∧
      valuation L (∑ p, algebraMap K L (c p) * (z p.1 * u p.2)) =
        valuation L (algebraMap K L (c p0) * (z p0.1 * u p0.2))

theorem valuation_independence {I J : Type*} [Finite I] [Finite J]
    (z : I → L) (u : J → L) (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i i', i ≠ i' → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      valuation L (algebraMap K L c * z i) ≠ valuation L (algebraMap K L d * z i'))
    (hu : ∀ j, valuation L (u j) = 1)
    (hindep : LinearIndependent 𝓀[K] (fun j ↦ residueOfValOne (hu j))) :
    LinearIndependent K (fun p : I × J ↦ z p.1 * u p.2)

theorem fundamental_inequality [FiniteDimensional K L] :
    ramificationIndex K L * residueDegree K L ≤ Module.finrank K L

theorem isImmediate_iff_ramificationIndex_eq_one_and_residueDegree_eq_one :
    IsImmediate K L ↔ ramificationIndex K L = 1 ∧ residueDegree K L = 1
```

## The build, in layers

### Layer 0: the valuative extension

- **Canonical valuations form a `HasExtension`.** From `ValuativeExtension K L`
  the canonical valuations satisfy `(valuation K).HasExtension (valuation L)`.
  The integer-ring map `𝒪[K] → 𝒪[L]` is a local homomorphism, so Mathlib's
  residue-field algebra `𝓀[K] → 𝓀[L]` is available. This is not a global
  `IsLocalHom` instance on `algebraMap K L`.
  - *Prerequisites:* `Mathlib: ValuativeExtension`, `ValuativeRel.valuation`,
    `Valuation.HasExtension`, `Valuation.integer`, `IsLocalRing.ResidueField`.
  - *API:* `valuation_hasExtension`, `instIsLocalHom_integer`.
- **The two invariants.** Define `residueDegree` and `ramificationIndex` as
  above, and `valueGroupQuotient` as the quotient of `(ValueGroupWithZero L)ˣ`
  by that image. `mapValueGroupWithZero` is strictly monotone, so the induced
  map on units is injective.
  - *Prerequisites:* `Mathlib: mapValueGroupWithZero`,
    `mapValueGroupWithZero_strictMono`, `Subgroup.index`, `Units.map`.
  - *API:* `residueDegree`, `ramificationIndex`, `valueGroupQuotient`.
- **Identity and towers.** The identity algebra is a `ValuativeExtension`, with
  `e = f = 1`. A tower of valuative extensions is a valuative extension.
  `mapValueGroupWithZero` commutes with composition. Residue degree multiplies
  by the tower law. Ramification index multiplies by transporting the middle
  index along `mapValueGroupWithZero F L`.
  - *Prerequisites:* `Layer 0: the two invariants`;
    `Mathlib: Module.finrank_mul_finrank`, `MonoidHom.range_comp`,
    `Subgroup.index_map_of_injective`.
  - *Source:* Kuhlmann, Lemma 6.16.
  - *API:* `residueDegree_self`, `ramificationIndex_self`, `tower`,
    `mapValueGroupWithZero_comp`, `residueDegree_mul`, `ramificationIndex_mul`.
  - *False generalization:* the middle factor is not the index of a `comap`
    subgroup left inside `ValueGroupWithZero F`. The statement that multiplies
    is the transported index.

### Layer 1: valuation independence

- **One coset lemma.** If `v(c z₁) = v(d z₂)` with `c, d ∈ Kˣ` and
  `z₁, z₂ ∈ Lˣ`, then `v(z₁)` and `v(z₂)` determine the same class in
  `valueGroupQuotient K L`.
  - *API:* `quotientMk_eq_of_val_mul_eq`.
- **Scaling, residue combination, distinct-coset sum.** A nontrivial linear
  combination has a coefficient of maximal valuation. After scaling that
  coefficient to valuation `1`, residue-linear independence keeps the
  combination a unit. Grouping terms by value-group cosets and applying
  `Valuation.map_sum_eq_of_lt` yields the valuation of one maximal term.
  - *Source:* Kuhlmann, Lemma 6.12.
  - *API:* `exists_max_val_coeff`, `sum_eq_coeff_mul_scaled`,
    `val_scaledSum_eq_one`, `exists_max_val_mul`, `valuation_independence`.
  - *False generalization:* distinct valuations of the summands are not enough
    when the coefficients vary. The cosets have to be distinct, and the
    valuation-one family has to stay linearly independent over the residue
    field.

### Layer 2: finiteness and the inequality

- **Finiteness of `f` and of the value-group quotient.** An infinite
  `𝓀[K]`-linearly independent set of residues, or an infinite set of distinct
  value-group cosets, produces arbitrarily large `K`-linearly independent
  subsets of `L`, which a finite extension does not have.
  - *Source:* Kuhlmann, Lemma 6.13.
  - *API:* `finite_residueField_extension`, `residueDegree_pos`,
    `finite_valueGroup_quotient`, `ramificationIndex_ne_zero`.
- **The inequality.** Choose a residue basis and a set of coset representatives
  and apply `valuation_independence`. The cardinality of the product is
  `e f`.
  - *Source:* Kuhlmann, Lemma 6.13.
  - *API:* `fundamental_inequality`.
  - *False generalization:* dropping `FiniteDimensional K L` leaves the
    inequality true in the `0 ≤ _` reading of an infinite invariant, and false
    as a statement that `e` and `f` are finite. The milestone includes
    finiteness.
- **Immediate extensions.** `e(L/K) = 1` if and only if
  `mapValueGroupWithZero K L` is surjective, because every nonzero element of
  a `LinearOrderedCommGroupWithZero` is a unit. `f(L/K) = 1` if and only if
  the residue algebra map is surjective.
  - *Source:* Kuhlmann, Definition 6.1.
  - *API:* `IsImmediate`, `ramificationIndex_eq_one_iff`,
    `residueDegree_eq_one_iff`,
    `isImmediate_iff_ramificationIndex_eq_one_and_residueDegree_eq_one`.
  - *False generalization:* `e = f = 1` is not the equality `ef = [L:K]`. An
    immediate extension of positive degree is a defect extension.

## References

- Franz-Viktor Kuhlmann, *Valuation Theory*, book in preparation. Unfinished
  draft, available only at <https://www.fvkuhlmann.de/Fvkbook.htm>. Chapter 6,
  §6.3, Lemmas 6.12, 6.13 and 6.16, and Chapter 6, Definition 6.1.
- N. Bourbaki, *Commutative Algebra*, Chapters 1–7, Chapter VI, §3
  (`bourbaki1989b`).
