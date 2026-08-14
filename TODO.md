# Mathlib contribution TODO

This file is the working plan to turn this repository into a professional
`mathlib4` pull request. It records the review of 2026-08-13: mathematical
comparison with Kuhlmann, comparison with the current mathlib valuation API,
style/process gaps, and a phased path to a concrete PR.

**Current status: local sandbox rewritten; not ready to open a mathlib PR.**

The Lean file is sorry-free and now aims at the *full* simple fundamental
inequality of Kuhlmann 6.13: `e` and `f` are defined, identity and tower
lemmas are present, valuation independence is stated with residue linear
independence (6.12), and finiteness of `e` and `f` under
`FiniteDimensional` is proved, so `fundamental_inequality` no longer
escapes through the vacuous `e = 0` / `f = 0` branch.

It is still a standalone Lake project (not a mathlib fork), has not been
compiled against a fresh `lake exe cache get` in this rewrite, and has not
been through a mathlib style/CI/`#lint` pass or a Zulip design thread.

Do **not** open a PR from `https://github.com/linzialessandro/FundamentalInequality`.
Mathlib PRs are opened against `leanprover-community/mathlib4` from a
**fork of mathlib**, after a Zulip design discussion.

---

## 1. What this project actually proves

### Informal statement (target)

Let \((L\mid K,\, w\mid v)\) be an extension of valued fields, with
\(L\mid K\) finite. Write

- \(n = [L:K]\),
- \(e = e(w/v) = (wL : vK)\), the ramification index,
- \(f = f(w/v) = [Lw : Kv]\), the inertia / residue degree.

Then \(e\) and \(f\) are finite, and

\[
n \ge e\, f.
\]

This is the *simple* (one-extension) form of the fundamental inequality.

### Formal statement (current)

```lean
theorem Valuation.fundamentalInequality [FiniteDimensional K L] :
    Valuation.ramificationIndex vK vL * Valuation.residueDegree vK vL
      ≤ Module.finrank K L
```

with

```lean
def Valuation.residueDegree [vK.HasExtension vL] : ℕ :=
  Module.finrank
    (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

def Valuation.ramificationIndex [vK.HasExtension vL] : ℕ :=
  MonoidWithZeroHom.valueGroup (vL.comap (algebraMap K L)) |>.relIndex
    (MonoidWithZeroHom.valueGroup vL)
```

### Proof idea (matches the book)

1. If \(e = 0\) or \(f = 0\) as `ℕ`, conclude `0 ≤ n` and stop.
2. Otherwise take a residue-field basis of \(Lv/Kv\) and lift it to
   elements \(u_j \in L\) of valuation \(1\).
3. Take representatives \(z_i \in L^\times\) of the cosets of
   \(vL(K^\times)\) in \(vL(L^\times)\).
4. Prove the products \(z_i u_j\) are \(K\)-linearly independent
   (valuation independence).
5. Conclude \(e f = \#(I \times J) \le [L:K]\).

This is the standard argument of Kuhlmann, Lemmas 6.12–6.13.

### What is *not* proved

- The Ostrowski / several-extensions form
  \(\sum_i e_i f_i \le [L:K]\).
- Equality / vs-defectless characterisation (Kuhlmann 6.17).
- Comparison with Dedekind `Ideal.ramificationIdx` / `Ideal.inertiaDeg`.
- Identifying `e(u/v)` computed in \(\Gamma_F\) with the comap index
  in \(\Gamma_L\) via `IsEquiv.orderMonoidIso` (tower for `e` is the
  book's single-valuation form plus `ramificationIndex_mul_hasExtension`).
- Immediate \(\Leftrightarrow\) \(e = f = 1\).

Those last items belong in later PRs. Finiteness and the valuation form
of 6.12 are now in the sandbox file.

---

## 2. Book reference (correct this)

The file header and README now cite

> F.-V. Kuhlmann, *Valued Fields*, Chapter 6, §6.3, Lemmas 6.12–6.13.

(The earlier Chapter 4, §4.4 citation was wrong: Chapter 4 never states
\(n \ge ef\).)

The inequality is

> **Kuhlmann, Chapter 6, §6.3, Lemmas 6.12–6.13.**

| Book | Content |
|---|---|
| Lemma 6.12 | Valuation independence: distinct value cosets + residue-linearly independent units \(\Rightarrow\) the products \(z_i u_j\) are \(K\)-valuation independent. |
| Lemma 6.13 | If \(L\mid K\) is finite then \(Lv\mid Kv\) and \(vL/vK\) are finite, and \([L:K] \ge (vL:vK)\,[Lv:Kv]\). |
| After 6.13 | Definitions of \(e\) and \(f\); \(n \ge ef\); immediate iff \(e = f = 1\). |
| Lemma 6.14 | Finite extensions of finitely ramified / formally \(\mathfrak{p}\)-adic fields stay in the class (application). |
| Lemma 6.16 | Multiplicativity of \(e\) and \(f\) in towers. |
| Lemma 6.17 | Finite vs-defectless \(\Leftrightarrow\) valuation basis \(\Leftrightarrow\) \(n = ef\). |

Also cite Bourbaki, *Algèbre commutative*, Ch. VI (mathlib's
`Extension.lean` already uses this). Add a BibTeX entry to
`mathlib4/docs/references.bib` when the PR is opened; do not leave a
free-text citation.

---

## 3. How this sits in current mathlib

Inspected against `mathlib4` master (Valuation folder as of the 2026-08-13
review) and against `HasExtension` in

`Mathlib/RingTheory/Valuation/Extension.lean`.

### Already in mathlib (reuse, do not reinvent)

- `Valuation`, `Valuation.IsEquiv`, `Valuation.comap`.
- `Valuation.HasExtension vR vA` : `vR` is equivalent to
  `vA.comap (algebraMap R A)`. **Equivalence, not equality.** This is
  why ramification must be computed from
  `valueGroup (vL.comap (algebraMap K L))` inside \(\Gamma_L^\times\),
  not from `valueGroup vK` (a possibly different ordered group).
- Algebra instances: `vK.valuationSubring → vL.valuationSubring`,
  residue-field algebra map, `LiesOver` for maximal ideals,
  `val_map_le_one_iff`, `algebraMap_residue_eq_residue_algebraMap`.
- `IsLocalRing.ResidueField` of a valuation subring.
- `Subgroup.relIndex`.
- Dedekind / number-field ramification:
  `Ideal.ramificationIdx`, `Ideal.inertiaDeg`
  (different API; discrete / ideal-theoretic).
- Galois ramification *groups*:
  `ValuationSubring.decompositionSubgroup`,
  `ValuationSubring.inertiaSubgroup`
  in `Mathlib/RingTheory/Valuation/RamificationGroup.lean`.
  These are **not** \(e\) and \(f\).

### Not in mathlib (this contribution)

- `Valuation.ramificationIndex` / `Valuation.residueDegree`.
- Valuation independence for field extensions.
- The fundamental inequality \(n \ge ef\) for a general valued-field
  finite extension.

So the topic is in scope and the definitions would be new, not a
duplicate. Naming must be discussed so it does not collide with
`ramificationIdx` / `inertiaDeg`.

### Suggested file location (confirm on Zulip)

```
Mathlib/RingTheory/Valuation/Ramification.lean
```

or a small cluster:

```
Mathlib/RingTheory/Valuation/ValueGroup.lean      -- if extra API is needed
Mathlib/RingTheory/Valuation/Independence.lean    -- Lemma 6.12
Mathlib/RingTheory/Valuation/Ramification.lean    -- e, f, inequality
```

Use `Extension.lean` as the style template (`module`, `public import`,
`public section`, existing authors of the valuation extension API).

Current mathlib Valuation files to stay consistent with:

- `Basic.lean`
- `Extension.lean`          ← primary integration point
- `ValuationSubring.lean`
- `Integers.lean`
- `RamificationGroup.lean`  ← name clash risk; different concept
- `Discrete/`               ← later comparison with discrete valuations

---

## 4. Blocking mathematical gap

Kuhlmann 6.13 includes **finiteness**. The current proof does not.

`ramificationIndex` and `residueDegree` are `ℕ`. Mathlib's `Nat.card` /
`Module.finrank` send infinite objects to `0`. The main proof then does:

```lean
by_cases he : e = 0
· rw [he, zero_mul]
  exact Nat.zero_le _
by_cases hf : f = 0
· rw [hf, mul_zero]
  exact Nat.zero_le _
```

If \(e\) or \(f\) is infinite this branch fires and the inequality holds
vacuously as \(0 \le n\). That does **not** prove they are finite.

### Required extra theorems (same PR as the inequality)

```lean
theorem ramificationIndex_ne_zero
    [vK.HasExtension vL] [FiniteDimensional K L] :
    ramificationIndex vK vL ≠ 0

theorem residueDegree_pos
    [vK.HasExtension vL] [FiniteDimensional K L] :
    0 < residueDegree vK vL
```

Equivalently (often nicer as the primary statements):

```lean
theorem finite_valueGroup_quotient
    [vK.HasExtension vL] [FiniteDimensional K L] :
    Finite (valueGroup vL ⧸ (valueGroup (vL.comap (algebraMap K L))).comap _)

theorem finite_residueField_extension
    [vK.HasExtension vL] [FiniteDimensional K L] :
    Module.Finite
      (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)
```

**Argument:** the same independence proof, with arbitrarily large finite
sets of coset representatives or residue-independent units, would produce
arbitrarily large \(K\)-linearly independent families, contradicting
`FiniteDimensional K L`. The current `e = 0` / `f = 0` branches must be
replaced by this, or kept only after finiteness is already known.

Without these lemmas the formal theorem is strictly weaker than 6.13,
and the applications in the README (closure of finitely ramified and
formally \(\mathfrak{p}\)-adic fields under finite extensions) do not
follow.

---

## 5. API design decisions (resolve on Zulip before rewriting)

### 5.1 `ℕ` vs `ℕ∞` vs `Cardinal`

- Book: \(e\) and \(f\) are cardinals, possibly infinite.
- Current choice: `ℕ` with “infinite = 0”, same as `finrank` / `relIndex`.
- Alternative: `ℕ∞` or `Cardinal` is more honest and harder to use.

**Recommendation to propose:** keep `ℕ`, and **prove** `≠ 0` / `pos`
under `FiniteDimensional`. This matches existing mathlib dimension API.

### 5.2 Names

| Proposed | Alternative | Notes |
|---|---|---|
| `Valuation.ramificationIndex` | `ramificationIdx` | Dedekind theory already uses `Ideal.ramificationIdx`. |
| `Valuation.residueDegree` | `inertiaDeg`, `inertiaDegree` | Kuhlmann says “inertia degree”; mathlib Dedekind uses `inertiaDeg`. |

**Recommendation to propose:** `ramificationIndex` and `residueDegree`
on `Valuation`, with a docstring that points at the Dedekind names and
promises a comparison lemma later. Do not silently reuse
`ramificationIdx`.

### 5.3 Valuation independence statement

Kuhlmann 6.12 (target API):

> If the \(v(z_i)\) lie in distinct cosets modulo \(vK\), and the
> residues of units \(u_j \in \mathcal{O}_L\) are \(Kv\)-linearly
> independent, then the products \(z_i u_j\) are \(K\)-linearly
> independent (in fact valuation-independent).

Current file:

- `valuation_independence` takes an ad hoc “no-cancellation”
  predicate, not residue linear independence.
- `linearIndependent_of_val_distinct_coset` is unused.
- `linearIndependent_of_val_no_cancel` is unused.

**Required:** restate the public lemma as 6.12. Keep no-cancellation
only as a private helper, or delete it.

### 5.4 Minimum API for the first PR

Must have:

- `residueDegree`, `ramificationIndex` (docs: \(f\), \(e\)).
- `ramificationIndex_ne_zero`, `residueDegree_pos` under
  `FiniteDimensional`.
- `ramificationIndex_id` / `residueDegree_id`: identity extension
  has \(e = f = 1\).
- Tower multiplicativity (true without finiteness, using `relIndex`
  and `finrank` tower; state carefully when a factor is `0`).
- Valuation independence (6.12).
- `fundamentalInequality` (6.13).

Nice but later PRs:

- Immediate \(\Leftrightarrow\) \(e = f = 1\).
- Equality \(\Leftrightarrow\) vs-defectless \(\Leftrightarrow\)
  valuation basis (6.17).
- Ostrowski \(\sum_i e_i f_i \le n\).
- Comparison with `Ideal.ramificationIdx` / `Ideal.inertiaDeg`.
- Lemma 6.14 (finitely ramified / formally \(\mathfrak{p}\)-adic
  closed under finite extensions) — needs those classes defined first.

### 5.5 Scope of PR 1

Do **not** put independence, Ostrowski, defect, and Dedekind comparison
in one PR. Mathlib wants small PRs.

Suggested split (after Zulip):

1. **PR A** — definitions of \(e\), \(f\), identity and tower lemmas,
   finiteness under `FiniteDimensional`.
2. **PR B** — valuation independence (6.12).
3. **PR C** — fundamental inequality (6.13), using A and B.

If reviewers prefer one PR, A+B+C is acceptable *after* the code is
factored and the style pass is done. Still no Ostrowski / 6.17.

---

## 6. Style and CI checklist (current file fails this)

Compare every new file to
`Mathlib/RingTheory/Valuation/Extension.lean` and to

- https://leanprover-community.github.io/contribute/style.html
- https://leanprover-community.github.io/contribute/naming.html
- https://leanprover-community.github.io/contribute/doc.html
- https://leanprover-community.github.io/contribute/commit.html

### Header / imports

- [ ] Copyright header (existing authors of touched files + Alessandro Linzi).
- [ ] `module` on its own line after the header.
- [ ] Blank line, then grouped `public import`s, alphabetical.
- [ ] No unused imports. Current unused / suspicious:
  `ValuationRing`, `IsIntegral.Basic`, `FieldTheory.Separable`,
  `FieldTheory.Tower`, several `LinearAlgebra.Dimension.*` (keep only
  what is used after the rewrite).
- [ ] No extra blank lines after the import block.

### Module docstring

```
/-!
# Title

Summary.

## Main definitions
## Main results
## Implementation notes   -- ℕ convention; HasExtension vs equality
## References             -- BibTeX keys, not free text
## Tags
-/
```

- [ ] Correct Kuhlmann reference (Ch. 6 §6.3).
- [ ] Tags: `valuation`, `ramification index`, `residue degree`,
  `inertia degree`, `fundamental inequality`, `valued field`.

### Declarations

- [ ] Docstring on every `def` and on every theorem with mathematical
  content.
- [ ] Explicit binder types; explicit return types.
- [ ] Hypotheses left of the colon.
- [ ] `fun … ↦` not `λ`.
- [ ] Lines \(\le 100\) characters.
- [ ] **No empty lines inside declarations** (linter).
- [ ] No informal implementation comments that should be lemmas.
- [ ] Prefer `push_neg` / `by_contra!` over `push Not`.
- [ ] One tactic per line unless closing a tiny goal.
- [ ] Do not squeeze terminal `simp`.
- [ ] `lemma` vs `theorem`: independence and the inequality are
  theorems; `sum_eq_zero_implies_val_eq` is a lemma.

### Proof structure

The main theorem is a ~250-line tactic script. Extract at least:

- [ ] Lift of a residue basis to units of valuation 1.
- [ ] Choice of coset representatives in the value group.
- [ ] Criterion: same coset iff the ratio of values lies in
  \(v(K^\times)\).
- [ ] After scaling by a max-valuation coefficient, the residue linear
  combination is nonzero (the \(j_0\) coordinate is \(1\)).
- [ ] The scaled sum is a unit in the valuation ring.

Delete or use:

- [ ] `linearIndependent_of_val_distinct_coset`
- [ ] `linearIndependent_of_val_no_cancel`

### Lint / build (inside the mathlib checkout)

```bash
lake exe cache get
lake build Mathlib.RingTheory.Valuation.Ramification
# at the bottom of the new file while developing:
#   #lint
#   #lint only docBlame
#   #lint only docBlame docBlameThm
lake exe mk_all   # if a new file was added
```

- [ ] Green CI on the PR.
- [ ] `!bench` only if the PR adds instances / `simp` lemmas that
  could affect search. First PR should add almost none.

---

## 7. Process (mandatory, not optional)

Source: https://leanprover-community.github.io/contribute/index.html
and https://leanprover-community.github.io/contribute/how-to-contribute.html

### 7.1 Zulip first

Post in `#mathlib4` **before** opening a PR. A draft:

> I have a sorry-free formalization of the simple fundamental
> inequality for a finite extension of valued fields
> \((L\mid K,\, w\mid v)\):
>
> \[
> [L:K] \ge e(w/v)\, f(w/v),
> \]
>
> including (to be added) finiteness of \(e\) and \(f\), following
> Kuhlmann, *Valued Fields*, Ch. 6 §6.3 (Lemmas 6.12–6.13).
>
> Proposed names, on top of `Valuation.HasExtension`:
> `Valuation.ramificationIndex`, `Valuation.residueDegree : ℕ`
> (infinite \(\mapsto 0\), plus `≠ 0` lemmas under
> `FiniteDimensional`), living in
> `Mathlib/RingTheory/Valuation/Ramification.lean`.
>
> This is the *single-extension* form only, not
> \(\sum_i e_i f_i \le n\), and not the Dedekind
> `Ideal.ramificationIdx` comparison.
>
> Does this match how people want \(e\) and \(f\) to sit next to
> `HasExtension` and the existing Dedekind names?
>
> I would be grateful for a reviewer from the valuation / local-fields
> side.

Natural reviewers to mention (do not ping aggressively): people around
`HasExtension` — Filippo A. E. Nuccio, María Inés de Frutos-Fernández,
Jiedong Jiang, Bichang Lei — and anyone active on valued fields.

Wait for design feedback. If names or the `ℕ` convention change, change
them *before* the big rewrite.

### 7.2 You own the conversation

The human author must:

- write Zulip and GitHub comments in their own words (LLM text on
  Zulip/GitHub is not allowed);
- understand and be able to justify every design choice without an AI;
- disclose AI use in the PR description if the Lean was substantially
  LLM-generated, and add the `LLM-generated` label via the comment
  `LLM-generated`.

Low-quality undisclosed LLM PRs are closed without comment.

### 7.3 Fork mathlib; do not PR this repo

```bash
# one-time
# 1. Fork https://github.com/leanprover-community/mathlib4
# 2. Add your GitHub username to your Zulip profile

git clone https://github.com/YOUR_USERNAME/mathlib4.git
cd mathlib4
lake exe cache get

# each contribution
git switch master
git pull upstream master    # after adding the official remote
git switch -c feat/valuation-ramification
```

Remotes:

```bash
git remote add upstream https://github.com/leanprover-community/mathlib4.git
git remote -v
# origin   = your fork
# upstream = leanprover-community/mathlib4
```

This sandbox (`linzialessandro/FundamentalInequality`) stays as a
development / notes repo. `TODO.md` lives here for reference. The
actual code that gets reviewed is the copy inside the mathlib checkout.

### 7.4 PR title and body

Follow https://leanprover-community.github.io/contribute/commit.html

Title (imperative, no capital, no final dot):

```
feat(RingTheory/Valuation): ramification index, residue degree and fundamental inequality
```

or, if split:

```
feat(RingTheory/Valuation): define ramification index and residue degree
feat(RingTheory/Valuation): valuation independence for field extensions
feat(RingTheory/Valuation): fundamental inequality for finite extensions
```

Body (adapt):

```
Define the ramification index `e(w/v)` and residue degree `f(w/v)` of
an extension of valued fields, and prove the simple fundamental
inequality

  e * f ≤ [L : K]

for a finite extension, including finiteness of `e` and `f`.

This is Kuhlmann, Valued Fields, Lemma 6.13 (Ch. 6 §6.3), also in
Bourbaki, Commutative Algebra, VI. It is the single-extension form;
the Ostrowski sum over all extensions of `v` to `L` is left to a
later PR. No comparison with `Ideal.ramificationIdx` is included yet.

`e` and `f` are `ℕ`, with the usual `finrank` / `relIndex` convention
that an infinite value is `0`. Separate lemmas show they are nonzero
under `FiniteDimensional`.

## Implementation notes

- Ramification is the `relIndex` of
  `valueGroup (vL.comap (algebraMap K L))` in `valueGroup vL`,
  so it is well-defined under `HasExtension` (equivalence, not
  equality of valuations).
- Residue degree is `finrank` of the residue fields of the two
  `valuationSubring`s.

AI use: <state tools and how they were used, or delete this line>.

---

- [ ] depends on: #XXXX   -- only if split
```

If Lean was substantially LLM-generated, comment `LLM-generated` on
the PR to apply the label.

### 7.5 After opening

- [ ] Confirm CI is green (or `awaiting-CI` until it is).
- [ ] Topic label `t-ring-theory` (bot usually sets this; fix if wrong).
- [ ] Post the PR link on the Zulip thread.
- [ ] Do **not** rebase after review starts; merge `master` if needed.
- [ ] Address review comments with new commits; resolve threads;
      remove `awaiting-author` when done.
- [ ] Do not add `easy` (new definitions, \(\gg 25\) lines).

---

## 8. Concrete rewrite tasks (in order)

Work in the mathlib fork after Zulip feedback. Use this list as the
implementation checklist.

### Phase 0 — discussion

- [ ] Write and post the Zulip message in §7.1.
- [ ] Record the agreed names, `ℕ` convention, and file path in this
      file (update §5).
- [ ] Decide PR split (A/B/C vs one PR).

### Phase 1 — skeleton in mathlib

- [ ] Branch `feat/valuation-ramification` on up-to-date `master`.
- [ ] Create the agreed file(s) with header, `module`, public imports,
      module docstring.
- [ ] `lake exe mk_all`.
- [ ] Empty compile: `lake build` the new module.

### Phase 2 — definitions + elementary API

- [x] `residueDegree` with docstring \(f(w/v) = [Lw:Kv]\).
- [x] `ramificationIndex` with docstring \(e(w/v) = (wL:vK)\),
      implemented via comap value group + `relIndex`.
- [x] `residueDegree_self`, `ramificationIndex_self`.
- [x] Tower lemmas (`residueDegree_mul`, `ramificationIndex_mul`,
      and `ramificationIndex_mul_hasExtension`).
      The two-valuation form of `e(w/v) = e(w/u) e(u/v)` still
      identifies `e(u/v)` with the comap index in \(\Gamma_L\), not
      yet via `IsEquiv.orderMonoidIso`.
- [x] `ramificationIndex_ne_zero`, `residueDegree_pos`
      (and `finite_valueGroup_quotient`,
      `finite_residueField_extension`).

### Phase 3 — independence (6.12)

- [x] Lemma: a finite sum of nonzero terms with pairwise distinct
      valuations cannot be zero (`exists_eq_val_of_sum_eq_zero`,
      using `Valuation.map_sum_eq_of_lt`).
- [x] Lemma: distinct value-coset representatives are linearly
      independent over \(K\).
- [x] Theorem: valuation independence in the residue form of 6.12
      (`exists_max_val_mul`; linear independence is the corollary
      `valuation_independence`).
- [x] Delete unused no-cancellation public API
      (`linearIndependent_of_val_no_cancel` is gone; the helper is
      private).

### Phase 4 — inequality (6.13)

- [x] Construct the \(u_j\) (lifts of a residue basis, valuation 1).
- [x] Construct the \(z_i\) (coset representatives).
- [x] Apply independence.
- [x] Compare cardinalities: `Fintype.card (Fin e × Fin f) = e * f`.
- [x] No vacuous `e = 0` / `f = 0` escape; finiteness already known
      or proved here.

### Phase 5 — style pass

- [ ] 100-column wrap.
- [ ] No blank lines inside declarations.
- [ ] `#lint`, `docBlame`, `docBlameThm`.
- [ ] Factor any remaining 50+ line proof blocks.
- [ ] Unused imports / variables gone.
- [ ] BibTeX key added to `docs/references.bib` if a new citation
      is needed (`bibtool` as in the doc guide).

### Phase 6 — open PR

- [ ] Self-review the diff as if you were a mathlib reviewer.
- [ ] Title/body as in §7.4.
- [ ] AI disclosure if applicable.
- [ ] Link Zulip thread in the PR or in a first comment.
- [ ] Watch CI; download cache after it passes.

---

## 9. Mathematical notes for the rewrite

### Why comap value groups

`HasExtension` only gives `vK.IsEquiv (vL.comap (algebraMap K L))`.
Equivalent valuations have isomorphic value groups and the same
valuation ring, but not definitionally the same `Γ`. The index

\[
e = \bigl[v_L(L^\times) : v_L(K^\times)\bigr]
\]

is computed entirely inside \(\Gamma_L^\times\):

```lean
valueGroup (vL.comap (algebraMap K L))   -- = vL(Kˣ) ≤ ΓLˣ
  |>.relIndex
    (valueGroup vL)                      -- = vL(Lˣ) ≤ ΓLˣ
```

`Subgroup.relIndex H K` is \([K : H \cap K]\). Here \(H \subseteq K\),
so this is \([vL(L^\times):vL(K^\times)]\). Keep this; do not switch to
`valueGroup vK`.

### Why residue fields of valuation subrings

`HasExtension` already provides

- `Algebra vK.valuationSubring vL.valuationSubring`,
- `IsLocalHom` of that map,
- `LiesOver` of maximal ideals,
- compatibility of residue maps.

So `Module.finrank Kv Lv` is the correct \(f\). Do not build a custom
residue-field type.

### Residue argument (do not “fix” this)

In the construction of `hu_no_cancel`, one maximises \(v_K(d_j)\) at
some \(j_0\), scales by \(d_{j_0}^{-1}\), and looks at residues. Other
coefficients with the *same* valuation may also have nonzero residue.
That is fine: the residue linear combination has \(j_0\)-coordinate
`1`, so linear independence of the residue basis implies the
combination is nonzero. The sum in the valuation ring is therefore a
unit and has valuation `1`. Keep this; do not try to force a unique
maximum.

### Independence vs valuation-independence

Kuhlmann proves *valuation* independence (the valuation of a linear
combination equals the min of the terms, in additive notation). Linear
independence is the corollary used for \(n \ge ef\). For the first PR,
linear independence is enough. If the valuation-independence form is
easy from the same proof, include it: it is the statement of 6.12 and
will be wanted for 6.17 later.

### `relIndex` and `0`

`relIndex` is `0` when the index is infinite. That is why
`ramificationIndex_ne_zero` is a real theorem, not `rfl`.

---

## 10. Current repo map

```
FundamentalInequality/                 -- this sandbox
  FundamentalInequality.lean           -- the formalization (601 lines)
  lakefile.toml                        -- pins mathlib v4.30.0
  lean-toolchain                       -- leanprover/lean4:v4.30.0
  lake-manifest.json
  README.md                            -- update citation when convenient
  LICENSE                              -- Apache 2.0 (good)
  TODO.md                              -- this file
```

Mathlib PRs must target **current master**, not `v4.30.0`. The pin is
only for local sandbox builds.

Declarations after the 2026-08-14 local rewrite:

| Name | Role | Action |
|---|---|---|
| `Valuation.residueDegree` | \(f\) | documented; identity / tower / pos |
| `Valuation.ramificationIndex` | \(e\) | documented; identity / tower / ne_zero |
| `exists_eq_val_of_sum_eq_zero` | helper | kept as lemma |
| `linearIndependent_of_val_distinct_coset` | 6.12, \(J=1\) | used for finiteness of \(e\) |
| `exists_max_val_mul` | 6.12, valuation independence | public theorem |
| `valuation_independence` | 6.12, linear independence | corollary |
| `fundamental_inequality` | 6.13 + finiteness | no vacuous `0`-escape |
| `fundamentalInequality` | alias | kept for the old name |

---

## 11. What “done” looks like

A PR is ready to open when all of the following hold.

- [ ] Zulip thread exists and the agreed design is the one in the PR.
- [ ] Code lives on a branch of a **mathlib4 fork**, not this repo.
- [x] `e` and `f` are defined, documented, and have identity / tower /
      finiteness lemmas. (local sandbox; not yet on a mathlib fork)
- [x] Independence is Lemma 6.12 (residues; valuation form
      `exists_max_val_mul`, plus linear-independence corollary).
- [x] `fundamental_inequality` is 6.13, including finiteness of \(e,f\).
- [ ] No `sorry`, no unused public lemmas, `#lint` clean.
      (`sorry`-free by construction; `#lint` not run.)
- [ ] Style matches `Extension.lean`.
- [ ] PR title/body follow commit conventions; AI disclosed if needed.
- [ ] Author can explain every definition and proof step on Zulip
      without an AI.

Until that list is checked, keep iterating here or on the fork. Do not
open the PR early to “get in the queue”: unready new-definition PRs
cost reviewers time and can be closed.

---

## 12. Later work (not this contribution)

Track these so they are not accidentally stuffed into PR 1.

- [ ] Ostrowski: \(\sum_i e(w_i/v)\, f(w_i/v) \le [L:K]\) over all
      extensions of \(v\) to \(L\). Needs existence / listing of
      extensions.
- [ ] Defect \(d = n / (ef)\) and Ostrowski with defect.
- [ ] Vs-defectless / valuation basis / \(n = ef\) (Kuhlmann 6.17).
- [ ] `Ideal.ramificationIdx` / `inertiaDeg` comparison for the
      valuation attached to a prime of a Dedekind domain.
- [ ] Finitely ramified and formally \(\mathfrak{p}\)-adic classes,
      and Lemma 6.14.
- [ ] Immediate extensions in the sense of Kuhlmann 6.1, related to
      \(e = f = 1\).

---

## 13. Links

- Sandbox repo: https://github.com/linzialessandro/FundamentalInequality
- mathlib4: https://github.com/leanprover-community/mathlib4
- Contribute: https://leanprover-community.github.io/contribute/index.html
- How to contribute: https://leanprover-community.github.io/contribute/how-to-contribute.html
- Style: https://leanprover-community.github.io/contribute/style.html
- Naming: https://leanprover-community.github.io/contribute/naming.html
- Docs: https://leanprover-community.github.io/contribute/doc.html
- PR titles: https://leanprover-community.github.io/contribute/commit.html
- Git guide: https://leanprover-community.github.io/contribute/git.html
- Zulip `#mathlib4`: https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4
- `HasExtension` docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Valuation/Extension.html
- Book PDFs (local): `../../Valued Fields/bookch6.pdf` (start p. 143, §6.3)
