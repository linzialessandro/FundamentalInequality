# Formalization of the Fundamental Inequality of Valued Fields

Author: **Alessandro Linzi**

This repository is a local sandbox for a `mathlib4` contribution. It formalizes
the **simple fundamental inequality** for a finite extension of valued fields
in Lean 4, following Kuhlmann, *Valued Fields*, Chapter 6, §6.3
(Lemmas 6.12–6.13 and 6.16).

It is not a pull request against mathlib. The intended destination, after a
Zulip design discussion, is a branch of a **fork of mathlib** (see `TODO.md`).

## Mathematical background

Let \((L\mid K,\, w\mid v)\) be an extension of valued fields, with \(L\mid K\)
finite. Write

- \(n = [L:K]\),
- \(e = e(w/v) = (wL : vK)\), the ramification index,
- \(f = f(w/v) = [Lw : Kv]\), the inertia / residue degree.

Then \(e\) and \(f\) are finite, and

\[
n \ge e\, f.
\]

This is the *single-extension* form. The Ostrowski sum \(\sum_i e_i f_i \le n\)
over all extensions of \(v\) to \(L\), the vs-defectless characterisation
\(n = ef\), and the comparison with Dedekind `Ideal.ramificationIdx` /
`Ideal.inertiaDeg` are left to later work.

The argument is the standard one of Kuhlmann, Lemmas 6.12–6.13:

1. Prove finiteness of \(e\) and \(f\) from valuation independence: an infinite
   independent family would produce arbitrarily large \(K\)-linearly independent
   sets, contradicting \([L:K] < \infty\).
2. Lift a residue basis of \(Lw/Kv\) to units \(u_j \in L\) of valuation \(1\).
3. Take representatives \(z_i \in L^\times\) of the cosets of \(vL(K^\times)\)
   in \(vL(L^\times)\).
4. The products \(z_i u_j\) are \(K\)-linearly independent (Lemma 6.12).
5. Hence \(ef = \#(I \times J) \le [L:K]\).

## Main declarations

All live in `FundamentalInequality.lean`, in the `Valuation` namespace.

| Name | Role |
| --- | --- |
| `residueDegree` | \(f(w/v) = [Lw : Kv]\) (`ℕ`, infinite \(\mapsto 0\)) |
| `ramificationIndex` | \(e(w/v) = (wL : vK)\) via `comap` + `relIndex` |
| `residueDegree_self`, `ramificationIndex_self` | identity extension: \(e = f = 1\) |
| `residueDegree_mul`, `ramificationIndex_mul` | tower multiplicativity (Lemma 6.16) |
| `residueDegree_pos`, `ramificationIndex_ne_zero` | finiteness under `FiniteDimensional` |
| `valuation_independence` | Lemma 6.12 (residue form) |
| `fundamental_inequality` | Lemma 6.13, including finiteness of \(e,f\) |

`e` is computed from `valueGroup (vL.comap (algebraMap K L))` inside
\(\Gamma_L^\times\), so it is well-defined under `HasExtension` (equivalence of
valuations, not equality). Residue degree is `finrank` of the residue fields of
the two `valuationSubring`s.

## References

- F.-V. Kuhlmann, *Valued Fields*, Chapter 6, §6.3, Lemmas 6.12–6.13 and 6.16.
  Local copy: `Book/bookch6.pdf` (start p. 143).
- N. Bourbaki, *Algèbre commutative*, Chapter VI.

The older citation of Chapter 4, §4.4 was incorrect: that chapter never states
\(n \ge ef\).

## Building

The repository uses `lake`. It pins mathlib `v4.30.0` for local sandbox builds
only; a mathlib PR must target current `master`.

**Always** download the precompiled cache before the first build. Compiling
mathlib from scratch can take over an hour:

```bash
lake exe cache get
lake build
```

There are no `sorry`s. After `lake exe cache get`, `lake build` should only
need to compile this module.

## License

Apache 2.0. See [LICENSE](LICENSE).
