# Formalization of the Fundamental Inequality of Valued Fields

This repository contains the formalization of the **Fundamental Inequality** for finite extensions of valued fields in Lean 4. The project is designed and structured as a direct contribution to `mathlib4`.

## Mathematical Background

In valuation theory, consider a finite extension $L|K$ of valued fields with valuation $v$. The degree of the extension $n = [L:K]$ can be related to two vital structural invariants:

1. **Ramification Index**, $e = e(L|K; v) := (vL : vK)$: The index of the value group of $K$ inside the value group of $L$.
2. **Inertia Degree**, $f = f(L|K; v) := [L\bar{v} : K\bar{v}]$: The degree of the extension of the residue field of $L$ over the residue field of $K$.

Which are both finite in this case. The **Fundamental Inequality** states that:
$$ [L:K] \ge (vL:vK) [L\bar{v}:K\bar{v}] $$

Or, expressed in a form which is easy to remember:
$$ n \ge e f $$

This fundamental inequality is of great importance in valuation theory. As an application of the fundamental inequality, it provides the structural constraint necessary to show that important classes of valued fields (such as finitely ramified fields and formally $\mathfrak{p}$-adic fields) are closed under finite extensions.

This project formally defines these invariants and establishes this inequality for arbitrary finite extensions of valued fields in Lean 4.

## Project Structure

The formalization is entirely contained within `FundamentalInequality.lean`. The file structure is explicitly flat to align with standard Mathlib architectural guidelines for component contributions.

### Main Definitions and Theorems
- `Valuation.ramificationIndex vK vL`: The ramification index $e$.
- `Valuation.residueDegree vK vL`: The residue degree $f$.
- `Valuation.fundamentalInequality`: The main theorem stating `e * f ≤ Module.finrank K L`.

To achieve this, the repository introduces auxiliary lemmas establishing the valuation independence of field elements, such as `Valuation.linearIndependent_of_val_distinct_coset` and `Valuation.valuation_independence`.

## Compilation and Usage

The repository uses `lake`, the Lean 4 package manager.

### Prerequisites
- Install [elan](https://github.com/leanprover/elan), the Lean version manager.
- A compatible version of Lean 4 (automatically handled by `elan` based on the `lean-toolchain` file).

### Building the Project

**Important**: This project depends on `mathlib`, which is extremely large. Compiling it from scratch locally can take over an hour and may appear to hang your system.

To avoid compiling `mathlib` yourself, you should **always** download the precompiled cache before building the project for the first time:

```bash
lake exe cache get
```

Once the cache is downloaded and unpacked, you can compile the project and verify the proofs by running:
```bash
lake build
```
This will quickly compile the `FundamentalInequality` module and run the Lean compiler to check the integrity of all proofs. There are no `sorry` blocks in the codebase; the build compiles seamlessly and silently.

## License

This project is licensed under the Apache 2.0 License. See the [LICENSE](LICENSE) file for more information.
