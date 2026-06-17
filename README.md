# Formalization of the Fundamental Inequality of Valued Fields

This repository contains the formalization of the **Fundamental Inequality** for finite extensions of valued fields in Lean 4. The project is designed and structured as a direct contribution to `mathlib4`.

## Mathematical Background

In valuation theory, if $K$ is a field equipped with a valuation $v$ (taking values in a linearly ordered commutative group with zero $\Gamma_K$), and $L$ is a finite extension of $K$ with extended valuation $w$, we can relate the degree of the extension to two important invariants:

1. **Ramification Index**, $e(w/v)$: The index of the value group $v(K^\times)$ inside $w(L^\times)$.
2. **Residue Degree**, $f(w/v)$: The degree of the extension of the residue field of $L$ over the residue field of $K$.

The **Fundamental Inequality** states that:
$$ e(w/v) \cdot f(w/v) \le [L : K] $$

This project formally defines these invariants and establishes this inequality for arbitrary finite extensions of valued fields.

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
To compile the project and verify the proofs, run the following from the root directory:
```bash
lake build
```
This will compile the `FundamentalInequality` module and run the Lean compiler to check the integrity of all proofs. There are no `sorry` blocks in the codebase; the build compiles seamlessly and silently.

## License

This project is licensed under the Apache 2.0 License. See the [LICENSE](LICENSE) file for more information.
