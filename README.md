# Lean-SysID

Lean 4 code accompanying the paper

> **From Pen-and-Paper to Machine-Checked Proofs: Lean for System Identification**
> Manas Mejari, Dario Piga, Marco Forgione
> IDSIA Dalle Molle Institute for Artificial Intelligence, USI-SUPSI, Lugano, Switzerland

The paper introduces the [Lean 4](https://lean-lang.org/) proof assistant and its mathematical
library [Mathlib](https://github.com/leanprover-community/mathlib4) to a system identification
and control audience. It assumes no prior exposure to formal methods. This repository contains
every Lean proof discussed in the paper.

## Contents

All files are in [`Lean codes/`](Lean%20codes).

| File | Content |
|------|---------|
| [`Tutorial.lean`](Lean%20codes/Tutorial.lean) | Warm-up examples: a one-line `linarith` proof, the same fact proved step by step, invariance of the interval `{x : abs x ≤ r}` for `x⁺ = a x` with `abs a ≤ 1`, and invariance along the whole trajectory by induction. |
| [`Identification.lean`](Lean%20codes/Identification.lean) | Lemma 2 of the paper: for `y = φ θ`, the parameter `θ` is identifiable from one data point iff `φ₁ ≠ 0` (persistent excitation), and then the estimator `y₁ / φ₁` is exact. |
| [`Lemma_3_1_Ljung.lean`](Lean%20codes/Lemma_3_1_Ljung.lean) | Ljung (1999), Lemma 3.1: inverting the noise filter, `H⁻¹(q) v(t) = e(t)`. The formalization makes explicit that, for white noise with finite variance, the claim holds *almost surely* (`lemma_3_1`), and adds the missing steps of the proof (Cauchy product identity (3.10), absolute convergence of the double series, interchange of summation). |
| [`Template.lean`](Lean%20codes/Template.lean) | A template and building blocks for system identification in Lean, in Ljung's notation: signals, model structures, identifiability, the ARX structure and a proof that it is globally identifiable, the PEM criterion `V_N`, persistent excitation, and state-space simulation. |


Each file begins with a header comment that states the results, the notation and the
formalization choices. The `-- ANCHOR:` comments mark the code excerpts reproduced in the paper.

Lean tactics and notation used in the paper are given in the table. 

## Building the code

The files require Lean 4 and Mathlib, and were tested with Lean v4.35.0 and the matching Mathlib release. `Tutorial.lean`, `Identification.lean`, `Template.lean`,
`Lemma_3_1_Ljung.lean` import only `Mathlib` and compile on their own.


1. Install Lean through [elan](https://lean-lang.org/install/) (or the VS Code Lean 4 extension).
2. Create a Lean project that depends on Mathlib and fetch the precompiled Mathlib cache:

   ```bash
   lake new LeanSysID math
   ```

   ```bash
   cd LeanSysID && lake exe cache get
   ```

3. Copy the `.lean` files into the project and open them in VS Code, or check a single file with

   ```bash
   lake env lean LeanSysID/Tutorial.lean
   ```


## References

- L. Ljung. *System Identification: Theory for the User*, 2nd ed. Prentice Hall, 1999.



