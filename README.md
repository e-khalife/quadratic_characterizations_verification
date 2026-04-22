# Formal Verification of Quadratic Characterizations for Saturation Functions

This repository contains an automated pipeline that connects numerical convex optimization (Sum-of-Squares) with formal verification. It proves that a set of generated quadratic polynomials safely over-approximates a piecewise continuous saturation function over specific regions of interest (ROI). 

The proofs are built using interactive theorem proving (**Coq/Rocq**) and automated SMT-based deductive verification (**Frama-C / ACSL**).

## Methodology Overview

1. **Polynomial Synthesis (MATLAB):** Quadratic constraints are generated, to characterize the unit saturation function, using the data-driven method provided in the paper. They are then verified using Sum-of-Squares (SOS) feasibility problems. 
2. **Foundational Proof (Rocq):** To avoid the internal limits of Cylindrical Algebraic Decomposition (CAD) in non-linear real arithmetic (`nra`), the pipeline uses exact unscaled rational fractions. It avoids complex non-linear searches by providing explicit algebraic discriminant identities, reducing the proof to linear real arithmetic (`lra`).
3. **Deductive Verification (Frama-C):** The ROI is divided into separate subsets (left saturation, linear region, right saturation) using ACSL axioms. SMT solvers prove the over-approximation lemmas across the continuous real domain.

## Usage & Verification

To ensure reproducibility without setting up complex local environments, you can run the verification using standard Docker containers.

### 1. Frama-C / ACSL Verification
Using the `frama-c/frama-c` Docker image, execute the following command to verify the constraints using Z3 and Alt-Ergo:

```bash
frama-c -wp -wp-model real -wp-cache none -wp-timeout 30 -wp-prover z3,alt-ergo saturation_quad_char.c
```

**Verification Results:**
All 21 scheduled goals are successfully proven by the SMT solvers in under a second.
```text
[kernel] Parsing saturation_quad_char.c (with preprocessing)
[wp] Warning: Missing RTE guards
[wp] 21 goals scheduled
[wp] Proved goals:   21 / 21
  Qed:             0
  Alt-Ergo :      12 (5ms-16ms-88ms)
  Z3 4.13.3:       9 (10ms-33ms-130ms)
[wp:pedantic-assigns] saturation_quad_char.c:250: Warning: 
  No 'assigns' specification for function 'main'.
  Callers assumptions might be imprecise.
```
*(Note: The RTE and assigns warnings are expected because Frama-C is analyzing a purely logical C file without memory assignments).*

### 2. Rocq Foundational Proof
Using the `coqorg/coq` Docker image, compile the interactive proof script:

```bash
coqc saturation_quad_char.v
```

**Verification Results:**
The command runs without output, meaning the Rocq kernel has formally checked every logical step without errors. The repository includes the resulting compiled files (`.vo`, `.vos`, `.vok`).

---

## Alternative Method for Rocq/Frama-C: Adaptive Hybrid SOS Decomposition

For highly non-linear, higher-degree, or highly complex functions where standard SMT/CAD solvers fail because the coefficients become too large, we describe an alternative **Adaptive Deflated Gram Matrix Decomposition** method.

### How it works:
1. **Reduction & Cholesky Decomposition:** Instead of sending raw polynomials to the solver, the Gram matrix $Q$ is calculated for the SOS polynomials and reduced by an $\epsilon$-margin to account for floating-point errors. It then extracts the explicit squared binomial multipliers using eigenvalue/Cholesky decomposition ($Q = V \sqrt{D}$).
2. **Proof by Abstraction (Rocq):** A Rocq proof is automatically generated. Instead of searching for Positivstellensatz certificates, Rocq simply verifies the linear addition of explicitly defined squared terms ($M_i(x)^2 \ge 0$), removing the need for complex non-linear solving.
3. **Residual Verification (Frama-C):** A hybrid Frama-C file imports the Rocq-certified SOS abstraction as an axiom. Frama-C is then only used to prove that the difference between the original floating-point polynomial (minus the $\epsilon$-margin) and the Rocq-certified sum-of-squares expansion is within a small error tolerance.

This method assigns the heavy algebraic factoring to the SOS solver, the positivity proof to Rocq, and the final floating-point error checking to Frama-C. This allows formal verification to scale to more complex functions.