# Formal Verification of Quadratic Characterizations for tanh and Saturation

This repository contains the verification files and the benchmark networks of the paper

> E. Khalife, M. Farhood, and P.-L. Garoche, "Quadratic Characterizations for Reachability Analysis of Neural Networks," 2026. arXiv:2605.20482.

It proves that two families of quadratic constraints safely over-approximate the graph of the hyperbolic tangent on [−20, 20] and the graph of the unit saturation function on [−5, 5]. Each constraint has the form q(x, y) = a x² + b y² + c xy + d x + e y + f ≥ 0, with x the input and y the output of the activation function.

## Repository layout

- `frama-c/saturation_quad_char.c` — Frama-C lemmas for the five saturation constraints.
- `frama-c/tanh_quad_char.c` — Frama-C lemmas for the eight data-driven tanh constraints.
- `rocq/saturation_quad_char.v` — Rocq proof of the saturation constraints.
- `networks.zip` — the tanh benchmark networks, attached to release 1.0 (see the last section).

## Methodology Overview

1. **Generation (MATLAB):** The constraints are generated with the data-driven method of the paper on subregions of one half of the domain, and the other half is obtained by symmetry. For the saturation function, the subregions are [−5, −1.2] and [−1.5, −0.5]; together with 1 − y² ≥ 0, the family has five constraints. For tanh, the subregions are [−4, −1.5], [−2, 0], [−2, −0.7] and [−1.2, −0.5]; together with 1 − y² ≥ 0, the family has nine constraints. The saturation coefficients are rounded to six decimals and the tanh coefficients to 17 significant digits; these rounded constraints are the ones verified and used in the paper.

2. **SOS Verification (MATLAB):** The saturation graph consists of three pieces (y = −1, y = x, y = 1), and each constraint is certified on each piece for x in [−100, 100]. For tanh, the graph is enclosed in narrow bands: a constant band for |x| ≥ 6 and, on eight subintervals of [−6, 6], a band around a degree-7 polynomial approximation. All 80 certificates (8 constraints × 10 bands) succeed.

3. **Rocq Proof (saturation):** The proof uses exact fractions. For each constraint and each piece of the graph, it gives an explicit algebraic identity, so that Rocq only has to check linear inequalities. The proof contains no admitted steps.

4. **Frama-C Verification:** The saturation lemmas state the five constraints on the three pieces of the graph, with no bound on x. For tanh, [−6, 6] is split into 11 to 15 pieces per constraint, and on each piece tanh lies in a narrow band around a straight line, computed with 50-digit arithmetic and rounded outward; the tails |x| ≥ 6 use the constant band of step 2. Each lemma is therefore a simple quadratic inequality, which Z3 and Alt-Ergo prove with their default settings. Each tanh lemma proves q ≥ τ, where the margin τ ≤ 2·10⁻¹⁴ covers the rounding of the coefficients to double precision, and is declared with `check lemma`, so that it is proved independently of the others.

## Usage & Verification

The checks require Frama-C with its WP plug-in, Z3 and Alt-Ergo, and Rocq. The outputs below were obtained with Z3 4.8.12 and Alt-Ergo 2.5.4.

### 1. Frama-C Verification

**Saturation:**

```bash
frama-c -wp -wp-cache none -wp-model real -wp-timeout 60 -wp-prover z3,alt-ergo frama-c/saturation_quad_char.c
```

All goals are proven: the 21 lemmas and two automatic checks on the empty `main` function.

```text
[kernel] Parsing saturation_quad_char.c (with preprocessing)
[wp] Warning: Missing RTE guards
[wp] 21 goals scheduled
[wp] Proved goals:   23 / 23
  Terminating:       1
  Unreachable:       1
  Qed:               0
  Alt-Ergo 2.5.4:   12 (8ms-13ms-50ms)
  Z3 4.8.12:         9 (11ms-62ms-298ms)
[wp:pedantic-assigns] saturation_quad_char.c:250: Warning:
  No 'assigns' specification for function 'main'.
  Callers assumptions might be imprecise.
```

*(The two warnings are expected: the file contains only definitions and lemmas.)*

**tanh:**

```bash
frama-c -wp -wp-cache none -wp-model real -wp-timeout 60 -wp-prover z3,alt-ergo frama-c/tanh_quad_char.c
```

All 114 goals are proven.

```text
[kernel] Parsing tanh_quad_char.c (with preprocessing)
[wp] 114 goals scheduled
[wp] Proved goals:  114 / 114
  Qed:               0 (0.50ms-0.11ms-1ms)
  Alt-Ergo 2.5.4:   35 (7ms-10ms-31ms)
  Z3 4.8.12:        79 (10ms-14ms-28ms)
```

### 2. Rocq Proof

```bash
coqc rocq/saturation_quad_char.v
```

The command runs without output, meaning that Rocq has checked every step of the proof.

## Alternative Method for Rocq/Frama-C: Hybrid SOS Decomposition

For more complex functions, where the solvers fail because the polynomials and their coefficients become too large, the work can be split between the three tools:

1. **Decomposition (MATLAB):** The sum-of-squares certificate is computed, shrunk by a small margin to absorb floating-point errors, and written explicitly as a sum of squared terms.
2. **Proof by Abstraction (Rocq):** A Rocq proof is generated automatically; Rocq only checks that the sum of the given squared terms is nonnegative.
3. **Residual Check (Frama-C):** Frama-C takes the Rocq result as an axiom and only proves that the original polynomial (minus the margin) is close enough to the certified sum of squares.

## Benchmark Networks

The networks of the tanh benchmark (Section VI of the paper) are provided in [`networks.zip`](https://github.com/e-khalife/quadratic_characterizations_verification/releases/download/1.0/networks.zip) (137 MB), attached to release 1.0 of this repository. The archive contains 27 folders `In_{nx}_L_{L}_N_{N}`, one per configuration, with input dimension nx in {10, 20, 40}, L in {2, 4, 6} hidden layers and width N in {16, 32, 64}. Each folder holds 100 files `model_{k}.mat` with the weights `W{l}` and biases `b{l}`, l = 1, …, L+1, of a network with random weights, tanh activations and two outputs. The input set is ‖x‖∞ ≤ 1, and the preactivation bounds of every network lie within [−20, 20], the domain on which the tanh characterization is verified. The ACAS Xu networks are the standard release of Katz et al. (CAV 2017) and are not included.
