(*
 * FORMAL VERIFICATION: QUADRATIC CHARACTERIZATION of the UNIT SATURATION FUNCTION
 * Constraints: 5 quadratic inequalities
 *
 * Compile and verify: coqc saturation_quad_char.v
 *)


Require Import Reals.
Require Import Psatz.
Open Scope R_scope.

(* --- 1. Region of Interest (ROI) Definitions --- *)
(* Mathematical definitions of the saturation function bounds *)

Definition in_subset_1 (x y : R) : Prop :=
  y = -1 /\ x >= -100 /\ x <= -1.

Definition in_subset_2 (x y : R) : Prop :=
  y = x /\ x >= -1 /\ x <= 1.

Definition in_subset_3 (x y : R) : Prop :=
  y = 1 /\ x >= 1 /\ x <= 100.

(* The full ROI is the union of the three sub-domains *)
Definition in_ROI (x y : R) : Prop :=
  in_subset_1 x y \/ in_subset_2 x y \/ in_subset_3 x y.

(* --- 2. Polynomial Evaluations --- *)

Definition eval_Q1 (x y : R) : R :=
  0 * (x * x) + (-1) * (y * y) + 0 * (x * y) +
  0 * x + 0 * y + 1.

Definition eval_Q2 (x y : R) : R :=
  (133 / 500000) * (x * x) + (-67761 / 200000) * (y * y) + (30773 / 40000) * (x * y) +
  (19277 / 25000) * x + (5053 / 125000) * y + (383129 / 1000000).

Definition eval_Q3 (x y : R) : R :=
  (219081 / 500000) * (x * x) + (-935989 / 1000000) * (y * y) + (134607 / 250000) * (x * y) +
  (1441947 / 1000000) * x + (-1368953 / 1000000) * y + (33807 / 1000000).

Definition eval_Q4 (x y : R) : R :=
  (133 / 500000) * (x * x) + (-67761 / 200000) * (y * y) + (30773 / 40000) * (x * y) +
  (-19277 / 25000) * x + (-5053 / 125000) * y + (383129 / 1000000).

Definition eval_Q5 (x y : R) : R :=
  (219081 / 500000) * (x * x) + (-935989 / 1000000) * (y * y) + (134607 / 250000) * (x * y) +
  (-1441947 / 1000000) * x + (1368953 / 1000000) * y + (33807 / 1000000).

(* --- 3. Individual Lemmas --- *)

Lemma Q1_on_subset_1 : forall x y : R,
  in_subset_1 x y -> eval_Q1 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_1, eval_Q1 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  remember (x * x) as x2.
  nra.
Qed.

Lemma Q1_on_subset_2 : forall x y : R,
  in_subset_2 x y -> eval_Q1 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_2, eval_Q1 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Provide algebraic factorization hint *)
  assert (H_pos: (-1) * (x * x) + 0 * x + 1 >= 0).
  {
    assert (H_id: (-1) * (x * x) + 0 * x + 1 = 1 * (1 - x) * (1 + x)) by nra.
    rewrite H_id.
    nra.
  }
  remember (x * x) as x2.
  lra.
Qed.

Lemma Q1_on_subset_3 : forall x y : R,
  in_subset_3 x y -> eval_Q1 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_3, eval_Q1 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  remember (x * x) as x2.
  nra.
Qed.

Lemma Q2_on_subset_1 : forall x y : R,
  in_subset_1 x y -> eval_Q2 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_1, eval_Q2 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Explicitly abstract the fractional nonlinear terms to bypass CAD limits *)
  assert (H_pos: (133 / 500000) * (x * x) + (351 / 200000) * x + (39 / 10000) >= 0).
  {
    assert (H_id: (133 / 125000) * ((133 / 500000) * (x * x) + (351 / 200000) * x + (39 / 10000)) = ((133 / 250000) * x + (351 / 200000)) * ((133 / 250000) * x + (351 / 200000)) + (42783 / 40000000000)) by nra.
    assert (H_sq: ((133 / 250000) * x + (351 / 200000)) * ((133 / 250000) * x + (351 / 200000)) >= 0). { remember ((133 / 250000) * x + (351 / 200000)) as Z; nra. }
    remember ((133 / 500000) * (x * x) + (351 / 200000) * x + (39 / 10000)) as P.
    remember (((133 / 250000) * x + (351 / 200000)) * ((133 / 250000) * x + (351 / 200000))) as S2.
    lra.
  }
  remember (x * x) as x2.
  lra.
Qed.

Lemma Q2_on_subset_2 : forall x y : R,
  in_subset_2 x y -> eval_Q2 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_2, eval_Q2 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Explicitly abstract the fractional nonlinear terms to bypass CAD limits *)
  assert (H_pos: (215393 / 500000) * (x * x) + (50719 / 62500) * x + (383129 / 1000000) >= 0).
  {
    assert (H_id: (215393 / 125000) * ((215393 / 500000) * (x * x) + (50719 / 62500) * x + (383129 / 1000000)) = ((215393 / 250000) * x + (50719 / 62500)) * ((215393 / 250000) * x + (50719 / 62500)) + (41192389 / 25000000000)) by nra.
    assert (H_sq: ((215393 / 250000) * x + (50719 / 62500)) * ((215393 / 250000) * x + (50719 / 62500)) >= 0). { remember ((215393 / 250000) * x + (50719 / 62500)) as Z; nra. }
    remember ((215393 / 500000) * (x * x) + (50719 / 62500) * x + (383129 / 1000000)) as P.
    remember (((215393 / 250000) * x + (50719 / 62500)) * ((215393 / 250000) * x + (50719 / 62500))) as S2.
    lra.
  }
  remember (x * x) as x2.
  lra.
Qed.

Lemma Q2_on_subset_3 : forall x y : R,
  in_subset_3 x y -> eval_Q2 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_3, eval_Q2 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  remember (x * x) as x2.
  nra.
Qed.

Lemma Q3_on_subset_1 : forall x y : R,
  in_subset_1 x y -> eval_Q3 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_1, eval_Q3 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Explicitly abstract the fractional nonlinear terms to bypass CAD limits *)
  assert (H_pos: (219081 / 500000) * (x * x) + (903519 / 1000000) * x + (466771 / 1000000) >= 0).
  {
    assert (H_id: (219081 / 125000) * ((219081 / 500000) * (x * x) + (903519 / 1000000) * x + (466771 / 1000000)) = ((219081 / 250000) * x + (903519 / 1000000)) * ((219081 / 250000) * x + (903519 / 1000000)) + (1738676247 / 1000000000000)) by nra.
    assert (H_sq: ((219081 / 250000) * x + (903519 / 1000000)) * ((219081 / 250000) * x + (903519 / 1000000)) >= 0). { remember ((219081 / 250000) * x + (903519 / 1000000)) as Z; nra. }
    remember ((219081 / 500000) * (x * x) + (903519 / 1000000) * x + (466771 / 1000000)) as P.
    remember (((219081 / 250000) * x + (903519 / 1000000)) * ((219081 / 250000) * x + (903519 / 1000000))) as S2.
    lra.
  }
  remember (x * x) as x2.
  lra.
Qed.

Lemma Q3_on_subset_2 : forall x y : R,
  in_subset_2 x y -> eval_Q3 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_2, eval_Q3 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Explicitly abstract the fractional nonlinear terms to bypass CAD limits *)
  assert (H_pos: (40601 / 1000000) * (x * x) + (36497 / 500000) * x + (33807 / 1000000) >= 0).
  {
    assert (H_id: (40601 / 250000) * ((40601 / 1000000) * (x * x) + (36497 / 500000) * x + (33807 / 1000000)) = ((40601 / 500000) * x + (36497 / 500000)) * ((40601 / 500000) * x + (36497 / 500000)) + (20283499 / 125000000000)) by nra.
    assert (H_sq: ((40601 / 500000) * x + (36497 / 500000)) * ((40601 / 500000) * x + (36497 / 500000)) >= 0). { remember ((40601 / 500000) * x + (36497 / 500000)) as Z; nra. }
    remember ((40601 / 1000000) * (x * x) + (36497 / 500000) * x + (33807 / 1000000)) as P.
    remember (((40601 / 500000) * x + (36497 / 500000)) * ((40601 / 500000) * x + (36497 / 500000))) as S2.
    lra.
  }
  remember (x * x) as x2.
  lra.
Qed.

Lemma Q3_on_subset_3 : forall x y : R,
  in_subset_3 x y -> eval_Q3 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_3, eval_Q3 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  remember (x * x) as x2.
  nra.
Qed.

Lemma Q4_on_subset_1 : forall x y : R,
  in_subset_1 x y -> eval_Q4 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_1, eval_Q4 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  remember (x * x) as x2.
  nra.
Qed.

Lemma Q4_on_subset_2 : forall x y : R,
  in_subset_2 x y -> eval_Q4 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_2, eval_Q4 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Explicitly abstract the fractional nonlinear terms to bypass CAD limits *)
  assert (H_pos: (215393 / 500000) * (x * x) + (-50719 / 62500) * x + (383129 / 1000000) >= 0).
  {
    assert (H_id: (215393 / 125000) * ((215393 / 500000) * (x * x) + (-50719 / 62500) * x + (383129 / 1000000)) = ((215393 / 250000) * x + (-50719 / 62500)) * ((215393 / 250000) * x + (-50719 / 62500)) + (41192389 / 25000000000)) by nra.
    assert (H_sq: ((215393 / 250000) * x + (-50719 / 62500)) * ((215393 / 250000) * x + (-50719 / 62500)) >= 0). { remember ((215393 / 250000) * x + (-50719 / 62500)) as Z; nra. }
    remember ((215393 / 500000) * (x * x) + (-50719 / 62500) * x + (383129 / 1000000)) as P.
    remember (((215393 / 250000) * x + (-50719 / 62500)) * ((215393 / 250000) * x + (-50719 / 62500))) as S2.
    lra.
  }
  remember (x * x) as x2.
  lra.
Qed.

Lemma Q4_on_subset_3 : forall x y : R,
  in_subset_3 x y -> eval_Q4 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_3, eval_Q4 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Explicitly abstract the fractional nonlinear terms to bypass CAD limits *)
  assert (H_pos: (133 / 500000) * (x * x) + (-351 / 200000) * x + (39 / 10000) >= 0).
  {
    assert (H_id: (133 / 125000) * ((133 / 500000) * (x * x) + (-351 / 200000) * x + (39 / 10000)) = ((133 / 250000) * x + (-351 / 200000)) * ((133 / 250000) * x + (-351 / 200000)) + (42783 / 40000000000)) by nra.
    assert (H_sq: ((133 / 250000) * x + (-351 / 200000)) * ((133 / 250000) * x + (-351 / 200000)) >= 0). { remember ((133 / 250000) * x + (-351 / 200000)) as Z; nra. }
    remember ((133 / 500000) * (x * x) + (-351 / 200000) * x + (39 / 10000)) as P.
    remember (((133 / 250000) * x + (-351 / 200000)) * ((133 / 250000) * x + (-351 / 200000))) as S2.
    lra.
  }
  remember (x * x) as x2.
  lra.
Qed.

Lemma Q5_on_subset_1 : forall x y : R,
  in_subset_1 x y -> eval_Q5 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_1, eval_Q5 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  remember (x * x) as x2.
  nra.
Qed.

Lemma Q5_on_subset_2 : forall x y : R,
  in_subset_2 x y -> eval_Q5 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_2, eval_Q5 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Explicitly abstract the fractional nonlinear terms to bypass CAD limits *)
  assert (H_pos: (40601 / 1000000) * (x * x) + (-36497 / 500000) * x + (33807 / 1000000) >= 0).
  {
    assert (H_id: (40601 / 250000) * ((40601 / 1000000) * (x * x) + (-36497 / 500000) * x + (33807 / 1000000)) = ((40601 / 500000) * x + (-36497 / 500000)) * ((40601 / 500000) * x + (-36497 / 500000)) + (20283499 / 125000000000)) by nra.
    assert (H_sq: ((40601 / 500000) * x + (-36497 / 500000)) * ((40601 / 500000) * x + (-36497 / 500000)) >= 0). { remember ((40601 / 500000) * x + (-36497 / 500000)) as Z; nra. }
    remember ((40601 / 1000000) * (x * x) + (-36497 / 500000) * x + (33807 / 1000000)) as P.
    remember (((40601 / 500000) * x + (-36497 / 500000)) * ((40601 / 500000) * x + (-36497 / 500000))) as S2.
    lra.
  }
  remember (x * x) as x2.
  lra.
Qed.

Lemma Q5_on_subset_3 : forall x y : R,
  in_subset_3 x y -> eval_Q5 x y >= 0.
Proof.
  intros x y H_in.
  unfold in_subset_3, eval_Q5 in *.
  destruct H_in as [Hy [Hx1 Hx2]].
  subst y.
  (* Explicitly abstract the fractional nonlinear terms to bypass CAD limits *)
  assert (H_pos: (219081 / 500000) * (x * x) + (-903519 / 1000000) * x + (466771 / 1000000) >= 0).
  {
    assert (H_id: (219081 / 125000) * ((219081 / 500000) * (x * x) + (-903519 / 1000000) * x + (466771 / 1000000)) = ((219081 / 250000) * x + (-903519 / 1000000)) * ((219081 / 250000) * x + (-903519 / 1000000)) + (1738676247 / 1000000000000)) by nra.
    assert (H_sq: ((219081 / 250000) * x + (-903519 / 1000000)) * ((219081 / 250000) * x + (-903519 / 1000000)) >= 0). { remember ((219081 / 250000) * x + (-903519 / 1000000)) as Z; nra. }
    remember ((219081 / 500000) * (x * x) + (-903519 / 1000000) * x + (466771 / 1000000)) as P.
    remember (((219081 / 250000) * x + (-903519 / 1000000)) * ((219081 / 250000) * x + (-903519 / 1000000))) as S2.
    lra.
  }
  remember (x * x) as x2.
  lra.
Qed.

(* --- 4. Main Over-Approximation Theorem --- *)
(* This theorem proves that the conjunction of all 5 polynomials soundly overapproximates
   the entire Region of Interest. *)

Lemma over_approximation : forall x y : R,
  in_ROI x y ->
    eval_Q1 x y >= 0 /\
    eval_Q2 x y >= 0 /\
    eval_Q3 x y >= 0 /\
    eval_Q4 x y >= 0 /\
    eval_Q5 x y >= 0.
Proof.
  intros x y H_ROI.
  unfold in_ROI in H_ROI.

  (* The 'destruct' tactic breaks the logical OR of the ROI down into 3 separate branches. 
     We must prove the entire AND conjunction holds true within each individual subset. *)
  destruct H_ROI as [H1 | [H2 | H3]].

  - (* Subset 1 *)
    split. { apply Q1_on_subset_1; exact H1. }
    split. { apply Q2_on_subset_1; exact H1. }
    split. { apply Q3_on_subset_1; exact H1. }
    split. { apply Q4_on_subset_1; exact H1. }
    apply Q5_on_subset_1; exact H1.
  - (* Subset 2 *)
    split. { apply Q1_on_subset_2; exact H2. }
    split. { apply Q2_on_subset_2; exact H2. }
    split. { apply Q3_on_subset_2; exact H2. }
    split. { apply Q4_on_subset_2; exact H2. }
    apply Q5_on_subset_2; exact H2.
  - (* Subset 3 *)
    split. { apply Q1_on_subset_3; exact H3. }
    split. { apply Q2_on_subset_3; exact H3. }
    split. { apply Q3_on_subset_3; exact H3. }
    split. { apply Q4_on_subset_3; exact H3. }
    apply Q5_on_subset_3; exact H3.
Qed.

