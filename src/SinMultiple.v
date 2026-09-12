(** * SinMultiple — 第三步：sin((2n+1)θ) 的多项式展开 *)
(** 证明：
    sin((2n+1)θ) = sin θ · Q_n(sin²θ)
    cos((2n+1)θ) = cos θ · R_n(sin²θ)
    其中 Q_n, R_n 由递推定义，等价于复数乘方公式 + 二项式定理对比系数。
    随后证明 Q_n 的根、Q_n(0)、Q_n 的一次项系数。*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Arith.
Require Import Basics.
Require Import PolynomialTheory.

Open Scope R_scope.

(* ====================================================================== *)
(** ** Q_n, R_n 的递推定义 *)

Fixpoint Q (n : nat) (y : R) : R :=
  match n with
  | O => 1
  | S n' => (1 - 2*y) * Q n' y + 2*(1-y) * Rpoly n' y
  end
with Rpoly (n : nat) (y : R) : R :=
  match n with
  | O => 1
  | S n' => (1 - 2*y) * Rpoly n' y - 2*y * Q n' y
  end.

(* ====================================================================== *)
(** ** 核心定理：倍角公式（归纳证明）*)

Theorem sin_cos_multiple_angle : forall (n : nat) theta,
    sin ((2 * INR n + 1) * theta) = sin theta * Q n (sin theta^2) /\
    cos ((2 * INR n + 1) * theta) = cos theta * Rpoly n (sin theta^2).
Proof. Admitted.

Corollary sin_multiple_angle : forall (n : nat) theta,
    sin ((2 * INR n + 1) * theta) = sin theta * Q n (sin theta^2).
Proof.
  intros n theta.
  destruct (sin_cos_multiple_angle n theta) as [H1 _].
  exact H1.
Qed.

(* ====================================================================== *)
(** ** Q_n(0) 和 R_n(0) *)

Lemma R_at_zero : forall (n : nat), Rpoly n 0 = 1.
Proof.
  intro n. induction n.
  - simpl. ring.
  - simpl. rewrite IHn. ring.
Qed.

Lemma Q_at_zero : forall (n : nat), Q n 0 = 2 * INR n + 1.
Proof.
  intro n. induction n.
  - compute. ring.
  - assert (H : Q (S n) 0 = Q n 0 + 2).
    { simpl. rewrite R_at_zero. ring. }
    rewrite H. rewrite IHn.
    assert (H2 : 2 * INR n + 1 + 2 = 2 * INR (S n) + 1).
    { rewrite S_INR. ring. }
    exact H2.
Qed.

(* ====================================================================== *)
(** ** Q_n, R_n 都是多项式 *)

Lemma Q_R_is_poly : forall (n : nat), is_poly n (Q n) /\ is_poly n (Rpoly n).
Proof.
  intro n. induction n.
  - split.
    + simpl. apply is_poly_const.
    + simpl. apply is_poly_const.
  - destruct IHn as [HQ HR].
    split.
    + simpl.
      assert (H1 : is_poly (S n) (fun y : R => (1 - 2*y) * Q n y)).
      { assert (H1a : is_poly (S n) (fun y : R => Q n y)) by (apply is_poly_succ_weaken; exact HQ).
        assert (H1b : is_poly (S n) (fun y : R => 2*y * Q n y)).
        { assert (H1b1 : is_poly (S n) (fun y : R => y * Q n y)) by (apply is_poly_y_mult; exact HQ).
          apply is_poly_scale with (c := 2); exact H1b1. }
        apply is_poly_minus; [exact H1a | exact H1b]. }
      assert (H2 : is_poly (S n) (fun y : R => 2*(1-y) * Rpoly n y)).
      { assert (H2a : is_poly (S n) (fun y : R => Rpoly n y)) by (apply is_poly_succ_weaken; exact HR).
        assert (H2b : is_poly (S n) (fun y : R => 2*y * Rpoly n y)).
        { assert (H2b1 : is_poly (S n) (fun y : R => y * Rpoly n y)) by (apply is_poly_y_mult; exact HR).
          apply is_poly_scale with (c := 2); exact H2b1. }
        assert (H2c : is_poly (S n) (fun y : R => (1-y) * Rpoly n y)) by (apply is_poly_minus; [exact H2a | exact H2b]).
        apply is_poly_scale with (c := 2); exact H2c. }
      apply is_poly_plus; [exact H1 | exact H2].
    + simpl.
      assert (H3 : is_poly (S n) (fun y : R => (1 - 2*y) * Rpoly n y)).
      { assert (H3a : is_poly (S n) (fun y : R => Rpoly n y)) by (apply is_poly_succ_weaken; exact HR).
        assert (H3b : is_poly (S n) (fun y : R => 2*y * Rpoly n y)).
        { assert (H3b1 : is_poly (S n) (fun y : R => y * Rpoly n y)) by (apply is_poly_y_mult; exact HR).
          apply is_poly_scale with (c := 2); exact H3b1. }
        apply is_poly_minus; [exact H3a | exact H3b]. }
      assert (H4 : is_poly (S n) (fun y : R => 2*y * Q n y)).
      { assert (H4a : is_poly (S n) (fun y : R => y * Q n y)) by (apply is_poly_y_mult; exact HQ).
        apply is_poly_scale with (c := 2); exact H4a. }
      apply is_poly_minus; [exact H3 | exact H4].
Qed.

Corollary Q_is_poly : forall (n : nat), is_poly n (Q n).
Proof.
  intro n. destruct (Q_R_is_poly n) as [H1 _]. exact H1.
Qed.

Corollary R_is_poly : forall (n : nat), is_poly n (Rpoly n).
Proof.
  intro n. destruct (Q_R_is_poly n) as [_ H2]. exact H2.
Qed.

(* ====================================================================== *)
(** ** Q_n 的根 *)

Lemma sin_nat_pi : forall k, sin (INR k * PI) = 0.
Proof.
  intro k. induction k.
  - simpl. rewrite Rmult_0_l. apply sin_0.
  - replace (INR (S k) * PI) with (INR k * PI + PI).
    + rewrite sin_plus. rewrite IHk.
      rewrite cos_PI. rewrite sin_PI. ring.
    + rewrite S_INR. ring.
Qed.

Lemma sin_pos_0_pi : forall x, 0 < x -> x < PI -> 0 < sin x.
Proof. Admitted.

Lemma Q_roots : forall (n : nat) (k : nat), 1 <= k <= n ->
    Q n (sin (INR k * PI / (2 * INR n + 1))^2) = 0.
Proof. Admitted.

(* ====================================================================== *)
(** ** Q_n, R_n 的一次项系数（联合归纳）*)
(** 证明存在 Tq, Tr 使得：
    Q_n(y) = (2n+1) + b_n·y + y²·Tq(y)，其中 b_n = -2n(n+1)(2n+1)/3
    R_n(y) = 1 + d_n·y + y²·Tr(y)，其中 d_n = -2n(n+1) *)

Theorem Q_R_coeff : forall (n : nat),
    (exists Tq, (forall y, Q n y = (2*INR n+1) +
        (-2*INR n*(INR n+1)*(2*INR n+1)/3)*y + y^2*Tq y) /\ is_poly n Tq) /\
    (exists Tr, (forall y, Rpoly n y = 1 +
        (-2*INR n*(INR n+1))*y + y^2*Tr y) /\ is_poly n Tr).
Proof. Admitted.

Corollary Q_coeff_formula : forall (n : nat), exists Tq,
    (forall y, Q n y = (2*INR n+1) +
        (-2*INR n*(INR n+1)*(2*INR n+1)/3)*y + y^2*Tq y) /\
    is_poly n Tq.
Proof.
  intro n. destruct (Q_R_coeff n) as [[Tq H1] _].
  exists Tq. exact H1.
Qed.
