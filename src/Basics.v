(** * Basics — 基础工具引理 *)
(** 本文件提供有限和、有限积的定义，以及贯穿整个证明的基础算术引理。
    全部内容仅涉及高中数学范围内的代数运算。 *)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Arith.

Open Scope R_scope.

(* ====================================================================== *)
(** ** 有限和与有限积 *)

(** [sum0 f n] = f(0) + f(1) + ... + f(n) *)
Fixpoint sum0 (f : nat -> R) (n : nat) : R :=
  match n with
  | O => f O
  | S n' => sum0 f n' + f (S n')
  end.

(** [sum1 f n] = f(1) + f(2) + ... + f(n)  （从 1 开始） *)
Fixpoint sum1 (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S n' => sum1 f n' + f (S n')
  end.

(** [prod1 f n] = f(1) * f(2) * ... * f(n) *)
Fixpoint prod1 (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 1
  | S n' => prod1 f n' * f (S n')
  end.

(* ====================================================================== *)
(** ** 求和基本性质 *)

Lemma sum1_S : forall f n, sum1 f (S n) = sum1 f n + f (S n).
Proof. intros; simpl; ring. Qed.

Lemma sum1_zero : forall f, sum1 f O = 0.
Proof. intros; simpl; ring. Qed.

(** INR 递推引理：Coq 标准库中 INR 定义有 S O 特殊分支，
    simpl 无法在变量下化简，故显式证明。*)
Lemma INR_S : forall n : nat, INR (S n) = INR n + 1.
Proof.
  intros n. destruct n; simpl; ring.
Qed.

Lemma sum1_add : forall f g n,
    sum1 (fun k => f k + g k) n = sum1 f n + sum1 g n.
Proof.
  intros f g n. induction n; simpl.
  - ring.
  - rewrite IHn. ring.
Qed.

Lemma sum1_const : forall (c : R) n,
    sum1 (fun _ => c) n = INR n * c.
Proof.
  intros c n. induction n.
  - simpl; ring.
  - simpl sum1. rewrite IHn, INR_S. ring.
Qed.

Lemma sum1_scale : forall (c : R) f n,
    sum1 (fun k => c * f k) n = c * sum1 f n.
Proof.
  intros c f n. induction n; simpl.
  - ring.
  - rewrite IHn. ring.
Qed.

(* ====================================================================== *)
(** ** 乘积基本性质 *)

Lemma prod1_S : forall f n, prod1 f (S n) = prod1 f n * f (S n).
Proof. intros; simpl; ring. Qed.

Lemma prod1_zero : forall f, prod1 f O = 1.
Proof. intros; simpl; ring. Qed.

(* ====================================================================== *)
(** ** 自然数平方和公式：sum_{k=1}^n k^2 = n(n+1)(2n+1)/6 *)

Lemma sum_sq_formula : forall n,
    sum1 (fun k => (INR k)^2) n =
    INR n * (INR n + 1) * (2 * INR n + 1) / 6.
Proof.
  induction n.
  - vm_compute. ring.
  - rewrite sum1_S, IHn. repeat rewrite INR_S. field; ring.
Qed.

(* ====================================================================== *)
(** ** 常用实数引理 *)

Lemma R_sqr_nonneg : forall x : R, x^2 >= 0.
Proof. intros; nra. Qed.

Lemma Rinv_pos : forall x, 0 < x -> 0 < /x.
Proof. intros; apply Rinv_0_lt_compat; lra. Qed.

Lemma Rsqr_inv_pos : forall x, x <> 0 -> 0 < /x^2.
Proof.
  intros x Hx. apply Rinv_0_lt_compat. nra.
Qed.

(** 若 0 < a < b，则 1/b < 1/a *)
Lemma Rinv_lt_contravar : forall a b, 0 < a -> a < b -> /b < /a.
Proof.
  intros; apply Rinv_lt; lra.
Qed.
