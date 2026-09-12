(** * CotSum — 第四步：余割/余切平方和恒等式 *)
(** 证明：
    Σ_{k=1}^n csc²(kπ/(2n+1)) = 2n(n+1)/3
    Σ_{k=1}^n cot²(kπ/(2n+1)) = n(2n-1)/3 *)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Arith.
Require Import Basics.
Require Import TrigInequalities.
Require Import PolynomialTheory.
Require Import SinMultiple.

Open Scope R_scope.

(* ====================================================================== *)
(** ** 辅助引理 *)

Lemma prod1_has_zero : forall (f : nat -> R) (n k : nat), 1 <= k <= n -> f k = 0 -> prod1 f n = 0.
Proof.
  intros f n k H Hfk.
  induction n.
  - exfalso.
    destruct H as [Hle1 Hle0].
    assert (Hk : k = O). { apply Nat.le_0_r. exact Hle0. }
    rewrite Hk in Hle1.
    exact (Nat.nle_succ_0 O Hle1).
  - destruct (Nat.eq_dec k (S n)).
    + subst. simpl. rewrite Hfk. ring.
    + assert (Hk : (k <= n)%nat). lia.
      simpl. rewrite IHn; [|lia|exact Hfk]. ring.
Qed.

Lemma sum1_ext : forall (f g : nat -> R) (n : nat), (forall k : nat, 1 <= k <= n -> f k = g k) ->
    sum1 f n = sum1 g n.
Proof.
  intros f g n H.
  induction n.
  - reflexivity.
  - simpl.
    assert (H' : forall k : nat, 1 <= k <= n -> f k = g k).
    { intros k Hk. apply H. lra. }
    rewrite (IHn H').
    f_equal. apply H. lra.
Qed.

Lemma sum1_lt : forall (f g : nat -> R) (n : nat), 1 <= n ->
    (forall k : nat, 1 <= k <= n -> f k < g k) ->
    sum1 f n < sum1 g n.
Proof.
  intros f g n Hn H.
  induction n.
  - exfalso. lia.
  - simpl.
    destruct n.
    + apply H. lra.
    + assert (H' : forall k : nat, 1 <= k <= S n -> f k < g k).
      { intros k Hk. apply H. lra. }
      assert (Hih : sum1 f (S n) < sum1 g (S n)) by (apply IHn; [lra|exact H']).
      assert (Hlast : f (S (S n)) < g (S (S n))) by (apply H; lra).
      lra.
Qed.

(* ====================================================================== *)
(** ** sin 在 (0, π/2) 上严格递增 *)
(** sin y - sin x = 2 cos((x+y)/2) sin((y-x)/2) > 0 *)

Lemma sin_strictly_inc_0_pi2 : forall (x y : R),
    0 <= x -> x < y -> y <= PI / 2 -> sin x < sin y.
Proof. Admitted.

(** 推论：sin²(kπ/(2n+1)) 两两不同且非零 *)
Lemma roots_distinct : forall (n i j : nat),
    1 <= i <= n -> 1 <= j <= n -> i <> j ->
    sin (INR i * PI / (2 * INR n + 1))^2 <>
    sin (INR j * PI / (2 * INR n + 1))^2.
Proof. Admitted.

(* ====================================================================== *)
(** ** 乘积恒等式 *)
(** Q_n(y) = (2n+1) · ∏_{k=1}^n (1 - y/sin²(kπ/(2n+1))) *)

(** 辅助：对 1 ≤ k ≤ n，0 < kπ/(2n+1) < π，故 sin > 0，sin² > 0 *)
Lemma angle_sin_pos : forall (n k : nat), 1 <= k <= n ->
    0 < sin (INR k * PI / (2 * INR n + 1)).
Proof. Admitted.

(** 右端是多项式：有限个一次因子的乘积 *)
Lemma product_is_poly : forall (n : nat) (r : nat -> R),
    is_poly n (fun y => prod1 (fun k => 1 - y / r k) n).
Proof. Admitted.

Theorem product_identity : forall (n : nat) (y : R),
    Q n y = (2 * INR n + 1) *
            prod1 (fun k => 1 - y / sin (INR k * PI / (2 * INR n + 1))^2) n.
Proof. Admitted.

(* ====================================================================== *)
(** ** 余割平方和 *)

Theorem csc_sq_sum : forall (n : nat),
    sum1 (fun k => 1 / sin (INR k * PI / (2 * INR n + 1))^2) n =
    2 * INR n * (INR n + 1) / 3.
Proof. Admitted.

(* ====================================================================== *)
(** ** 余切平方和 *)

Theorem cot_sq_sum : forall (n : nat),
    sum1 (fun k => (cot (INR k * PI / (2 * INR n + 1)))^2) n =
    INR n * (2 * INR n - 1) / 3.
Proof. Admitted.
