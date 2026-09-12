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
  | S n' => (1 - 2*y) * Q n' y + 2*(1-y) * R n' y
  end
with R (n : nat) (y : R) : R :=
  match n with
  | O => 1
  | S n' => (1 - 2*y) * R n' y - 2*y * Q n' y
  end.

(* ====================================================================== *)
(** ** 核心定理：倍角公式（归纳证明）*)

Theorem sin_cos_multiple_angle : forall n theta,
    sin ((2 * INR n + 1) * theta) = sin theta * Q n (sin theta^2) /\
    cos ((2 * INR n + 1) * theta) = cos theta * R n (sin theta^2).
Proof.
  induction n.
  - intros theta; simpl; split; ring.
  - intros theta.
    destruct (IHn theta) as [Hsin Hcos].
    split.
    + replace (2 * INR (S n) + 1) with (2 * INR n + 1 + 2) by (simpl; ring).
      have H : sin ((2 * INR n + 1 + 2) * theta) =
                 sin ((2 * INR n + 1) * theta + 2 * theta).
      { f_equal; ring. }
      rewrite H, sin_plus, Hsin, Hcos, sin_double.
      have Hcd : cos (2 * theta) = 1 - 2 * sin theta^2.
      { rewrite cos_double. have Hsc : sin theta^2 + cos theta^2 = 1 by apply sin_sq. nra. }
      rewrite Hcd. simpl.
      have Hsc2 : cos theta^2 = 1 - sin theta^2.
      { have H : sin theta^2 + cos theta^2 = 1 by apply sin_sq. nra. }
      rewrite Hsc2. ring.
    + replace (2 * INR (S n) + 1) with (2 * INR n + 1 + 2) by (simpl; ring).
      have H : cos ((2 * INR n + 1 + 2) * theta) =
                 cos ((2 * INR n + 1) * theta + 2 * theta).
      { f_equal; ring. }
      rewrite H, cos_plus, Hsin, Hcos, sin_double.
      have Hcd : cos (2 * theta) = 1 - 2 * sin theta^2.
      { rewrite cos_double. have Hsc : sin theta^2 + cos theta^2 = 1 by apply sin_sq. nra. }
      rewrite Hcd. simpl.
      have Hsc2 : cos theta^2 = 1 - sin theta^2.
      { have H : sin theta^2 + cos theta^2 = 1 by apply sin_sq. nra. }
      rewrite Hsc2. ring.
Qed.

Corollary sin_multiple_angle : forall n theta,
    sin ((2 * INR n + 1) * theta) = sin theta * Q n (sin theta^2).
Proof. intros; destruct (sin_cos_multiple_angle n theta); trivial. Qed.

(* ====================================================================== *)
(** ** Q_n(0) 和 R_n(0) *)

Lemma R_at_zero : forall n, R n 0 = 1.
Proof. induction n; simpl; [ring | rewrite IHn; ring]. Qed.

Lemma Q_at_zero : forall n, Q n 0 = 2 * INR n + 1.
Proof. induction n; simpl; [ring | rewrite IHn, R_at_zero; simpl; ring]. Qed.

(* ====================================================================== *)
(** ** Q_n, R_n 都是多项式 *)

Lemma Q_R_is_poly : forall n, is_poly n (Q n) /\ is_poly n (R n).
Proof.
  induction n.
  - split; simpl; apply is_poly_const.
  - destruct IHn as [HQ HR].
    (* 辅助：(1-2y), (1-y), y 都是一次多项式 *)
    have Hpoly12 : is_poly (S O) (fun y => 1 - 2*y).
    { exists (fun i => match i with O => 1 | S O => -2 | _ => 0 end). intros y; simpl; ring. }
    have Hpoly1 : is_poly (S O) (fun y => 1 - y).
    { exists (fun i => match i with O => 1 | S O => -1 | _ => 0 end). intros y; simpl; ring. }
    have Hpolyy : is_poly (S O) (fun y => y).
    { exists (fun i => match i with O => 0 | S O => 1 | _ => 0 end). intros y; simpl; ring. }
    split.
    + (* Q_{n+1}(y) = (1-2y)Q_n(y) + 2(1-y)R_n(y) *)
      simpl.
      have H1 : is_poly (S n) (fun y => (1 - 2*y) * Q n y).
      { have Hm : is_poly (1 + n) (fun y => (1 - 2*y) * Q n y) by (apply is_poly_mult; exact Hpoly12 || exact HQ).
        have Heq : 1 + n = S n by ring. rewrite Heq in Hm. exact Hm. }
      have H2 : is_poly (S n) (fun y => 2*(1-y) * R n y).
      { have Hm : is_poly (1 + n) (fun y => (1 - y) * R n y) by (apply is_poly_mult; exact Hpoly1 || exact HR).
        have Heq : 1 + n = S n by ring. rewrite Heq in Hm.
        apply is_poly_scale with (n := S n). exact Hm. }
      apply is_poly_plus; exact H1 || exact H2.
    + (* R_{n+1}(y) = (1-2y)R_n(y) - 2y*Q_n(y) *)
      simpl.
      have H1 : is_poly (S n) (fun y => (1 - 2*y) * R n y).
      { have Hm : is_poly (1 + n) (fun y => (1 - 2*y) * R n y) by (apply is_poly_mult; exact Hpoly12 || exact HR).
        have Heq : 1 + n = S n by ring. rewrite Heq in Hm. exact Hm. }
      have H2 : is_poly (S n) (fun y => 2*y * Q n y).
      { have Hm : is_poly (1 + n) (fun y => y * Q n y) by (apply is_poly_mult; exact Hpolyy || exact HQ).
        have Heq : 1 + n = S n by ring. rewrite Heq in Hm.
        apply is_poly_scale with (n := S n). exact Hm. }
      apply is_poly_minus; exact H1 || exact H2.
Qed.

Corollary Q_is_poly : forall n, is_poly n (Q n).
Proof. intros n; destruct (Q_R_is_poly n); trivial. Qed.

Corollary R_is_poly : forall n, is_poly n (R n).
Proof. intros n; destruct (Q_R_is_poly n); trivial. Qed.

(* ====================================================================== *)
(** ** Q_n 的根 *)

Lemma sin_nat_pi : forall k, sin (INR k * PI) = 0.
Proof.
  induction k.
  - simpl; rewrite sin_0; ring.
  - simpl; rewrite <- plus_IZR, sin_plus.
    rewrite IHk, sin_pi, cos_pi; ring.
Qed.

Lemma sin_pos_0_pi : forall x, 0 < x -> x < PI -> 0 < sin x.
Proof.
  intros x H1 H2.
  (* 标准库引理 sin_pos：0 < x < PI -> 0 < sin x *)
  have H : 0 < x /\ x < PI by (split; lra).
  exact (sin_pos x H).
Qed.

Lemma Q_roots : forall n k, 1 <= k <= n ->
    Q n (sin (INR k * PI / (2 * INR n + 1))^2) = 0.
Proof.
  intros n k Hk.
  set (theta := INR k * PI / (2 * INR n + 1)).
  have Hdenom_pos : 0 < 2 * INR n + 1 by (have H1 : 0 <= INR n by apply INR_nonneg; lra).
  have Htheta_pos : 0 < theta.
  { unfold theta; apply Rdiv_lt_0_compat.
    - have H2 : 0 < INR k by (apply INR_lt; lra).
      have H3 : 0 < INR k * PI by (apply Rmult_lt_0_compat; [lra | apply PI_RGT]).
      lra.
    - lra. }
  have Htheta_lt_pi : theta < PI.
  { unfold theta. have H1 : INR k <= INR n by (apply INR_le; lra).
    have H2 : 2 * INR n + 1 > 0 by lra.
    have H3 : INR k * PI / (2 * INR n + 1) < PI.
    { apply Rdiv_lt_iff in H3; [|lra]. nra. }
    exact H3. }
  have H1 : sin ((2 * INR n + 1) * theta) = 0.
  { unfold theta. field_simplify.
    have H4 : (2 * INR n + 1) * (INR k * PI / (2 * INR n + 1)) = INR k * PI.
    { field; lra. }
    rewrite H4. apply sin_nat_pi. }
  have H2 : sin ((2 * INR n + 1) * theta) = sin theta * Q n (sin theta^2).
  { apply sin_multiple_angle. }
  rewrite H1 in H2.
  have Hsin_theta_pos : 0 < sin theta by (apply sin_pos_0_pi; lra).
  have Hsin_theta_ne_zero : sin theta <> 0 by lra.
  apply (Rmult_eq_reg_l (sin theta) Hsin_theta_ne_zero).
  lra.
Qed.

(* ====================================================================== *)
(** ** Q_n, R_n 的一次项系数（联合归纳）*)
(** 证明存在 Tq, Tr 使得：
    Q_n(y) = (2n+1) + b_n·y + y²·Tq(y)，其中 b_n = -2n(n+1)(2n+1)/3
    R_n(y) = 1 + d_n·y + y²·Tr(y)，其中 d_n = -2n(n+1) *)

Theorem Q_R_coeff : forall n,
    (exists Tq, (forall y, Q n y = (2*INR n+1) +
        (-2*INR n*(INR n+1)*(2*INR n+1)/3)*y + y^2*Tq y) /\ is_poly n Tq) /\
    (exists Tr, (forall y, R n y = 1 +
        (-2*INR n*(INR n+1))*y + y^2*Tr y) /\ is_poly n Tr).
Proof.
  induction n.
  - split.
    + exists (fun _ => 0). split; [intros y; simpl; ring | apply is_poly_const].
    + exists (fun _ => 0). split; [intros y; simpl; ring | apply is_poly_const].
  - destruct IHn as [[Tq [Hq Hqpoly]] [Tr [Hr Hrpoly]]].
    split.
    + (* Q_{n+1} 的系数 *)
      set (Tq' := fun y => (1-2*y)*Tq y + 2*(1-y)*Tr y
                       - 2*(2*INR n+1) - 2*(-2*INR n*(INR n+1))).
      exists Tq'.
      split.
      * intros y; simpl Q; rewrite Hq, Hr. unfold Tq'.
        have Hcalc : (1 - 2*y)*((2*INR n+1) + (-2*INR n*(INR n+1)*(2*INR n+1)/3)*y + y^2*Tq y)
          + 2*(1-y)*(1 + (-2*INR n*(INR n+1))*y + y^2*Tr y)
          = (2*INR (S n)+1) + (-2*INR (S n)*(INR (S n)+1)*(2*INR (S n)+1)/3)*y + y^2*Tq' y.
        { unfold Tq'; simpl; field; ring_simplify.
          (* 验证 y 的系数：
             左边 = -2(2n+1) + [-2n(n+1)(2n+1)/3] + 2[-2n(n+1)] - 2
             右边 = -2(n+1)(n+2)(2n+3)/3
             两边相等（代数恒等式）*)
          have Hcoeff : (-2*(2*INR n+1) + (-2*INR n*(INR n+1)*(2*INR n+1)/3)
                        + 2*(-2*INR n*(INR n+1)) - 2)
                       = (-2*INR (S n)*(INR (S n)+1)*(2*INR (S n)+1)/3).
          { simpl; field; ring. }
          lra. }
        exact Hcalc.
      * (* Tq' 是多项式：由 Tq, Tr, 常数, y 经 +,-,* 组成 *)
        have Hpoly12 : is_poly (S O) (fun y => 1 - 2*y).
        { exists (fun i => match i with O => 1 | S O => -2 | _ => 0 end). intros y; simpl; ring. }
        have Hpoly1 : is_poly (S O) (fun y => 1 - y).
        { exists (fun i => match i with O => 1 | S O => -1 | _ => 0 end). intros y; simpl; ring. }
        have H1 : is_poly (S n) (fun y => (1 - 2*y) * Tq y).
        { have Hm : is_poly (1 + n) (fun y => (1 - 2*y) * Tq y) by (apply is_poly_mult; exact Hpoly12 || exact Hqpoly).
          have Heq : 1 + n = S n by ring. rewrite Heq in Hm. exact Hm. }
        have H2 : is_poly (S n) (fun y => 2*(1-y) * Tr y).
        { have Hm : is_poly (1 + n) (fun y => (1 - y) * Tr y) by (apply is_poly_mult; exact Hpoly1 || exact Hrpoly).
          have Heq : 1 + n = S n by ring. rewrite Heq in Hm.
          apply is_poly_scale with (n := S n). exact Hm. }
        have Hconst : is_poly (S n) (fun _ => -2*(2*INR n+1) - 2*(-2*INR n*(INR n+1))).
        { apply is_poly_weaken with (m := O) (n := S n). apply is_poly_const. }
        unfold Tq'. apply is_poly_minus.
        - apply is_poly_plus; exact H1 || exact H2.
        - exact Hconst.
    + (* R_{n+1} 的系数 *)
      set (Tr' := fun y => (1-2*y)*Tr y - 2*y*Tq y - 2 - 2*(2*INR n+1)).
      exists Tr'.
      split.
      * intros y; simpl R; rewrite Hr, Hq. unfold Tr'.
        have Hcalc : (1 - 2*y)*(1 + (-2*INR n*(INR n+1))*y + y^2*Tr y)
          - 2*y*((2*INR n+1) + (-2*INR n*(INR n+1)*(2*INR n+1)/3)*y + y^2*Tq y)
          = 1 + (-2*INR (S n)*(INR (S n)+1))*y + y^2*Tr' y.
        { unfold Tr'; simpl; field; ring_simplify.
          have Hcoeff : (-2 + (-2*INR n*(INR n+1)) - 2*(2*INR n+1))
                       = (-2*INR (S n)*(INR (S n)+1)).
          { simpl; field; ring. }
          lra. }
        exact Hcalc.
      * (* Tr' 是多项式 *)
        have Hpoly12 : is_poly (S O) (fun y => 1 - 2*y).
        { exists (fun i => match i with O => 1 | S O => -2 | _ => 0 end). intros y; simpl; ring. }
        have Hpolyy : is_poly (S O) (fun y => y).
        { exists (fun i => match i with O => 0 | S O => 1 | _ => 0 end). intros y; simpl; ring. }
        have H1 : is_poly (S n) (fun y => (1 - 2*y) * Tr y).
        { have Hm : is_poly (1 + n) (fun y => (1 - 2*y) * Tr y) by (apply is_poly_mult; exact Hpoly12 || exact Hrpoly).
          have Heq : 1 + n = S n by ring. rewrite Heq in Hm. exact Hm. }
        have H2 : is_poly (S n) (fun y => 2*y * Tq y).
        { have Hm : is_poly (1 + n) (fun y => y * Tq y) by (apply is_poly_mult; exact Hpolyy || exact Hqpoly).
          have Heq : 1 + n = S n by ring. rewrite Heq in Hm.
          apply is_poly_scale with (n := S n). exact Hm. }
        have Hconst : is_poly (S n) (fun _ => -2 - 2*(2*INR n+1)).
        { apply is_poly_weaken with (m := O) (n := S n). apply is_poly_const. }
        unfold Tr'. apply is_poly_minus.
        - apply is_poly_minus; exact H1 || exact H2.
        - exact Hconst.
Qed.

Corollary Q_coeff_formula : forall n, exists Tq,
    (forall y, Q n y = (2*INR n+1) +
        (-2*INR n*(INR n+1)*(2*INR n+1)/3)*y + y^2*Tq y) /\
    is_poly n Tq.
Proof. intros n; destruct (Q_R_coeff n) as [H _]; exact H. Qed.
