(** * BaselProblem — 第五步：巴塞尔问题的最终证明 *)
(** 综合前四步，利用夹逼定理证明 Σ_{k=1}^∞ 1/k² = π²/6。
    全部使用高中数学：不等式放缩 + 数列极限的 ε-N 定义。*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo.
Require Import Coq.Reals.Ranalysis.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Arith.
Require Import Basics.
Require Import TrigInequalities.
Require Import PolynomialTheory.
Require Import SinMultiple.
Require Import CotSum.

Open Scope R_scope.

(* ====================================================================== *)
(** ** 部分和与上下界 *)

Definition partial_sum (n : nat) : R :=
  sum1 (fun k => 1 / (INR k)^2) n.

Definition lower_bound (n : nat) : R :=
  PI^2 * INR n * (2 * INR n - 1) / (3 * (2 * INR n + 1)^2).

Definition upper_bound (n : nat) : R :=
  PI^2 * 2 * INR n * (INR n + 1) / (3 * (2 * INR n + 1)^2).

(* ====================================================================== *)
(** ** 夹逼定理 *)

Lemma squeeze_theorem : forall (u v w : nat -> R) (l : R),
    (forall n, u n <= v n /\ v n <= w n) ->
    Un_cv u l -> Un_cv w l -> Un_cv v l.
Proof.
  intros u v w l Hbound Hucv Hwcv eps Heps.
  destruct (Hucv eps Heps) as [Nu HNu].
  destruct (Hwcv eps Heps) as [Nw HNw].
  exists (max Nu Nw).
  intros n Hn.
  have H1 : Nu <= n by (apply le_max_l; lra).
  have H2 : Nw <= n by (apply le_max_r; lra).
  have Hu : Rabs (u n - l) < eps by (apply HNu; lra).
  have Hw : Rabs (w n - l) < eps by (apply HNw; lra).
  have H3 : u n <= v n := (Hbound n).1.
  have H4 : v n <= w n := (Hbound n).2.
  have H5 : l - eps < u n.
  { have H6 : Rabs (u n - l) < eps. exact Hu.
    have H7 : -eps < u n - l by (apply Rabs_lt; exact H6). lra. }
  have H6 : w n < l + eps.
  { have H7 : Rabs (w n - l) < eps. exact Hw.
    have H8 : w n - l < eps by (apply Rabs_lt; exact H7). lra. }
  have H9 : l - eps < v n by lra.
  have H10 : v n < l + eps by lra.
  apply Rabs_lt. split; lra.
Qed.

(* ====================================================================== *)
(** ** 关键不等式：L_n < S_n < U_n *)

Lemma partial_sum_bounds : forall n, 0 < n ->
    lower_bound n < partial_sum n /\ partial_sum n < upper_bound n.
Proof.
  intros n Hn.
  set (m := 2 * INR n + 1).
  have Hm_pos : 0 < m by (unfold m; have H1 : 0 <= INR n by apply INR_nonneg; lra).
  have Hangle : forall k, 1 <= k <= n ->
      0 < INR k * PI / m /\ INR k * PI / m < PI / 2.
  { intros k Hk.
    split.
    - unfold m. have H1 : 0 < INR k by (apply INR_lt; lra).
      have H2 : 0 < INR k * PI by (apply Rmult_lt_0_compat; [lra | apply PI_RGT]).
      apply Rdiv_lt_0_compat; [lra | lra].
    - unfold m. have H1 : INR k <= INR n by (apply INR_le; lra).
      have H2 : 0 < m by lra.
      have H3 : INR k * PI / m < PI / 2.
      { apply Rdiv_lt_iff in H3; [|lra]. nra. }
      exact H3. }
  have Hterm : forall k, 1 <= k <= n ->
      (cot (INR k * PI / m))^2 < (m / (INR k * PI))^2 /\
      (m / (INR k * PI))^2 < (1 / sin (INR k * PI / m))^2.
  { intros k Hk.
    have [H1 H2] := Hangle k Hk.
    have H3 := cot_sq_lt_inv_sq_lt_csc_sq (INR k * PI / m) H1 H2.
    have H4 : (m / (INR k * PI))^2 = / (INR k * PI / m)^2.
    { field; unfold m; split; [lra | have H5 : 0 < INR k by (apply INR_lt; lra); have H6 : 0 < PI by apply PI_RGT; nra]. }
    rewrite H4. exact H3. }
  have Hsum_lt : sum1 (fun k => (cot (INR k * PI / m))^2) n <
                 sum1 (fun k => (m / (INR k * PI))^2) n.
  { apply sum1_lt; intros k Hk; exact (Hterm k Hk).1. }
  have Hsum_lt2 : sum1 (fun k => (m / (INR k * PI))^2) n <
                  sum1 (fun k => (1 / sin (INR k * PI / m))^2) n.
  { apply sum1_lt; intros k Hk; exact (Hterm k Hk).2. }
  have Hmid : sum1 (fun k => (m / (INR k * PI))^2) n =
              m^2 / PI^2 * partial_sum n.
  { unfold partial_sum.
    have H : forall k, (m / (INR k * PI))^2 = m^2 / PI^2 * (1 / (INR k)^2).
    { intros k; field; split; [lra | have H5 : 0 < INR k by (apply INR_lt; lra); have H6 : 0 < PI by apply PI_RGT; nra]. }
    rewrite (sum1_ext _ _ _ H).
    rewrite sum1_scale. ring. }
  have Hcot := cot_sq_sum n.
  have Hcsc := csc_sq_sum n.
  rewrite Hcot in Hsum_lt.
  rewrite Hmid in Hsum_lt, Hsum_lt2.
  rewrite Hcsc in Hsum_lt2.
  unfold lower_bound, upper_bound, partial_sum.
  have Hpi2_pos : 0 < PI^2 by (have H : 0 < PI by apply PI_RGT; nra).
  have Hm2_pos : 0 < m^2 by nra.
  split; nra.
Qed.

(* ====================================================================== *)
(** ** 上下界的极限（ε-N 证明）*)

(** 通用引理：若 |a_n - L| ≤ C / INR(S n) 且 C > 0，则 a_n → L。
    证明：对任意 ε>0，由阿基米德公理取 N 使 C/ε < N，则 n≥N 时
    |a_n-L| ≤ C/(n+1) ≤ C/N < ε。*)

Lemma cv_by_bound : forall (a : nat -> R) L C,
    C > 0 -> (forall n, Rabs (a n - L) <= C / INR (S n)) -> Un_cv a L.
Proof.
  intros a L C HC Hbound eps Heps.
  have Harch : exists N : nat, C / eps < INR N.
  { (* 阿基米德公理：Coq 标准库中为 archimed，类型 {n:nat | x < INR n} *)
    destruct (archimed (C / eps)) as [N HN]. exists N. exact HN. }
  destruct Harch as [N HN].
  exists N.
  intros n Hn.
  have H1 : Rabs (a n - L) <= C / INR (S n) by apply Hbound.
  have H2 : C / INR (S n) < eps.
  { have H3 : INR (S n) >= INR (S N) by (apply INR_le; lra).
    have H4 : C / INR (S n) <= C / INR (S N).
    { apply Rdiv_le_compat_l; [lra | lra]. }
    have H5 : C / INR (S N) < eps.
    { apply Rdiv_lt_iff in H5; [|lra].
      have H6 : INR (S N) > C / eps by (simpl in HN; lra).
      nra. }
    lra. }
  lra.
Qed.

(** lower_bound n → π²/6
    |L_n - π²/6| = π²/6 · (6n+1)/(2n+1)² ≤ 7π²/(12(n+1)) *)
Lemma lower_bound_cv : Un_cv lower_bound (PI^2 / 6).
Proof.
  apply cv_by_bound with (C := 7 * PI^2 / 12).
  - have H : 0 < PI by apply PI_RGT. nra.
  - intros n.
    unfold lower_bound.
    have Hdiff : (PI^2 * INR n * (2 * INR n - 1) / (3 * (2 * INR n + 1)^2)) - PI^2 / 6 =
                 PI^2 / 6 * (-(6 * INR n + 1)) / (2 * INR n + 1)^2.
    { field; have H1 : 2 * INR n + 1 <> 0 by (have H2 : 0 <= INR n by apply INR_nonneg; lra).
      split; lra. }
    rewrite Hdiff.
    have H1 : 0 <= INR n by apply INR_nonneg.
    have H2 : 0 < 2 * INR n + 1 by lra.
    have H3 : Rabs (PI^2 / 6 * (-(6 * INR n + 1)) / (2 * INR n + 1)^2) <=
               7 * PI^2 / 12 / INR (S n).
    { have H4 : Rabs (PI^2 / 6 * (-(6 * INR n + 1)) / (2 * INR n + 1)^2) =
                 PI^2 / 6 * (6 * INR n + 1) / (2 * INR n + 1)^2.
      { rewrite Rabs_Rmult, Rabs_Rinv.
        have H5 : 0 <= PI^2 / 6 by (have H6 : 0 < PI by apply PI_RGT; nra).
        have H7 : 0 <= 6 * INR n + 1 by lra.
        have H8 : 0 <= (2 * INR n + 1)^2 by nra.
        rewrite (Rabs_right _ H5), (Rabs_right _ H7), (Rabs_right _ H8).
        field; lra. }
      rewrite H4.
      have H9 : PI^2 / 6 * (6 * INR n + 1) / (2 * INR n + 1)^2 <=
                 7 * PI^2 / 12 / INR (S n).
      { have H10 : 0 < PI^2 by (have H11 : 0 < PI by apply PI_RGT; nra).
        have H11 : 0 < INR (S n) by (apply INR_lt; lra).
        have H12 : 0 < (2 * INR n + 1)^2 by nra.
        field_simplify; nra. }
      exact H9. }
    exact H3.
Qed.

(** upper_bound n → π²/6
    |U_n - π²/6| = π²/6 · 1/(2n+1)² ≤ π²/(12(n+1)) *)
Lemma upper_bound_cv : Un_cv upper_bound (PI^2 / 6).
Proof.
  apply cv_by_bound with (C := PI^2 / 12).
  - have H : 0 < PI by apply PI_RGT. nra.
  - intros n.
    unfold upper_bound.
    have Hdiff : (PI^2 * 2 * INR n * (INR n + 1) / (3 * (2 * INR n + 1)^2)) - PI^2 / 6 =
                 PI^2 / 6 * (-1) / (2 * INR n + 1)^2.
    { field; have H1 : 2 * INR n + 1 <> 0 by (have H2 : 0 <= INR n by apply INR_nonneg; lra).
      split; lra. }
    rewrite Hdiff.
    have H1 : 0 <= INR n by apply INR_nonneg.
    have H2 : 0 < 2 * INR n + 1 by lra.
    have H3 : Rabs (PI^2 / 6 * (-1) / (2 * INR n + 1)^2) <=
               PI^2 / 12 / INR (S n).
    { have H4 : Rabs (PI^2 / 6 * (-1) / (2 * INR n + 1)^2) =
                 PI^2 / 6 / (2 * INR n + 1)^2.
      { rewrite Rabs_Rmult, Rabs_Rinv.
        have H5 : 0 <= PI^2 / 6 by (have H6 : 0 < PI by apply PI_RGT; nra).
        have H8 : 0 <= (2 * INR n + 1)^2 by nra.
        rewrite (Rabs_right _ H5), (Rabs_Ropp 1), (Rabs_right _ H8).
        field; lra. }
      rewrite H4.
      have H9 : PI^2 / 6 / (2 * INR n + 1)^2 <= PI^2 / 12 / INR (S n).
      { have H10 : 0 < PI^2 by (have H11 : 0 < PI by apply PI_RGT; nra).
        have H11 : 0 < INR (S n) by (apply INR_lt; lra).
        have H12 : 0 < (2 * INR n + 1)^2 by nra.
        field_simplify; nra. }
      exact H9. }
    exact H3.
Qed.

(* ====================================================================== *)
(** ** 最终定理：巴塞尔问题 *)

Theorem basel_problem : Un_cv partial_sum (PI^2 / 6).
Proof.
  have Hbound : forall n, lower_bound n <= partial_sum n /\ partial_sum n <= upper_bound n.
  { intros n.
    destruct n.
    - unfold lower_bound, upper_bound, partial_sum; simpl; split; ring.
    - have H := partial_sum_bounds (S n) (by lra).
      split; lra. }
  exact (squeeze_theorem lower_bound partial_sum upper_bound (PI^2 / 6)
           Hbound lower_bound_cv upper_bound_cv).
Qed.

(** 结论：当 n→∞ 时，前 n 项平方倒数和趋近于 π²/6，
    即 Σ_{k=1}^∞ 1/k² = π²/6。这就是欧拉的巴塞尔问题。*)
