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
Require Import PolynomialTheory.
Require Import SinMultiple.

Open Scope R_scope.

(* ====================================================================== *)
(** ** 辅助引理 *)

Lemma prod1_has_zero : forall f n k, 1 <= k <= n -> f k = 0 -> prod1 f n = 0.
Proof.
  intros f n k Hk Hfk.
  induction n.
  - exfalso; lra.
  - destruct (Nat.eq_dec k (S n)).
    + subst; simpl; rewrite Hfk; ring.
    + simpl; rewrite IHn; [ring | lra].
Qed.

Lemma sum1_ext : forall f g n, (forall k, 1 <= k <= n -> f k = g k) ->
    sum1 f n = sum1 g n.
Proof.
  intros f g n H; induction n; simpl; try ring.
  rewrite IHn; [ring | intros k Hk; apply H; lra].
Qed.

Lemma sum1_lt : forall f g n, (forall k, 1 <= k <= n -> f k < g k) ->
    sum1 f n < sum1 g n.
Proof.
  intros f g n H; induction n.
  - simpl; lra.
  - simpl; rewrite IHn; [lra | intros k Hk; apply H; lra].
Qed.

(* ====================================================================== *)
(** ** sin 在 (0, π/2) 上严格递增 *)
(** sin y - sin x = 2 cos((x+y)/2) sin((y-x)/2) > 0 *)

Lemma sin_strictly_inc_0_pi2 : forall x y,
    0 <= x -> x < y -> y <= PI / 2 -> sin x < sin y.
Proof.
  intros x y Hx Hxy Hy.
  set (A := (x + y) / 2). set (B := (y - x) / 2).
  have HAB1 : y = A + B by (unfold A, B; ring).
  have HAB2 : x = A - B by (unfold A, B; ring).
  have H1 : sin y - sin x = 2 * cos A * sin B.
  { rewrite HAB1, HAB2.
    have Hsin_plus : sin (A + B) = sin A * cos B + cos A * sin B by apply sin_plus.
    have Hsin_minus : sin (A - B) = sin A * cos B - cos A * sin B.
    { have Hneg1 : sin (A - B) = sin (A + (-B)) by (f_equal; ring).
      rewrite Hneg1, sin_plus, sin_neg, cos_neg. ring. }
    rewrite Hsin_plus, Hsin_minus. ring. }
  rewrite H1.
  have Hcos_pos : 0 < cos A.
  { have H4 : 0 <= A by (unfold A; lra).
    have H5 : A < PI / 2 by (unfold A; lra).
    (* 标准库 cos_pos：-PI/2 < t < PI/2 -> 0 < cos t；A=0 时 cos 0=1>0 *)
    case (Rlt_le_dec A 0).
    - exfalso; lra.
    - intros HA0.
      case (Rlt_le_dec A (PI / 2)).
      + intros HAl. apply cos_pos. split; lra.
      + exfalso; lra. }
  have Hsin_pos : 0 < sin B.
  { have H4 : 0 < B by (unfold B; lra).
    have H5 : B < PI by (unfold B; lra).
    exact (sin_pos_0_pi B H4 H5). }
  nra.
Qed.

(** 推论：sin²(kπ/(2n+1)) 两两不同且非零 *)
Lemma roots_distinct : forall n i j,
    1 <= i <= n -> 1 <= j <= n -> i <> j ->
    sin (INR i * PI / (2 * INR n + 1))^2 <>
    sin (INR j * PI / (2 * INR n + 1))^2.
Proof.
  intros n i j Hi Hj Hij.
  wlog Hlt : i < j.
  { destruct (Nat.lt_trichotomy i j); [trivial | | exfalso; apply Hij; lra].
    - symmetry; apply Hlt; lra. }
  set (xi := INR i * PI / (2 * INR n + 1)).
  set (xj := INR j * PI / (2 * INR n + 1)).
  have Hdenom_pos : 0 < 2 * INR n + 1 by (have H1 : 0 <= INR n by apply INR_nonneg; lra).
  have Hxi_nonneg : 0 <= xi.
  { unfold xi. have H1 : 0 <= INR i by (apply INR_le; lra).
    have H2 : 0 <= INR i * PI by (apply Rmult_le_0_compat; [lra | have H3 : 0 <= PI by (have H4 : 0 < PI by apply PI_RGT; lra)]).
    apply Rdiv_le_0_compat; [lra | lra]. }
  have Hxj_le : xj <= PI / 2.
  { unfold xj. have H1 : INR j <= INR n by (apply INR_le; lra).
    have H2 : 0 < 2 * INR n + 1 by lra.
    have H3 : INR j * PI / (2 * INR n + 1) <= PI / 2.
    { apply Rdiv_le_iff in H3; [|lra]. nra. }
    exact H3. }
  have Hxi_lt_xj : xi < xj.
  { unfold xi, xj. have H1 : INR i < INR j by (apply INR_lt; lra).
    have H2 : 0 < PI by apply PI_RGT.
    have H3 : 0 < 2 * INR n + 1 by lra.
    nra. }
  have Hsin_lt : sin xi < sin xj by (apply sin_strictly_inc_0_pi2; lra).
  have Hsin_pos : 0 < sin xi.
  { unfold xi. have H1 : 0 < INR i by (apply INR_lt; lra).
    have H2 : 0 < INR i * PI by (apply Rmult_lt_0_compat; [lra | apply PI_RGT]).
    have H3 : 0 < xi by (apply Rdiv_lt_0_compat; [lra | lra]).
    have H4 : xi < PI by (unfold xi; have H5 : INR i <= INR n by (apply INR_le; lra); nra).
    exact (sin_pos_0_pi xi H3 H4). }
  have Hsinj_pos : 0 < sin xj.
  { unfold xj. have H1 : 0 < INR j by (apply INR_lt; lra).
    have H2 : 0 < INR j * PI by (apply Rmult_lt_0_compat; [lra | apply PI_RGT]).
    have H3 : 0 < xj by (apply Rdiv_lt_0_compat; [lra | lra]).
    have H4 : xj < PI by (unfold xj; have H5 : INR j <= INR n by (apply INR_le; lra); nra).
    exact (sin_pos_0_pi xj H3 H4). }
  nra.
Qed.

(* ====================================================================== *)
(** ** 乘积恒等式 *)
(** Q_n(y) = (2n+1) · ∏_{k=1}^n (1 - y/sin²(kπ/(2n+1))) *)

(** 辅助：对 1 ≤ k ≤ n，0 < kπ/(2n+1) < π，故 sin > 0，sin² > 0 *)
Lemma angle_sin_pos : forall n k, 1 <= k <= n ->
    0 < sin (INR k * PI / (2 * INR n + 1)).
Proof.
  intros n k Hk.
  have Hdenom_pos : 0 < 2 * INR n + 1 by (have H1 : 0 <= INR n by apply INR_nonneg; lra).
  have Hangle_pos : 0 < INR k * PI / (2 * INR n + 1).
  { have H1 : 0 < INR k by (apply INR_lt; lra).
    have H2 : 0 < INR k * PI by (apply Rmult_lt_0_compat; [lra | apply PI_RGT]).
    apply Rdiv_lt_0_compat; [lra | lra]. }
  have Hangle_lt_pi : INR k * PI / (2 * INR n + 1) < PI.
  { have H1 : INR k <= INR n by (apply INR_le; lra).
    have H2 : 0 < 2 * INR n + 1 by lra.
    have H3 : INR k * PI / (2 * INR n + 1) < PI.
    { apply Rdiv_lt_iff in H3; [|lra]. nra. }
    exact H3. }
  exact (sin_pos_0_pi _ Hangle_pos Hangle_lt_pi).
Qed.

(** 右端是多项式：有限个一次因子的乘积 *)
Lemma product_is_poly : forall n (r : nat -> R),
    is_poly n (fun y => prod1 (fun k => 1 - y / r k) n).
Proof.
  intros n r.
  induction n.
  - simpl; apply is_poly_const.
  - simpl.
    have H1 : is_poly n (fun y => prod1 (fun k => 1 - y / r k) n) by exact IHn.
    have H2 : is_poly (S O) (fun y => 1 - y / r (S n)).
    { exists (fun i => match i with O => 1 | S O => -/r (S n) | _ => 0 end).
      intros y; simpl; ring. }
    have H3 : is_poly (S n) (fun y => prod1 (fun k => 1 - y / r k) n * (1 - y / r (S n))).
    { apply is_poly_mult with (m := n) (n := 1); exact H1 || exact H2. }
    exact H3.
Qed.

Theorem product_identity : forall n y,
    Q n y = (2 * INR n + 1) *
            prod1 (fun k => 1 - y / sin (INR k * PI / (2 * INR n + 1))^2) n.
Proof.
  intros n.
  set (P := fun y => Q n y).
  set (r := fun k => sin (INR k * PI / (2 * INR n + 1))^2).
  set (Rprod := fun y => (2 * INR n + 1) * prod1 (fun k => 1 - y / r k) n).
  have HPpoly : is_poly n P by (unfold P; apply Q_is_poly).
  have HRpoly : is_poly n Rprod.
  { unfold Rprod. apply is_poly_scale with (n := n).
    apply is_poly_weaken with (m := n) (n := O). apply product_is_poly. }
  set (pts := fun i : nat =>
    match i with
    | O => 0
    | S k => r (S k)
    end).
  have Hdist : forall i j, i < S n -> j < S n -> i <> j -> pts i <> pts j.
  { intros i j Hi Hj Hij.
    destruct i as [|i']; destruct j as [|j'].
    - exfalso; apply Hij; reflexivity.
    - (* i=0, j=S j' *) unfold pts, r. simpl.
      have H : 0 < r (S j') by (unfold r; have H2 := angle_sin_pos n (S j') (by lra); nra).
      lra.
    - (* i=S i', j=0 *) unfold pts, r. simpl.
      have H : 0 < r (S i') by (unfold r; have H2 := angle_sin_pos n (S i') (by lra); nra).
      lra.
    - (* i=S i', j=S j' *) unfold pts, r. simpl. apply roots_distinct; lra. }
  have Heq : forall i, i < S n -> P (pts i) = Rprod (pts i).
  { intros i Hi.
    destruct i as [|i'].
    - (* y = 0 *)
      unfold P, Rprod, pts. simpl.
      rewrite Q_at_zero.
      have Hprod0 : prod1 (fun k : nat => 1 - 0 / r k) n = 1.
      { induction n; simpl; [ring | rewrite IHn; ring]. }
      rewrite Hprod0; ring.
    - (* y = r (S i') *)
      unfold P, Rprod, pts, r.
      have Hroot : 1 <= S i' <= n by (simpl in Hi; lra).
      have Hq : Q n (sin (INR (S i') * PI / (2 * INR n + 1))^2) = 0
        by (apply Q_roots; lra).
      rewrite Hq.
      have Hprod : prod1 (fun k : nat => 1 - sin (INR (S i') * PI / (2 * INR n + 1))^2 /
                            sin (INR k * PI / (2 * INR n + 1))^2) n = 0.
      { have Hdenom : sin (INR (S i') * PI / (2 * INR n + 1))^2 <> 0.
        { have Hpos := angle_sin_pos n (S i') (by lra). nra. }
        have Hfactor : (1 - sin (INR (S i') * PI / (2 * INR n + 1))^2 /
                          sin (INR (S i') * PI / (2 * INR n + 1))^2) = 0.
        { field; split; lra. }
        exact (prod1_has_zero _ n (S i') (by lra) Hfactor). }
      rewrite Hprod; ring. }
  have H : forall y, P y = Rprod y by (apply poly_unique with (n := n); trivial).
  exact H.
Qed.

(* ====================================================================== *)
(** ** 余割平方和 *)

Theorem csc_sq_sum : forall n,
    sum1 (fun k => 1 / sin (INR k * PI / (2 * INR n + 1))^2) n =
    2 * INR n * (INR n + 1) / 3.
Proof.
  intros n.
  have Hpid : forall y, Q n y = (2 * INR n + 1) *
      prod1 (fun k => 1 - y / sin (INR k * PI / (2 * INR n + 1))^2) n
    by apply product_identity.
  destruct (Q_coeff_formula n) as [Tq [Hq Hqpoly]].
  set (r := fun k => sin (INR k * PI / (2 * INR n + 1))^2).
  have Hr_nonzero : forall k, 1 <= k <= n -> r k <> 0.
  { intros k Hk; unfold r; have Hpos := angle_sin_pos n k Hk; nra. }
  destruct (vieta_product_expansion n (2 * INR n + 1) r Hr_nonzero)
    as [S [HS HSpoly]].
  have Hcoeff : (-2 * INR n * (INR n + 1) * (2 * INR n + 1) / 3) =
                - (2 * INR n + 1) * sum1 (fun k => 1 / r k) n.
  { apply coeff_compare_general with (n := n) (m := n) (a := 2*INR n+1)
      (S := Tq) (T := S).
    - exact Hqpoly.
    - exact HSpoly.
    - intros y.
      have H1 : Q n y = (2*INR n+1) + (-2*INR n*(INR n+1)*(2*INR n+1)/3)*y + y^2*Tq y
        by apply Hq.
      have H2 : (2*INR n+1) * prod1 (fun k => 1 - y / r k) n =
                 (2*INR n+1) - (2*INR n+1) * sum1 (fun k => 1 / r k) n * y + y^2*S y
        by apply HS.
      rewrite H1, H2 in Hpid. exact (Hpid y). }
  have Hpos : 2 * INR n + 1 <> 0.
  { have H1 : 0 <= INR n by apply INR_nonneg. lra. }
  unfold r in Hcoeff.
  lra.
Qed.

(* ====================================================================== *)
(** ** 余切平方和 *)

Theorem cot_sq_sum : forall n,
    sum1 (fun k => (cot (INR k * PI / (2 * INR n + 1)))^2) n =
    INR n * (2 * INR n - 1) / 3.
Proof.
  intros n.
  have Hcsc : sum1 (fun k => 1 / sin (INR k * PI / (2 * INR n + 1))^2) n =
               2 * INR n * (INR n + 1) / 3
    by apply csc_sq_sum.
  have Hcot_csc : forall x, sin x <> 0 -> (cot x)^2 = 1 / sin x^2 - 1.
  { intros x Hsin.
    unfold cot.
    have H : (cos x / sin x)^2 = 1 / sin x^2 - 1.
    { have Hsc : sin x^2 + cos x^2 = 1 by apply sin_sq.
      field; split; [lra | nra]. }
    exact H. }
  have Hsin_nonzero : forall k, 1 <= k <= n ->
      sin (INR k * PI / (2 * INR n + 1)) <> 0.
  { intros k Hk; have Hpos := angle_sin_pos n k Hk; lra. }
  have Hsum_cot : sum1 (fun k => (cot (INR k * PI / (2 * INR n + 1)))^2) n =
      sum1 (fun k => 1 / sin (INR k * PI / (2 * INR n + 1))^2 - 1) n.
  { apply sum1_ext; intros k Hk. apply Hcot_csc, Hsin_nonzero; trivial. }
  rewrite Hsum_cot.
  have H3 : sum1 (fun k => 1 / sin (INR k * PI / (2 * INR n + 1))^2 - 1) n =
           sum1 (fun k => 1 / sin (INR k * PI / (2 * INR n + 1))^2) n - INR n.
  { rewrite sum1_add, sum1_const. ring. }
  rewrite H3, Hcsc.
  field; ring.
Qed.
