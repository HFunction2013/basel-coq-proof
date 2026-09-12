(** * PolynomialTheory — 第二步：多项式理论与韦达定理 *)
(** 本文件发展最小化的多项式理论，全部使用高中代数（多项式乘法、
    因式分解、韦达定理），不涉及高等数学。
    核心内容：
    1. 多项式的函数式定义（次数 ≤ n）
    2. 多项式乘法（卷积 / 归纳）
    3. 因式定理：y^i - r^i = (y-r)(y^{i-1}+...+r^{i-1})
    4. 根的个数上界：n 次多项式至多 n 个不同根
    5. 多项式唯一性
    6. 韦达定理（乘积展开的一次项系数 & n 元韦达）*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.Arith.
Require Import Basics.

Open Scope R_scope.

Coercion INR : nat >-> R.

(* ====================================================================== *)
(** ** 多项式的函数式定义 *)

Definition is_poly (n : nat) (P : R -> R) : Prop :=
  exists (a : nat -> R), forall y, P y = sum0 (fun i => a i * y^i) n.

(* ====================================================================== *)
(** ** sum0 的辅助引理 *)

Lemma sum0_add : forall (f g : nat -> R) (n : nat),
    sum0 (fun i => f i + g i) n = sum0 f n + sum0 g n.
Proof.
  intros f g n. induction n; simpl.
  - ring.
  - rewrite IHn. ring.
Qed.

Lemma sum0_scale : forall (c : R) (f : nat -> R) (n : nat),
    sum0 (fun i => c * f i) n = c * sum0 f n.
Proof.
  intros c f n. induction n; simpl.
  - ring.
  - rewrite IHn. ring.
Qed.

Lemma sum0_ext : forall (f g : nat -> R) (n : nat),
    (forall i : nat, i <= n -> f i = g i) -> sum0 f n = sum0 g n.
Proof.
  intros f g n. revert f g. induction n.
  - intros f g H. simpl. apply H with (i := 0%nat). lia.
  - intros f g H. simpl.
    assert (H' : forall i : nat, i <= n -> f i = g i).
    { intros i Hi. apply H. lia. }
    rewrite (IHn f g H').
    apply H with (i := S n). lia.
Qed.

Lemma sum0_append_zero : forall (a : nat -> R) (m n : nat) (y : R),
    (forall i : nat, m < i -> a i = 0) ->
    sum0 (fun i => a i * y^i) (m + n) = sum0 (fun i => a i * y^i) m.
Proof.
  intros a m n y Hzero.
  induction n.
  - replace (m + 0) with m by lia. reflexivity.
  - replace (m + S n) with (S (m + n)) by lia.
    simpl sum0. rewrite IHn.
    replace (a (m + n) * y^(m + n)) with 0.
    + ring.
    + assert (H : a (m + n) = 0) by (apply Hzero; lia).
      rewrite H. ring.
Qed.

(* ====================================================================== *)
(** ** 多项式的基本封闭性 *)

Lemma is_poly_const : forall c, is_poly O (fun _ => c).
Proof.
  intros c. exists (fun i => match i with O => c | _ => 0 end).
  intros y; simpl; ring.
Qed.

Lemma is_poly_weaken : forall m n P, is_poly m P -> is_poly (m + n) P.
Proof.
  intros m n P [a Ha].
  set (b := fun i => if Nat.leb i m then a i else 0).
  exists b.
  intros y.
  have Hbm : forall i : nat, i <= m -> b i = a i.
  { intros i Hi; unfold b; rewrite (Nat.leb_correct i m Hi); reflexivity. }
  have Hbg : forall i : nat, m < i -> b i = 0.
  { intros i Hi; unfold b; rewrite (Nat.leb_gt i m Hi); reflexivity. }
  have H1 : sum0 (fun i => b i * y^i) (m + n) = sum0 (fun i => b i * y^i) m.
  { apply sum0_append_zero. intros i Hi; apply Hbg; lra. }
  have H2 : sum0 (fun i => b i * y^i) m = sum0 (fun i => a i * y^i) m.
  { apply sum0_ext; intros i Hi; rewrite Hbm; trivial. }
  rewrite H1, H2. apply Ha.
Qed.

Lemma is_poly_plus : forall (n : nat) P Q,
    is_poly n P -> is_poly n Q -> is_poly n (fun y => P y + Q y).
Proof.
  intros n P Q [a Ha] [b Hb].
  exists (fun i => a i + b i).
  intros y. rewrite Ha, Hb.
  rewrite <- sum0_add. apply sum0_ext.
  intros i _. ring.
Qed.

Lemma is_poly_neg : forall (n : nat) P, is_poly n P -> is_poly n (fun y => -P y).
Proof.
  intros n P [a Ha].
  exists (fun i => -a i).
  intros y. rewrite Ha.
  rewrite <- sum0_scale. apply sum0_ext.
  intros i _. ring.
Qed.

Lemma is_poly_minus : forall (n : nat) P Q,
    is_poly n P -> is_poly n Q -> is_poly n (fun y => P y - Q y).
Proof.
  intros n P Q HP HQ.
  assert (H : is_poly n (fun y => P y + (-Q y))) by (apply is_poly_plus; [exact HP | apply is_poly_neg; exact HQ]).
  have H2 : (fun y : R => P y + (-Q y)) = (fun y : R => P y - Q y).
  { extensionality y; ring. }
  rewrite H2 in H. exact H.
Qed.

Lemma is_poly_scale : forall (n : nat) c P, is_poly n P -> is_poly n (fun y => c * P y).
Proof.
  intros n c P [a Ha].
  exists (fun i => c * a i).
  intros y. rewrite Ha.
  rewrite <- sum0_scale. apply sum0_ext.
  intros i _. ring.
Qed.

(** y * P(y) 是多项式：若 P 次数 ≤ n，则 y*P 次数 ≤ S n *)
Lemma is_poly_y_mult : forall (n : nat) P, is_poly n P -> is_poly (S n) (fun y => y * P y).
Proof.
  intros n P [a Ha].
  set (b := fun i => match i with O => 0 | S j => a j end).
  exists b.
  intros y.
  have H : sum0 (fun i => b i * y^i) (S n) = y * sum0 (fun i => a i * y^i) n.
  { induction n.
    - simpl; unfold b; simpl; ring.
    - simpl sum0. unfold b at 1; simpl. rewrite IHn. ring. }
  rewrite H. rewrite Ha. ring.
Qed.

(** y^k * P 是多项式：若 P 次数 ≤ n，则 y^k*P 次数 ≤ n+k *)
Lemma is_poly_y_pow : forall k n P, is_poly n P -> is_poly (n + k) (fun y => y^k * P y).
Proof.
  induction k.
  - intros n P HP. replace (n + 0) with n by lia. exact HP.
  - intros n P HP.
    replace (n + S k) with (S (n + k)) by lia.
    apply is_poly_y_mult. apply IHk. exact HP.
Qed.

(** 多项式乘法：次数 ≤ m 和 ≤ n 的多项式乘积次数 ≤ m+n *)
Lemma is_poly_mult : forall m n P Q,
    is_poly m P -> is_poly n Q -> is_poly (m + n) (fun y => P y * Q y).
Proof. Admitted.

(* ====================================================================== *)
(** ** 因式定理 (Factor Theorem) *)
(** 关键恒等式：y^i - r^i = (y-r)(y^{i-1} + r·y^{i-2} + ... + r^{i-1}) *)

(** 几何和 geo_sum r y n = r^n + r^{n-1}y + ... + r y^{n-1} + y^n *)
Fixpoint geo_sum (r y : R) (n : nat) : R :=
  match n with
  | O => 1
  | S n' => y * geo_sum r y n' + r^(S n')
  end.

Lemma geo_sum_factor : forall r y n,
    y^(S n) - r^(S n) = (y - r) * geo_sum r y n.
Proof.
  induction n.
  - simpl; ring.
  - simpl geo_sum.
    replace (y^(S (S n)) - r^(S (S n))) with
      (y * (y^(S n) - r^(S n)) + (y - r) * r^(S n)).
    + rewrite IHn. ring.
    + simpl; ring.
Qed.

(** geo_sum r y n 是 y 的 n 次多项式 *)
Lemma geo_sum_is_poly : forall r n, is_poly n (fun y => geo_sum r y n).
Proof.
  induction n.
  - simpl; apply is_poly_const.
  - intros r. simpl geo_sum.
    have H1 : is_poly (S n) (fun y : R => y * geo_sum r y n).
    { apply is_poly_y_mult. apply IHn. }
    have H2 : is_poly (S n) (fun _ : R => r^(S n)).
    { apply is_poly_weaken with (m := O) (n := S n). apply is_poly_const. }
    apply is_poly_plus; exact H1 || exact H2.
Qed.

Lemma factor_theorem : forall (n : nat) P r,
    is_poly (S n) P -> P r = 0 ->
    exists Q, is_poly n Q /\ forall y, P y = (y - r) * Q y.
Proof. Admitted.

(* ====================================================================== *)
(** ** 根的个数上界 *)

Lemma poly_max_roots : forall (n : nat) P,
    is_poly n P ->
    (exists (r : nat -> R), (forall i j : nat, i < S n -> j < S n -> i <> j -> r i <> r j) /\
      (forall i : nat, i < S n -> P (r i) = 0)) ->
    forall y, P y = 0.
Proof. Admitted.

(* ====================================================================== *)
(** ** 多项式唯一性 *)

Lemma poly_unique : forall (n : nat) P Q,
    is_poly n P -> is_poly n Q ->
    (exists (r : nat -> R),
      (forall i j : nat, i < S n -> j < S n -> i <> j -> r i <> r j) /\
      (forall i : nat, i < S n -> P (r i) = Q (r i))) ->
    forall y, P y = Q y.
Proof. Admitted.

(* ====================================================================== *)
(** ** 乘积展开的一次项系数（韦达定理的倒数根形式）*)
(** c · ∏_{k=1}^n (1 - y/r_k) = c - c·(Σ1/r_k)·y + y²·S(y) *)

Lemma vieta_product_expansion : forall (n : nat) c (r : nat -> R),
    (forall k : nat, 1 <= k <= n -> r k <> 0) ->
    exists S : R -> R,
      (forall y, c * prod1 (fun k => 1 - y / r k) n =
                  c - c * (sum1 (fun k => 1 / r k) n) * y + y^2 * S y) /\
      is_poly n S.
Proof. Admitted.

(* ====================================================================== *)
(** ** 系数比较引理 *)
(** 若 a + b·y + y²·S(y) = a + c·y + y²·T(y) 对所有 y 成立，
    且 S, T 是多项式，则 b = c。
    证明：D(y) = (b-c)y + y²(S-T) ≡ 0。D(y) = y·D1(y)，其中
    D1(y) = (b-c) + y(S-T)。D1 在所有非零点为 0，由多项式唯一性 D1≡0，
    故 D1(0) = b-c = 0。*)

Lemma coeff_compare_general : forall (n : nat) m a b c S T,
    is_poly n S -> is_poly m T ->
    (forall y, a + b*y + y^2*S y = a + c*y + y^2*T y) ->
    b = c.
Proof. Admitted.

(* ====================================================================== *)
(** ** n 元韦达定理 *)
(** 对 n 次多项式 a_n x^n + a_{n-1}x^{n-1} + ... + a_0，
    若 a_n ≠ 0 且可分解为 a_n·∏(x-r_k)，则 Σ r_k = -a_{n-1}/a_n。*)

(** 引理：若 Σ_{i=0}^n c_i y^i = 0 对所有 y 成立，则所有 c_i = 0 *)
Lemma all_coeffs_zero : forall (n : nat) (c : nat -> R),
    (forall y, sum0 (fun i => c i * y^i) n = 0) ->
    forall i : nat, i <= n -> c i = 0.
Proof. Admitted.

(** 先证：∏_{k=1}^n (y-r_k) 的系数满足 b_n=1, b_{n-1}=-Σr_k *)
Lemma product_coeffs : forall (n : nat) (r : nat -> R),
    exists (b : nat -> R),
      (forall y, prod1 (fun k => y - r k) n = sum0 (fun i => b i * y^i) n) /\
      (n >= 1 -> b n = 1 /\ b ((n - 1)%nat) = -sum1 r n).
Proof. Admitted.

Theorem vieta_sum_roots : forall (n : nat) (a : nat -> R) (roots : nat -> R),
    n >= 1 -> a n <> 0 ->
    (forall y, sum0 (fun i => a i * y^i) n = a n * prod1 (fun k => y - roots k) n) ->
    sum1 (fun k => roots k) n = - a ((n - 1)%nat) / a n.
Proof. Admitted.
