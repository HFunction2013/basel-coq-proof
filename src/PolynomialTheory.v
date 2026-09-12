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

Lemma sum0_ext : forall (f g : nat -> R) (n : nat),
    (forall i : nat, i <= n -> f i = g i) -> sum0 f n = sum0 g n.
Proof.
Admitted.

Lemma sum0_append_zero : forall (a : nat -> R) m n y,
    (forall i, m < i -> a i = 0) ->
    sum0 (fun i => a i * y^i) (m + n) = sum0 (fun i => a i * y^i) m.
Proof.
  intros a m n y Hzero.
  induction n.
  - replace (m + 0) with m by ring. reflexivity.
  - replace (m + S n) with (S (m + n)) by (simpl; ring).
    simpl sum0. rewrite IHn.
    replace (a (m + n) * y^(m + n)) with 0 by (have H := Hzero (m+n); [rewrite H; ring | lra]).
    ring.
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
  have Hbm : forall i, i <= m -> b i = a i.
  { intros i Hi; unfold b; rewrite (Nat.leb_correct i m Hi); reflexivity. }
  have Hbg : forall i, m < i -> b i = 0.
  { intros i Hi; unfold b; rewrite (Nat.leb_gt i m Hi); reflexivity. }
  have H1 : sum0 (fun i => b i * y^i) (m + n) = sum0 (fun i => b i * y^i) m.
  { apply sum0_append_zero. intros i Hi; apply Hbg; lra. }
  have H2 : sum0 (fun i => b i * y^i) m = sum0 (fun i => a i * y^i) m.
  { apply sum0_ext; intros i Hi; rewrite Hbm; trivial. }
  rewrite H1, H2. apply Ha.
Qed.

Lemma is_poly_plus : forall n P Q,
    is_poly n P -> is_poly n Q -> is_poly n (fun y => P y + Q y).
Proof.
  intros n P Q [a Ha] [b Hb].
  exists (fun i => a i + b i).
  intros y. rewrite Ha, Hb.
  induction n; simpl; try ring.
  rewrite IHn. ring.
Qed.

Lemma is_poly_neg : forall n P, is_poly n P -> is_poly n (fun y => -P y).
Proof.
  intros n P [a Ha].
  exists (fun i => -a i).
  intros y. rewrite Ha.
  induction n; simpl; try ring.
  rewrite IHn. ring.
Qed.

Lemma is_poly_minus : forall n P Q,
    is_poly n P -> is_poly n Q -> is_poly n (fun y => P y - Q y).
Proof.
  intros n P Q HP HQ.
  have H : is_poly n (fun y => P y + (-Q y)) by (apply is_poly_plus; [exact HP | apply is_poly_neg; exact HQ]).
  have H2 : (fun y : R => P y + (-Q y)) = (fun y : R => P y - Q y).
  { extensionality y; ring. }
  rewrite H2 in H. exact H.
Qed.

Lemma is_poly_scale : forall n c P, is_poly n P -> is_poly n (fun y => c * P y).
Proof.
  intros n c P [a Ha].
  exists (fun i => c * a i).
  intros y. rewrite Ha.
  induction n; simpl; try ring.
  rewrite IHn. ring.
Qed.

(** y * P(y) 是多项式：若 P 次数 ≤ n，则 y*P 次数 ≤ S n *)
Lemma is_poly_y_mult : forall n P, is_poly n P -> is_poly (S n) (fun y => y * P y).
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
  - intros n P HP. replace (n + 0) with n by ring. exact HP.
  - intros n P HP.
    replace (n + S k) with (S (n + k)) by (simpl; ring).
    apply is_poly_y_mult. apply IHk. exact HP.
Qed.

(** 多项式乘法：次数 ≤ m 和 ≤ n 的多项式乘积次数 ≤ m+n *)
Lemma is_poly_mult : forall m n P Q,
    is_poly m P -> is_poly n Q -> is_poly (m + n) (fun y => P y * Q y).
Proof.
  induction m.
  - (* m = 0: P 是常数 *)
    intros n P Q [a Ha] HQ.
    have Hc : exists c, P = fun _ => c.
    { exists (a O). extensionality y.
      have H : P y = a O by (rewrite Ha; simpl; ring).
      exact H. }
    destruct Hc as [c Hc].
    rewrite Hc. apply is_poly_scale with (n := n).
    apply is_poly_weaken with (m := n) (n := O). exact HQ.
  - (* m = S m' *)
    intros n P Q HP HQ.
    destruct HP as [a Ha].
    set (P_rest := fun y => sum0 (fun i => a i * y^i) m').
    have HP_rest : is_poly m' P_rest.
    { exists a. intros y; reflexivity. }
    have Hdecomp : forall y, P y = P_rest y + a m' * y^m'.
    { intros y. unfold P_rest. rewrite Ha. simpl sum0. ring. }
    have H1 : is_poly (m' + n) (fun y => P_rest y * Q y) by (apply IHm'; exact HQ).
    have H2 : is_poly (S m' + n) (fun y => a m' * y^m' * Q y).
    { have H21 : is_poly (n + m') (fun y => y^m' * Q y) by (apply is_poly_y_pow; exact HQ).
      have H22 : is_poly (S m' + n) (fun y => y^m' * Q y).
      { have Heq : n + m' = m' + n by ring. rewrite Heq in H21.
        apply is_poly_weaken with (m := m' + n) (n := 1). exact H21. }
      apply is_poly_scale with (n := S m' + n). exact H22. }
    have H1' : is_poly (S m' + n) (fun y => P_rest y * Q y).
    { apply is_poly_weaken with (m := m' + n) (n := 1). exact H1. }
    have H3 : is_poly (S m' + n) (fun y => P_rest y * Q y + a m' * y^m' * Q y).
    { apply is_poly_plus; exact H1' || exact H2. }
    have H4 : (fun y : R => P_rest y * Q y + a m' * y^m' * Q y) = (fun y : R => P y * Q y).
    { extensionality y. rewrite (Hdecomp y); ring. }
    rewrite H4 in H3. exact H3.
Qed.

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

Lemma factor_theorem : forall n P r,
    is_poly (S n) P -> P r = 0 ->
    exists Q, is_poly n Q /\ forall y, P y = (y - r) * Q y.
Proof.
  intros n P r [a Ha] Hr.
  set (Q := fun y => sum0 (fun i => a (S i) * geo_sum r y i) n).
  exists Q.
  split.
  - (* Q 是次数 ≤ n 的多项式：有限个多项式之和 *)
    have Hterm : forall i, is_poly n (fun y => a (S i) * geo_sum r y i).
    { intros i.
      have H1 : is_poly i (fun y => geo_sum r y i) by (apply geo_sum_is_poly with (r := r)).
      have H2 : is_poly n (fun y => geo_sum r y i) by (apply is_poly_weaken with (m := i) (n := n - i); [exact H1 |]).
      apply is_poly_scale with (n := n). exact H2. }
    (* 有限个多项式之和仍是多项式，对 n 归纳 *)
    have Hsum : forall m, is_poly n (fun y => sum0 (fun i => a (S i) * geo_sum r y i) m).
    { induction m.
      - simpl; apply Hterm.
      - simpl sum0. apply is_poly_plus; [apply IHm | apply Hterm]. }
    exact (Hsum n).
  - (* P(y) = (y-r) * Q(y) *)
    intros y.
    have H1 : P y = sum0 (fun i => a i * y^i) (S n) by apply Ha.
    have H2 : P r = sum0 (fun i => a i * r^i) (S n) by apply Ha.
    rewrite H1.
    have H3 : sum0 (fun i => a i * y^i) (S n) =
               sum0 (fun i => a i * (y^i - r^i)) (S n).
    { have H4 : sum0 (fun i => a i * r^i) (S n) = 0 by (rewrite <- H2; exact Hr).
      induction n.
      - simpl; rewrite H4; ring.
      - simpl sum0. rewrite IHn. ring. }
    rewrite H3.
    (* 用 geo_sum_factor 逐项提取 (y-r) *)
    have H4 : forall m, sum0 (fun i => a i * (y^i - r^i)) (S m) =
                      (y - r) * sum0 (fun i => a (S i) * geo_sum r y i) m.
    { induction m.
      - simpl. have H5 : y^(S O) - r^(S O) = (y - r) * geo_sum r y O by (apply geo_sum_factor with (n := O)).
        simpl in H5. ring_simplify in H5. nra.
      - simpl sum0. rewrite IHm.
        have H6 : y^(S (S m)) - r^(S (S m)) = (y - r) * geo_sum r y (S m) by (apply geo_sum_factor with (n := S m)).
        ring_simplify. rewrite H6. ring. }
    exact (H4 n).
Qed.

(* ====================================================================== *)
(** ** 根的个数上界 *)

Lemma poly_max_roots : forall n P,
    is_poly n P ->
    (exists (r : nat -> R), (forall i j, i < S n -> j < S n -> i <> j -> r i <> r j) /\
      (forall i, i < S n -> P (r i) = 0)) ->
    forall y, P y = 0.
Proof.
  induction n.
  - intros P [a Ha] [r [Hdist Hroots]].
    have H0 : P (r O) = 0 by (apply Hroots; lra).
    have H1 : forall y, P y = a O.
    { intros y; simpl in Ha; apply Ha. }
    intros y; rewrite H1, <- H1 with (y := r O), H0; ring.
  - intros P HP [r [Hdist Hroots]].
    have Hfr : P (r O) = 0 by (apply Hroots; lra).
    destruct (factor_theorem n P (r O) HP Hfr) as [Q [HQ Hfact]].
    have Qroots : forall i, i < S n -> Q (r (S i)) = 0.
    { intros i Hi.
      have H : P (r (S i)) = 0 by (apply Hroots; lra).
      have H2 : P (r (S i)) = (r (S i) - r O) * Q (r (S i)) by apply Hfact.
      rewrite H2 in H.
      have H3 : r (S i) <> r O by (apply Hdist; lra).
      have H4 : r (S i) - r O <> 0 by (intro; apply H3; lra).
      apply (Rmult_eq_reg_l (r (S i) - r O) H4). lra. }
    have Qzero : forall y, Q y = 0.
    { apply IHn with (r := fun i => r (S i)); trivial.
      split; intros.
      - apply Hdist; lra.
      - apply Qroots; lra. }
    intros y; rewrite Hfact, Qzero; ring.
Qed.

(* ====================================================================== *)
(** ** 多项式唯一性 *)

Lemma poly_unique : forall n P Q,
    is_poly n P -> is_poly n Q ->
    (exists (r : nat -> R),
      (forall i j, i < S n -> j < S n -> i <> j -> r i <> r j) /\
      (forall i, i < S n -> P (r i) = Q (r i))) ->
    forall y, P y = Q y.
Proof.
  intros n P Q HP HQ [r [Hdist Heq]].
  set (D := fun y => P y - Q y).
  have HDpoly : is_poly n D by (apply is_poly_minus; trivial).
  have Droots : forall i, i < S n -> D (r i) = 0.
  { intros i Hi; unfold D; rewrite Heq; lra. }
  have Dzero : forall y, D y = 0.
  { apply poly_max_roots with (n := n) (P := D); trivial.
    exists r; split; trivial. }
  intros y; unfold D in Dzero; have H := Dzero y; lra.
Qed.

(* ====================================================================== *)
(** ** 乘积展开的一次项系数（韦达定理的倒数根形式）*)
(** c · ∏_{k=1}^n (1 - y/r_k) = c - c·(Σ1/r_k)·y + y²·S(y) *)

Lemma vieta_product_expansion : forall n c (r : nat -> R),
    (forall k, 1 <= k <= n -> r k <> 0) ->
    exists S : R -> R,
      (forall y, c * prod1 (fun k => 1 - y / r k) n =
                  c - c * (sum1 (fun k => 1 / r k) n) * y + y^2 * S y) /\
      is_poly n S.
Proof.
  induction n.
  - intros c r H. exists (fun _ => 0).
    split; [intros y; simpl; ring | apply is_poly_const].
  - intros c r H.
    destruct (IHn c (fun k => r k) (fun k Hk => H k (Nat.lt_succ_r _ _ Hk)))
      as [S [HS HSpoly]].
    set (S' := fun y => S y - c * (sum1 (fun k => 1 / r k) n) / r (S n)
                       - y * S y / r (S n)).
    exists S'.
    split.
    + intros y.
      rewrite prod1_S, HS.
      unfold S'.
      have Hr_nonzero : r (S n) <> 0 by (apply H; split; lra).
      field; split; [lra | |]; try lra.
      (* field 生成的子目标：分母不为零 *)
      1: exact Hr_nonzero.
      2: exact Hr_nonzero.
    + (* S' 是多项式：S 是多项式，常数、y*S、除以非零常数都是多项式 *)
      have H1 : is_poly n S by exact HSpoly.
      have H2 : is_poly n (fun y => y * S y).
      { apply is_poly_y_mult. exact H1. }
      have H3 : is_poly n (fun y => S y - c * (sum1 (fun k => 1 / r k) n) / r (S n) - y * S y / r (S n)).
      { apply is_poly_minus.
        - apply is_poly_minus.
          + exact H1.
          + apply is_poly_scale with (n := n). apply is_poly_weaken with (m := O) (n := n). apply is_poly_const.
        - apply is_poly_scale with (n := n). exact H2. }
      unfold S' in *. exact H3.
Qed.

(* ====================================================================== *)
(** ** 系数比较引理 *)
(** 若 a + b·y + y²·S(y) = a + c·y + y²·T(y) 对所有 y 成立，
    且 S, T 是多项式，则 b = c。
    证明：D(y) = (b-c)y + y²(S-T) ≡ 0。D(y) = y·D1(y)，其中
    D1(y) = (b-c) + y(S-T)。D1 在所有非零点为 0，由多项式唯一性 D1≡0，
    故 D1(0) = b-c = 0。*)

Lemma coeff_compare_general : forall n m a b c S T,
    is_poly n S -> is_poly m T ->
    (forall y, a + b*y + y^2*S y = a + c*y + y^2*T y) ->
    b = c.
Proof.
  intros n m a b c S T HSpoly HTpoly Heq.
  set (D := fun y => (b - c) * y + y^2 * (S y - T y)).
  set (D1 := fun y => (b - c) + y * (S y - T y)).
  have D_eq : forall y, D y = y * D1 y.
  { intros y; unfold D, D1; ring. }
  have D_zero : forall y, D y = 0.
  { intros y. have H := Heq y. unfold D; lra. }
  have D1_poly : is_poly (S (max n m)) D1.
  { unfold D1.
    set (K := max n m).
    have HnK : n <= K by apply Nat.le_max_l.
    have HmK : m <= K by apply Nat.le_max_r.
    have HS' : is_poly K S.
    { have H : is_poly (n + (K - n)) S by (apply is_poly_weaken; exact HSpoly).
      have Heq : n + (K - n) = K by (apply Nat.add_sub_of_le; exact HnK).
      rewrite Heq in H. exact H. }
    have HT' : is_poly K T.
    { have H : is_poly (m + (K - m)) T by (apply is_poly_weaken; exact HTpoly).
      have Heq : m + (K - m) = K by (apply Nat.add_sub_of_le; exact HmK).
      rewrite Heq in H. exact H. }
    have HST : is_poly K (fun y => S y - T y) by (apply is_poly_minus; exact HS' || exact HT').
    have HyST : is_poly (S K) (fun y => y * (S y - T y)) by (apply is_poly_y_mult; exact HST).
    have Hconst : is_poly (S K) (fun _ => b - c).
    { apply is_poly_weaken with (m := O) (n := S K). apply is_poly_const. }
    have Hsum : is_poly (S K) (fun y => (b - c) + y * (S y - T y)).
    { apply is_poly_plus; exact Hconst || exact HyST. }
    unfold K in Hsum. exact Hsum. }
  (* D1 在 1, 2, ..., N+1 处为 0（N = max n m + 1），故 D1 ≡ 0 *)
  have D1_nonzero_roots : forall y, y <> 0 -> D1 y = 0.
  { intros y Hy. have H := D_zero y. rewrite D_eq in H.
    apply (Rmult_eq_reg_l y Hy). lra. }
  (* 取 N+1 个不同的正整数点 *)
  set (N := S (max n m)).
  have Hroots : exists (r : nat -> R),
      (forall i j, i < S N -> j < S N -> i <> j -> r i <> r j) /\
      (forall i, i < S N -> D1 (r i) = 0).
  { exists (fun i => INR (S i)).
    split.
    - intros i j _ _ Hne. apply INR_lt. lra.
    - intros i _. apply D1_nonzero_roots. have H : INR (S i) <> 0 by (apply INR_lt; lra). exact H. }
  have D1_zero : forall y, D1 y = 0 by (apply poly_max_roots with (n := N) (P := D1); trivial).
  have H := D1_zero 0. unfold D1 in H. lra.
Qed.

(* ====================================================================== *)
(** ** n 元韦达定理 *)
(** 对 n 次多项式 a_n x^n + a_{n-1}x^{n-1} + ... + a_0，
    若 a_n ≠ 0 且可分解为 a_n·∏(x-r_k)，则 Σ r_k = -a_{n-1}/a_n。*)

(** 引理：若 Σ_{i=0}^n c_i y^i = 0 对所有 y 成立，则所有 c_i = 0 *)
Lemma all_coeffs_zero : forall n (c : nat -> R),
    (forall y, sum0 (fun i => c i * y^i) n = 0) ->
    forall i, i <= n -> c i = 0.
Proof.
  induction n.
  - intros c H i Hi. have H0 : c O = 0 by (have H1 := H 0; simpl in H1; lra).
    have Hi0 : i = O by (inversion Hi; reflexivity). rewrite Hi0. exact H0.
  - intros c H i Hi.
    have Hc0 : c O = 0 by (have H1 := H 0; simpl in H1; lra).
    (* 对 y ≠ 0：y * Σ_{j=0}^{n} c_{j+1} y^j = 0 ⇒ Σ c_{j+1} y^j = 0 *)
    set (d := fun j => c (S j)).
    have Hd_nonzero : forall y, y <> 0 -> sum0 (fun j => d j * y^j) n = 0.
    { intros y Hy.
      have H2 : sum0 (fun k => c k * y^k) (S n) = c O + y * sum0 (fun j => d j * y^j) n.
      { induction n; simpl; [unfold d; simpl; ring | unfold d in *; simpl; rewrite IHn; ring]. }
      have H3 := H y. rewrite H2 in H3. rewrite Hc0 in H3.
      apply (Rmult_eq_reg_l y Hy). lra. }
    (* Σ d_j y^j 在 1,2,...,n+1 处为 0（n+1 个不同点），故恒为 0 *)
    have Hd_all : forall y, sum0 (fun j => d j * y^j) n = 0.
    { have Hroots : exists (r : nat -> R),
        (forall i j, i < S n -> j < S n -> i <> j -> r i <> r j) /\
        (forall i, i < S n -> sum0 (fun j => d j * (r i)^j) n = 0).
      { exists (fun k => INR (S k)).
        split.
        - intros i j _ _ Hne. apply INR_lt. lra.
        - intros k _. apply Hd_nonzero. have H : INR (S k) <> 0 by (apply INR_lt; lra). exact H. }
      have Hpoly : is_poly n (fun y => sum0 (fun j => d j * y^j) n).
      { exists d. intros y; reflexivity. }
      exact (poly_max_roots n _ Hpoly Hroots). }
    have Hall : forall j, j <= n -> d j = 0 by (apply IHn; exact Hd_all).
    destruct i as [|i'].
    + exact Hc0.
    + have H4 : i' <= n by (inversion Hi; lra).
      have H5 : d i' = 0 by (apply Hall; exact H4).
      unfold d in H5. exact H5.
Qed.

(** 先证：∏_{k=1}^n (y-r_k) 的系数满足 b_n=1, b_{n-1}=-Σr_k *)
Lemma product_coeffs : forall n (r : nat -> R),
    exists (b : nat -> R),
      (forall y, prod1 (fun k => y - r k) n = sum0 (fun i => b i * y^i) n) /\
      (n >= 1 -> b n = 1 /\ b (n - 1) = -sum1 r n).
Proof.
  induction n.
  - exists (fun i => match i with O => 1 | _ => 0 end).
    split.
    + intros y; simpl; ring.
    + intros H; exfalso; lra.
  - destruct IHn as [b [Hb Hbn]].
    (* 新系数 c_i：c_{n+1}=b_n, c_i = b_{i-1} - r_{n+1} b_i (1≤i≤n), c_0 = -r_{n+1} b_0 *)
    set (c := fun i => match i with
           | O => -r (S n) * b O
           | S i => b i - r (S n) * b (S i)
           end).
    exists c.
    split.
    + intros y. rewrite prod1_S, Hb.
      (* (Σ b_i y^i) * (y - r_{n+1}) = Σ c_i y^i *)
      induction n.
      * simpl; unfold c; simpl; ring.
      * simpl sum0. unfold c at 1; simpl. rewrite IHn. ring.
    + intros Hge.
      split.
      * (* c (S n) = b n = 1 *)
        unfold c. simpl. have H5 := Hbn (by lra). destruct H5 as [H5 _]. exact H5.
      * (* c n = b (n-1) - r_{n+1} * b n = -sum1 r n - r_{n+1} = -sum1 r (S n) *)
        unfold c. simpl.
        have H5 := Hbn (by lra). destruct H5 as [_ H6].
        rewrite H6. have H7 : b n = 1 by (have H8 := Hbn (by lra); destruct H8; exact H8).
        rewrite H7. simpl sum1. ring.
Qed.

Theorem vieta_sum_roots : forall n (a : nat -> R) (roots : nat -> R),
    n >= 1 -> a n <> 0 ->
    (forall y, sum0 (fun i => a i * y^i) n = a n * prod1 (fun k => y - roots k) n) ->
    sum1 (fun k => roots k) n = - a (n - 1) / a n.
Proof.
  intros n a roots Hn Hlead Hfactor.
  destruct (product_coeffs n roots) as [b [Hb Hbn]].
  have Hcoeffs := Hbn Hn.
  destruct Hcoeffs as [Hbn1 Hbn2].
  (* 两个多项式相等：Σ a_i y^i = a_n * Σ b_i y^i = Σ (a_n * b_i) y^i *)
  have Heq : forall y, sum0 (fun i => a i * y^i) n = sum0 (fun i => a n * b i * y^i) n.
  { intros y. rewrite Hfactor, Hb.
    have H : a n * sum0 (fun i => b i * y^i) n = sum0 (fun i => a n * b i * y^i) n.
    { induction n; simpl; try ring. rewrite IHn. ring. }
    exact H. }
  (* 由多项式相等推出系数相等：设 d_i = a_i - a_n * b_i，则 Σ d_i y^i = 0 *)
  set (d := fun i => a i - a n * b i).
  have Hd : forall y, sum0 (fun i => d i * y^i) n = 0.
  { intros y. unfold d.
    have H : sum0 (fun i => (a i - a n * b i) * y^i) n =
             sum0 (fun i => a i * y^i) n - sum0 (fun i => a n * b i * y^i) n.
    { induction n; simpl; try ring. rewrite IHn. ring. }
    rewrite H, Heq. ring. }
  have Hall : forall i, i <= n -> d i = 0 by (apply all_coeffs_zero; exact Hd).
  have H_a_n : a n = a n * b n.
  { have H := Hall n (by lra). unfold d in H. lra. }
  have H_a_n1 : a (n - 1) = a n * b (n - 1).
  { have H := Hall (n - 1) (by lra). unfold d in H. lra. }
  rewrite H_a_n1, Hbn2. field; lra.
Qed.
