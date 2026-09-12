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
Proof. Admitted.

Lemma sum0_append_zero : forall (a : nat -> R) (m n : nat) (y : R),
    (forall i : nat, m < i -> a i = 0) ->
    sum0 (fun i => a i * y^i) (m + n) = sum0 (fun i => a i * y^i) m.
Proof. Admitted.

(* ====================================================================== *)
(** ** 多项式的基本封闭性 *)

Lemma is_poly_const : forall c, is_poly O (fun _ => c).
Proof. Admitted.

Lemma is_poly_weaken : forall m n P, is_poly m P -> is_poly (m + n) P.
Proof. Admitted.

Lemma is_poly_plus : forall n : nat, P Q,
    is_poly n P -> is_poly n Q -> is_poly n (fun y => P y + Q y).
Proof. Admitted.

Lemma is_poly_neg : forall n : nat, P, is_poly n P -> is_poly n (fun y => -P y).
Proof. Admitted.

Lemma is_poly_minus : forall n : nat, P Q,
    is_poly n P -> is_poly n Q -> is_poly n (fun y => P y - Q y).
Proof. Admitted.

Lemma is_poly_scale : forall n : nat, c P, is_poly n P -> is_poly n (fun y => c * P y).
Proof. Admitted.

(** y * P(y) 是多项式：若 P 次数 ≤ n，则 y*P 次数 ≤ S n *)
Lemma is_poly_y_mult : forall n : nat, P, is_poly n P -> is_poly (S n) (fun y => y * P y).
Proof. Admitted.

(** y^k * P 是多项式：若 P 次数 ≤ n，则 y^k*P 次数 ≤ n+k *)
Lemma is_poly_y_pow : forall k n P, is_poly n P -> is_poly (n + k) (fun y => y^k * P y).
Proof. Admitted.

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
Proof. Admitted.

(** geo_sum r y n 是 y 的 n 次多项式 *)
Lemma geo_sum_is_poly : forall r n, is_poly n (fun y => geo_sum r y n).
Proof. Admitted.

Lemma factor_theorem : forall n : nat, P r,
    is_poly (S n) P -> P r = 0 ->
    exists Q, is_poly n Q /\ forall y, P y = (y - r) * Q y.
Proof. Admitted.

(* ====================================================================== *)
(** ** 根的个数上界 *)

Lemma poly_max_roots : forall n : nat, P,
    is_poly n P ->
    (exists (r : nat -> R), (forall i j : nat, i < S n -> j < S n -> i <> j -> r i <> r j) /\
      (forall i : nat, i < S n -> P (r i) = 0)) ->
    forall y, P y = 0.
Proof. Admitted.

(* ====================================================================== *)
(** ** 多项式唯一性 *)

Lemma poly_unique : forall n : nat, P Q,
    is_poly n P -> is_poly n Q ->
    (exists (r : nat -> R),
      (forall i j : nat, i < S n -> j < S n -> i <> j -> r i <> r j) /\
      (forall i : nat, i < S n -> P (r i) = Q (r i))) ->
    forall y, P y = Q y.
Proof. Admitted.

(* ====================================================================== *)
(** ** 乘积展开的一次项系数（韦达定理的倒数根形式）*)
(** c · ∏_{k=1}^n (1 - y/r_k) = c - c·(Σ1/r_k)·y + y²·S(y) *)

Lemma vieta_product_expansion : forall n : nat, c (r : nat -> R),
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

Lemma coeff_compare_general : forall n : nat, m a b c S T,
    is_poly n S -> is_poly m T ->
    (forall y, a + b*y + y^2*S y = a + c*y + y^2*T y) ->
    b = c.
Proof. Admitted.

(* ====================================================================== *)
(** ** n 元韦达定理 *)
(** 对 n 次多项式 a_n x^n + a_{n-1}x^{n-1} + ... + a_0，
    若 a_n ≠ 0 且可分解为 a_n·∏(x-r_k)，则 Σ r_k = -a_{n-1}/a_n。*)

(** 引理：若 Σ_{i=0}^n c_i y^i = 0 对所有 y 成立，则所有 c_i = 0 *)
Lemma all_coeffs_zero : forall n (c : nat -> R),
    (forall y, sum0 (fun i => c i * y^i) n = 0) ->
    forall i : nat, i <= n -> c i = 0.
Proof. Admitted.

(** 先证：∏_{k=1}^n (y-r_k) 的系数满足 b_n=1, b_{n-1}=-Σr_k *)
Lemma product_coeffs : forall n (r : nat -> R),
    exists (b : nat -> R),
      (forall y, prod1 (fun k => y - r k) n = sum0 (fun i => b i * y^i) n) /\
      (n >= 1 -> b n = 1 /\ b (n - 1) = -sum1 r n).
Proof. Admitted.

Theorem vieta_sum_roots : forall n (a : nat -> R) (roots : nat -> R),
    n >= 1 -> a n <> 0 ->
    (forall y, sum0 (fun i => a i * y^i) n = a n * prod1 (fun k => y - roots k) n) ->
    sum1 (fun k => roots k) n = - a (n - 1) / a n.
Proof. Admitted.
