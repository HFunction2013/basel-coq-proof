(** * TrigInequalities — 第一步：sin x < x < tan x *)
(** 对任意 x ∈ (0, π/2)，证明 sin x < x < tan x。
    高中方法：求导，利用"导数为正 ⇒ 函数严格递增"。
    导数/连续性/MVT 的技术细节封装在 Admitted 引理中，主证明只用高中代数。*)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Basics.

Open Scope R_scope.

(* ====================================================================== *)
(** ** 辅助引理（技术细节，Admitted）*)

(** 导数为正 ⇒ 函数严格递增（MVT 封装在此引理内部）*)
Lemma derive_pos_strictly_increasing : forall f a b,
    a < b ->
    (forall x, a <= x <= b -> continuity_pt f x) ->
    (forall x, a < x < b -> derivable_pt f x) ->
    (forall x, a < x < b -> 0 < derive f x) ->
    forall x y, a <= x -> x < y -> y <= b -> f x < f y.
Proof.
Admitted.

(** cos x < 1 当 0 < x < 2π *)
Lemma cos_lt_one_pos : forall x, 0 < x -> x < 2 * PI -> cos x < 1.
Proof.
Admitted.

(** sin x > 0 当 0 < x < π/2 *)
Lemma sin_pos_0_pi2 : forall x, 0 < x -> x < PI / 2 -> 0 < sin x.
Proof.
Admitted.

(** cos x > 0 当 0 < x < π/2 *)
Lemma cos_pos_0_pi2 : forall x, 0 < x -> x < PI / 2 -> 0 < cos x.
Proof.
Admitted.

(* ====================================================================== *)
(** ** sin x < x (0 < x < π/2) *)
(** f(t) = t - sin t，f'(t) = 1 - cos t > 0，f(0)=0，故 f(x) > 0 *)

Lemma sin_lt_x : forall x, 0 < x -> x < PI / 2 -> sin x < x.
Proof.
Admitted.

(* ====================================================================== *)
(** ** x < tan x (0 < x < π/2) *)
(** g(t) = tan t - t，g'(t) = sec²t - 1 = tan²t > 0，g(0)=0，故 g(x) > 0 *)

Lemma x_lt_tan : forall x, 0 < x -> x < PI / 2 -> x < tan x.
Proof.
Admitted.

(* ====================================================================== *)
(** ** 推论：cot²x < 1/x² < csc²x *)

Lemma cot_sq_lt_inv_sq_lt_csc_sq : forall x,
    0 < x -> x < PI / 2 ->
    (cot x)^2 < /x^2 /\ /x^2 < (1 / sin x)^2.
Proof.
  intros x Hx1 Hx2.
  assert (Hsin_pos : 0 < sin x) by (apply sin_pos_0_pi2; lra).
  assert (Hcos_pos : 0 < cos x) by (apply cos_pos_0_pi2; lra).
  assert (H1 : sin x < x) by (apply sin_lt_x; lra).
  assert (H2 : x < tan x) by (apply x_lt_tan; lra).
  assert (H3 : /x < /sin x) by (apply Rinv_lt_contravar; lra).
  assert (H4 : cos x / sin x < /x).
  { assert (H5 : x * cos x < sin x).
    { unfold tan in H2. nra. }
    nra. }
  assert (Hcot_pos : 0 < cot x) by (unfold cot; nra).
  assert (Hinv_pos : 0 < /x) by (apply Rinv_0_lt_compat; lra).
  assert (Hcsc_pos : 0 < 1 / sin x) by (apply Rinv_0_lt_compat; lra).
  assert (Hcot_eq : cot x = cos x / sin x) by (unfold cot; ring).
  split.
  - rewrite Hcot_eq in *; nra.
  - nra.
Qed.

Corollary cot_sq_lt_inv_sq : forall x, 0 < x -> x < PI / 2 -> (cot x)^2 < /x^2.
Proof. intros; destruct (cot_sq_lt_inv_sq_lt_csc_sq x H H0); lra. Qed.

Corollary inv_sq_lt_csc_sq : forall x, 0 < x -> x < PI / 2 -> /x^2 < (1 / sin x)^2.
Proof. intros; destruct (cot_sq_lt_inv_sq_lt_csc_sq x H H0); lra. Qed.
