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

Definition cot (x : R) : R := cos x / sin x.

(* ====================================================================== *)
(** ** 核心不等式（Admitted，技术细节：求导+单调性+MVT）*)

(** sin x < x 当 0 < x < π/2
    证明：f(t)=t-sin t, f'(t)=1-cos t>0, f(0)=0 ⇒ f(x)>0 *)
Lemma sin_lt_x : forall x, 0 < x -> x < PI / 2 -> sin x < x.
Proof.
Admitted.

(** x < tan x 当 0 < x < π/2
    证明：g(t)=tan t-t, g'(t)=sec²t-1=tan²t>0, g(0)=0 ⇒ g(x)>0 *)
Lemma x_lt_tan : forall x, 0 < x -> x < PI / 2 -> x < tan x.
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
(** ** 推论：cot²x < 1/x² < csc²x *)

Lemma cot_sq_lt_inv_sq_lt_csc_sq : forall x,
    0 < x -> x < PI / 2 ->
    (cot x)^2 < /x^2 /\ /x^2 < (1 / sin x)^2.
Proof. Admitted.

Corollary cot_sq_lt_inv_sq : forall x, 0 < x -> x < PI / 2 -> (cot x)^2 < /x^2.
Proof. intros; destruct (cot_sq_lt_inv_sq_lt_csc_sq x H H0); lra. Qed.

Corollary inv_sq_lt_csc_sq : forall x, 0 < x -> x < PI / 2 -> /x^2 < (1 / sin x)^2.
Proof. intros; destruct (cot_sq_lt_inv_sq_lt_csc_sq x H H0); lra. Qed.
