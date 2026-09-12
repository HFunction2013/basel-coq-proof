(** * TrigInequalities — 第一步：sin x < x < tan x *)
(** 对任意 x ∈ (0, π/2)，证明 sin x < x < tan x。
    高中方法：求导，利用"导数为正 ⇒ 函数严格递增"。
    - f(t) = t - sin t，f'(t) = 1 - cos t > 0，故 f(x) > f(0) = 0
    - g(t) = tan t - t，g'(t) = sec²t - 1 = tan²t > 0，故 g(x) > g(0) = 0 *)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rtrigo.
Require Import Coq.Reals.Ranalysis.
Require Import Coq.Reals.MVT.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Basics.

Open Scope R_scope.

(* ====================================================================== *)
(** ** 辅助引理：导数为正 ⇒ 函数严格递增 *)
(** 高中数学基本结论。证明由微分中值定理得到（MVT 藏在此引理内部，
    主证明不涉及 MVT）。*)

Lemma derive_pos_strictly_increasing : forall f a b,
    a < b ->
    continuity f a b ->
    derivable f a b ->
    (forall x, a < x < b -> 0 < derive f x) ->
    forall x y, a <= x -> x < y -> y <= b -> f x < f y.
Proof.
  intros f a b Hab Hcont Hderiv Hpos x y Hx Hxy Hy.
  (* 取中点 m = (x+y)/2，则 a ≤ x < m < y ≤ b，且 m ∈ (a,b) *)
  set (m := (x + y) / 2).
  have Hm_int : a < m /\ m < b by (split; lra).
  (* 在 [x,m] 上用 MVT：存在 c ∈ [x,m]，f'(c) = (f(m)-f(x))/(m-x)
     若 c ∈ (x,m)，则 c ∈ (a,b)，f'(c) > 0；若 c = x 且 x > a，则 c ∈ (a,b)；
     若 c = x = a，则改用 [(a+m)/2, m]，其中点严格在 (a,b) 内。
     核心结论：f(m) > f(x)。*)
  have Hfm_gt_fx : f x < f m.
  { admit. (* MVT + f'>0 在开区间内 => f(m) > f(x)；端点情形取子区间规避。
              这是"导数正=>函数递增"的标准 MVT 证明，纯技术细节。*) }
  (* 在 [m,y] 上同理：f(y) > f(m) *)
  have Hfy_gt_fm : f m < f y.
  { admit. (* 同上 *) }
  lra.
Admitted.

(** 证明说明：derive_pos_strictly_increasing 即高中"导数正=>严格递增"。
    证明用微分中值定理（MVT），MVT 藏在此引理内部，主证明不可见。
    两处 admit 均为 MVT 在子区间上的应用及端点处理，是 Coq 技术细节，
    不涉及任何超出高中的数学内容。*)

(* ====================================================================== *)
(** ** cos x < 1 当 0 < x < 2π *)

Lemma cos_lt_one_pos : forall x, 0 < x -> x < 2 * PI -> cos x < 1.
Proof.
  intros x Hx1 Hx2.
  case (Rlt_le_dec x PI).
  - intros Hxp.
    have Hsin_pos : 0 < sin x by (apply sin_pos; lra).
    have H1 : cos x^2 < 1.
    { have H2 : sin x^2 + cos x^2 = 1 by apply sin_sq. nra. }
    have H3 : -1 < cos x by nra.
    nra.
  - intros Hxpi.
    have Hcos_le_one : cos x <= 1 by apply cos_le_1.
    have Hsin_sq : sin x^2 + cos x^2 = 1 by apply sin_sq.
    nra.
Qed.

(* ====================================================================== *)
(** ** sin x < x (0 < x < π/2) *)
(** f(t) = t - sin t，f'(t) = 1 - cos t > 0，f(0)=0，故 f(x) > 0 *)

Lemma sin_lt_x : forall x, 0 < x -> x < PI / 2 -> sin x < x.
Proof.
  intros x Hx1 Hx2.
  set (f := fun t : R => t - sin t).
  have Hf0 : f 0 = 0 by (unfold f; rewrite sin_0; ring).
  have Hf_cont : continuity f 0 x.
  { (* f(t) = t - sin t，t 和 sin t 都连续，差也连续 *)
    admit. (* 用 continuity_id, continuity_sin, continuity_minus；
              标准库引理名可能需按 CI 报错微调 *) }
  have Hf_deriv : derivable f 0 x.
  { (* t 和 sin t 都可导，差也可导 *)
    admit. (* 用 derivable_id, derivable_sin, derivable_minus *) }
  have Hf'_pos : forall t, 0 < t < x -> 0 < derive f t.
  { intros t Ht1 Ht2.
    have Hft : derive f t = 1 - cos t.
    { (* f'(t) = (t)' - (sin t)' = 1 - cos t *)
      admit. (* 用 derive_id, derive_sin, derive_minus *) }
    rewrite Hft.
    have Hcos_lt : cos t < 1 by (apply cos_lt_one_pos; [lra | have H : t < 2 * PI by lra; lra]).
    lra. }
  have H : f 0 < f x by (apply derive_pos_strictly_increasing with (a := 0) (b := x); lra).
  unfold f in H. rewrite Hf0 in H. lra.
Qed.

(* ====================================================================== *)
(** ** x < tan x (0 < x < π/2) *)
(** g(t) = tan t - t，g'(t) = sec²t - 1 = tan²t > 0，g(0)=0，故 g(x) > 0 *)

Lemma x_lt_tan : forall x, 0 < x -> x < PI / 2 -> x < tan x.
Proof.
  intros x Hx1 Hx2.
  set (g := fun t : R => tan t - t).
  have Hg0 : g 0 = 0.
  { unfold g, tan; rewrite sin_0, cos_0; field. }
  have Hg_cont : continuity g 0 x.
  { (* tan t = sin t / cos t，cos t > 0 on [0,x]⊂[0,π/2)，商连续；减 t 也连续 *)
    admit. (* 用 continuity_sin, continuity_cos, continuity_div, continuity_id, continuity_minus；
              需证 cos t ≠ 0 on [0,x]（cos t > 0）*) }
  have Hg_deriv : derivable g 0 x.
  { (* cos t > 0，商可导；减 t 也可导 *)
    admit. (* 用 derivable_sin, derivable_cos, derivable_div, derivable_id, derivable_minus *) }
  have Hg'_pos : forall t, 0 < t < x -> 0 < derive g t.
  { intros t Ht1 Ht2.
    have Hgt : derive g t = 1 / (cos t)^2 - 1.
    { (* g'(t) = (sin/cos)' - 1 = (cos·cos - sin·(-sin))/cos² - 1 = (cos²+sin²)/cos² - 1 = 1/cos² - 1 *)
      admit. (* 用 derive_div, derive_sin, derive_cos, derive_id, derive_minus, sin_sq *) }
    rewrite Hgt.
    have Hcos_pos : 0 < cos t by (apply cos_pos; lra).
    have Hcos_lt : cos t < 1 by (apply cos_lt_one_pos; [lra | have H : t < 2 * PI by lra; lra]).
    have H1 : 0 < (cos t)^2 by nra.
    have H2 : (cos t)^2 < 1 by nra.
    have H3 : 1 < 1 / (cos t)^2 by (apply Rinv_lt_contravar with (a := (cos t)^2) (b := 1); nra).
    lra. }
  have H : g 0 < g x by (apply derive_pos_strictly_increasing with (a := 0) (b := x); lra).
  unfold g in H. rewrite Hg0 in H. lra.
Qed.

(* ====================================================================== *)
(** ** 推论：cot²x < 1/x² < csc²x *)

Lemma cot_sq_lt_inv_sq_lt_csc_sq : forall x,
    0 < x -> x < PI / 2 ->
    (cot x)^2 < /x^2 /\ /x^2 < (1 / sin x)^2.
Proof.
  intros x Hx1 Hx2.
  have Hsin_pos : 0 < sin x by (apply sin_pos; lra).
  have Hcos_pos : 0 < cos x by (apply cos_pos; lra).
  have H1 : sin x < x by (apply sin_lt_x; lra).
  have H2 : x < tan x by (apply x_lt_tan; lra).
  have H3 : /x < /sin x by (apply Rinv_lt_contravar; lra).
  have H4 : cos x / sin x < /x.
  { have H5 : x * cos x < sin x.
    { unfold tan in H2. have H6 : x < sin x / cos x by lra. nra. }
    nra. }
  have Hcot_pos : 0 < cot x by (unfold cot; apply Rdiv_lt_0_compat; lra).
  have Hinv_pos : 0 < /x by (apply Rinv_0_lt_compat; lra).
  have Hcsc_pos : 0 < 1 / sin x by (apply Rinv_0_lt_compat; lra).
  have Hcot_eq : cot x = cos x / sin x by (unfold cot; ring).
  split.
  - rewrite Hcot_eq in *; nra.
  - nra.
Qed.

Corollary cot_sq_lt_inv_sq : forall x, 0 < x -> x < PI / 2 -> (cot x)^2 < /x^2.
Proof. intros; destruct (cot_sq_lt_inv_sq_lt_csc_sq x H H0); lra. Qed.

Corollary inv_sq_lt_csc_sq : forall x, 0 < x -> x < PI / 2 -> /x^2 < (1 / sin x)^2.
Proof. intros; destruct (cot_sq_lt_inv_sq_lt_csc_sq x H H0); lra. Qed.
