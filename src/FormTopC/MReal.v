Require Import 
  FormTopC.FormTop
  FormTopC.Cont
  Algebra.OrderC
  Algebra.PreOrder
  Numbers.QPosFacts
  CoRN.metric2.Metric
  FormTopC.Metric
  CoRN.model.totalorder.QposMinMax
  QArith.Qminmax
  CoRN.algebra.COrdAbs
  CoRN.model.ordfields.Qordfield
  CoRN.model.metric2.Qmetric
  CoRN.metric2.ProductMetric
  Coq.micromega.Lra
  Algebra.SetsC.

Definition unit_RSetoid : RSetoid.
Proof.
refine (
  {| st_car := unit
   ; st_eq := fun _ _ => True |}); firstorder.
Defined. 

(* One-point metric space *)
Definition MOne : MetricSpace.
Proof.
unshelve econstructor.
- exact (unit_RSetoid).
	- exact (fun e _ _ => (0 <= e)%Q).
- simpl. intros. split; intros.
  + exact
      (proj1 (Qle_comp 0 0 (Qeq_refl 0) _ _ H) H0).
  + exact
      (proj2 (Qle_comp 0 0 (Qeq_refl 0) _ _ H) H0).
- simpl. constructor.
  + intros e He x. exact He.
  + intros e x y He. exact He.
  + intros e1 e2 x y z He1 He2.
    exact (Qplus_le_compat 0 e1 0 e2 He1 He2).
  + intros e x y He.
    apply Qnot_lt_le. intros Hneg.
    assert (Hopp : (0 < - e)%Q).
    { change (- 0 < - e)%Q. apply Qopp_lt_compat. exact Hneg. }
    assert (Hhalf : (0 < (1#2))%Q) by reflexivity.
    assert (Hpos : (0 < (- e) * (1#2))%Q).
    { apply Qmult_lt_0_compat; assumption. }
    specialize (He ((- e) * (1#2))%Q Hpos).
    assert (Hprod : (e * (1#2) < 0 * (1#2))%Q).
    { apply Qmult_lt_compat_r; assumption. }
    assert (Hsum : (e + (- e) * (1#2) == e * (1#2))%Q) by ring.
    assert (Hzero : (0 == 0 * (1#2))%Q) by ring.
    pose proof
      (proj2
         (Qlt_compat (e + (- e) * (1#2))%Q (e * (1#2))%Q Hsum
            0%Q (0 * (1#2))%Q Hzero)
         Hprod) as Hlt.
    exact (Qlt_not_le _ _ Hlt He).
  + intros e x y He. exact He.
  + intros e x y Hnn.
    destruct (Q_dec 0 e) as [[Hlt | Hgt] | Heq].
    * apply Qlt_le_weak. exact Hlt.
    * exfalso. apply Hnn. intros Hle.
      exact (Qlt_not_le _ _ Hgt Hle).
    * apply (proj2 (Qle_lteq 0 e)). right. exact Heq.
Defined.

Import Metric.

Existing Instances PreO PreO.PreOrder_I.

Lemma tt_cont :
  IGCont.pt (FormalSpace.IGS Metric) (fun _ : Ball MOne => True).
Proof.
constructor.
- exists (tt, Qpos1). unfold In. auto.
- intros. destruct b, c. destruct m, m0.
  exists (tt, Qpos_min q q0). split.
  split; le_down; apply le_ball_center.
  apply Qpos_min_lb_l. apply Qpos_min_lb_r.
  auto.
- auto.
- intros a c ix l H. destruct ix. 
  destruct a, c. destruct H. destruct m, m0.
  simpl.
  + exists (tt, Qpos_min q0 q). split. auto.
    split. le_down. apply le_ball_center. apply Qpos_min_lb_l.
    exists (tt, q). reflexivity.
    apply le_ball_center. apply Qpos_min_lb_r.
  + simpl in *. destruct a, c, H.
    destruct m, m0.
    destruct (Qpos_smaller q).
    exists (tt, x). split. auto.
    split. le_down.
    apply le_ball_center. apply Qlt_le_weak. assumption.
    exists (tt, x). unfold In. apply lt_ball_center.
    apply (@le_ball_radius MOne (tt, q) (tt, q0)) in l. 
    simpl in l.
    eapply Qlt_le_trans; eassumption. reflexivity.
Qed.

Section Yoneda.
Context {X : MetricSpace}.

Lemma from_One_lip
  (f : MOne -> X) (k : Qpos) : Lipschitz f k.
Proof.
unfold Lipschitz.
simpl. intros. destruct x, x'.
apply ball_refl.
apply Qmult_le_0_compat.
apply Qpossec.Qpos_nonneg. exact H.
Qed.

(** Applying this map to the unique point in the
    one-point space will give us the point which is
    the embedding of
    [x: X] into its metric completion.
*)
Definition from_One_cont (x : X) :
  IGCont.t
    (toPSL (FormalSpace.IGS (@Metric MOne)))
    (FormalSpace.IGS (@Metric X))
  (lift (fun _ : MOne => x) Qpos1).
Proof.
apply Cont. apply from_One_lip.
Qed.

End Yoneda.

(** Now let's get to the real numbers. *)

Definition MQ : MetricSpace := Q_as_MetricSpace.

Definition binop (f : MQ -> MQ -> MQ) (p : ProductMS MQ MQ) : MQ :=
  let (x, y) := p in f x y.

Lemma Qle_eq {x y : Q} : x == y -> x <= y.
Proof.
intros xeqy. rewrite xeqy. reflexivity.
Qed.

Lemma plus_Lip : Lipschitz (binop Qplus) (Qpos1 + Qpos1).
Proof.
unfold Lipschitz. intros. 
destruct x, x', H.
unfold binop.
eapply ball_weak_le.
Focus 2.  eapply Qball_plus; eassumption.
simpl. apply Qle_eq. ring.
Qed.

Local Open Scope Q.

(* This lemma is taken from 
  [QboundBelow_uc_prf] here:
  https://github.com/robbertkrebbers/corn/blob/8b864e218dd1a682746c25c4b56e225f120be957/reals/fast/CRGroupOps.v#L396
*)
Lemma Qball_between :
 forall e a b0 b1, Qball e b0 b1 -> b0 <= a <= b1 -> Qball e a b1.
Proof.
  intros e a b0 b1 H [H1 H2].
  unfold Qball in *.
  unfold AbsSmall in *.
  destruct H as [Hlo Hhi].
  split.
   apply Qle_trans with (b0-b1).
    exact Hlo.
   apply (minus_resp_leEq _ b0).
   assumption.
  apply Qle_trans with 0.
   apply (shift_minus_leEq _ a).
   stepr b1.
    assumption.
   simpl; ring.
  assert (Hb : (b0 <= b1)%Q) by (eapply Qle_trans; eassumption).
  assert (Hdiff : (b0 - b1 <= 0)%Q).
  { apply (shift_minus_leEq _ b0).
    stepr b1. exact Hb. simpl; ring. }
  pose proof (Qle_trans _ _ _ Hlo Hdiff) as Hminus.
  pose proof (Qopp_le_compat _ _ Hminus) as Hnonneg.
  setoid_replace (- - e)%Q with e in Hnonneg by ring.
  exact Hnonneg.
Qed.


Lemma max_Lip : Lipschitz (binop Qmax) Qpos1.
Proof.
unfold Lipschitz. intros.
destruct x, x', H. unfold binop. simpl.
simpl in *.
eapply ball_weak_le. eapply Qle_eq. simpl. ring_simplify.
reflexivity.
apply Q.max_case_strong.
intros. rewrite <- H1.  assumption.
apply Q.max_case_strong. intros. rewrite <- H1.
auto. auto. intros.
eapply Qball_between.
admit. admit.
apply Q.max_case_strong. intros. rewrite <- H1. auto.
intros. 
admit. 
auto.
Admitted.

Lemma min_Lip : Lipschitz (binop Qmin) Qpos1.
Admitted.
