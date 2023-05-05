Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.
Require Import DG4iSL_dec.
Require Import DG4iSL_exch.
Require Import DG4iSL_wkn.
Require Import DG4iSL_adm_unBox_L.
Require Import DG4iSL_inv_AndR_AndL.
Require Import DG4iSL_inv_OrL.
Require Import DG4iSL_inv_AtomImpL.
Require Import DG4iSL_inv_AndImpL.
Require Import DG4iSL_inv_OrImpL.
Require Import DG4iSL_inv_ImpImpL_R.
Require Import DG4iSL_inv_ImpImpL_L.
Require Import DG4iSL_inv_ImpR.
Require Import DG4iSL_inv_BoxImpL_R.
Require Export DG4iSL_ctr_prelims1.
Require Import DG4iSL_ctr_prelims2.

Set Implicit Arguments.

(* Now we can prove that contraction is admissible. *)

Theorem G4iSL_ctr_L : forall (m k: nat) s
        (D0 : derrec G4iSL_rules (fun _ => False) s),
        k = (derrec_height D0) ->
          (forall sc A,
          (m = weight_form A) ->
          (@ctr_L A s sc) ->
          derrec G4iSL_rules (fun _ => False) sc).
Proof.
(* Setting up the strong induction on the weight. *)
pose (strong_inductionT (fun (x:nat) => forall (k: nat) s
        (D0 : derrec G4iSL_rules (fun _ => False) s),
        k = (derrec_height D0) ->
          (forall sc A,
          (x = weight_form A) ->
          (@ctr_L A s sc) ->
          derrec G4iSL_rules (fun _ => False) sc))).
apply d. intros n PIH. clear d.

(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : Seq)
(D0 : derrec G4iSL_rules (fun _ : Seq => False) s),
x = derrec_height D0 ->
forall (sc : Seq) (A : MPropF),
n = weight_form A ->
ctr_L A s sc ->
derrec G4iSL_rules (fun _ : Seq => False) sc)).
apply d. intros m SIH. clear d.

assert (DersNil: dersrec (G4iSL_rules) (fun _ : Seq => False) []). apply dersrec_nil.

(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- intros hei sc A ctr. inversion f.
(* D0 ends with an application of rule *)
- intros hei sc A wei ctr. inversion ctr. inversion g.
  (* IdP *)
  * inversion H1. rewrite <- H in H5. inversion H5. subst. assert (InT (# P) (Γ0 ++ A :: Γ1 ++ Γ2)).
    assert (InT (# P) (Γ0 ++ A :: Γ1 ++ A :: Γ2)). rewrite <- H7. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H. destruct H. apply InT_or_app ; auto. inversion i. subst. apply InT_or_app. right.
    apply InT_eq. subst. apply InT_app_or in H0. destruct H0. apply InT_or_app. right. apply InT_cons.
    apply InT_or_app ; auto. inversion i0. subst. apply InT_or_app. right. apply InT_eq. subst. apply InT_or_app.
    right. apply InT_cons. apply InT_or_app ; auto. apply InT_split in H. destruct H. destruct s. rewrite e.
    pose (IdPRule_I P x x0). apply IdP in i. pose (derI _ i DersNil). auto.
  (* BotL *)
  * inversion H1. rewrite <- H in H5. inversion H5. subst. assert (InT (Bot) (Γ0 ++ A :: Γ1 ++ Γ2)).
    assert (InT (Bot) (Γ0 ++ A :: Γ1 ++ A :: Γ2)). rewrite <- H7. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H. destruct H. apply InT_or_app ; auto. inversion i. subst. apply InT_or_app. right.
    apply InT_eq. subst. apply InT_app_or in H0. destruct H0. apply InT_or_app. right. apply InT_cons.
    apply InT_or_app ; auto. inversion i0. subst. apply InT_or_app. right. apply InT_eq. subst. apply InT_or_app.
    right. apply InT_cons. apply InT_or_app ; auto. apply InT_split in H. destruct H. destruct s. rewrite e.
    pose (BotLRule_I x x0 A0). apply BotL in b. pose (derI _ b DersNil). auto.
  (* AndR *)
  * inversion H1. subst. inversion H5. subst. pose (AndR_app_ctr_L ctr H1). repeat destruct s.
    repeat destruct p. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    simpl in SIH.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    assert (E11: weight_form A = weight_form A). auto.
    pose (SIH (derrec_height x1) E (Γ0 ++ A :: Γ1 ++ A :: Γ2, A1) x1 E1 x A E11 c0).
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (SIH (derrec_height x2) E2 (Γ0 ++ A :: Γ1 ++ A :: Γ2, B) x2 E3 x0 A E11 c).
    pose (dlCons d1 DersNil). pose (dlCons d0 d2). apply AndR in a.
    pose (derI _ a d3). auto.
  (* AndL *)
  * inversion H1. subst. inversion H5. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
     pose (AndL_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ A1 :: B :: Γ4, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). apply AndL in a.
        pose (derI _ a d1). auto.
    + assert (J1: derrec_height x = derrec_height x). auto.
       pose (AndR_AndL_hpinv _ _ _ J1). destruct p. clear s0. pose (s _ a0). destruct s0. clear s.
       assert (E: weight_form x0 < weight_form (x0 ∧ x1)). simpl. lia.
       assert (E1: derrec_height x5 = derrec_height x5). auto.
       assert (E11: weight_form x0 = weight_form x0). auto.
       pose (PIH _ E (derrec_height x5) x2 x5 E1 x3 x0 E11 c0).
       assert (E2: weight_form x1 < weight_form (x0 ∧ x1)). simpl. lia.
       assert (E3: derrec_height d0 = derrec_height d0). auto.
       assert (E12: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E2 (derrec_height d0) x3 d0 E3 x4 x1 E12 c).
       pose (dlCons d1 DersNil). apply AndL in a.
       pose (derI _ a d2). auto.
  (* OrR1 *)
  * inversion H1. subst. inversion H5. subst. pose (OrR1_app_ctr_L ctr H1). repeat destruct s.
    repeat destruct p. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    assert (E11: weight_form A = weight_form A). auto.
    pose (SIH (derrec_height x0) E (Γ0 ++ A :: Γ1 ++ A :: Γ2, A1) x0 E1 x A E11 c).
    pose (dlCons d0 DersNil). apply OrR1 in o.
    pose (derI _ o d1). auto.
  (* OrR2 *)
  * inversion H1. subst. inversion H5. subst. pose (OrR2_app_ctr_L ctr H1). repeat destruct s.
    repeat destruct p. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    assert (E11: weight_form A = weight_form A). auto.
    pose (SIH (derrec_height x0) E (Γ0 ++ A :: Γ1 ++ A :: Γ2, B) x0 E1 x A E11 c).
    pose (dlCons d0 DersNil). apply OrR2 in o.
    pose (derI _ o d1). auto.
  (* OrL *)
  * inversion H1. subst. inversion H5. subst.
    repeat destruct p. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    pose (OrL_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ A1 :: Γ4, A0) x E1 x1 A E11 c0).
        assert (E2: derrec_height x0 < S (dersrec_height d)). lia.
        assert (E3: derrec_height x0 = derrec_height x0). auto.
        pose (SIH (derrec_height x0) E2 (Γ3 ++ B :: Γ4, A0) x0 E3 x2 A E11 c).
        pose (dlCons d1 DersNil). pose (dlCons d0 d2). apply OrL in o.
        pose (derI _ o d3). auto.
    + assert (J1: derrec_height x = derrec_height x). auto.
       pose (OrL_hpinv _ _ _ J1 _ _ o1). repeat destruct s. destruct p.
       assert (J2: derrec_height x0 = derrec_height x0). auto.
       pose (OrL_hpinv _ _ _ J2 _ _ o0). repeat destruct s. destruct p.
       assert (E: weight_form x1 < weight_form (x1 ∨ x2)). simpl ; lia.
       assert (E1: derrec_height x9 = derrec_height x9). auto.
       assert (E11: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E (derrec_height x9) x3 x9 E1 x7 x1 E11 c0).
       assert (E2: weight_form x2 < weight_form (x1 ∨ x2)). simpl ; lia.
       assert (E3: derrec_height x12 = derrec_height x12). auto.
       assert (E12: weight_form x2 = weight_form x2). auto.
       pose (PIH _ E2 (derrec_height x12) x6 x12 E3 x8 x2 E12 c).
       pose (dlCons d1 DersNil). pose (dlCons d0 d2). apply OrL in o.
       pose (derI _ o d3). auto.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (ImpR_app_ctr_L ctr H1). destruct s.
    repeat destruct p.
    assert (E: derrec_height x < S (dersrec_height d)). lia.
    assert (E1: derrec_height x = derrec_height x). auto. simpl in SIH.
    assert (E11: weight_form A = weight_form A). auto.
    pose (SIH (derrec_height x) E (Γ3 ++ A1 :: Γ4, B) x E1 x0 A E11 c).
    pose (dlCons d0 DersNil). apply ImpR in i.
    pose (derI _ i d1). auto.
  (* AtomImpL1 *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (AtomImpL1_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto. simpl in SIH.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ # P :: Γ4 ++ A1 :: Γ5, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). apply AtomImpL1 in a.
        pose (derI _ a d1). auto.
    + assert (existsT2 D2 : derrec G4iSL_rules (fun _ : Seq => False) x2,
       derrec_height D2 <= derrec_height x).
       { destruct s0.
          - assert (J40: derrec_height x = derrec_height x). auto.
            pose (AtomImpL1_hpinv _ _ _ J40 _ a). destruct s0. exists x4. lia.
          - assert (J40: derrec_height x = derrec_height x). auto.
            pose (AtomImpL2_hpinv _ _ _ J40 _ a). destruct s0. exists x4. lia. }
       destruct X.
       assert (E: weight_form x1 < weight_form (# x0 → x1)). simpl ; lia.
       assert (E1: derrec_height x4 = derrec_height x4). auto.
       assert (E11: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E (derrec_height x4) x2 x4 E1 x3 x1 E11 c).
       pose (dlCons d0 DersNil). destruct s.
       apply AtomImpL1 in a. pose (derI _ a d1). auto.
       apply AtomImpL2 in a. pose (derI _ a d1). auto.
  (* AtomImpL2 *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (AtomImpL2_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto. simpl in SIH.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ A1 :: Γ4 ++ # P :: Γ5, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). destruct s.
        apply AtomImpL1 in a. pose (derI _ a d1). auto.
        apply AtomImpL2 in a. pose (derI _ a d1). auto.
    + assert (existsT2 D2 : derrec G4iSL_rules (fun _ : Seq => False) x2,
       derrec_height D2 <= derrec_height x).
       { destruct s0.
          - assert (J40: derrec_height x = derrec_height x). auto.
            pose (AtomImpL1_hpinv _ _ _ J40 _ a). destruct s0. exists x4. lia.
          - assert (J40: derrec_height x = derrec_height x). auto.
            pose (AtomImpL2_hpinv _ _ _ J40 _ a). destruct s0. exists x4. lia. }
       destruct X.
       assert (E: weight_form x1 < weight_form (# x0 → x1)). simpl ; lia.
       assert (E1: derrec_height x4 = derrec_height x4). auto.
       assert (E11: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E (derrec_height x4) x2 x4 E1 x3 x1 E11 c).
       pose (dlCons d0 DersNil). destruct s.
       apply AtomImpL1 in a. pose (derI _ a d1). auto.
       apply AtomImpL2 in a. pose (derI _ a d1). auto.
  (* AndImpL *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (AndImpL_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E (Γ3 ++ A1 → B → C :: Γ4, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). apply AndImpL in a. pose (derI _ a d1). auto.
    + assert (J1: derrec_height x = derrec_height x). auto.
       pose (AndImpL_hpinv _ _ _ J1 _ a0). destruct s.
       assert (E: weight_form (x0 → x1 → x2) < weight_form ((x0 ∧ x1) → x2)). simpl ; lia.
       assert (E1: derrec_height x5 = derrec_height x5). auto.
       assert (E11: weight_form (x0 → x1 → x2) = weight_form (x0 → x1 → x2)). auto.
       pose (PIH _ E (derrec_height x5) x3 x5 E1 x4 (x0 → x1 → x2) E11 c).
       pose (dlCons d0 DersNil). apply AndImpL in a. pose (derI _ a d1). auto.
  (* OrImpL *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (OrImpL_app_ctr_L ctr H1). repeat destruct s ; repeat destruct p ; subst.
    +  assert (E: derrec_height x < S (dersrec_height d)). lia.
        assert (E1: derrec_height x = derrec_height x). auto.
        assert (E11: weight_form A = weight_form A). auto.
        pose (SIH (derrec_height x) E  (Γ3 ++ A1 → C :: Γ4 ++ B → C :: Γ5, A0) x E1 x0 A E11 c).
        pose (dlCons d0 DersNil). apply OrImpL in o. pose (derI _ o d1). auto.
    + assert (J1: derrec_height x = derrec_height x). auto.
       pose (OrImpL_hpinv _ _ _ J1 _ o0). destruct s.
       assert (E: weight_form (x0 → x2) < weight_form ((x0 ∨ x1) → x2)). simpl ; lia.
       assert (E1: derrec_height x6 = derrec_height x6). auto.
       assert (E11: weight_form (x0 → x2) = weight_form (x0 → x2)). auto.
       pose (PIH _ E (derrec_height x6) x3 x6 E1 x4 (x0 → x2) E11 c0).
       assert (E2: weight_form (x1 → x2) < weight_form ((x0 ∨ x1) → x2)). simpl ; lia.
       assert (E3: derrec_height d0 = derrec_height d0). auto.
       assert (E12: weight_form (x1 → x2) = weight_form (x1 → x2)). auto.
       pose (PIH _ E2 (derrec_height d0) x4 d0 E3 x5 (x1 → x2) E12 c).
       pose (dlCons d1 DersNil). apply OrImpL in o. pose (derI _ o d2). auto.
  (* ImpImpL *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H0. destruct H0. repeat destruct s ; repeat destruct p ; subst.
    +  assert (J1: derrec_height x = derrec_height x). auto.
        assert (J2: (Γ0 ++ B → C :: Γ1 ++ (A1 → B) → C :: Γ2, A1 → B) = ((Γ0 ++ B → C :: Γ1) ++ (A1 → B) → C :: Γ2, A1 → B)).
        repeat rewrite <- app_assoc ; auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J1 J2). rewrite <- app_assoc in d0. simpl in d0.
        assert (E: weight_form (B → C) < weight_form ((A1 → B) → C)). simpl ; lia.
        assert (E1: derrec_height d0 = derrec_height d0). auto.
        assert (E2: weight_form (B → C) = weight_form (B → C)). auto.
        assert (E3: ctr_L (B → C) (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: B → C :: Γ2, A1 → B) (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: Γ2, A1 → B)).
        assert (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: B → C :: Γ2 = Γ0 ++ B → C :: (Γ1 ++ [A1]) ++ B → C :: B → C :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
        assert (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: Γ2 = Γ0 ++ B → C :: (Γ1 ++ [A1]) ++ B → C :: Γ2).
        repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
        pose (PIH _ E (derrec_height d0) _ _ E1 _ _ E2 E3).
        assert (E4: derrec_height d1 = derrec_height d1). auto.
        assert (E5: ctr_L (B → C) (Γ0 ++ B → C :: Γ1 ++ A1 :: B → C :: Γ2, A1 → B) (Γ0 ++ B → C :: Γ1 ++ A1 :: Γ2, A1 → B)).
        pose (ctr_LI (B → C) Γ0 (Γ1 ++ [A1]) Γ2 (A1 → B)). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
        pose (PIH _ E (derrec_height d1) _ _ E4 _ _ E2 E5).
        assert (E6: ImpRRule [(Γ0 ++ A1 :: B → C :: Γ1 ++ A1 :: Γ2, B)] (Γ0 ++ B → C :: Γ1 ++ A1 :: Γ2, A1 → B)).
        apply ImpRRule_I.
        pose (ImpR_inv _ _ d2 E6).
        assert (E7: weight_form A1 < weight_form ((A1 → B) → C)). simpl ; lia.
        assert (E8: derrec_height d3 = derrec_height d3). auto.
        assert (E9: weight_form A1 = weight_form A1). auto.
        assert (E10: ctr_L A1(Γ0 ++ A1 :: B → C :: Γ1 ++ A1 :: Γ2, B) (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, B)).
        pose (ctr_LI A1 Γ0 (B → C :: Γ1) Γ2 B). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
        pose (PIH _ E7 (derrec_height d3) _ _ E8 _ _ E9 E10).
        apply derI with (ps:=[(Γ0 ++ B → C :: Γ1 ++ Γ2, A1 → B);(Γ0 ++ C :: Γ1 ++ Γ2, A0)]).
        apply ImpImpL. apply ImpImpLRule_I. apply dlCons.
        apply derI with (ps:=[(Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, B)]). apply ImpR. apply ImpRRule_I.
        apply dlCons ; auto. apply dlCons ; auto.
        assert (E11: ImpImpLRule [((Γ0 ++ C :: Γ1) ++ B → C :: Γ2, A1 → B);((Γ0 ++ C :: Γ1) ++ C :: Γ2, A0)]
        ((Γ0 ++ C :: Γ1) ++ (A1 → B) → C :: Γ2, A0)). apply ImpImpLRule_I. repeat rewrite <- app_assoc in E11.
        simpl in E11.
        pose (ImpImpL_inv_R _ _ _ x0 E11).
        assert (E12: weight_form C < weight_form ((A1 → B) → C)). simpl ; lia.
        assert (E13: derrec_height d5 = derrec_height d5). auto.
        assert (E14: weight_form C = weight_form C). auto.
        assert (E15: ctr_L C (Γ0 ++ C :: Γ1 ++ C :: Γ2, A0) (Γ0 ++ C :: Γ1 ++ Γ2, A0)). apply ctr_LI.
        pose (PIH _ E12 (derrec_height d5) _ _ E13 _ _ E14 E15). auto.
    +  apply list_split_form in e2. destruct e2. repeat destruct s ; repeat destruct p ; subst.
        {  assert (J1: derrec_height x = derrec_height x). auto.
            assert (J2: (((Γ0 ++ [(A1 → B) → C]) ++ Γ1) ++ B → C :: Γ2, A1 → B) = (Γ0 ++ (A1 → B) → C :: Γ1 ++ B → C :: Γ2, A1 → B)).
            repeat rewrite <- app_assoc ; auto.
            pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J1 J2).
            assert (E: weight_form (B → C) < weight_form ((A1 → B) → C)). simpl ; lia.
            assert (E1: derrec_height d0 = derrec_height d0). auto.
            assert (E2: weight_form (B → C) = weight_form (B → C)). auto.
            assert (E3: ctr_L (B → C) (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ B → C :: Γ2, A1 → B) (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ Γ2, A1 → B)).
            assert (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ B → C :: Γ2 = (Γ0 ++ [A1]) ++ B → C :: (B → C :: Γ1) ++ B → C :: Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
            assert (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A1]) ++ B → C :: (B → C :: Γ1) ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
            pose (PIH _ E (derrec_height d0) _ _ E1 _ _ E2 E3).
            assert (E4: derrec_height d1 = derrec_height d1). auto.
            assert (E5: ctr_L (B → C) (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ Γ2, A1 → B) (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, A1 → B)).
            assert (Γ0 ++ A1 :: B → C :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A1]) ++ B → C :: [] ++ B → C :: Γ1 ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
            assert (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2 = (Γ0 ++ [A1]) ++ B → C :: [] ++ Γ1 ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
            pose (PIH _ E (derrec_height d1) _ _ E4 _ _ E2 E5).
            assert (E6: ImpRRule [(Γ0 ++ A1 :: A1 :: B → C :: Γ1 ++ Γ2, B)] (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, A1 → B)).
            apply ImpRRule_I.
            pose (ImpR_inv _ _ d2 E6).
            assert (E7: weight_form A1 < weight_form ((A1 → B) → C)). simpl ; lia.
            assert (E8: derrec_height d3 = derrec_height d3). auto.
            assert (E9: weight_form A1 = weight_form A1). auto.
            assert (E10: ctr_L A1(Γ0 ++ A1 :: A1 :: B → C :: Γ1 ++ Γ2, B) (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, B)).
            assert (Γ0 ++ A1 :: A1 :: B → C :: Γ1 ++ Γ2 = Γ0 ++ A1 :: [] ++ A1 :: B → C :: Γ1 ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H.
            assert (Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2 = Γ0 ++ A1 :: [] ++ B → C :: Γ1 ++ Γ2).
            repeat rewrite <- app_assoc ; simpl ; auto. rewrite H0. apply ctr_LI.
            pose (PIH _ E7 (derrec_height d3) _ _ E8 _ _ E9 E10).
            apply derI with (ps:=[(Γ0 ++ B → C :: Γ1 ++ Γ2, A1 → B);(Γ0 ++ C :: Γ1 ++ Γ2, A0)]).
            apply ImpImpL. apply ImpImpLRule_I. apply dlCons.
            apply derI with (ps:=[(Γ0 ++ A1 :: B → C :: Γ1 ++ Γ2, B)]). apply ImpR. apply ImpRRule_I.
            apply dlCons ; auto. apply dlCons ; auto.
            assert (E11: ImpImpLRule [(Γ0 ++ B → C :: Γ1 ++ C :: Γ2, A1 → B);(Γ0 ++ C :: Γ1 ++ C :: Γ2, A0)]
            (((Γ0 ++ [(A1 → B) → C]) ++ Γ1) ++ C :: Γ2, A0)). repeat rewrite <- app_assoc ; simpl.
            apply ImpImpLRule_I.
            pose (ImpImpL_inv_R _ _ _ x0 E11).
            assert (E12: weight_form C < weight_form ((A1 → B) → C)). simpl ; lia.
            assert (E13: derrec_height d5 = derrec_height d5). auto.
            assert (E14: weight_form C = weight_form C). auto.
            assert (E15: ctr_L C (Γ0 ++ C :: Γ1 ++ C :: Γ2, A0) (Γ0 ++ C :: Γ1 ++ Γ2, A0)). apply ctr_LI.
            pose (PIH _ E12 (derrec_height d5) _ _ E13 _ _ E14 E15). auto. }
        {  assert (E: derrec_height x < S (dersrec_height d)). lia.
           assert (E1: derrec_height x = derrec_height x). auto.
           assert (E2: weight_form A = weight_form A). auto.
           assert (E3: ctr_L A (((Γ0 ++ [A]) ++ (Γ1 ++ [A]) ++ x3) ++ B → C :: Γ4, A1 → B) (Γ0 ++ A :: Γ1 ++ x3 ++ B → C :: Γ4, A1 → B)).
           repeat rewrite <- app_assoc ; simpl. apply ctr_LI.
           pose (SIH (derrec_height x) E _ x E1 _ _ E2 E3).
           assert (E4: derrec_height x0 < S (dersrec_height d)). lia.
           assert (E5: derrec_height x0 = derrec_height x0). auto.
           assert (E6: ctr_L A (((Γ0 ++ [A]) ++ (Γ1 ++ [A]) ++ x3) ++ C :: Γ4, A0) (Γ0 ++ A :: Γ1 ++ x3 ++ C :: Γ4, A0)).
           repeat rewrite <- app_assoc ; simpl. apply ctr_LI.
           pose (SIH (derrec_height x0) E4 _ x0 E5 _ _ E2 E6).
           pose (dlCons d1 DersNil). pose (dlCons d0 d2).
           apply derI with (ps:=[(Γ0 ++ A :: Γ1 ++ x3 ++ B → C :: Γ4, A1 → B); (Γ0 ++ A :: Γ1 ++ x3 ++ C :: Γ4, A0)]) ; auto.
           apply ImpImpL.
           assert (Γ0 ++ A :: Γ1 ++ x3 ++ B → C :: Γ4 = (Γ0 ++ A :: Γ1 ++ x3) ++ B → C :: Γ4).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
           assert (Γ0 ++ A :: Γ1 ++ x3 ++ C :: Γ4 = (Γ0 ++ A :: Γ1 ++ x3) ++  C :: Γ4).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
           assert (Γ0 ++ A :: Γ1 ++ x3 ++(A1 → B) → C :: Γ4 = (Γ0 ++ A :: Γ1 ++ x3) ++ (A1 → B) → C :: Γ4).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply ImpImpLRule_I. }
        {  repeat destruct s ; repeat destruct p ; subst.
           assert (E: derrec_height x < S (dersrec_height d)). lia.
           assert (E1: derrec_height x = derrec_height x). auto.
           assert (E2: weight_form A = weight_form A). auto.
           assert (E3: ctr_L A (((Γ0 ++ [A]) ++ x2) ++ B → C :: x1 ++ A :: Γ2, A1 → B) (Γ0 ++ A :: x2 ++ B → C :: x1 ++ Γ2, A1 → B)).
           assert (((Γ0 ++ [A]) ++ x2) ++ B → C :: x1 ++ A :: Γ2 =Γ0 ++ A :: (x2 ++ B → C :: x1) ++ A :: Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
           assert (Γ0 ++ A :: x2 ++ B → C :: x1 ++ Γ2 =Γ0 ++ A :: (x2 ++ B → C :: x1) ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
           pose (SIH (derrec_height x) E _ x E1 _ _ E2 E3).
           assert (E4: derrec_height x0 < S (dersrec_height d)). lia.
           assert (E5: derrec_height x0 = derrec_height x0). auto.
           assert (E6: ctr_L A (((Γ0 ++ [A]) ++ x2) ++ C :: x1 ++ A :: Γ2, A0) (Γ0 ++ A :: x2 ++ C :: x1 ++ Γ2, A0)).
           assert (((Γ0 ++ [A]) ++ x2) ++ C :: x1 ++ A :: Γ2 =Γ0 ++ A :: (x2 ++ C :: x1) ++ A :: Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
           assert (Γ0 ++ A :: x2 ++ C :: x1 ++ Γ2 =Γ0 ++ A :: (x2 ++ C :: x1) ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
           pose (SIH (derrec_height x0) E4 _ x0 E5 _ _ E2 E6).
           pose (dlCons d1 DersNil). pose (dlCons d0 d2).
           apply derI with (ps:=[(Γ0 ++ A :: x2 ++ B → C :: x1 ++ Γ2, A1 → B); (Γ0 ++ A :: x2 ++ C :: x1 ++ Γ2, A0)]) ; auto.
           apply ImpImpL.
           assert (Γ0 ++ A :: x2 ++ B → C :: x1 ++ Γ2 = (Γ0 ++ A :: x2) ++ B → C :: x1 ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
           assert (Γ0 ++ A :: x2 ++ C :: x1 ++ Γ2 = (Γ0 ++ A :: x2) ++ C :: x1 ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
           assert (Γ0 ++ A :: (x2 ++ (A1 → B) → C :: x1) ++ Γ2 = (Γ0 ++ A :: x2) ++ (A1 → B) → C :: x1 ++ Γ2).
           repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2. apply ImpImpLRule_I. }
    + repeat destruct s ; repeat destruct p ; subst.
       assert (E: derrec_height x < S (dersrec_height d)). lia.
       assert (E1: derrec_height x = derrec_height x). auto.
       assert (E2: weight_form A = weight_form A). auto.
       assert (E3: ctr_L A (Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ A :: Γ2, A1 → B) (Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ Γ2, A1 → B)).
       assert (Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ A :: Γ2 =(Γ3 ++ B → C :: x1) ++ A :: Γ1 ++ A :: Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
       assert (Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ Γ2 =(Γ3 ++ B → C :: x1) ++ A :: Γ1 ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
       pose (SIH (derrec_height x) E _ x E1 _ _ E2 E3).
       assert (E4: derrec_height x0 < S (dersrec_height d)). lia.
       assert (E5: derrec_height x0 = derrec_height x0). auto.
       assert (E6: ctr_L A (Γ3 ++ C :: x1 ++ A :: Γ1 ++ A :: Γ2, A0) (Γ3 ++ C :: x1 ++ A :: Γ1 ++ Γ2, A0)).
       assert (Γ3 ++ C :: x1 ++ A :: Γ1 ++ A :: Γ2 =(Γ3 ++ C :: x1) ++ A :: Γ1 ++ A :: Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H.
       assert (Γ3 ++ C :: x1 ++ A :: Γ1 ++ Γ2 =(Γ3 ++ C :: x1) ++ A :: Γ1 ++ Γ2).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0. apply ctr_LI.
       pose (SIH (derrec_height x0) E4 _ x0 E5 _ _ E2 E6).
       pose (dlCons d1 DersNil). pose (dlCons d0 d2).
       apply derI with (ps:=[(Γ3 ++ B → C :: x1 ++ A :: Γ1 ++ Γ2, A1 → B); (Γ3 ++ C :: x1 ++ A :: Γ1 ++ Γ2, A0)]) ; auto.
       apply ImpImpL. repeat rewrite <- app_assoc. simpl. apply ImpImpLRule_I.
  (* BoxImpL *)
  * inversion H1. subst. inversion H5. subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    pose (BoxImpL_app_ctr_L ctr H1). repeat destruct s.
    + destruct p. destruct s. destruct p. destruct (dec_is_box A).
       -- destruct s ; subst.
          apply derI with (ps:=[x2;x1]). apply BoxImpL ; auto. apply dlCons. 2: apply dlCons ; auto. simpl in c0.
          assert (E1: derrec_height x = derrec_height x). auto.
          assert (E2: weight_form x3 < weight_form (Box x3)). simpl ; lia.
          assert (E3: weight_form x3 = weight_form x3). auto.
          pose (PIH _ E2 _ _ x E1 _ _ E3 c0) ; auto.
          assert (E: derrec_height x0 < S (dersrec_height d)). lia.
          assert (E1: derrec_height x0 = derrec_height x0). auto.
          assert (E2: weight_form (Box x3) = weight_form (Box x3)). auto.
          pose (SIH (derrec_height x0) E _ x0 E1 _ _ E2 c) ; auto.
      -- apply derI with (ps:=[x2;x1]). apply BoxImpL ; auto. apply dlCons. 2: apply dlCons ; auto.
         assert (E: derrec_height x < S (dersrec_height d)). lia.
         assert (E1: derrec_height x = derrec_height x). auto.
         assert (E2: weight_form A = weight_form A). auto.
         assert (unBox_formula A = A). destruct A ; auto. exfalso ; apply f ; eexists ; auto. rewrite H in c0.
         pose (SIH (derrec_height x) E _ x E1 _ _ E2 c0) ; auto.
         assert (E: derrec_height x0 < S (dersrec_height d)). lia.
         assert (E1: derrec_height x0 = derrec_height x0). auto.
         assert (E2: weight_form A = weight_form A). auto.
         assert (unBox_formula A = A). destruct A ; auto. exfalso ; apply f ; eexists ; auto. rewrite H in c0.
         pose (SIH (derrec_height x0) E _ x0 E1 _ _ E2 c) ; auto.
    + repeat destruct p ; subst. apply derI with (ps:=[x5;x8]). apply BoxImpL ; auto.
       pose (BoxImpL_inv_R _ _ _ x0 b0). pose (BoxImpL_inv_R _ _ _ x b1). apply dlCons. 2: apply dlCons ; auto.
       assert (E1: derrec_height d1 = derrec_height d1). auto.
       assert (E2: weight_form x2 < weight_form ((Box x1 → x2))). simpl ; lia.
       assert (E3: weight_form x2 = weight_form x2). auto.
       pose (PIH _ E2 _ _ d1 E1 _ _ E3 c0) ; auto.
       assert (E1: derrec_height d0 = derrec_height d0). auto.
       assert (E2: weight_form x2 < weight_form ((Box x1 → x2))). simpl ; lia.
       assert (E3: weight_form x2 = weight_form x2). auto.
       pose (PIH _ E2 _ _ d0 E1 _ _ E3 c) ; auto.
  (* SLR *)
  * inversion H1 ; subst. inversion H5 ; subst.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    pose (SLR_app_ctr_L ctr H1). destruct s. destruct p. destruct (dec_is_box A).
    + apply derI with (ps:=[x0]). apply SLR ; auto. apply dlCons ; auto. destruct s0 ; subst. simpl in c.
       assert (E1: derrec_height x = derrec_height x). auto.
       assert (E2: weight_form x1 < weight_form (Box x1)). simpl ; lia.
       assert (E3: weight_form x1 = weight_form x1). auto.
       pose (PIH _ E2 _ _ x E1 _ _ E3 c) ; auto.
    + apply derI with (ps:=[x0]). apply SLR ; auto. apply dlCons ; auto.
       assert (E: derrec_height x < S (dersrec_height d)). lia.
       assert (E1: derrec_height x = derrec_height x). auto.
       assert (E2: weight_form A = weight_form A). auto.
       assert (unBox_formula A = A). destruct A ; auto. exfalso ; apply f ; eexists ; auto. rewrite H in c.
       pose (SIH (derrec_height x) E _ x E1 _ _ E2 c) ; auto.
Qed.

Theorem G4iSL_adm_ctr_L : forall s, (derrec G4iSL_rules (fun _ => False) s) ->
          (forall sc A, (@ctr_L A s sc) ->
          derrec G4iSL_rules (fun _ => False) sc).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
assert (J2: weight_form A = weight_form A). auto.
pose (@G4iSL_ctr_L (weight_form A) _ _ X J1 sc A J2 H). auto.
Qed.
