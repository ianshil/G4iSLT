Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.
Require Import DG4iSL_exch.
Require Import DG4iSL_wkn.
Require Import DG4iSL_adm_unBox_L.
Require Import DG4iSL_remove_list.
Require Import DG4iSL_dec.
Require Import DG4iSL_inv_AndR_AndL.
Require Import DG4iSL_inv_OrL.
Require Import DG4iSL_inv_AtomImpL.
Require Import DG4iSL_inv_AndImpL.
Require Import DG4iSL_inv_OrImpL.
Require Import DG4iSL_inv_ImpImpL_R.
Require Import DG4iSL_inv_BoxImpL_R.
Require Import DG4iSL_ctr.

Theorem ImpL_hpinv_R : forall (m k : nat) s (D0: derrec G4iSL_rules (fun _ => False) s) A B Γ0 Γ1 C,
        m = (weight_form (Imp A B)) ->
        k = (derrec_height D0) ->
        (s = (Γ0 ++ Imp A B :: Γ1, C)) ->
        derrec G4iSL_rules (fun _ => False) (Γ0 ++ B :: Γ1, C).
Proof.
assert (DersNilF: dersrec G4iSL_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the weight. *)
pose (strong_inductionT (fun (x:nat) => forall k s (D0 : derrec G4iSL_rules (fun _ => False) s) A B Γ0 Γ1 C,
        x = (weight_form (Imp A B)) ->
        k = (derrec_height D0) ->
        (s = (Γ0 ++ Imp A B :: Γ1, C)) ->
        derrec G4iSL_rules (fun _ => False) (Γ0 ++ B :: Γ1, C))).
apply d. intros n PIH. clear d.

(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall s (D0 : derrec G4iSL_rules (fun _ => False) s) A B Γ0 Γ1 C,
        n = weight_form (Imp A B) ->
        x = (derrec_height D0) ->
        (s = (Γ0 ++ Imp A B :: Γ1, C)) ->
        derrec G4iSL_rules (fun _ => False) (Γ0 ++ B :: Γ1, C))).
apply d. intros m SIH. clear d.

(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros A B Γ0 Γ1 C wei hei eq. inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ A → B :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++ B :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. assert (IdPRule [] (x ++ # P :: x0, # P)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P :: x0, # P) H1 DersNilF). auto.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ A → B :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (⊥) (Γ0 ++ B :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, C)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, C) H1 DersNilF). auto.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    simpl in PIH. simpl in SIH.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ A → B :: Γ1, A0) = (Γ0 ++ A → B :: Γ1, A0)). auto.
    assert (J40: S (weight_form A + weight_form B) = S (weight_form A + weight_form B)). auto.
    pose (SIH _ J2 _ x _ _ _ _ _ J40 J3 J4).
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J7 : (Γ0 ++ A → B :: Γ1, B0) = (Γ0 ++ A → B :: Γ1, B0)). auto.
    pose (SIH _ J5 _ x0 _ _ _ _ _ J40 J6 J7).
    assert (AndRRule [(Γ0 ++ B :: Γ1, A0); (Γ0 ++ B :: Γ1, B0)]
    (Γ0 ++ B :: Γ1, A0 ∧ B0)). apply AndRRule_I. pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
    apply AndR in H0.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
   (ps:=[(Γ0 ++ B :: Γ1, A0); (Γ0 ++ B :: Γ1, B0)])
    (Γ0 ++ B :: Γ1, And A0 B0) H0 d3). auto.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J2: derrec_height x < S (dersrec_height d)). lia.
      assert (J3: derrec_height x = derrec_height x). reflexivity.
      assert (J4 : (((Γ0 ++ [A → B]) ++ x0) ++ A0 :: B0 :: Γ3, C) = (Γ0 ++ A → B :: x0 ++ A0 :: B0 :: Γ3, C)).
      repeat rewrite <- app_assoc. auto.
      assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
      pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
      assert (AndLRule [((Γ0 ++ B :: x0) ++ A0 :: B0 :: Γ3, C)]
       ((Γ0 ++ B :: x0) ++ A0 ∧ B0 :: Γ3, C)). apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       pose (dlCons d0 DersNilF). apply AndL in H0.
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x0 ++ A0 :: B0 :: Γ3, C)])
       (Γ0 ++ B :: x0 ++ A0 ∧ B0 :: Γ3, C) H0 d1). auto.
  +  repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
      assert (J4 : (Γ2 ++ A0 :: B0 :: x ++ A → B :: Γ1, C) = ((Γ2 ++ A0 :: B0 :: x) ++ A → B :: Γ1, C)).
      repeat rewrite <- app_assoc. auto.
      assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
      pose (SIH _ J2 _ x0 _ _ _ _ _ J70 J3 J4).
      pose (dlCons d0 DersNilF).
      assert (AndLRule [((Γ2 ++ A0 :: B0 :: x) ++ B :: Γ1, C)]
       ((Γ2 ++ A0 ∧ B0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply AndLRule_I.
       apply AndL in H0.
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:=[((Γ2 ++ A0 :: B0 :: x) ++ B :: Γ1, C)])
      ((Γ2 ++ A0 ∧ B0 :: x) ++ B :: Γ1, C) H0 d1). auto.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ A → B :: Γ1, A0) = (Γ0 ++ A → B :: Γ1, A0)). auto.
    assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
    pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
    assert (OrR1Rule [(Γ0 ++ B :: Γ1, A0)]
    (Γ0 ++ B :: Γ1, Or A0 B0)). apply OrR1Rule_I. pose (dlCons d0 DersNilF).
    apply OrR1 in H0.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ B :: Γ1, A0)])
    (Γ0 ++ B  :: Γ1, Or A0 B0) H0 d1). auto.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ A → B :: Γ1, B0) = (Γ0 ++ A → B :: Γ1, B0)). auto.
    assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
    pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
    assert (OrR2Rule [(Γ0 ++ B :: Γ1, B0)]
    (Γ0 ++ B :: Γ1, Or A0 B0)). apply OrR2Rule_I. pose (dlCons d0 DersNilF).
    apply OrR2 in H0.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ B :: Γ1, B0)])
    (Γ0 ++ B  :: Γ1, Or A0 B0) H0 d1). auto.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (J2: derrec_height x < S (dersrec_height d)). lia.
      assert (J3: derrec_height x = derrec_height x). reflexivity.
      assert (J4 : (((Γ0 ++ [A → B]) ++ x0) ++ A0 :: Γ3, C) = (Γ0 ++ A → B :: (x0 ++ A0 :: Γ3), C)). repeat rewrite <- app_assoc. auto.
      assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
      pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      assert (J7 : (((Γ0 ++ [A → B]) ++ x0) ++ B0 :: Γ3, C) = (Γ0 ++ A → B :: (x0 ++ B0 :: Γ3), C)). repeat rewrite <- app_assoc. auto.
      pose (SIH _ J5 _ x1 _ _ _ _ _ J70 J6 J7).
      assert (OrLRule [((Γ0 ++ B :: x0) ++ A0 :: Γ3, C);((Γ0 ++ B :: x0) ++ B0 :: Γ3, C)]
      ((Γ0 ++ B :: x0) ++ A0 ∨ B0 :: Γ3, C)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ B :: x0 ++ A0 :: Γ3, C); (Γ0 ++ B :: x0 ++ B0 :: Γ3, C)])
      (Γ0 ++ B :: x0 ++ A0 ∨ B0 :: Γ3, C) H0 d3). auto.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
      assert (J4 :(Γ2 ++ A0 :: x ++ A → B :: Γ1, C) = ((Γ2 ++ A0 :: x) ++ A → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
      assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
      pose (SIH _ J2 _ x0 _ _ _ _ _ J70 J3 J4).
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      assert (J7 : (Γ2 ++ B0 :: x ++ A → B :: Γ1, C) = ((Γ2 ++ B0 :: x) ++ A → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
      pose (SIH _ J5 _ x1 _ _ _ _ _ J70 J6 J7).
      assert (OrLRule [((Γ2 ++ A0 :: x) ++ B :: Γ1, C);((Γ2 ++ B0 :: x) ++ B :: Γ1, C)]
      ((Γ2 ++ A0 ∨ B0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply OrLRule_I. apply OrL in H0.
      pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:=[((Γ2 ++ A0 :: x) ++ B :: Γ1, C); ((Γ2 ++ B0 :: x) ++ B :: Γ1, C)])
      ((Γ2 ++ A0 ∨ B0 :: x) ++ B :: Γ1, C) H0 d3). auto.
  (* ImpR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (J50: derrec_height x = derrec_height x). auto.
    assert (J51: list_exch_L (Γ2 ++ A0 :: Γ3, B0) (A0 :: Γ0 ++ A → B :: Γ1, B0)).
    assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). auto. rewrite H0.
    assert (A0 :: Γ0 ++ A → B :: Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). rewrite <- H2. auto. rewrite H1.
    apply list_exch_LI.
    pose (G4iSL_hpadm_list_exch_L (derrec_height x) _ x J50 _ J51). destruct s.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J4: (A0 :: Γ0 ++ A → B :: Γ1, B0) = ((A0 :: Γ0) ++ A → B :: Γ1, B0)). repeat rewrite <- app_assoc. auto.
    assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
    pose (SIH _ J2 _ x0 _ _ _ _ _ J70 J3 J4).
    assert (ImpRRule [(([] ++ A0 :: Γ0) ++ B :: Γ1, B0)] ([] ++ Γ0 ++ B :: Γ1, A0 → B0)). repeat rewrite <- app_assoc. apply ImpRRule_I.
    simpl in H0. apply ImpR in H0. pose (dlCons d0 DersNilF).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
    (ps:=[((A0 :: Γ0) ++ B :: Γ1, B0)]) (Γ0 ++ B :: Γ1, A0 → B0) H0 d1). auto.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   + assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x1) ++ # P :: Γ3 ++ A0 :: Γ4, C) = (Γ0 ++ A → B :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (AtomImpL1Rule [((Γ0 ++ B :: x1) ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       ((Γ0 ++ B :: x1) ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)). apply AtomImpL1Rule_I.
       repeat rewrite <- app_assoc in H0. apply AtomImpL1 in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)])
       (Γ0 ++ B :: x1 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C) H0 d1). auto.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. subst. repeat rewrite <- app_assoc. auto. }
      { assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ # P :: ((x0 ++ [A → B]) ++ x2) ++ A0 :: Γ4, C) = ((Γ2 ++ # P :: x0) ++ A → B :: x2 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
         assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
         pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
         assert (AtomImpL1Rule [((Γ2 ++ # P :: x0) ++ B :: x2 ++ A0 :: Γ4, C)]
         ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4, C)).
         assert ((Γ2 ++ # P :: x0) ++ B :: x2 ++ A0 :: Γ4 = Γ2 ++ # P :: (x0 ++ B :: x2) ++ A0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H0.
         assert ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4 = Γ2 ++ # P :: (x0 ++ B :: x2) ++ # P → A0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H1. apply AtomImpL1Rule_I. apply AtomImpL1 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ # P :: x0) ++ B :: x2 ++ A0 :: Γ4, C)])
         ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4, C) H0 d1). auto. }
      { repeat destruct s. repeat destruct p ; subst.
         assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ A → B :: Γ1, C) = ((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ A → B :: Γ1, C)).
         repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
         assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
         pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
         assert (AtomImpL1Rule [((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ B :: Γ1, C)]
         ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
         apply AtomImpL1Rule_I. apply AtomImpL1 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ B :: Γ1, C)])
         ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ B :: Γ1, C) H0 d1). auto. }
  (* AtomImpL2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1 ; subst. auto.
   + assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x1) ++ A0 :: Γ3 ++ # P :: Γ4, C) = (Γ0 ++ A → B :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (AtomImpL2Rule [((Γ0 ++ B :: x1) ++ A0 :: Γ3 ++ # P :: Γ4, C)]
       ((Γ0 ++ B :: x1) ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
       repeat rewrite <- app_assoc in H0. apply AtomImpL2 in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)])
       (Γ0 ++ B :: x1 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C) H0 d1). auto.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ A0 :: ((x0 ++ [A → B]) ++ x2) ++ # P :: Γ4, C) = ((Γ2 ++ A0 :: x0) ++ A → B :: x2 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc. auto.
         assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
         pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
         assert (AtomImpL2Rule [((Γ2 ++ A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C)]
         ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C)).
         assert ((Γ2 ++ A0 :: x0) ++ B :: x2 ++ # P :: Γ4 = Γ2 ++ A0 :: (x0 ++ B :: x2) ++ # P :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H0.
         assert ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P  :: Γ4 = Γ2 ++ # P → A0 :: (x0 ++ B :: x2) ++ # P :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H1. apply AtomImpL2Rule_I. apply AtomImpL2 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C)])
         ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C) H0 d1). auto. }
      { repeat destruct s. repeat destruct p ; subst.
         assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ A → B :: Γ1, C) = ((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ A → B :: Γ1, C)).
         repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
         assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
         pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
         assert (AtomImpL2Rule [((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C)]
         ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
         apply AtomImpL2Rule_I. apply AtomImpL2 in H0. pose (dlCons d0 DersNilF).
         pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C)])
         ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C) H0 d1). auto. }
 (* AndImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ0 ++ A0 → B0 → B :: Γ1, C) = (Γ0 ++ A0 → B0 → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       assert (J71: weight_form (A0 → B0 → B) < weight_form ((A0 ∧ B0) → B)). simpl ; lia.
       assert (J72: weight_form (A0 → B0 → B) = weight_form (A0 → (B0 → B))). auto.
       pose (PIH _ J71 _ _ _ _ _ _ _ _ J72 J3 J4).
       assert (J6: derrec_height d0 = derrec_height d0). reflexivity.
       assert (J7: (Γ0 ++ B0 → B :: Γ1, C) = (Γ0 ++ B0 → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       assert (J73: weight_form (B0 → B) < weight_form ((A0 ∧ B0) → B)). simpl ; lia.
       assert (J74: weight_form (B0 → B) = weight_form (B0 → B)). auto.
       pose (PIH _ J73 _ _ _ _ _ _ _ _ J74 J6 J7). auto.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x1) ++ A0 → B0 → C0 :: Γ3, C) = (Γ0 ++ A → B :: x1 ++ A0 → B0 → C0 :: Γ3, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (AndImpLRule [((Γ0 ++ B :: x1) ++ A0 → B0 → C0 :: Γ3, C)]
       ((Γ0 ++ B :: x1) ++ (A0 ∧ B0) → C0 :: Γ3, C)). apply AndImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply AndImpL in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x1 ++ A0 → B0 → C0 :: Γ3, C)])
       (Γ0 ++ B :: x1 ++ (A0 ∧ B0) → C0 :: Γ3, C) H0 d1). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ2 ++ A0 → B0 → C0 :: x0 ++ A → B :: Γ1, C) = ((Γ2 ++ A0 → B0 → C0 :: x0) ++ A → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (AndImpLRule [((Γ2 ++ A0 → B0 → C0 :: x0) ++ B :: Γ1, C)]
       ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
       apply AndImpL in H0. pose (dlCons d0 DersNilF).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ A0 → B0 → C0 :: x0) ++ B :: Γ1, C)])
       ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ B :: Γ1, C) H0 d1). auto.
  (* OrImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ0 ++ A0 → B :: Γ3 ++ B0 → B :: Γ4, C) = (Γ0 ++ A0 → B :: Γ3 ++ B0 → B :: Γ4, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J73: weight_form (A0 → B) < weight_form ((A0 ∨ B0) → B)). simpl ; lia.
       assert (J74: weight_form (A0 → B) = weight_form (A0 → B)). auto.
       pose (PIH _ J73 _ _ _ _ _ _ _ _ J74 J3 J4).
       assert (J6: derrec_height d0 = derrec_height d0). reflexivity.
       assert (J7: (Γ0 ++ B :: Γ3 ++ B0 → B :: Γ4, C) = ((Γ0 ++ B :: Γ3) ++ B0 → B :: Γ4, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J71: weight_form (B0 → B) < weight_form ((A0 ∨ B0) → B)). simpl ; lia.
       assert (J72: weight_form (B0 → B) = weight_form (B0 → B)). auto.
       pose (PIH _ J71 _ _ _ _ _ _ _ _ J72 J6 J7).
       assert (J8: ctr_L B ((Γ0 ++ B :: Γ3) ++ B :: Γ4, C) (Γ0 ++ B :: Γ3 ++ Γ4, C)). repeat rewrite <- app_assoc ; simpl.
       apply ctr_LI.
       assert (J9: derrec_height d1 = derrec_height d1). auto.
       assert (J10: weight_form B = weight_form B). auto.
       pose (@G4iSL_ctr_L _ _ _ _ J9 _ _ J10 J8). auto.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x1) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) = (Γ0 ++ A → B ::  x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (OrImpLRule [((Γ0 ++ B :: x1) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)]
       ((Γ0 ++ B :: x1) ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply OrImpL in H0.
       pose (dlCons d0 DersNilF).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)])
       (Γ0 ++ B :: x1 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C) H0 d1). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J50: derrec_height x = derrec_height x). auto.
       assert (J51: list_exch_L (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++ A → B :: Γ1, C)).
       assert (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4 = (Γ2 ++ [A0 → C0]) ++ [] ++ Γ3 ++ [B0 → C0] ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       assert (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++ A → B :: Γ1 = (Γ2 ++ [A0 → C0]) ++ [B0 → C0] ++ Γ3 ++ [] ++ Γ4).
       rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
       pose (G4iSL_hpadm_list_exch_L (derrec_height x) _ x J50 _ J51). destruct s.
       assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
       assert (J4: (Γ2 ++ A0 → C0 :: B0 → C0 :: x0 ++ A → B :: Γ1, C) = ((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ A → B :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x1 _ _ _ _ _ J70 J3 J4).
       assert (OrImpLRule [((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ B :: Γ1, C)]
       ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: Γ1, C)).
       assert ((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ B :: Γ1 = Γ2 ++ A0 → C0 :: [] ++ B0 → C0 :: x0 ++ B :: Γ1).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
       assert ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: Γ1 = Γ2 ++ (A0 ∨ B0) → C0 :: [] ++ x0 ++ B :: Γ1).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
       apply OrImpLRule_I.  apply OrImpL in H0. pose (dlCons d0 DersNilF).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ A0 → C0 :: B0 → C0 :: x0) ++ B :: Γ1, C)])
       ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: Γ1, C) H0 d1). auto.
  (* ImpImpL *)
 * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
       pose (derI (Γ0 ++ (A0 → B0) → B :: Γ1, C) g d).
       assert (J40: derrec_height d0 = derrec_height d0). auto.
       pose (ImpImpL_hpinv_R _ _ _ J40 _ _ H). destruct s. auto.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [A → B]) ++ x2) ++ B0 → C0 :: Γ3, A0 → B0) = (Γ0 ++ A → B :: x2 ++ B0 → C0 :: Γ3, A0 → B0)).
       repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (((Γ0 ++ [A → B]) ++ x2) ++ C0 :: Γ3, C) = (Γ0 ++ A → B :: x2 ++ C0 :: Γ3, C)).
       repeat rewrite <- app_assoc. auto.
       pose (SIH _ J5 _ x0 _ _ _ _ _ J70 J6 J7).
       assert (ImpImpLRule [((Γ0 ++ B :: x2) ++ B0 → C0 :: Γ3, A0 → B0);((Γ0 ++ B :: x2) ++ C0 :: Γ3, C)]
       ((Γ0 ++ B :: x2) ++ (A0 → B0) → C0 :: Γ3, C)). apply ImpImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply ImpImpL in H0.
       pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ B :: x2 ++ B0 → C0 :: Γ3, A0 → B0); (Γ0 ++ B :: x2 ++ C0 :: Γ3, C)])
       (Γ0 ++ B :: x2 ++ (A0 → B0) → C0 :: Γ3, C) H0 d3). auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ2 ++ B0 → C0 :: x1 ++ A → B :: Γ1, A0 → B0) = ((Γ2 ++ B0 → C0 :: x1) ++ A → B :: Γ1, A0 → B0)). repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J2 _ x _ _ _ _ _ J70 J3 J4).
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (Γ2 ++ C0 :: x1 ++ A → B :: Γ1, C) = ((Γ2 ++ C0 :: x1) ++ A → B :: Γ1, C)).
       repeat rewrite <- app_assoc. auto.
       pose (SIH _ J5 _ x0 _ _ _ _ _ J70 J6 J7).
       assert (ImpImpLRule [((Γ2 ++ B0 → C0 :: x1) ++ B :: Γ1, A0 → B0);((Γ2 ++ C0 :: x1) ++ B :: Γ1, C)]
       ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
       apply ImpImpL in H0. pose (dlCons d1 DersNilF). pose (dlCons d0 d2).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ B0 → C0 :: x1) ++ B :: Γ1, A0 → B0); ((Γ2 ++ C0 :: x1) ++ B :: Γ1, C)])
       ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ B :: Γ1, C) H0 d3). auto.
  (* BoxImpL *)
 * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d) ; auto.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst.
       pose (derI (Γ0 ++ Box A0 → B :: Γ1, C) g d).
       assert (J40: derrec_height d0 = derrec_height d0). auto.
       pose (BoxImpL_hpinv_R _ _ _ J40 _ _ H). destruct s. auto.
   +  assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (((Γ0 ++ [A → B]) ++ x2) ++ B0 :: Γ3, C) = (Γ0 ++ A → B :: x2 ++ B0 :: Γ3, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J5 _ x0 _ _ _ _ _ J70 J6 J7).
       assert (J8: derrec_height x < S (dersrec_height d)). lia.
       assert (J9: derrec_height x = derrec_height x). reflexivity.
       assert (J10: (unBoxed_list ((Γ0 ++ [A → B]) ++ x2) ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0) = (unBoxed_list Γ0 ++ A → B :: unBoxed_list x2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0)).
       repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; auto.
       assert (J80: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J8 _ x _ _ _ _ _ J80 J9 J10).
       apply derI with (ps:=[(unBoxed_list Γ0 ++ unBox_formula B :: unBoxed_list x2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0);(Γ0 ++ B :: x2 ++ B0 :: Γ3, C)]). apply BoxImpL.
       pose (@BoxImpLRule_I A0 B0 C (Γ0 ++ B :: x2) Γ3).
       repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
       apply dlCons ; auto. 2: apply dlCons ; auto.
       apply unBox_left_adm_gen ; auto.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (Γ2 ++ B0 :: x1 ++ A → B :: Γ1, C) = ((Γ2 ++ B0 :: x1) ++ A → B :: Γ1, C)).
       repeat rewrite <- app_assoc. auto.
       assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J5 _ x0 _ _ _ _ _ J70 J6 J7).
       assert (J8: derrec_height x < S (dersrec_height d)). lia.
       assert (J9: derrec_height x = derrec_height x). reflexivity.
       assert (J10: (unBoxed_list Γ2 ++ B0 :: unBoxed_list (x1 ++ A → B :: Γ1) ++ [Box A0], A0) = ((unBoxed_list Γ2 ++ B0 :: unBoxed_list x1) ++ A → B :: unBoxed_list Γ1 ++ [Box A0], A0)).
       repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; auto.
       assert (J80: weight_form (A → B) = weight_form (A → B)). auto.
       pose (SIH _ J8 _ x _ _ _ _ _ J80 J9 J10).
       apply derI with (ps:=[((unBoxed_list Γ2 ++ B0 :: unBoxed_list x1) ++ unBox_formula B :: unBoxed_list Γ1 ++ [Box A0], A0);((Γ2 ++ B0 :: x1) ++ B :: Γ1, C)]). apply BoxImpL.
       pose (@BoxImpLRule_I A0 B0 C Γ2 (x1 ++ B :: Γ1)). repeat rewrite <- app_assoc ; simpl.
       repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
       apply dlCons ; auto. 2: apply dlCons ; auto. apply unBox_left_adm_gen ; auto.
  (* SLR *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d) ; auto.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    assert (J7: (unBoxed_list (Γ0 ++ A → B :: Γ1) ++ [Box A0], A0) = (unBoxed_list Γ0 ++ A → B :: unBoxed_list Γ1 ++ [Box A0], A0)).
    repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; auto.
    assert (J70: weight_form (A → B) = weight_form (A → B)). auto.
    pose (SIH _ J5 _ x _ _ _ _ _ J70 J6 J7). apply derI with (ps:=[(unBoxed_list Γ0 ++ unBox_formula B :: unBoxed_list Γ1 ++ [Box A0], A0)]).
    apply SLR. pose (@SLRRule_I A0 (Γ0 ++ B :: Γ1)).
    repeat rewrite unBox_app_distrib in s ; simpl in s ; repeat rewrite <- app_assoc in s ; simpl in s ; apply s.
    apply dlCons ; auto. apply unBox_left_adm_gen ; auto.
Qed.

Theorem ImpL_inv_R : forall A B Γ0 Γ1 C, derrec G4iSL_rules (fun _ => False) (Γ0 ++ Imp A B :: Γ1, C) ->
                  derrec G4iSL_rules (fun _ => False) (Γ0 ++ B :: Γ1, C).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). auto.
assert (J2: (Γ0 ++ A → B :: Γ1, C) = (Γ0 ++ A → B :: Γ1, C)). auto.
assert (J3: weight_form (A → B) = weight_form (A → B)). auto.
pose (ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J3 J1 J2). auto.
Qed.

