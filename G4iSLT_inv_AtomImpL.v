Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import G4iSLT_calc.
Require Import G4iSLT_list_lems.
Require Import G4iSLT_remove_list.
Require Import G4iSLT_dec.
Require Import G4iSLT_exch.
Require Import G4iSLT_wkn.
Require Import G4iSLT_adm_unBox_L.

Theorem AtomImpL_hpinv : forall n s (D0 : derrec G4iSLT_rules (fun _ => False) s) P A Γ0 Γ1 C ,
                      (n = derrec_height D0) ->
                      (s = (Γ0 ++ (# P → A) :: Γ1, C)) ->
                      existsT2 (D1: (derrec G4iSLT_rules (fun _ => False) (Γ0 ++ A :: Γ1, C))), (derrec_height D1 <= n).
Proof.
assert (DersNilF: dersrec G4iSLT_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall s (D0 : derrec G4iSLT_rules (fun _ => False) s) P A Γ0 Γ1 C,
                      (x = derrec_height D0) ->
                      (s = (Γ0 ++ (# P → A) :: Γ1, C)) ->
                      existsT2 (D1: (derrec G4iSLT_rules (fun _ => False) (Γ0 ++ A :: Γ1, C))), (derrec_height D1 <= x))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros P A Γ0 Γ1 C hei eq. inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P0 (Γ0 ++ # P → A :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P0 (Γ0 ++ A :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. assert (IdPRule [] (x ++ # P0 :: x0, # P0)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ # P0 :: x0, # P0) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (Bot) (Γ0 ++ # P → A :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (Bot) (Γ0 ++ A :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ Bot :: x0, C)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ Bot :: x0, C) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    simpl in IH.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ # P → A :: Γ1, A0) = (Γ0 ++ # P → A :: Γ1, A0)). auto.
    pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J7 : (Γ0 ++ # P → A :: Γ1, B) = (Γ0 ++ # P → A :: Γ1, B)). auto.
    pose (IH _ J5 _ x0 _ _ _ _ _ J6 J7). destruct s.
    assert (AndRRule [(Γ0 ++ A :: Γ1, A0); (Γ0 ++ A :: Γ1, B)]
    (Γ0 ++ A :: Γ1, A0 ∧ B)). apply AndRRule_I. pose (dlCons x2 DersNilF). pose (dlCons x1 d0).
    apply AndR in H0.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
   (ps:=[(Γ0 ++ A :: Γ1, A0); (Γ0 ++ A :: Γ1, B)])
    (Γ0 ++ A :: Γ1, And A0 B) H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J2: derrec_height x < S (dersrec_height d)). lia.
      assert (J3: derrec_height x = derrec_height x). reflexivity.
      assert (J4 : (((Γ0 ++ [# P → A]) ++ x0) ++ A0 :: B :: Γ3, C) = (Γ0 ++ # P → A :: x0 ++ A0 :: B :: Γ3, C)).
      repeat rewrite <- app_assoc. auto.
      pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
      assert (AndLRule [((Γ0 ++ A :: x0) ++ A0 :: B :: Γ3, C)]
       ((Γ0 ++ A :: x0) ++ A0 ∧ B :: Γ3, C)). apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       pose (dlCons x1 DersNilF). apply AndL in H0.
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: x0 ++ A0 :: B :: Γ3, C)])
       (Γ0 ++ A :: x0 ++ A0 ∧ B :: Γ3, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
  +  repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
      assert (J4 : (Γ2 ++ A0 :: B :: x ++ # P → A :: Γ1, C) = ((Γ2 ++ A0 :: B :: x) ++ # P → A :: Γ1, C)).
      repeat rewrite <- app_assoc. auto. pose (IH _ J2 _ x0 _ _ _ _ _ J3 J4). destruct s.
      pose (dlCons x1 DersNilF).
      assert (AndLRule [((Γ2 ++ A0 :: B :: x) ++ A :: Γ1, C)]
       ((Γ2 ++ A0 ∧ B :: x) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. apply AndLRule_I.
       apply AndL in H0.
      pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
      (ps:=[((Γ2 ++ A0 :: B :: x) ++ A :: Γ1, C)])
      ((Γ2 ++ A0 ∧ B :: x) ++ A :: Γ1, C) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ # P → A :: Γ1, A0) = (Γ0 ++ # P → A :: Γ1, A0)). auto.
    pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
    assert (OrR1Rule [(Γ0 ++ A :: Γ1, A0)]
    (Γ0 ++ A :: Γ1, Or A0 B)). apply OrR1Rule_I. pose (dlCons x0 DersNilF).
    apply OrR1 in H0.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A :: Γ1, A0)])
    (Γ0 ++ A  :: Γ1, Or A0 B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J2: derrec_height x < S (dersrec_height d)). lia.
    assert (J3: derrec_height x = derrec_height x). reflexivity.
    assert (J4 : (Γ0 ++ # P → A :: Γ1, B) = (Γ0 ++ # P → A :: Γ1, B)). auto.
    pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
    assert (OrR2Rule [(Γ0 ++ A :: Γ1, B)]
    (Γ0 ++ A :: Γ1, Or A0 B)). apply OrR2Rule_I. pose (dlCons x0 DersNilF).
    apply OrR2 in H0.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A :: Γ1, B)])
    (Γ0 ++ A  :: Γ1, Or A0 B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (J2: derrec_height x < S (dersrec_height d)). lia.
      assert (J3: derrec_height x = derrec_height x). reflexivity.
      assert (J4 : (((Γ0 ++ [# P → A]) ++ x0) ++ A0 :: Γ3, C) = (Γ0 ++ # P → A :: (x0 ++ A0 :: Γ3), C)). repeat rewrite <- app_assoc. auto.
      pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      assert (J7 : (((Γ0 ++ [# P → A]) ++ x0) ++ B :: Γ3, C) = (Γ0 ++ # P → A :: (x0 ++ B :: Γ3), C)). repeat rewrite <- app_assoc. auto.
      pose (IH _ J5 _ x1 _ _ _ _ _ J6 J7). destruct s.
      assert (OrLRule [((Γ0 ++ A :: x0) ++ A0 :: Γ3, C);((Γ0 ++ A :: x0) ++ B :: Γ3, C)]
      ((Γ0 ++ A :: x0) ++ A0 ∨ B :: Γ3, C)). apply OrLRule_I. apply OrL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ A :: x0 ++ A0 :: Γ3, C); (Γ0 ++ A :: x0 ++ B :: Γ3, C)])
      (Γ0 ++ A :: x0 ++ A0 ∨ B :: Γ3, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
      assert (J4 :(Γ2 ++ A0 :: x ++ # P → A :: Γ1, C) = ((Γ2 ++ A0 :: x) ++ # P → A :: Γ1, C)). repeat rewrite <- app_assoc. auto.
      pose (IH _ J2 _ x0 _ _ _ _ _ J3 J4). destruct s.
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      assert (J7 : (Γ2 ++ B :: x ++ # P → A :: Γ1, C) = ((Γ2 ++ B :: x) ++ # P → A :: Γ1, C)). repeat rewrite <- app_assoc. auto.
      pose (IH _ J5 _ x1 _ _ _ _ _ J6 J7). destruct s.
      assert (OrLRule [((Γ2 ++ A0 :: x) ++ A :: Γ1, C);((Γ2 ++ B :: x) ++ A :: Γ1, C)]
      ((Γ2 ++ A0 ∨ B :: x) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. apply OrLRule_I. apply OrL in H0.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
      (ps:=[((Γ2 ++ A0 :: x) ++ A :: Γ1, C); ((Γ2 ++ B :: x) ++ A :: Γ1, C)])
      ((Γ2 ++ A0 ∨ B :: x) ++ A :: Γ1, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (J50: derrec_height x = derrec_height x). auto.
    assert (J51: list_exch_L (Γ2 ++ A0 :: Γ3, B) (A0 :: Γ0 ++ # P → A :: Γ1, B)).
    assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). auto. rewrite H0.
    assert (A0 :: Γ0 ++ # P → A :: Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). rewrite <- H2. auto. rewrite H1.
    apply list_exch_LI.
    pose (G4iSLT_hpadm_list_exch_L (derrec_height x) _ x J50 _ J51). destruct s.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J4: (A0 :: Γ0 ++ # P → A :: Γ1, B) = ((A0 :: Γ0) ++ # P → A :: Γ1, B)). repeat rewrite <- app_assoc. auto.
    pose (IH _ J2 _ x0 _ _ _ _ _ J3 J4). destruct s.
    assert (ImpRRule [(([] ++ A0 :: Γ0) ++ A :: Γ1, B)] ([] ++ Γ0 ++ A :: Γ1, A0 → B)). repeat rewrite <- app_assoc. apply ImpRRule_I.
    simpl in H0. apply ImpR in H0. pose (dlCons x1 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[((A0 :: Γ0) ++ A :: Γ1, B)]) (Γ0 ++ A :: Γ1, A0 → B) H0 d0). exists d1. simpl. rewrite dersrec_height_nil ; auto.
    simpl in l0. lia.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   + assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [# P → A]) ++ x1) ++ # P0 :: Γ3 ++ A0 :: Γ4, C) = (Γ0 ++ # P → A :: x1 ++ # P0 :: Γ3 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
       assert (AtomImpL1Rule [((Γ0 ++ A :: x1) ++ # P0 :: Γ3 ++ A0 :: Γ4, C)]
       ((Γ0 ++ A :: x1) ++ # P0 :: Γ3 ++ # P0 → A0 :: Γ4, C)). apply AtomImpL1Rule_I.
       repeat rewrite <- app_assoc in H0. apply AtomImpL1 in H0.
       pose (dlCons x0 DersNilF).
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: x1 ++ # P0 :: Γ3 ++ A0 :: Γ4, C)])
       (Γ0 ++ A :: x1 ++ # P0 :: Γ3 ++ # P0 → A0 :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. subst. repeat rewrite <- app_assoc. exists x. simpl. lia. }
      { assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ # P0 :: ((x0 ++ [# P → A]) ++ x2) ++ A0 :: Γ4, C) = ((Γ2 ++ # P0 :: x0) ++ # P → A :: x2 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
         pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
         assert (AtomImpL1Rule [((Γ2 ++ # P0 :: x0) ++ A :: x2 ++ A0 :: Γ4, C)]
         ((Γ2 ++ # P0 :: x0) ++ A :: x2 ++ # P0 → A0 :: Γ4, C)).
         assert ((Γ2 ++ # P0 :: x0) ++ A :: x2 ++ A0 :: Γ4 = Γ2 ++ # P0 :: (x0 ++ A :: x2) ++ A0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H0.
         assert ((Γ2 ++ # P0 :: x0) ++ A :: x2 ++ # P0 → A0 :: Γ4 = Γ2 ++ # P0 :: (x0 ++ A :: x2) ++ # P0 → A0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H1. apply AtomImpL1Rule_I. apply AtomImpL1 in H0. pose (dlCons x1 DersNilF).
         pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ # P0 :: x0) ++ A :: x2 ++ A0 :: Γ4, C)])
         ((Γ2 ++ # P0 :: x0) ++ A :: x2 ++ # P0 → A0 :: Γ4, C) H0 d0). exists d1. simpl.
         rewrite dersrec_height_nil. lia. reflexivity. }
      { repeat destruct s. repeat destruct p ; subst.
         assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ # P0 :: Γ3 ++ A0 :: x1 ++ # P → A :: Γ1, C) = ((Γ2 ++ # P0 :: Γ3 ++ A0 :: x1) ++ # P → A :: Γ1, C)).
         repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
         pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
         assert (AtomImpL1Rule [((Γ2 ++ # P0 :: Γ3 ++ A0 :: x1) ++ A :: Γ1, C)]
         ((Γ2 ++ # P0 :: Γ3 ++ # P0 → A0 :: x1) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
         apply AtomImpL1Rule_I. apply AtomImpL1 in H0. pose (dlCons x0 DersNilF).
         pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ # P0 :: Γ3 ++ A0 :: x1) ++ A :: Γ1, C)])
         ((Γ2 ++ # P0 :: Γ3 ++ # P0 → A0 :: x1) ++ A :: Γ1, C) H0 d0). exists d1. simpl.
         rewrite dersrec_height_nil. lia. reflexivity. }
  (* AtomImpL2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1 ; subst. exists x ; simpl ; lia.
   + assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [# P → A]) ++ x1) ++ A0 :: Γ3 ++ # P0 :: Γ4, C) = (Γ0 ++ # P → A :: x1 ++ A0 :: Γ3 ++ # P0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
       assert (AtomImpL2Rule [((Γ0 ++ A :: x1) ++ A0 :: Γ3 ++ # P0 :: Γ4, C)]
       ((Γ0 ++ A :: x1) ++ # P0 → A0 :: Γ3 ++ # P0 :: Γ4, C)). apply AtomImpL2Rule_I.
       repeat rewrite <- app_assoc in H0. apply AtomImpL2 in H0.
       pose (dlCons x0 DersNilF).
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: x1 ++ A0 :: Γ3 ++ # P0 :: Γ4, C)])
       (Γ0 ++ A :: x1 ++ # P0 → A0 :: Γ3 ++ # P0 :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ A0 :: ((x0 ++ [# P → A]) ++ x2) ++ # P0 :: Γ4, C) = ((Γ2 ++ A0 :: x0) ++ # P → A :: x2 ++ # P0 :: Γ4, C)). repeat rewrite <- app_assoc. auto.
         pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
         assert (AtomImpL2Rule [((Γ2 ++ A0 :: x0) ++ A :: x2 ++ # P0 :: Γ4, C)]
         ((Γ2 ++ # P0 → A0 :: x0) ++ A :: x2 ++ # P0 :: Γ4, C)).
         assert ((Γ2 ++ A0 :: x0) ++ A :: x2 ++ # P0 :: Γ4 = Γ2 ++ A0 :: (x0 ++ A :: x2) ++ # P0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H0.
         assert ((Γ2 ++ # P0 → A0 :: x0) ++ A :: x2 ++ # P0  :: Γ4 = Γ2 ++ # P0 → A0 :: (x0 ++ A :: x2) ++ # P0 :: Γ4). repeat rewrite <- app_assoc. auto.
         rewrite H1. apply AtomImpL2Rule_I. apply AtomImpL2 in H0. pose (dlCons x1 DersNilF).
         pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ A0 :: x0) ++ A :: x2 ++ # P0 :: Γ4, C)])
         ((Γ2 ++ # P0 → A0 :: x0) ++ A :: x2 ++ # P0 :: Γ4, C) H0 d0). exists d1. simpl.
         rewrite dersrec_height_nil. lia. reflexivity. }
      { repeat destruct s. repeat destruct p ; subst.
         assert (J2: derrec_height x < S (dersrec_height d)). lia.
         assert (J3: derrec_height x = derrec_height x). reflexivity.
         assert (J4: (Γ2 ++ A0 :: Γ3 ++ # P0 :: x1 ++ # P → A :: Γ1, C) = ((Γ2 ++ A0 :: Γ3 ++ # P0 :: x1) ++ # P → A :: Γ1, C)).
         repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
         pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
         assert (AtomImpL2Rule [((Γ2 ++ A0 :: Γ3 ++ # P0 :: x1) ++ A :: Γ1, C)]
         ((Γ2 ++ # P0 → A0 :: Γ3 ++ # P0 :: x1) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
         apply AtomImpL2Rule_I. apply AtomImpL2 in H0. pose (dlCons x0 DersNilF).
         pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
         (ps:=[((Γ2 ++ A0 :: Γ3 ++ # P0 :: x1) ++ A :: Γ1, C)])
         ((Γ2 ++ # P0 → A0 :: Γ3 ++ # P0 :: x1) ++ A :: Γ1, C) H0 d0). exists d1. simpl.
         rewrite dersrec_height_nil. lia. reflexivity. }
 (* AndImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [# P → A]) ++ x1) ++ A0 → B → C0 :: Γ3, C) = (Γ0 ++ # P → A :: x1 ++ A0 → B → C0 :: Γ3, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
       assert (AndImpLRule [((Γ0 ++ A :: x1) ++ A0 → B → C0 :: Γ3, C)]
       ((Γ0 ++ A :: x1) ++ (A0 ∧ B) → C0 :: Γ3, C)). apply AndImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply AndImpL in H0.
       pose (dlCons x0 DersNilF).
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: x1 ++ A0 → B → C0 :: Γ3, C)])
       (Γ0 ++ A :: x1 ++ (A0 ∧ B) → C0 :: Γ3, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ2 ++ A0 → B → C0 :: x0 ++ # P → A :: Γ1, C) = ((Γ2 ++ A0 → B → C0 :: x0) ++ # P → A :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
       assert (AndImpLRule [((Γ2 ++ A0 → B → C0 :: x0) ++ A :: Γ1, C)]
       ((Γ2 ++ (A0 ∧ B) → C0 :: x0) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. apply AndImpLRule_I.
       apply AndImpL in H0. pose (dlCons x1 DersNilF).
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ A0 → B → C0 :: x0) ++ A :: Γ1, C)])
       ((Γ2 ++ (A0 ∧ B) → C0 :: x0) ++ A :: Γ1, C) H0 d0). exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [# P → A]) ++ x1) ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) = (Γ0 ++ # P → A ::  x1 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
       assert (OrImpLRule [((Γ0 ++ A :: x1) ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)]
       ((Γ0 ++ A :: x1) ++ (A0 ∨ B) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply OrImpL in H0.
       pose (dlCons x0 DersNilF).
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: x1 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)])
       (Γ0 ++ A :: x1 ++ (A0 ∨ B) → C0 :: Γ3 ++ Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J50: derrec_height x = derrec_height x). auto.
       assert (J51: list_exch_L (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) (Γ2 ++ A0 → C0 :: B → C0 :: x0 ++ # P → A :: Γ1, C)).
       assert (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4 = (Γ2 ++ [A0 → C0]) ++ [] ++ Γ3 ++ [B → C0] ++ Γ4).
       repeat rewrite <- app_assoc. auto. rewrite H0.
       assert (Γ2 ++ A0 → C0 :: B → C0 :: x0 ++ # P → A :: Γ1 = (Γ2 ++ [A0 → C0]) ++ [B → C0] ++ Γ3 ++ [] ++ Γ4).
       rewrite <- e1 ; repeat rewrite <- app_assoc ; auto. rewrite H1. apply list_exch_LI.
       pose (G4iSLT_hpadm_list_exch_L (derrec_height x) _ x J50 _ J51). destruct s.
       assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
       assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
       assert (J4: (Γ2 ++ A0 → C0 :: B → C0 :: x0 ++ # P → A :: Γ1, C) = ((Γ2 ++ A0 → C0 :: B → C0 :: x0) ++ # P → A :: Γ1, C)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x1 _ _ _ _ _ J3 J4). destruct s.
       assert (OrImpLRule [((Γ2 ++ A0 → C0 :: B → C0 :: x0) ++ A :: Γ1, C)]
       ((Γ2 ++ (A0 ∨ B) → C0 :: x0) ++ A :: Γ1, C)).
       assert ((Γ2 ++ A0 → C0 :: B → C0 :: x0) ++ A :: Γ1 = Γ2 ++ A0 → C0 :: [] ++ B → C0 :: x0 ++ A :: Γ1).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H0.
       assert ((Γ2 ++ (A0 ∨ B) → C0 :: x0) ++ A :: Γ1 = Γ2 ++ (A0 ∨ B) → C0 :: [] ++ x0 ++ A :: Γ1).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H1.
       apply OrImpLRule_I.  apply OrImpL in H0. pose (dlCons x2 DersNilF).
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ A0 → C0 :: B → C0 :: x0) ++ A :: Γ1, C)])
       ((Γ2 ++ (A0 ∨ B) → C0 :: x0) ++ A :: Γ1, C) H0 d0). exists d1. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
  (* ImpImpL *)
 * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (((Γ0 ++ [# P → A]) ++ x2) ++ B → C0 :: Γ3, A0 → B) = (Γ0 ++ # P → A :: x2 ++ B → C0 :: Γ3, A0 → B)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (((Γ0 ++ [# P → A]) ++ x2) ++ C0 :: Γ3, C) = (Γ0 ++ # P → A :: x2 ++ C0 :: Γ3, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J5 _ x0 _ _ _ _ _ J6 J7). destruct s.
       assert (ImpImpLRule [((Γ0 ++ A :: x2) ++ B → C0 :: Γ3, A0 → B);((Γ0 ++ A :: x2) ++ C0 :: Γ3, C)]
       ((Γ0 ++ A :: x2) ++ (A0 → B) → C0 :: Γ3, C)). apply ImpImpLRule_I.
       repeat rewrite <- app_assoc in H0. apply ImpImpL in H0.
       pose (dlCons x3 DersNilF). pose (dlCons x1 d0).
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[(Γ0 ++ A :: x2 ++ B → C0 :: Γ3, A0 → B); (Γ0 ++ A :: x2 ++ C0 :: Γ3, C)])
       (Γ0 ++ A :: x2 ++ (A0 → B) → C0 :: Γ3, C) H0 d1). repeat rewrite <- app_assoc. exists d2. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J2: derrec_height x < S (dersrec_height d)). lia.
       assert (J3: derrec_height x = derrec_height x). reflexivity.
       assert (J4: (Γ2 ++ B → C0 :: x1 ++ # P → A :: Γ1, A0 → B) = ((Γ2 ++ B → C0 :: x1) ++ # P → A :: Γ1, A0 → B)). repeat rewrite <- app_assoc. auto.
       pose (IH _ J2 _ x _ _ _ _ _ J3 J4). destruct s.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (Γ2 ++ C0 :: x1 ++ # P → A :: Γ1, C) = ((Γ2 ++ C0 :: x1) ++ # P → A :: Γ1, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J5 _ x0 _ _ _ _ _ J6 J7). destruct s.
       assert (ImpImpLRule [((Γ2 ++ B → C0 :: x1) ++ A :: Γ1, A0 → B);((Γ2 ++ C0 :: x1) ++ A :: Γ1, C)]
       ((Γ2 ++ (A0 → B) → C0 :: x1) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. apply ImpImpLRule_I.
       apply ImpImpL in H0. pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
       (ps:=[((Γ2 ++ B → C0 :: x1) ++ A :: Γ1, A0 → B); ((Γ2 ++ C0 :: x1) ++ A :: Γ1, C)])
       ((Γ2 ++ (A0 → B) → C0 :: x1) ++ A :: Γ1, C) H0 d1). exists d2. simpl.
       rewrite dersrec_height_nil. lia. reflexivity.
  (* BoxImpL *)
 * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (((Γ0 ++ [# P → A]) ++ x2) ++ B :: Γ3, C) = (Γ0 ++ # P → A :: x2 ++ B :: Γ3, C)).
       repeat rewrite <- app_assoc. auto.
       pose (IH _ J5 _ x0 _ _ _ _ _ J6 J7). destruct s.
       assert (J8: derrec_height x < S (dersrec_height d)). lia.
       assert (J9: derrec_height x = derrec_height x). reflexivity.
       assert (J10: (unBoxed_list ((Γ0 ++ [# P → A]) ++ x2) ++ B :: unBoxed_list Γ3 ++ [Box A0], A0) = (unBoxed_list Γ0 ++ # P → A :: unBoxed_list x2 ++ B :: unBoxed_list Γ3 ++ [Box A0], A0)).
       repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc ; simpl ; auto.
       pose (IH _ J8 _ x _ _ _ _ _ J9 J10). destruct s.
       assert (BoxImpLRule [(unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list x2 ++ B :: unBoxed_list Γ3 ++ [Box A0], A0);(Γ0 ++ A :: x2 ++ B :: Γ3, C)] (Γ0 ++ A :: x2 ++ Box A0 → B :: Γ3, C)).
       pose (@BoxImpLRule_I A0 B C (Γ0 ++ A :: x2) Γ3). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b ; auto.
       apply BoxImpL in H0.
       pose (unBox_left_hpadm_gen _ _ _ _ x3). destruct s. pose (dlCons x1 DersNilF). pose (dlCons x4 d0).
       pose (derI _ H0 d1). exists d2. simpl. rewrite dersrec_height_nil ; auto. simpl in l0. lia.
   +  repeat destruct s. repeat destruct p ; subst.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J7: (Γ2 ++ B :: x1 ++ # P → A :: Γ1, C) = ((Γ2 ++ B :: x1) ++ # P → A :: Γ1, C)).
       repeat rewrite <- app_assoc. auto. pose (IH _ J5 _ x0 _ _ _ _ _ J6 J7). destruct s.
       assert (J8: derrec_height x < S (dersrec_height d)). lia.
       assert (J9: derrec_height x = derrec_height x). reflexivity.
       assert (J10: (unBoxed_list Γ2 ++ B :: unBoxed_list (x1 ++ # P → A :: Γ1) ++ [Box A0], A0) = ((unBoxed_list Γ2 ++ B :: unBoxed_list x1) ++ # P → A :: unBoxed_list Γ1 ++ [Box A0], A0)).
       repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc ; simpl ; auto. pose (IH _ J8 _ x _ _ _ _ _ J9 J10). destruct s.
       assert (BoxImpLRule [((unBoxed_list Γ2 ++ B :: unBoxed_list x1) ++ unBox_formula A :: unBoxed_list Γ1 ++ [Box A0], A0);((Γ2 ++ B :: x1) ++ A :: Γ1, C)] ((Γ2 ++ Box A0 → B :: x1) ++ A :: Γ1, C)).
       pose (@BoxImpLRule_I A0 B C Γ2 (x1 ++ A :: Γ1)). repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b.
       repeat rewrite <- app_assoc ; simpl ; apply b. apply BoxImpL in H0.
       pose (unBox_left_hpadm_gen _ _ _ _ x3). destruct s. pose (dlCons x2 DersNilF). pose (dlCons x4 d0).
       pose (derI _ H0 d1).  exists d2. simpl. rewrite dersrec_height_nil ; auto. simpl in l0. lia.
  (* SLR *)
  * inversion H. subst. simpl.
    assert (SLRRule [(unBoxed_list (Γ0 ++ A :: Γ1) ++ [Box A0], A0)] (Γ0 ++ A :: Γ1, Box A0)). apply SLRRule_I ; auto. apply SLR in H0.
    assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    assert (J7: (unBoxed_list (Γ0 ++ # P → A :: Γ1) ++ [Box A0], A0) = (unBoxed_list Γ0 ++ # P → A :: unBoxed_list Γ1 ++ [Box A0], A0)).
    repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc ; simpl ; auto. pose (IH _ J5 _ x _ _ _ _ _ J6 J7). destruct s.
    pose (unBox_left_hpadm_gen _ _ _ _ x0). destruct s. repeat rewrite unBox_app_distrib in H0 ; simpl in H0 ; repeat rewrite <- app_assoc in H0.
    pose (dlCons x1 DersNilF). pose (derI _ H0 d0). exists d1. simpl. simpl in l. rewrite dersrec_height_nil. lia. auto.
Qed.

Theorem AtomImpL_inv : forall P A Γ0 Γ1 C, (derrec G4iSLT_rules (fun _ => False) (Γ0 ++ (# P → A) :: Γ1, C)) ->
                                      (derrec G4iSLT_rules (fun _ => False) (Γ0 ++ A :: Γ1, C)).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
assert (J2: (Γ0 ++ # P → A :: Γ1, C) = (Γ0 ++ # P → A :: Γ1, C)). auto.
pose (AtomImpL_hpinv (derrec_height X) (Γ0 ++ # P → A :: Γ1, C) X P A Γ0 Γ1 C J1 J2). destruct s. auto.
Qed.

Theorem AtomImpL1_hpinv : forall (k : nat) concl
        (D0 : derrec G4iSLT_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem, ((AtomImpL1Rule [prem] concl) ->
          existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) prem),
          (derrec_height D1 <= k)))).
Proof.
intros. inversion H0. subst.
assert (J1:  derrec_height D0 = derrec_height D0). auto.
assert (J2: (Γ0 ++ # P :: Γ1 ++ # P → A :: Γ2, C) = ((Γ0 ++ # P :: Γ1) ++ # P → A :: Γ2, C)).
repeat rewrite <- app_assoc ; auto.
pose (@AtomImpL_hpinv _ _ _ _ _ _ _ _ J1 J2). destruct s.
assert (Γ0 ++ # P :: Γ1 ++ A :: Γ2 = (Γ0 ++ # P :: Γ1) ++ A :: Γ2). rewrite <- app_assoc ; auto. rewrite H.
exists x. simpl in l. lia.
Qed.

Theorem AtomImpL2_hpinv : forall (k : nat) concl
        (D0 : derrec G4iSLT_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem, ((AtomImpL2Rule [prem] concl) ->
          existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) prem),
          (derrec_height D1 <= k)))).
Proof.
intros. inversion H0. subst.
assert (J1:  derrec_height D0 = derrec_height D0). auto.
assert (J2: (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C) = (Γ0 ++ # P → A :: Γ1 ++ # P :: Γ2, C)).
repeat rewrite <- app_assoc ; auto.
pose (@AtomImpL_hpinv _ _ _ _ _ _ _ _ J1 J2). destruct s. exists x. lia.
Qed.








