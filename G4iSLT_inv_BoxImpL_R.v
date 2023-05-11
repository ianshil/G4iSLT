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


Theorem BoxImpL_hpinv_R : forall (k : nat) concl
        (D0 : derrec G4iSLT_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem1 prem2, ((BoxImpLRule [prem1;prem2] concl) ->
          existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) prem2),
          derrec_height D1 <= k))).
Proof.
assert (DersNilF: dersrec G4iSLT_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec G4iSLT_rules (fun _ : Seq => False) concl),
x = (derrec_height D0) ->
          ((forall prem1 prem2, ((BoxImpLRule [prem1;prem2] concl) ->
          existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) prem2),
          derrec_height D1 <= x))))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. intros prem1 prem2 RA. inversion RA. subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ Box A → B :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (Γ0 ++  B :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. assert (IdPRule [] (x ++ # P :: x0, # P)). apply IdPRule_I. apply IdP in H1.
    pose (derI _ H1 DersNilF). exists d0. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ Box A → B :: Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (⊥) (Γ0 ++ B :: Γ1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, C)). apply BotLRule_I. apply BotL in H1.
    pose (derI _ H1 DersNilF). exists d0. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J1: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A], A); (Γ0 ++ B :: Γ1, A0)] (Γ0 ++ Box A → B :: Γ1, A0)).
    apply BoxImpLRule_I. simpl in IH.
    assert (J2: derrec_height x < S (dersrec_height d)). lia. assert (J3: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J2 _ _ J3 _ _ J1). destruct s.
    assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ0 ++ B :: Γ1, B0)] (Γ0 ++ Box A → B :: Γ1, B0)).
    apply BoxImpLRule_I ; auto.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (AndRRule [(Γ0 ++ B :: Γ1, A0); (Γ0 ++ B :: Γ1, B0)] (Γ0 ++ B :: Γ1, And A0 B0)).
    apply AndRRule_I. pose (dlCons x2 DersNilF). pose (dlCons x1 d0). apply AndR in H0.
    pose (derI _ H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndLRule [((Γ0 ++ B :: x0) ++ A0 :: B0 :: Γ3, C)] ((Γ0 ++ B :: x0) ++ And A0 B0 :: Γ3, C)).
      apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x0 ++ unBox_formula A0 :: unBox_formula B0 :: unBoxed_list Γ3 ++ [Box A], A);(Γ0 ++ B :: x0 ++ A0 :: B0 :: Γ3, C)]
       (((Γ0 ++ [Box A → B]) ++ x0) ++ A0 :: B0 :: Γ3, C)). repeat rewrite <- app_assoc ; simpl.
       pose (@BoxImpLRule_I A B C Γ0 (x0 ++ A0 :: B0 :: Γ3)).
       repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
       assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s. pose (dlCons x1 DersNilF). apply AndL in H0.
       pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndLRule [(Γ2 ++ A0 :: B0 :: x ++ B :: Γ1, C)]((Γ2 ++ A0 ∧ B0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc ; simpl ;
      apply AndLRule_I.
      assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ unBox_formula A0 :: unBox_formula B0 :: unBoxed_list x ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ A0 :: B0 :: x ++ B :: Γ1, C)] (Γ2 ++ A0 :: B0 :: x ++ Box A → B :: Γ1, C)).
      pose (@BoxImpLRule_I A B C (Γ2 ++ A0 :: B0 :: x) Γ1).
      repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s. pose (dlCons x1 DersNilF). apply AndL in H0.
      pose (derI _ H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ0 ++ B :: Γ1, A0)] (Γ0 ++ Box A → B :: Γ1, A0)). apply BoxImpLRule_I ; auto.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (OrR1Rule [(Γ0 ++ B :: Γ1, A0)] (Γ0 ++ B :: Γ1, Or A0 B0)). apply OrR1Rule_I. pose (dlCons x0 DersNilF).
    apply OrR1 in H0. pose (derI _ H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ0 ++ B :: Γ1, B0)] (Γ0 ++ Box A → B :: Γ1, B0)).
    apply BoxImpLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (OrR2Rule [(Γ0 ++ B :: Γ1, B0)]
    (Γ0 ++ B :: Γ1, Or A0 B0)). apply OrR2Rule_I. pose (dlCons x0 DersNilF).
    apply OrR2 in H0. pose (derI _ H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (OrLRule [((Γ0 ++ B :: x0) ++ A0 :: Γ3, C);((Γ0 ++ B :: x0) ++ B0 :: Γ3, C)] ((Γ0 ++ B :: x0) ++ Or A0 B0 :: Γ3, C)).
      apply OrLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x0 ++ unBox_formula A0 :: unBoxed_list Γ3 ++ [Box A], A);(Γ0 ++ B :: x0 ++ A0 :: Γ3, C)]
       (((Γ0 ++ [Box A → B]) ++ x0) ++ A0 :: Γ3, C)). repeat rewrite <- app_assoc ; simpl.
       pose (@BoxImpLRule_I A B C Γ0 (x0 ++ A0 :: Γ3)).
       repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
       assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       assert (J7: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x0 ++ unBox_formula B0 :: unBoxed_list Γ3 ++ [Box A], A);(Γ0 ++ B :: x0 ++ B0 :: Γ3, C)]
       (((Γ0 ++ [Box A → B]) ++ x0) ++ B0 :: Γ3, C)). repeat rewrite <- app_assoc ; simpl.
       pose (@BoxImpLRule_I A B C Γ0 (x0 ++ B0 :: Γ3)).
       repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
       assert (J8: derrec_height x1 < S (dersrec_height d)). lia. assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
       pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
       pose (dlCons x3 DersNilF). pose (dlCons x2 d0). apply OrL in H0.
       pose (derI _ H0 d1). repeat rewrite <- app_assoc. exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (OrLRule [(Γ2 ++ A0 :: x ++ B :: Γ1, C);(Γ2 ++ B0 :: x ++ B :: Γ1, C)]((Γ2 ++ A0 ∨ B0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc ; simpl ;
      apply OrLRule_I.
      assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ unBox_formula A0 :: unBoxed_list x ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ A0 :: x ++ B :: Γ1, C)] (Γ2 ++ A0 :: x ++ Box A → B :: Γ1, C)).
      pose (@BoxImpLRule_I A B C (Γ2 ++ A0 :: x) Γ1).
      repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
      assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: BoxImpLRule [(unBoxed_list Γ2 ++ unBox_formula B0 :: unBoxed_list x ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ B0 :: x ++ B :: Γ1, C)] (Γ2 ++ B0 :: x ++ Box A → B :: Γ1, C)).
      pose (@BoxImpLRule_I A B C (Γ2 ++ B0 :: x) Γ1).
      repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
      assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      pose (dlCons x3 DersNilF). pose (dlCons x2 d0). apply OrL in H0.
      pose (derI _ H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl.
     assert (J50: derrec_height x = derrec_height x). auto.
     pose (list_exch_LI [] Γ2 [] [A0] Γ3 B0). simpl in l. rewrite H2 in l.
     pose (G4iSLT_hpadm_list_exch_L _ _ _ J50 _ l). destruct s.
     pose (ImpRRule_I A0 B0 [] (Γ0 ++ B :: Γ1)). simpl in i. apply ImpR in i.
     assert (J4: BoxImpLRule [(unBox_formula A0 :: unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A], A);(A0 :: Γ0 ++ B :: Γ1, B0)] (A0 :: Γ0 ++ Box A → B :: Γ1, B0)).
     pose (@BoxImpLRule_I A B B0 (A0 :: Γ0) Γ1). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
     assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
     assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
     pose (IH _ J5 _ _ J6 _ _ J4). destruct s. pose (dlCons x1 DersNilF).
     pose (derI _ i d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (AtomImpL1Rule [((Γ0 ++ B :: x1) ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       ((Γ0 ++ B :: x1) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, C)). apply AtomImpL1Rule_I.
       assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x1 ++ # P :: unBoxed_list Γ3 ++ unBox_formula A0 :: unBoxed_list Γ4 ++ [Box A], A); (Γ0 ++ B :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       (((Γ0 ++ [Box A → B]) ++ x1) ++ # P :: Γ3 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc ; simpl.
       pose (@BoxImpLRule_I A B C Γ0 (x1 ++ # P :: Γ3 ++ A0 :: Γ4)).
       repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x0 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc in H0.
       pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (AtomImpL1Rule [(Γ2 ++ # P :: (x0 ++ B :: x2) ++ A0 :: Γ4, C)]
        (Γ2 ++ # P :: (x0 ++ B :: x2) ++ Imp # P A0 :: Γ4, C)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc in H0 ; simpl in H0.
        assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ # P :: unBoxed_list x0 ++ B :: unBoxed_list x2 ++ unBox_formula A0 :: unBoxed_list Γ4 ++ [Box A], A); (Γ2 ++ # P :: x0 ++ B :: x2 ++ A0 :: Γ4, C)]
        (Γ2 ++ # P :: ((x0 ++ [Box A → B]) ++ x2) ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc ; simpl.
        pose (@BoxImpLRule_I A B C (Γ2 ++ # P :: x0) (x2 ++ A0 :: Γ4)).
        repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
        repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply AtomImpL1 in H0.
        pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
      { repeat destruct s ; repeat destruct p ; subst. simpl.
        assert (AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ B :: Γ1, C)]
        (Γ2 ++ # P :: Γ3 ++ Imp # P A0 :: x1 ++ B :: Γ1, C)). apply AtomImpL1Rule_I.
        assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ # P :: unBoxed_list Γ3 ++ unBox_formula A0 :: unBoxed_list x1 ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ B :: Γ1, C)]
        (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ Box A → B :: Γ1, C)).
        pose (@BoxImpLRule_I A B C (Γ2 ++ # P :: Γ3 ++ A0 :: x1) Γ1).
        repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
        repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x0 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
  (* AtomImpL2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (AtomImpL2Rule [((Γ0 ++ B :: x1) ++ A0 :: Γ3 ++ # P :: Γ4, C)]
       ((Γ0 ++ B :: x1) ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
       assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x1 ++ unBox_formula A0 :: unBoxed_list Γ3 ++ # P :: unBoxed_list Γ4 ++ [Box A], A); (Γ0 ++ B :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)]
       (((Γ0 ++ [Box A → B]) ++ x1) ++ A0 :: Γ3 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc ; simpl.
       pose (@BoxImpLRule_I A B C Γ0 (x1 ++ A0 :: Γ3 ++ # P :: Γ4)).
       repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
       repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
       assert (J5: derrec_height x < S (dersrec_height d)). lia.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
       pose (dlCons x0 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc in H0.
       pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (AtomImpL2Rule [(Γ2 ++ A0 :: (x0 ++ B :: x2) ++ # P :: Γ4, C)]
        (Γ2 ++ Imp # P A0 :: (x0 ++ B :: x2) ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc in H0 ; simpl in H0.
        assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ unBox_formula A0 :: unBoxed_list x0 ++ B :: unBoxed_list x2 ++ # P :: unBoxed_list Γ4 ++ [Box A], A); (Γ2 ++ A0 :: x0 ++ B :: x2 ++ # P :: Γ4, C)]
        (Γ2 ++ A0 :: ((x0 ++ [Box A → B]) ++ x2) ++ # P :: Γ4, C)). repeat rewrite <- app_assoc ; simpl.
        pose (@BoxImpLRule_I A B C (Γ2 ++ A0 :: x0) (x2 ++ # P :: Γ4)).
        repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
        repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x1 DersNilF). apply AtomImpL2 in H0.
        pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
      { repeat destruct s ; repeat destruct p ; subst. simpl.
        assert (AtomImpL2Rule [(Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ B :: Γ1, C)]
        (Γ2 ++ Imp # P A0 :: Γ3 ++ # P :: x1 ++ B :: Γ1, C)). apply AtomImpL2Rule_I.
        assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ unBox_formula A0 :: unBoxed_list Γ3 ++ # P :: unBoxed_list x1 ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ B :: Γ1, C)]
        (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ Box A → B :: Γ1, C)).
        pose (@BoxImpLRule_I A B C (Γ2 ++ A0 :: Γ3 ++ # P :: x1) Γ1).
        repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
        repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.
        assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
        pose (dlCons x0 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
 (* AndImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     assert (AndImpLRule [((Γ0 ++ B :: x0) ++ A0 → B0 → C0 :: Γ3, C)]
    ((Γ0 ++ B :: x0) ++ (A0 ∧ B0) → C0 :: Γ3, C)). apply AndImpLRule_I. repeat rewrite <- app_assoc in H0.
     assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x0 ++ A0 → B0 → C0 :: unBoxed_list Γ3 ++ [Box A], A);(Γ0 ++ B :: x0 ++ A0 → B0 → C0 :: Γ3, C)]
     (((Γ0 ++ [Box A → B]) ++ x0) ++ A0 → B0 → C0 :: Γ3, C)). repeat rewrite <- app_assoc ; simpl.
     pose (@BoxImpLRule_I A B C Γ0 (x0 ++ A0 → B0 → C0 :: Γ3)).
     repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
     repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
     assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
     pose (IH _ J5 _ _ J6 _ _ J4). destruct s. pose (dlCons x1 DersNilF). apply AndImpL in H0.
     pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndImpLRule [((Γ2 ++ Imp A0 (Imp B0 C0) :: x) ++ B :: Γ1, C)]
      ((Γ2 ++ Imp (And A0 B0) C0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc. apply AndImpLRule_I.
      assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ A0 → B0 → C0 :: unBoxed_list x ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ A0 → B0 → C0 :: x ++ B :: Γ1, C)]
      (Γ2 ++ A0 → B0 → C0 :: x ++ Box A → B :: Γ1, C)).
      pose (@BoxImpLRule_I A B C (Γ2 ++ A0 → B0 → C0 :: x) Γ1).
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      pose (dlCons x1 DersNilF). apply AndImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc in H0. pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
      lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (OrImpLRule [((Γ0 ++ B :: x0) ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)]
       ((Γ0 ++ B :: x0) ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x0 ++ Imp A0 C0 :: unBoxed_list Γ3 ++ Imp B0 C0 :: unBoxed_list Γ4 ++ [Box A], A);(Γ0 ++ B :: x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)]
       (((Γ0 ++ [Box A → B]) ++ x0) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)). repeat rewrite <- app_assoc. simpl.
       pose (@BoxImpLRule_I A B C Γ0 (x0 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4)).
       repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
       repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
       assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). destruct s. pose (dlCons x1 DersNilF). apply OrImpL in H0.
       pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J50: derrec_height x0 = derrec_height x0). auto.
      assert (J51: list_exch_L (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C) (Γ2 ++ A0 → C0 :: B0 → C0 :: x ++ Box A → B :: Γ1, C)).
      pose (list_exch_LI (Γ2 ++ [A0 → C0]) [] Γ3 [B0 → C0] Γ4 C). simpl in l. repeat rewrite <- app_assoc in l. simpl in l. rewrite <- e0 ; auto.
      pose (G4iSLT_hpadm_list_exch_L _ _ _ J50 _ J51). destruct s. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
      assert (OrImpLRule [(Γ2 ++ A0 → C0 :: [] ++ B0 → C0 :: x ++ B :: Γ1, C)] (Γ2 ++ Imp (Or A0 B0) C0 :: [] ++ x ++ B :: Γ1, C)).
      apply OrImpLRule_I. simpl in H0.
      assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ A0 → C0 :: B0 → C0 :: unBoxed_list x ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ A0 → C0 :: B0 → C0 :: x ++ B :: Γ1, C)]
      (Γ2 ++ A0 → C0 :: B0 → C0 :: x ++ Box A → B :: Γ1, C)).
      pose (@BoxImpLRule_I A B C (Γ2 ++ A0 → C0 :: B0 → C0 :: x) Γ1).
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J5: derrec_height x1 < S (dersrec_height d)). lia. assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s. pose (dlCons x2 DersNilF). apply OrImpL in H0.
      pose (derI _ H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* ImpImpL *)
 * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
      assert (ImpImpLRule [((Γ0 ++ B :: x0) ++ Imp B0 C0 :: Γ3, Imp A0 B0); ((Γ0 ++ B :: x0) ++ C0 :: Γ3, C)]
      ((Γ0 ++ B :: x0) ++ Imp (Imp A0 B0) C0 :: Γ3, C)). apply ImpImpLRule_I. apply ImpImpL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x0 ++ B0 → C0 :: unBoxed_list Γ3 ++ [Box A], A);(Γ0 ++ B :: x0 ++ B0 → C0 :: Γ3, A0 → B0)]
      (((Γ0 ++ [Box A → B]) ++ x0) ++ B0 → C0 :: Γ3, A0 → B0)). repeat rewrite <- app_assoc. simpl.
      pose (@BoxImpLRule_I A B (A0 → B0) Γ0 (x0 ++ B0 → C0 :: Γ3)).
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x0 ++ unBox_formula C0 :: unBoxed_list Γ3 ++ [Box A], A);(Γ0 ++ B :: x0 ++ C0 :: Γ3, C)] (((Γ0 ++ [Box A → B]) ++ x0) ++ C0 :: Γ3, C)).
      pose (@BoxImpLRule_I A B C Γ0 (x0 ++ C0 :: Γ3)). repeat rewrite <- app_assoc. simpl.
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia. assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s. pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI _ H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      repeat rewrite <- app_assoc. simpl.
      assert (ImpImpLRule [(Γ2 ++ Imp B0 C0 :: x ++ B :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x ++ B :: Γ1, C)]
      (Γ2 ++ Imp (Imp A0 B0) C0 :: x ++ B :: Γ1, C)). apply ImpImpLRule_I. apply ImpImpL in H0.
      assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ B0 → C0 :: unBoxed_list x ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ B0 → C0 :: x ++ B :: Γ1, A0 → B0)]
      (Γ2 ++ B0 → C0 :: x ++ Box A → B :: Γ1, A0 → B0)).
      pose (@BoxImpLRule_I A B (A0 → B0) (Γ2 ++ B0 → C0 :: x) Γ1).
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: BoxImpLRule [(unBoxed_list Γ2 ++ unBox_formula C0 :: unBoxed_list x ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ C0 :: x ++ B :: Γ1, C)] (Γ2 ++ C0 :: x ++ Box A → B :: Γ1, C)).
      pose (@BoxImpLRule_I A B C (Γ2 ++ C0 :: x) Γ1).
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia. assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s. pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
      pose (derI _ H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BoxImpL *)
 * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1. subst. exists x0. lia.
   + assert (J4: BoxImpLRule [(unBoxed_list Γ0 ++ B :: unBoxed_list x2 ++ unBox_formula B0 :: unBoxed_list Γ3 ++ [Box A], A);(Γ0 ++ B :: x2 ++ B0 :: Γ3, C)] (((Γ0 ++ [Box A → B]) ++ x2) ++ B0 :: Γ3, C)).
      pose (@BoxImpLRule_I A B C Γ0 (x2 ++ B0 :: Γ3)). repeat rewrite <- app_assoc. simpl.
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: BoxImpLRule [(unBoxed_list (unBoxed_list Γ0) ++ B :: unBoxed_list (unBoxed_list x2) ++ unBox_formula B0 :: unBoxed_list (unBoxed_list Γ3) ++ [A0] ++ [Box A], A);(unBoxed_list Γ0 ++ B :: unBoxed_list x2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0)]
      (unBoxed_list ((Γ0 ++ [Box A → B]) ++ x2) ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0)). repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc. simpl.
      pose (@BoxImpLRule_I A B A0 (unBoxed_list Γ0) (unBoxed_list x2 ++ B0 :: unBoxed_list Γ3  ++ [Box A0])).
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J8: derrec_height x < S (dersrec_height d)). lia. assert (J9: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      assert (J10: BoxImpLRule [(unBoxed_list Γ0 ++ unBox_formula B :: unBoxed_list x2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0); (Γ0 ++ B :: x2 ++ B0 :: Γ3, C)] (Γ0 ++ B :: x2 ++ Box A0 → B0 :: Γ3, C)).
      pose (@BoxImpLRule_I A0 B0 C (Γ0 ++ B :: x2) Γ3).
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b. apply BoxImpL in J10. pose (dlCons x1 DersNilF).
      pose (unBox_left_hpadm_gen _ _ _ _ x3). destruct s. pose (dlCons x4 d0).
      pose (derI _ J10 d1). repeat rewrite <- app_assoc. exists d2. simpl. rewrite dersrec_height_nil ; auto. simpl in l0. lia.
   + repeat destruct s. repeat destruct p ; subst.
      assert (J4: BoxImpLRule [(unBoxed_list Γ2 ++ unBox_formula B0 :: unBoxed_list x1 ++ B :: unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ B0 :: x1 ++ B :: Γ1, C)] (Γ2 ++ B0 :: x1 ++ Box A → B :: Γ1, C)).
      pose (@BoxImpLRule_I A B C (Γ2 ++ B0 :: x1) Γ1).
      repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
      assert (J7: BoxImpLRule [(unBoxed_list (unBoxed_list Γ2) ++ unBox_formula B0 :: unBoxed_list (unBoxed_list x1) ++ B :: unBoxed_list (unBoxed_list Γ1) ++ [A0] ++ [Box A], A);(unBoxed_list Γ2 ++ B0 :: unBoxed_list x1 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0)]
      (unBoxed_list Γ2 ++ B0 :: unBoxed_list (x1 ++ Box A → B :: Γ1) ++ [Box A0], A0)). rewrite unBox_app_distrib ; repeat rewrite <- app_assoc. simpl.
      pose (@BoxImpLRule_I A B A0 (unBoxed_list Γ2 ++ B0 :: unBoxed_list x1) (unBoxed_list Γ1 ++ [Box A0])).
      repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
      assert (J8: derrec_height x < S (dersrec_height d)). lia. assert (J9: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). destruct s.
      assert (J10: BoxImpLRule [(unBoxed_list Γ2 ++ B0 :: unBoxed_list x1 ++ unBox_formula B :: unBoxed_list Γ1 ++ [Box A0], A0);(Γ2 ++ B0 :: x1 ++ B :: Γ1, C)] ((Γ2 ++ Box A0 → B0 :: x1) ++ B :: Γ1, C)).
      pose (@BoxImpLRule_I A0 B0 C Γ2 (x1 ++ B :: Γ1)). repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc. simpl.
      repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
      repeat rewrite <- app_assoc in b ; simpl in b ; apply b. apply BoxImpL in J10. pose (dlCons x2 DersNilF).
      pose (unBox_left_hpadm_gen B (unBoxed_list Γ2 ++ B0 :: unBoxed_list x1) (unBoxed_list Γ1 ++ [Box A0]) A0).
      repeat rewrite <- app_assoc in s ; simpl in s. pose (s x3). destruct s0. pose (dlCons x4 d0).
      pose (derI _ J10 d1). exists d2. simpl. rewrite dersrec_height_nil ; auto. simpl in l0. lia.
  (* SLR *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (J4: BoxImpLRule [(unBoxed_list (unBoxed_list Γ0) ++ B :: unBoxed_list (unBoxed_list Γ1) ++ [A0] ++ [Box A], A);(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0)]
    (unBoxed_list (Γ0 ++ Box A → B :: Γ1) ++ [Box A0], A0)). repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc. simpl.
    pose (@BoxImpLRule_I A B A0 (unBoxed_list Γ0) (unBoxed_list Γ1 ++ [Box A0])).
    repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
    repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). destruct s.
    assert (J10: SLRRule [(unBoxed_list Γ0 ++ unBox_formula B :: unBoxed_list Γ1 ++ [Box A0], A0)] (Γ0 ++ B :: Γ1, Box A0)).
    pose (@SLRRule_I A0 (Γ0 ++ B :: Γ1)).
    repeat rewrite unBox_app_distrib in s ; simpl in s ; repeat rewrite <- app_assoc in s ; simpl in s ; apply s.
    apply SLR in J10. pose (unBox_left_hpadm_gen _ _ _ _ x0). destruct s.
    pose (dlCons x1 DersNilF). pose (derI _ J10 d0). exists d1. simpl. rewrite dersrec_height_nil ; auto. simpl in l0. lia.
Qed.

Theorem BoxImpL_inv_R : forall concl prem1 prem2, (derrec G4iSLT_rules (fun _ => False) concl) ->
                                      (BoxImpLRule [prem1;prem2] concl) ->
                                      (derrec G4iSLT_rules (fun _ => False) prem2).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (BoxImpL_hpinv_R _ _ X J1). pose (s _ _ H). destruct s0. assumption.
Qed.







