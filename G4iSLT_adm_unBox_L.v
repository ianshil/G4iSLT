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

Theorem unBox_left_hpadm0 : forall (k : nat) s
        (D0 : derrec G4iSLT_rules (fun _ => False) s),
        k = (derrec_height D0) ->
        (forall A Γ0 Γ1 C, (s = (Γ0 ++ Box A :: Γ1, C)) ->
          existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) (Γ0 ++ A :: Γ1, C)),
          derrec_height D1 <= k).
Proof.
assert (DersNilF: dersrec G4iSLT_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall s
        (D0 : derrec G4iSLT_rules (fun _ => False) s),
        x = (derrec_height D0) ->
        (forall A Γ0 Γ1 C, (s = (Γ0 ++ Box A :: Γ1, C)) ->
          existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) (Γ0 ++ A :: Γ1, C)),
          derrec_height D1 <= x))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0 ; simpl in IH.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei A Γ0 Γ1 C eq. subst. inversion g ; subst.
  (* IdP *)
  * inversion H ; subst.  assert (InT (# P) (Γ0 ++ A :: Γ1)). assert (InT (# P) (Γ0 ++ Box A :: Γ1)). rewrite <- H2. apply InT_or_app ; right ; apply InT_eq.
    apply InT_app_or in H0. apply InT_or_app ; destruct H0 ; auto. inversion i ; subst. inversion H1. right ; apply InT_cons ; auto.
    apply InT_split in H0. destruct H0. destruct s ; subst. rewrite e. pose (IdPRule_I P x x0). apply IdP in i.
    pose (derI _ i d). exists d0 ; simpl ; lia.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ A :: Γ1)). assert (InT (⊥) (Γ0 ++ Box A :: Γ1)). rewrite <- H2. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. inversion i ; subst. inversion H1. apply InT_or_app. right.
    apply InT_cons. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e. pose (BotLRule_I x x0 C). apply BotL in b.
    pose (derI _ b d). exists d0 ; auto.
   (* AndR *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    pose (AndRRule_I A0 B (Γ0 ++ A :: Γ1)). apply AndR in a.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    assert (J7: (Γ0 ++ Box A :: Γ1, A0) = (Γ0 ++ Box A :: Γ1, A0)). auto. pose (IH _ J5 _ _ J6 _ _ _ _ J7).
    assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J10: (Γ0 ++ Box A :: Γ1, B) = (Γ0 ++ Box A :: Γ1, B)). auto. pose (IH _ J8 _ _ J9 _ _ _ _ J10).
    destruct s. destruct s0. pose (dlCons x2 DersNilF). pose (dlCons x1 d0).  pose (derI _ a d1). exists d2. simpl.
    rewrite dersrec_height_nil ; auto. lia.
  (* AndL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + pose (AndLRule_I A0 B C (Γ0 ++ A :: x1) Γ3). repeat rewrite <- app_assoc in a ; simpl in a ; apply AndL in a.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (((Γ0 ++ [Box A]) ++ x1) ++ A0 :: B :: Γ3, C) = (Γ0 ++ Box A :: x1 ++ A0 :: B :: Γ3, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s. pose (dlCons x0 DersNilF). pose (derI _ a d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
    + repeat destruct s ; repeat destruct p ; subst.
        assert (AndLRule [((Γ2 ++ A0 :: B :: x0) ++ A :: Γ1, C)] ((Γ2 ++ And A0 B :: x0) ++ A :: Γ1, C)).
        pose (AndLRule_I A0 B C Γ2 (x0 ++ A :: Γ1)). repeat rewrite <- app_assoc ; simpl ; auto. apply AndL in H0.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (Γ2 ++ A0 :: B :: x0 ++ Box A :: Γ1, C) = ((Γ2 ++ A0 :: B :: x0) ++ Box A :: Γ1, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s. pose (dlCons x1 DersNilF). pose (derI _ H0 d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* OrR1 *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    pose (OrR1Rule_I A0 B (Γ0 ++ A :: Γ1)). apply OrR1 in o.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    assert (J7: (Γ0 ++ Box A :: Γ1, A0) = (Γ0 ++ Box A :: Γ1, A0)). auto. pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s.
    pose (dlCons x0 DersNilF). pose (derI _ o d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* OrR2 *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    pose (OrR2Rule_I A0 B (Γ0 ++ A :: Γ1)). apply OrR2 in o.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    assert (J7: (Γ0 ++ Box A :: Γ1, B) = (Γ0 ++ Box A :: Γ1, B)). auto. pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s.
    pose (dlCons x0 DersNilF). pose (derI _ o d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* OrL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + pose (OrLRule_I A0 B C (Γ0 ++ A :: x2) Γ3). repeat rewrite <- app_assoc in o ; simpl in o ; apply OrL in o.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (((Γ0 ++ [Box A]) ++ x2) ++ A0 :: Γ3, C) = (Γ0 ++ Box A :: x2 ++ A0 :: Γ3, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7).
        assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
        assert (J10: (((Γ0 ++ [Box A]) ++ x2) ++ B :: Γ3, C) = (Γ0 ++ Box A :: x2 ++ B :: Γ3, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J8 _ _ J9 _ _ _ _ J10). destruct s. destruct s0. pose (dlCons x3 DersNilF). pose (dlCons x1 d0). pose (derI _ o d1).
        exists d2. simpl ; rewrite dersrec_height_nil ; auto ; lia.
    + repeat destruct s ; repeat destruct p ; subst.
        assert (OrLRule [((Γ2 ++ A0 :: x1) ++ A :: Γ1, C); ((Γ2 ++ B :: x1) ++ A :: Γ1, C)] ((Γ2 ++ A0 ∨ B :: x1) ++ A :: Γ1, C)).
        pose (OrLRule_I A0 B C Γ2 (x1 ++ A :: Γ1)). repeat rewrite <- app_assoc ; simpl ; auto. apply OrL in H0.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (Γ2 ++ A0 :: x1 ++ Box A :: Γ1, C) = ((Γ2 ++ A0 :: x1) ++ Box A :: Γ1, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7).
        assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
        assert (J10: (Γ2 ++ B :: x1 ++ Box A :: Γ1, C) = ((Γ2 ++ B :: x1) ++ Box A :: Γ1, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J8 _ _ J9 _ _ _ _ J10). destruct s. destruct s0. pose (dlCons x3 DersNilF). pose (dlCons x2 d0). pose (derI _ H0 d1).
        exists d2. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* ImpR *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (exch (Γ2 ++ A0 :: Γ3, B) (A0 :: Γ0 ++ Box A :: Γ1, B)). rewrite <- H2. pose (list_exch_LI [] [] Γ2 [A0] Γ3 B). simpl in l ; auto.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (G4iSLT_hpadm_list_exch_L _ _ _ J6 _ H0). destruct s.
    pose (ImpRRule_I A0 B [] (Γ0 ++ A :: Γ1)). simpl in i. apply ImpR in i.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
    assert (J7: (A0 :: Γ0 ++ Box A :: Γ1, B) = ((A0 :: Γ0) ++ Box A :: Γ1, B)). auto. pose (IH _ J5 _ _ J9 _ _ _ _ J7). simpl in s. destruct s.
    pose (dlCons x1 DersNilF). pose (derI _ i d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + pose (AtomImpL1Rule_I P A0 C (Γ0 ++ A :: x1) Γ3 Γ4). repeat rewrite <- app_assoc in a ; simpl in a ; apply AtomImpL1 in a.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (((Γ0 ++ [Box A]) ++ x1) ++ # P :: Γ3 ++ A0 :: Γ4, C) = (Γ0 ++ Box A :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s. pose (dlCons x0 DersNilF). pose (derI _ a d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
    + repeat destruct s ; repeat destruct p ; subst. apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
        -- inversion e1.
        -- pose (AtomImpL1Rule_I P A0 C Γ2 (x0 ++ A :: x2) Γ4). repeat rewrite <- app_assoc in a ; simpl in a ; apply AtomImpL1 in a. repeat rewrite <- app_assoc.
            assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
            assert (J7: (Γ2 ++ # P :: ((x0 ++ [Box A]) ++ x2) ++ A0 :: Γ4, C) = ((Γ2 ++ # P :: x0) ++ Box A :: x2 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc ; simpl ; auto.
            pose (IH _ J5 _ _ J6 _ _ _ _ J7). repeat rewrite <- app_assoc in s ; simpl in s. destruct s. pose (dlCons x1 DersNilF). pose (derI _ a d0).
            exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
        -- repeat destruct s ; repeat destruct p ; subst.
            pose (AtomImpL1Rule_I P A0 C Γ2 Γ3 (x1 ++ A :: Γ1)). repeat rewrite <- app_assoc in a ; simpl in a ; apply AtomImpL1 in a. repeat rewrite <- app_assoc ; simpl.
            assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
            assert (J7: (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ Box A :: Γ1, C) = ((Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ Box A :: Γ1, C)).
            repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto.
            pose (IH _ J5 _ _ J6 _ _ _ _ J7). repeat rewrite <- app_assoc in s ; simpl in s ; repeat rewrite <- app_assoc in s ; simpl in s. destruct s. pose (dlCons x0 DersNilF).
            pose (derI _ a d0). repeat rewrite <- app_assoc ; simpl. exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* AtomImpL2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + pose (AtomImpL2Rule_I P A0 C (Γ0 ++ A :: x1) Γ3 Γ4). repeat rewrite <- app_assoc in a ; simpl in a ; apply AtomImpL2 in a.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (((Γ0 ++ [Box A]) ++ x1) ++ A0 :: Γ3 ++ # P :: Γ4, C) = (Γ0 ++ Box A :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s. pose (dlCons x0 DersNilF). pose (derI _ a d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
    + repeat destruct s ; repeat destruct p ; subst. apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
        -- inversion e1.
        -- pose (AtomImpL2Rule_I P A0 C Γ2 (x0 ++ A :: x2) Γ4). repeat rewrite <- app_assoc in a ; simpl in a ; apply AtomImpL2 in a. repeat rewrite <- app_assoc.
            assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
            assert (J7: (Γ2 ++ A0 :: ((x0 ++ [Box A]) ++ x2) ++ # P :: Γ4, C) = ((Γ2 ++ A0 :: x0) ++ Box A :: x2 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc ; simpl ; auto.
            pose (IH _ J5 _ _ J6 _ _ _ _ J7). repeat rewrite <- app_assoc in s ; simpl in s. destruct s. pose (dlCons x1 DersNilF). pose (derI _ a d0).
            exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
        -- repeat destruct s ; repeat destruct p ; subst.
            pose (AtomImpL2Rule_I P A0 C Γ2 Γ3 (x1 ++ A :: Γ1)). repeat rewrite <- app_assoc in a ; simpl in a ; apply AtomImpL2 in a. repeat rewrite <- app_assoc ; simpl.
            assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
            assert (J7: (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ Box A :: Γ1, C) = ((Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ Box A :: Γ1, C)).
            repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto.
            pose (IH _ J5 _ _ J6 _ _ _ _ J7). repeat rewrite <- app_assoc in s ; simpl in s ; repeat rewrite <- app_assoc in s ; simpl in s. destruct s. pose (dlCons x0 DersNilF).
            pose (derI _ a d0). repeat rewrite <- app_assoc ; simpl. exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
 (* AndImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + pose (AndImpLRule_I A0 B C0 C (Γ0 ++ A :: x1) Γ3). repeat rewrite <- app_assoc in a ; simpl in a ; apply AndImpL in a.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (((Γ0 ++ [Box A]) ++ x1) ++ A0 → B → C0 :: Γ3, C) = (Γ0 ++ Box A :: x1 ++ A0 → B → C0 :: Γ3, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s. pose (dlCons x0 DersNilF). pose (derI _ a d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
    + repeat destruct s ; repeat destruct p ; subst.
        pose (AndImpLRule_I A0 B C0 C Γ2 (x0 ++ A :: Γ1)). repeat rewrite <- app_assoc in a ; simpl in a ; apply AndImpL in a. repeat rewrite <- app_assoc.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (Γ2 ++ A0 → B → C0 :: x0 ++ Box A :: Γ1, C) = ((Γ2 ++ A0 → B → C0 :: x0) ++ Box A :: Γ1, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). repeat rewrite <- app_assoc in s ; simpl in s. destruct s. pose (dlCons x1 DersNilF).
        pose (derI _ a d0). repeat rewrite <- app_assoc ; simpl ; exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* OrImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + pose (OrImpLRule_I A0 B C0 C (Γ0 ++ A :: x1) Γ3 Γ4). repeat rewrite <- app_assoc in o ; simpl in o ; apply OrImpL in o.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (((Γ0 ++ [Box A]) ++ x1) ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) = (Γ0 ++ Box A :: x1 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s. pose (dlCons x0 DersNilF). pose (derI _ o d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
    + repeat destruct s ; repeat destruct p ; subst.
       assert (exch (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) (B → C0 :: Γ2 ++ A0 → C0 :: x0 ++ Box A :: Γ1, C)). rewrite <- e1.
       pose (list_exch_LI [] [] (Γ2 ++ A0 → C0 :: Γ3) [B → C0] Γ4 C). simpl in l ; repeat rewrite <- app_assoc in l ; auto.
       assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (G4iSLT_hpadm_list_exch_L _ _ _ J6 _ H0). destruct s.
       pose (OrImpLRule_I A0 B C0 C Γ2 x0 (A :: Γ1)). repeat rewrite <- app_assoc in o ; simpl in o ; apply OrImpL in o. repeat rewrite <- app_assoc. simpl.
       assert (J5: derrec_height x1 < S (dersrec_height d)). lia. assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
       assert (J7: (B → C0 :: Γ2 ++ A0 → C0 :: x0 ++ Box A :: Γ1, C) = ((B → C0 :: Γ2 ++ A0 → C0 :: x0) ++ Box A :: Γ1, C)).
       repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto.
       pose (IH _ J5 _ _ J9 _ _ _ _ J7). repeat rewrite <- app_assoc in s ; simpl in s ; repeat rewrite <- app_assoc in s ; simpl in s.
       pose (list_exch_LI [] [B → C0] (Γ2 ++ A0 → C0 :: x0) [] (A :: Γ1) C). simpl in l0 ; repeat rewrite <- app_assoc in l0 ; auto. simpl in l0.
       destruct s. assert (J8: derrec_height x2 = derrec_height x2). reflexivity.
       pose (G4iSLT_hpadm_list_exch_L _ _ _ J8 _ l0). destruct s. pose (dlCons x3 DersNilF). pose (derI _ o d0). exists d1.
       simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* ImpImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + pose (ImpImpLRule_I A0 B C0 C (Γ0 ++ A :: x2) Γ3). repeat rewrite <- app_assoc in i ; simpl in i ; apply ImpImpL in i.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (((Γ0 ++ [Box A]) ++ x2) ++ B → C0 :: Γ3, A0 → B) = (Γ0 ++ Box A :: x2 ++ B → C0 :: Γ3, A0 → B)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). destruct s.
        assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
        assert (J10: (((Γ0 ++ [Box A]) ++ x2) ++ C0 :: Γ3, C) = (Γ0 ++ Box A :: x2 ++ C0 :: Γ3, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J8 _ _ J9 _ _ _ _ J10). destruct s. pose (dlCons x3 DersNilF). pose (dlCons x1 d0). pose (derI _ i d1). exists d2.
        simpl ; rewrite dersrec_height_nil ; auto ; lia.
    + repeat destruct s ; repeat destruct p ; subst.
       pose (ImpImpLRule_I A0 B C0 C Γ2 (x1 ++ A :: Γ1)). repeat rewrite <- app_assoc in i ; simpl in i ; apply ImpImpL in i.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        assert (J7: (Γ2 ++ B → C0 :: x1 ++ Box A :: Γ1, A0 → B) = ((Γ2 ++ B → C0 :: x1) ++ Box A :: Γ1, A0 → B)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J5 _ _ J6 _ _ _ _ J7). repeat rewrite <- app_assoc in s ; simpl in s. destruct s.
        assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
        assert (J10: (Γ2 ++ C0 :: x1 ++ Box A :: Γ1, C) = ((Γ2 ++ C0 :: x1) ++ Box A :: Γ1, C)). repeat rewrite <- app_assoc ; simpl ; auto.
        pose (IH _ J8 _ _ J9 _ _ _ _ J10). repeat rewrite <- app_assoc in s ; simpl in s. destruct s. pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
        repeat rewrite <- app_assoc ; simpl. pose (derI _ i d1). exists d2. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* BoxImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + assert (BoxImpLRule [(unBoxed_list (Γ0 ++ A :: x2) ++ B :: unBoxed_list Γ3 ++ [Box A0], A0);(Γ0 ++ A :: x2 ++ B :: Γ3, C)] (Γ0 ++ A :: x2 ++ Box A0 → B :: Γ3, C)).
       pose (@BoxImpLRule_I A0 B C (Γ0 ++ A :: x2) Γ3).
       repeat rewrite unBox_app_distrib ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite <- app_assoc ; simpl ; apply b ; auto.
       assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
       assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J10: (((Γ0 ++ [Box A]) ++ x2) ++ B :: Γ3, C) = (Γ0 ++ Box A :: x2 ++ B :: Γ3, C)). repeat rewrite <- app_assoc ; simpl ; auto.
       pose (IH _ J8 _ _ J9 _ _ _ _ J10). destruct s. simpl in IH.
       assert (existsT2 D1 : derrec G4iSLT_rules (fun _ : Seq => False) (unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list x2 ++ B :: unBoxed_list Γ3 ++ [Box A0], A0),
       derrec_height D1 <= derrec_height x).
       { destruct (dec_is_box A).
         -- destruct s ; subst. simpl.
             assert (J7: (unBoxed_list ((Γ0 ++ [Box (Box x3)]) ++ x2) ++ B :: unBoxed_list Γ3 ++ [Box A0], A0) = (unBoxed_list Γ0 ++ Box x3 :: unBoxed_list x2 ++ B :: unBoxed_list Γ3 ++ [Box A0], A0)).
             repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto.
             pose (IH _ J5 _ _ J6 _ _ _ _ J7) ; auto.
         -- assert (unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list x2 ++ B :: unBoxed_list Γ3 ++ [Box A0] = unBoxed_list ((Γ0 ++ [Box A]) ++ x2) ++ B :: unBoxed_list Γ3 ++ [Box A0]).
             repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto. destruct A ; auto. exfalso ; apply f ;eexists ; auto.
             rewrite H1. exists x ; auto. }
       apply BoxImpL in H0. repeat rewrite unBox_app_distrib in H0 ; repeat rewrite unBox_app_distrib in H0 ; repeat rewrite <- app_assoc in H0 ; simpl in H0 ; auto.
       destruct X. pose (dlCons x1 DersNilF). pose (dlCons x3 d0). pose (derI _ H0 d1). exists d2. simpl ; rewrite dersrec_height_nil ; auto ; lia.
    + repeat destruct s ; repeat destruct p ; subst.
       assert (BoxImpLRule [(unBoxed_list Γ2 ++ B :: (unBoxed_list x1 ++ unBox_formula A :: unBoxed_list Γ1) ++ [Box A0], A0);((Γ2 ++ B :: x1) ++ A :: Γ1, C)] ((Γ2 ++ Box A0 → B :: x1) ++ A :: Γ1, C)).
       pose (@BoxImpLRule_I A0 B C Γ2 (x1 ++ A :: Γ1)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite <- app_assoc ; simpl ; apply b ; auto.
       assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
       assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
       assert (J10: (Γ2 ++ B :: x1 ++ Box A :: Γ1, C) = ((Γ2 ++ B :: x1) ++ Box A :: Γ1, C)). repeat rewrite <- app_assoc ; simpl ; auto.
       pose (IH _ J8 _ _ J9 _ _ _ _ J10). destruct s. simpl in IH.
       assert (existsT2 D1 : derrec G4iSLT_rules (fun _ : Seq => False) (unBoxed_list Γ2 ++ B :: (unBoxed_list x1 ++ unBox_formula A :: unBoxed_list Γ1) ++ [Box A0], A0),
       derrec_height D1 <= derrec_height x).
       { destruct (dec_is_box A).
         -- destruct s ; subst. simpl.
             assert (J7: (unBoxed_list Γ2 ++ B :: unBoxed_list (x1 ++ Box (Box x3) :: Γ1) ++ [Box A0], A0) = ((unBoxed_list Γ2 ++ B :: unBoxed_list x1) ++ Box x3 :: unBoxed_list Γ1 ++ [Box A0], A0)).
             repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto.
             pose (IH _ J5 _ _ J6 _ _ _ _ J7) ; auto. repeat rewrite <- app_assoc ; simpl. repeat rewrite <- app_assoc in s ; auto.
         -- assert (unBoxed_list Γ2 ++ B :: (unBoxed_list x1 ++ unBox_formula A :: unBoxed_list Γ1) ++ [Box A0] = unBoxed_list Γ2 ++ B :: unBoxed_list (x1 ++ Box A :: Γ1) ++ [Box A0]).
             repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto. destruct A ; auto. exfalso ; apply f ;eexists ; auto.
             rewrite H1. exists x ; auto. }
       apply BoxImpL in H0. destruct X. pose (dlCons x2 DersNilF). pose (dlCons x3 d0). pose (derI _ H0 d1). exists d2. simpl ; rewrite dersrec_height_nil ; auto ; lia.
  (* SLR *)
  * inversion H ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (SLRRule [(unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list Γ1 ++ [Box A0], A0)] (Γ0 ++ A :: Γ1, Box A0)).
    pose (@SLRRule_I A0 (Γ0 ++ A :: Γ1)).  repeat rewrite unBox_app_distrib in s ; repeat rewrite <- app_assoc in s ; simpl in s ; repeat rewrite <- app_assoc ; simpl ; apply s ; auto.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    assert (existsT2 D1 : derrec G4iSLT_rules (fun _ : Seq => False) (unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list Γ1 ++ [Box A0], A0),
    derrec_height D1 <= derrec_height x).
    { destruct (dec_is_box A).
      -- destruct s ; subst. simpl.
          assert (J7: (unBoxed_list (Γ0 ++ Box (Box x0) :: Γ1) ++ [Box A0], A0) = (unBoxed_list Γ0 ++ (Box x0) :: unBoxed_list Γ1 ++ [Box A0], A0)).
          repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto.
          pose (IH _ J5 _ _ J6 _ _ _ _ J7) ; auto.
      -- assert (unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list Γ1 ++ [Box A0] = unBoxed_list (Γ0 ++ Box A :: Γ1) ++ [Box A0]).
          repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto. destruct A ; auto. exfalso ; apply f ;eexists ; auto.
          rewrite H1. exists x ; auto. }
     apply SLR in H0. destruct X. pose (dlCons x0 DersNilF). pose (derI _ H0 d0). exists d1. simpl ; rewrite dersrec_height_nil ; auto ; lia.
Qed.

Theorem unBox_left_hpadm : forall A Γ0 Γ1 C (D: G4iSLT_prv (Γ0 ++ Box A :: Γ1, C)),
        existsT2 (D0: G4iSLT_prv (Γ0 ++ A :: Γ1, C)), derrec_height D0 <= derrec_height D.
Proof.
intros.
assert (J1: derrec_height D = derrec_height D). reflexivity.
assert (J2: (Γ0 ++ Box A :: Γ1, C) = (Γ0 ++ Box A :: Γ1, C)). auto.
pose (unBox_left_hpadm0 _ _ _ J1 _ _ _ _ J2) ; auto.
Qed.

Theorem unBox_left_hpadm_gen : forall A Γ0 Γ1 C (D: G4iSLT_prv (Γ0 ++ A :: Γ1, C)),
        existsT2 (D0: G4iSLT_prv (Γ0 ++ unBox_formula A :: Γ1, C)), derrec_height D0 <= derrec_height D.
Proof.
intros. destruct (dec_is_box A).
- destruct s ; subst ; simpl. apply unBox_left_hpadm.
- destruct A ; simpl ; auto. 1-5: exists D ; auto. exfalso. apply f ; eexists ; auto.
Qed.

Theorem unBox_left_adm : forall A Γ0 Γ1 C, (G4iSLT_prv (Γ0 ++ Box A :: Γ1, C)) -> (G4iSLT_prv (Γ0 ++ A :: Γ1, C)).
Proof.
intros.
apply unBox_left_hpadm in X ; auto.
Qed.

Theorem unBox_left_adm_gen : forall A Γ0 Γ1 C, (G4iSLT_prv (Γ0 ++ A :: Γ1, C)) -> (G4iSLT_prv (Γ0 ++ unBox_formula A :: Γ1, C)).
Proof.
intros.
apply unBox_left_hpadm_gen in X ; auto.
Qed.

Theorem unBoxed_list_left_adm_gen : forall Γ1 Γ0 Γ2 C, (G4iSLT_prv (Γ0 ++ Γ1 ++ Γ2, C)) -> (G4iSLT_prv (Γ0 ++ unBoxed_list Γ1 ++ Γ2, C)).
Proof.
induction Γ1 ; simpl ; intros ; auto. apply unBox_left_adm_gen in X.
pose (IHΓ1 (Γ0 ++ [unBox_formula a]) Γ2). repeat rewrite <- app_assoc in g ; simpl in g ; auto.
Qed.

