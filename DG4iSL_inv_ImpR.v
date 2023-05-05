Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.
Require Import DG4iSL_remove_list.
Require Import DG4iSL_dec.
Require Import DG4iSL_exch.
Require Import DG4iSL_wkn.
Require Import DG4iSL_adm_unBox_L.

Theorem ImpR_hpinv : forall (k : nat) concl
        (D0 : derrec G4iSL_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem, ((ImpRRule [prem] concl) ->
          existsT2 (D1 : derrec G4iSL_rules (fun _ => False) prem),
          derrec_height D1 <= k))).
Proof.
assert (DersNilF: dersrec G4iSL_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec G4iSL_rules (fun _ : Seq => False) concl),
x = derrec_height D0 ->
((forall prem, ((ImpRRule [prem] concl) ->
          existsT2 (D1 : derrec G4iSL_rules (fun _ => False) prem),
          derrec_height D1 <= x))))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. intros prem RA. inversion RA. subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ A :: Γ1)). assert (InT (⊥) (Γ0 ++ Γ1)). rewrite <- H2. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, B)). apply BotLRule_I. apply BotL in H0.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[]) (x ++ ⊥ :: x0, B) H0 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H.
  (* AndL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    pose (ImpRRule_I A B [] (Γ2 ++ A0 :: B0 :: Γ3)). simpl in i.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ i). destruct s. pose (dlCons x0 DersNilF).
    pose (AndLRule_I A0 B0 B (A :: Γ2) Γ3). simpl in a. apply AndL in a. pose (derI _ a d0).
    assert (J1: derrec_height d1 = derrec_height d1). auto.
    pose (list_exch_LI [] [A] [] Γ0 Γ1 B). simpl in l0. rewrite <- H2 in l0.
    pose (G4iSL_hpadm_list_exch_L _ _ d1 J1 _ l0). destruct s. exists x1. simpl in l1.
    rewrite dersrec_height_nil in l1. lia. auto.
  (* OrR1 *)
  * inversion H.
  (* OrR2 *)
  * inversion H.
  (* OrL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    pose (ImpRRule_I A B [] (Γ2 ++ A0 :: Γ3)). simpl in i. pose (ImpRRule_I A B [] (Γ2 ++ B0 :: Γ3)). simpl in i0.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ i). destruct s.
    assert (J7: derrec_height x0 < S (dersrec_height d)). lia. assert (J8: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J7 _ _ J8 _ i0). destruct s. pose (dlCons x2 DersNilF). pose (dlCons x1 d0).
    pose (OrLRule_I A0 B0 B (A :: Γ2) Γ3). simpl in o. apply OrL in o. pose (derI _ o d1).
    assert (J1: derrec_height d2 = derrec_height d2). auto.
    pose (list_exch_LI [] [A] [] Γ0 Γ1 B). simpl in l1. rewrite <- H2 in l1.
    pose (G4iSL_hpadm_list_exch_L _ _ d2 J1 _ l1). destruct s. exists x3. simpl in l2.
    rewrite dersrec_height_nil in l2. lia. auto.
  (* ImpR *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (J1: derrec_height x = derrec_height x). auto.
    assert (J2: list_exch_L (Γ2 ++ A :: Γ3, B) (A :: Γ0 ++ Γ1, B)).
    rewrite <- H2. assert (A :: Γ2 ++ Γ3 = [] ++ [A] ++ Γ2 ++ [] ++ Γ3). auto. rewrite H0.
    assert (Γ2 ++ A :: Γ3 = [] ++ [] ++ Γ2 ++ [A] ++ Γ3). auto. rewrite H1. apply list_exch_LI.
    pose (G4iSL_hpadm_list_exch_L (derrec_height x) (Γ2 ++ A :: Γ3, B) x J1 (A :: Γ0 ++ Γ1, B) J2).
    destruct s.
    assert (J3: derrec_height x0 = derrec_height x0). auto.
    assert (J4: list_exch_L (A :: Γ0 ++ Γ1, B) (Γ0 ++ A :: Γ1, B)).
    assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). auto. rewrite H0.
    assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). auto. rewrite H1. apply list_exch_LI.
    pose (G4iSL_hpadm_list_exch_L (derrec_height x0) (A :: Γ0 ++ Γ1, B) x0 J3 (Γ0 ++ A :: Γ1, B) J4).
    destruct s. exists x1. lia.
  (* AtomImpL1 *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    pose (ImpRRule_I A B [] (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4)). simpl in i.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ i). destruct s. pose (dlCons x0 DersNilF).
    pose (AtomImpL1Rule_I P A0 B (A :: Γ2) Γ3 Γ4). simpl in a. apply AtomImpL1 in a. pose (derI _ a d0).
    assert (J1: derrec_height d1 = derrec_height d1). auto.
    pose (list_exch_LI [] [A] [] Γ0 Γ1 B). simpl in l0. rewrite <- H2 in l0.
    pose (G4iSL_hpadm_list_exch_L _ _ d1 J1 _ l0). destruct s. exists x1. simpl in l1.
    rewrite dersrec_height_nil in l1. lia. auto.
  (* AtomImpL2 *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    pose (ImpRRule_I A B [] (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4)). simpl in i.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ i). destruct s. pose (dlCons x0 DersNilF).
    pose (AtomImpL2Rule_I P A0 B (A :: Γ2) Γ3 Γ4). simpl in a. apply AtomImpL2 in a. pose (derI _ a d0).
    assert (J1: derrec_height d1 = derrec_height d1). auto.
    pose (list_exch_LI [] [A] [] Γ0 Γ1 B). simpl in l0. rewrite <- H2 in l0.
    pose (G4iSL_hpadm_list_exch_L _ _ d1 J1 _ l0). destruct s. exists x1. simpl in l1.
    rewrite dersrec_height_nil in l1. lia. auto.
 (* AndImpL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    pose (ImpRRule_I A B [] (Γ2 ++ A0 → B0 → C :: Γ3)). simpl in i.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ i). destruct s. pose (dlCons x0 DersNilF).
    pose (AndImpLRule_I A0 B0 C B (A :: Γ2) Γ3). simpl in a. apply AndImpL in a. pose (derI _ a d0).
    assert (J1: derrec_height d1 = derrec_height d1). auto.
    pose (list_exch_LI [] [A] [] Γ0 Γ1 B). simpl in l0. rewrite <- H2 in l0.
    pose (G4iSL_hpadm_list_exch_L _ _ d1 J1 _ l0). destruct s. exists x1. simpl in l1.
    rewrite dersrec_height_nil in l1. lia. auto.
  (* OrImpL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    pose (ImpRRule_I A B [] (Γ2 ++ A0 → C :: Γ3 ++ B0 → C :: Γ4)). simpl in i.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ i). destruct s. pose (dlCons x0 DersNilF).
    pose (OrImpLRule_I A0 B0 C B (A :: Γ2) Γ3 Γ4). simpl in o. apply OrImpL in o. pose (derI _ o d0).
    assert (J1: derrec_height d1 = derrec_height d1). auto.
    pose (list_exch_LI [] [A] [] Γ0 Γ1 B). simpl in l0. rewrite <- H2 in l0.
    pose (G4iSL_hpadm_list_exch_L _ _ d1 J1 _ l0). destruct s. exists x1. simpl in l1.
    rewrite dersrec_height_nil in l1. lia. auto.
  (* ImpImpL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    pose (ImpRRule_I A B [] (Γ2 ++ C :: Γ3)). simpl in i.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J5 _ _ J6 _ i). destruct s.
    assert (J1: derrec_height x = derrec_height x). auto.
    pose (wkn_LI A [] (Γ2 ++ B0 → C :: Γ3) (A0 → B0)). simpl in w.
    pose (G4iSL_wkn_L x J1 w). destruct s. pose (dlCons x1 DersNilF). pose (dlCons x2 d0).
    pose (ImpImpLRule_I A0 B0 C B (A :: Γ2) Γ3). simpl in i0. apply ImpImpL in i0. pose (derI _ i0 d1).
    assert (J2: derrec_height d2 = derrec_height d2). auto.
    pose (list_exch_LI [] [A] [] Γ0 Γ1 B). simpl in l1. rewrite <- H2 in l1.
    pose (G4iSL_hpadm_list_exch_L _ _ d2 J2 _ l1). destruct s. exists x3. simpl in l2.
    rewrite dersrec_height_nil in l2. lia. auto.
  (* BoxImpL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    pose (ImpRRule_I A B [] (Γ2 ++ B0 :: Γ3)). simpl in i.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J5 _ _ J6 _ i). destruct s.
    assert (J1: derrec_height x = derrec_height x). auto.
    pose (wkn_LI A [] (unBoxed_list Γ2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0]) A0). simpl in w.
    pose (G4iSL_wkn_L x J1 w). destruct s. pose (dlCons x1 DersNilF).
    assert (BoxImpLRule [((unBox_formula A :: unBoxed_list Γ2) ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0); ((A :: Γ2) ++ B0 :: Γ3, B)] ((A :: Γ2) ++ Box A0 → B0 :: Γ3, B)).
    pose (@BoxImpLRule_I A0 B0 B (A :: Γ2) Γ3). simpl in b ; simpl ; apply b.
    apply BoxImpL in H0. repeat rewrite <- app_assoc in H0. simpl in H0.
    pose (unBox_left_hpadm_gen A [] (unBoxed_list Γ2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0]) A0 x2).
    simpl in s. destruct s. pose (dlCons x3 d0). pose (derI _ H0 d1).
    assert (J2: derrec_height d2 = derrec_height d2). auto.
    pose (list_exch_LI [] [A] [] Γ0 Γ1 B). simpl in l1. rewrite <- H2 in l2.
    pose (G4iSL_hpadm_list_exch_L _ _ d2 J2 _ l2). destruct s. exists x4. simpl in l3.
    rewrite dersrec_height_nil in l3. lia. auto.
  (* GLR *)
  * inversion H.
Qed.

Theorem ImpR_inv : forall concl prem, (derrec G4iSL_rules (fun _ => False) concl) ->
                                      (ImpRRule [prem] concl) ->
                                      (derrec G4iSL_rules (fun _ => False) prem).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (ImpR_hpinv _  _ X J1). pose (s _ H). destruct s0. assumption.
Qed.
