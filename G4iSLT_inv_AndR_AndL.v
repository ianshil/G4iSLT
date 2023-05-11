Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import G4iSLT_calc.
Require Import G4iSLT_remove_list.
Require Import G4iSLT_list_lems.
Require Import G4iSLT_dec.
Require Import G4iSLT_exch.
Require Import G4iSLT_wkn.
Require Import G4iSLT_adm_unBox_L.

Theorem AndR_AndL_hpinv : forall (k : nat) concl
        (D0 : derrec G4iSLT_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem, ((AndLRule [prem] concl) ->
          existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) prem),
          derrec_height D1 <= k))) *
          ((forall prem1 prem2, ((AndRRule [prem1; prem2] concl) ->
          existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) prem1)
                   (D2 : derrec G4iSLT_rules (fun _ => False) prem2),
          (derrec_height D1 <= k) * (derrec_height D2 <= k)))).
Proof.
assert (DersNilF: dersrec G4iSLT_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec G4iSLT_rules (fun _ : Seq => False) concl), x = derrec_height D0 ->
((forall prem, ((AndLRule [prem] concl) -> existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) prem),
 derrec_height D1 <= x))) * ((forall prem1 prem2, ((AndRRule [prem1; prem2] concl) ->
 existsT2 (D1 : derrec G4iSLT_rules (fun _ => False) prem1) (D2 : derrec G4iSLT_rules (fun _ => False) prem2),
          (derrec_height D1 <= x) * (derrec_height D2 <= x)))))).
apply p. intros n IH. clear p.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. split.

(* Invertibility AndL *)
{ intros prem RA. inversion RA. subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ And A B :: Γ1)). rewrite <- H2. apply InT_or_app. right. apply InT_eq.
    assert (InT # P (Γ0 ++ A :: B :: Γ1)). apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. apply InT_cons. assumption. apply InT_split in H1. destruct H1.
    destruct s. rewrite e. assert (IdPRule [] (x ++ # P :: x0, # P)). apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[]) (x ++ # P :: x0, # P) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (Bot) (Γ0 ++ And A B :: Γ1)). rewrite <- H2. apply InT_or_app. right. apply InT_eq.
    assert (InT (Bot) (Γ0 ++ A :: B :: Γ1)). apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. apply InT_cons. auto. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ Bot :: x0, C)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[]) (x ++ Bot :: x0, C) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J1: AndLRule [(Γ0 ++ A :: B :: Γ1, B0)] (Γ0 ++ And A B :: Γ1, B0)). apply AndLRule_I. simpl in IH.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia. assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J2 _ _ J3). destruct p. clear s0. pose (s _ J1). destruct s0. clear s.
    assert (J4: AndLRule [(Γ0 ++ A :: B :: Γ1, A0)] (Γ0 ++ And A B :: Γ1, A0)). apply AndLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
    assert (AndRRule [(Γ0 ++ A :: B :: Γ1, A0); (Γ0 ++ A :: B :: Γ1, B0)]
   (Γ0 ++ A :: B :: Γ1, And A0 B0)). apply AndRRule_I. pose (dlCons x1 DersNilF). pose (dlCons x2 d0). apply AndR in H0.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: B :: Γ1, A0); (Γ0 ++ A :: B :: Γ1, B0)])
    (Γ0 ++ A :: B :: Γ1, And A0 B0) H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AndL *)
  * inversion H ; subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. exists x0. lia.
   + destruct x.
      { inversion e0. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. repeat rewrite <- app_assoc. simpl.
      exists x. lia. }
      { inversion e0.  subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J4: AndLRule [((Γ2 ++ A0 :: B0 :: x) ++ A :: B :: Γ1, C)] ((Γ2 ++ A0 :: B0 :: x) ++ And A B :: Γ1, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (AndLRule [(Γ2 ++ A0 :: B0 :: x ++ A :: B :: Γ1, C)] (Γ2 ++ And A0 B0 :: x ++ A :: B :: Γ1, C)).  apply AndLRule_I.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s. pose (dlCons x1 DersNilF). apply AndL in H0.
        pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 :: B0 :: x ++ A :: B :: Γ1, C)])
        (Γ2 ++ And A0 B0 :: x ++ A :: B :: Γ1, C) H0 d0). exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
    + destruct x.
       { simpl in e0. inversion e0. subst. clear e0. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
         pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
         assert (Γ0 ++ A0 :: B0 :: Γ3 = (Γ0 ++ []) ++ A0 :: B0 :: Γ3). repeat rewrite <- app_assoc. auto.
         rewrite H0. exists x. lia. }
       { inversion e0. subst. clear e0. assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
         pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. assert (AndLRule [((Γ0 ++ A :: B :: x) ++ A0 :: B0 :: Γ3, C)]
         ((Γ0 ++ A :: B :: x) ++ And A0 B0 :: Γ3, C)). apply AndLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
         assert (J4: AndLRule [(Γ0 ++ A :: B :: x ++ A0 :: B0 :: Γ3, C)]
         (Γ0 ++ And A B :: x ++ A0 :: B0 :: Γ3, C)). apply AndLRule_I. assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
         assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
         pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s ((Γ0 ++ A :: B :: x) ++ A0 :: B0 :: Γ3, C)).
         assert (AndLRule [((Γ0 ++ A :: B :: x) ++ A0 :: B0 :: Γ3, C)] ((Γ0 ++ And A B :: x) ++ A0 :: B0 :: Γ3, C)).
         repeat rewrite <- app_assoc. apply AndLRule_I. apply s0 in H1. destruct H1. pose (dlCons x1 DersNilF). apply AndL in H0.
         assert (Γ0 ++ A :: B :: x ++ A0 :: B0 :: Γ3 =(Γ0 ++ A :: B :: x) ++ A0 :: B0 :: Γ3).
         repeat rewrite <- app_assoc. auto. rewrite H1 in H0.
         pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[((Γ0 ++ A :: B :: x) ++ A0 :: B0 :: Γ3, C)])
         (Γ0 ++ A :: B :: x ++ And A0 B0 :: Γ3, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
         rewrite dersrec_height_nil. lia. reflexivity. }
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: AndLRule [(Γ0 ++ A :: B :: Γ1, A0)] (Γ0 ++ And A B :: Γ1, A0)). apply AndLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
    assert (OrR1Rule [(Γ0 ++ A :: B :: Γ1, A0)]
    (Γ0 ++ A :: B :: Γ1, Or A0 B0)). apply OrR1Rule_I. pose (dlCons x0 DersNilF). apply OrR1 in H0.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: B :: Γ1, A0)])
    (Γ0 ++ A :: B :: Γ1, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J4: AndLRule [(Γ0 ++ A :: B :: Γ1, B0)] (Γ0 ++ And A B :: Γ1, B0)). apply AndLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
    assert (OrR2Rule [(Γ0 ++ A :: B :: Γ1, B0)]
    (Γ0 ++ A :: B :: Γ1, Or A0 B0)). apply OrR2Rule_I. pose (dlCons x0 DersNilF). apply OrR2 in H0.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: B :: Γ1, B0)])
    (Γ0 ++ A :: B :: Γ1, Or A0 B0) H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrL *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0.
   + destruct x.
      { inversion e0. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        repeat rewrite <- app_assoc. simpl.
        assert (OrLRule [(Γ2 ++ A0 :: x ++ A :: B :: Γ1, C);(Γ2 ++ B0 :: x ++ A :: B :: Γ1, C)]
        (Γ2 ++ Or A0 B0 :: x ++ A :: B :: Γ1, C)). apply OrLRule_I. apply OrL in H0.
        assert (J4: AndLRule [((Γ2 ++ A0 :: x) ++ A :: B :: Γ1, C)]
        ((Γ2 ++ A0 :: x) ++ And A B :: Γ1, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
        assert (J7: AndLRule [((Γ2 ++ B0 :: x) ++ A :: B :: Γ1, C)]
        ((Γ2 ++ B0 :: x) ++ And A B :: Γ1, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J7. simpl in J7.
        assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
        pose (IH _ J8 _ _ J9). destruct p. clear s0. pose (s _ J7). destruct s0. clear s.
        pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
        pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 :: x ++ A :: B :: Γ1, C); (Γ2 ++ B0 :: x ++ A :: B :: Γ1, C)])
        (Γ2 ++ Or A0 B0 :: x ++ A :: B :: Γ1, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
    + destruct x.
       { simpl in e0. inversion e0. }
       { inversion e0. subst. clear e0. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
          assert (OrLRule [((Γ0 ++ A :: B :: x) ++ A0 :: Γ3, C);((Γ0 ++ A :: B :: x) ++ B0 :: Γ3, C)]
          ((Γ0 ++ A :: B :: x) ++ Or A0 B0 :: Γ3, C)). apply OrLRule_I. apply OrL in H0.
          repeat rewrite <- app_assoc in H0. simpl in H0.
          assert (J4: AndLRule [(Γ0 ++ A :: B :: x ++ A0 :: Γ3, C)]
          ((Γ0 ++ And A B :: x) ++ A0 :: Γ3, C)). repeat rewrite <- app_assoc. apply AndLRule_I.
          assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
          assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
          pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
          assert (J7: AndLRule [(Γ0 ++ A :: B :: x ++ B0 :: Γ3, C)]
          ((Γ0 ++ And A B :: x) ++ B0 :: Γ3, C)). repeat rewrite <- app_assoc. apply AndLRule_I.
          assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
          assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
          pose (IH _ J8 _ _ J9). destruct p. clear s0. pose (s _ J7). destruct s0. clear s.
          pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
          pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: B :: x ++ A0 :: Γ3, C); (Γ0 ++ A :: B :: x ++ B0 :: Γ3, C)])
          (Γ0 ++ A :: B :: x ++ Or A0 B0 :: Γ3, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil.
          lia. reflexivity. }
  (* ImpR *)
  * inversion H ; subst. simpl in IH. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (J31: derrec_height x = derrec_height x). reflexivity.
    pose (list_exch_LI [] Γ2 [] [A0] Γ3 B0). simpl in l. rewrite H2 in l.
    pose (G4iSLT_hpadm_list_exch_L _ _ x J31 _ l). destruct s. pose (ImpRRule_I A0 B0 [] (Γ0 ++ A :: B :: Γ1)). simpl in i.
    pose (AndLRule_I A B B0 (A0 :: Γ0) Γ1). simpl in a. assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ a). destruct s0. clear s.
    pose (dlCons x1 DersNilF). apply ImpR in i. pose (derI _ i d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AtomImpL1 *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0.
   + destruct x.
      { inversion e0. }
      { inversion e0.  subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
        - inversion e1.
        - destruct x0. simpl in e1. inversion e1. inversion e1. subst. clear e1. clear e0.
          assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
          assert (AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A0 :: x0 ++ A :: B :: Γ1, C)]
          (Γ2 ++ # P :: Γ3 ++ Imp # P A0 :: x0 ++ A :: B :: Γ1, C)). apply AtomImpL1Rule_I.
          assert (J4: AndLRule [((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ A :: B :: Γ1, C)] ((Γ2 ++ # P :: Γ3 ++ A0 :: x0) ++ And A B :: Γ1, C)).
          apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
          assert (J5: derrec_height x < S (dersrec_height d)). lia.
          assert (J6: derrec_height x = derrec_height x). reflexivity.
          pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
          pose (dlCons x1 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
          pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: x0 ++ A :: B :: Γ1, C)])
          (Γ2 ++ # P :: Γ3 ++ Imp (# P) A0 :: x0 ++ A :: B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
          lia. reflexivity.
        - destruct x0. simpl in e1. inversion e1. inversion e1. subst. simpl.
          assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. clear e0. clear e1.
          assert (AtomImpL1Rule [(Γ2 ++ # P :: (x ++ A :: B :: x0) ++ A0 :: Γ4, C)]
          (Γ2 ++ # P :: (x ++ A :: B :: x0) ++ Imp # P A0 :: Γ4, C)). apply AtomImpL1Rule_I.
          assert (J4: AndLRule [((Γ2 ++ # P :: x) ++ A :: B :: x0 ++ A0 :: Γ4, C)] ((Γ2 ++ # P :: x) ++ And A B :: x0 ++ A0 :: Γ4, C)).
          apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
          assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
          assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
          pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s (Γ2 ++ # P :: x ++ A :: B :: x0 ++ A0 :: Γ4, C)).
          assert (AndLRule [(Γ2 ++ # P :: x ++ A :: B :: x0 ++ A0 :: Γ4, C)] (Γ2 ++ # P :: (x ++ And A B :: x0) ++ A0 :: Γ4, C)).
          repeat rewrite <- app_assoc. simpl. auto. apply s0 in H1. destruct H1. clear s0. clear s.
          pose (dlCons x2 DersNilF). apply AtomImpL1 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in H0. simpl in H0.
          pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ # P :: x ++ A :: B :: x0 ++ A0 :: Γ4, C)])
          (Γ2 ++ # P :: x ++ A :: B :: x0 ++ Imp # P A0 :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
          lia. reflexivity. }
    + destruct x. simpl in e0. inversion e0. inversion e0. subst. clear e0.
       assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AtomImpL1Rule [((Γ0 ++ A :: B :: x) ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       ((Γ0 ++ A :: B :: x) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, C)). apply AtomImpL1Rule_I.
       assert (J4: AndLRule [(Γ0 ++ A :: B :: x ++ # P :: Γ3 ++ A0 :: Γ4, C)] (Γ0 ++ And A B :: x ++ # P :: Γ3 ++ A0 :: Γ4, C)). apply AndLRule_I.
       repeat rewrite <- app_assoc in J4. simpl in J4.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s ((Γ0 ++ A :: B :: x) ++ # P :: Γ3 ++ A0 :: Γ4, C)).
       assert (AndLRule [((Γ0 ++ A :: B :: x) ++ # P :: Γ3 ++ A0 :: Γ4, C)] ((Γ0 ++ And A B :: x) ++ # P :: Γ3 ++ A0 :: Γ4, C)).
       repeat rewrite <- app_assoc. simpl ; auto. apply s0 in H1. destruct H1.
       pose (dlCons x1 DersNilF). apply AtomImpL1 in H0.
       assert (((Γ0 ++ A :: B :: x) ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, C) = (Γ0 ++ A :: B :: x ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, C)).
       repeat rewrite <- app_assoc. auto. rewrite H1 in H0.
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[((Γ0 ++ A :: B :: x) ++ # P :: Γ3 ++ A0 :: Γ4, C)])
       (Γ0 ++ A :: B :: x ++ # P :: Γ3 ++ Imp # P A0 :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* AtomImpL2 *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0.
   + destruct x.
      { inversion e0. }
      { inversion e0.  subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
        - inversion e1.
        - destruct x0. simpl in e1. inversion e1. inversion e1. subst. clear e1. clear e0.
          assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
          assert (AtomImpL2Rule [(Γ2 ++ A0 :: Γ3 ++ # P :: x0 ++ A :: B :: Γ1, C)]
          (Γ2 ++ Imp # P A0 :: Γ3 ++ # P :: x0 ++ A :: B :: Γ1, C)). apply AtomImpL2Rule_I.
          assert (J4: AndLRule [((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ A :: B :: Γ1, C)] ((Γ2 ++ A0 :: Γ3 ++ # P :: x0) ++ And A B :: Γ1, C)).
          apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
          assert (J5: derrec_height x < S (dersrec_height d)). lia.
          assert (J6: derrec_height x = derrec_height x). reflexivity.
          pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
          pose (dlCons x1 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
          pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 :: Γ3 ++ # P :: x0 ++ A :: B :: Γ1, C)])
          (Γ2 ++ Imp (# P) A0 :: Γ3 ++ # P :: x0 ++ A :: B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
          lia. reflexivity.
        - destruct x0. simpl in e1. inversion e1. inversion e1. subst. simpl.
          assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. clear e0. clear e1.
          assert (AtomImpL2Rule [(Γ2 ++ A0 :: (x ++ A :: B :: x0) ++ # P :: Γ4, C)]
          (Γ2 ++ Imp # P A0 :: (x ++ A :: B :: x0) ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
          assert (J4: AndLRule [((Γ2 ++ A0 :: x) ++ A :: B :: x0 ++ # P :: Γ4, C)] ((Γ2 ++ A0 :: x) ++ And A B :: x0 ++ # P :: Γ4, C)).
          apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
          assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
          assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
          pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s (Γ2 ++ A0 :: x ++ A :: B :: x0 ++ # P :: Γ4, C)).
          assert (AndLRule [(Γ2 ++ A0 :: x ++ A :: B :: x0 ++ # P :: Γ4, C)] (Γ2 ++ A0 :: (x ++ And A B :: x0) ++ # P :: Γ4, C)).
          repeat rewrite <- app_assoc. simpl. auto. apply s0 in H1. destruct H1. clear s0. clear s.
          pose (dlCons x2 DersNilF). apply AtomImpL2 in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in H0. simpl in H0.
          pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 :: x ++ A :: B :: x0 ++ # P :: Γ4, C)])
          (Γ2 ++ Imp # P A0 :: x ++ A :: B :: x0 ++ # P :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
          lia. reflexivity. }
    + destruct x. simpl in e0. inversion e0. inversion e0. subst. clear e0.
       assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AtomImpL2Rule [((Γ0 ++ A :: B :: x) ++ A0 :: Γ3 ++ # P :: Γ4, C)]
       ((Γ0 ++ A :: B :: x) ++Imp # P A0  :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
       assert (J4: AndLRule [(Γ0 ++ A :: B :: x ++ A0 :: Γ3 ++ # P :: Γ4, C)] (Γ0 ++ And A B :: x ++ A0 :: Γ3 ++ # P :: Γ4, C)). apply AndLRule_I.
       repeat rewrite <- app_assoc in J4. simpl in J4.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s ((Γ0 ++ A :: B :: x) ++ A0 :: Γ3 ++ # P :: Γ4, C)).
       assert (AndLRule [((Γ0 ++ A :: B :: x) ++ A0 :: Γ3 ++ # P :: Γ4, C)] ((Γ0 ++ And A B :: x) ++ A0 :: Γ3 ++ # P :: Γ4, C)).
       repeat rewrite <- app_assoc. simpl ; auto. apply s0 in H1. destruct H1.
       pose (dlCons x1 DersNilF). apply AtomImpL2 in H0.
       assert (((Γ0 ++ A :: B :: x) ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, C) = (Γ0 ++ A :: B :: x ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, C)).
       repeat rewrite <- app_assoc. auto. rewrite H1 in H0.
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[((Γ0 ++ A :: B :: x) ++ A0 :: Γ3 ++ # P :: Γ4, C)])
       (Γ0 ++ A :: B :: x ++ Imp # P A0 :: Γ3 ++ # P :: Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
 (* AndImpL *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0.
   + destruct x.
      { inversion e0. }
      { inversion e0.  subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (AndImpLRule [((Γ2 ++ Imp A0 (Imp B0 C0) :: x) ++ A :: B :: Γ1, C)]
        ((Γ2 ++ Imp (And A0 B0) C0 :: x) ++ A :: B :: Γ1, C)). repeat rewrite <- app_assoc. simpl.
        repeat rewrite <- app_assoc. apply AndImpLRule_I.
        assert (J4: AndLRule [((Γ2 ++ Imp A0 (Imp B0 C0) :: x) ++ A :: B :: Γ1, C)] ((Γ2 ++ Imp A0 (Imp B0 C0) :: x) ++ And A B :: Γ1, C)).
        apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
        pose (dlCons x1 DersNilF). apply AndImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
        repeat rewrite <- app_assoc in H0.
        pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ Imp A0 (Imp B0 C0) :: x ++ A :: B :: Γ1, C)])
       (Γ2 ++ Imp (And A0 B0) C0 :: x ++ A :: B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil.
        lia. reflexivity. }
    + destruct x. simpl in e0. inversion e0. inversion e0. subst. clear e0.
       assert (J30: dersrec_height d = dersrec_height d). reflexivity.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (AndImpLRule [((Γ0 ++ A :: B :: x) ++ Imp A0 (Imp B0 C0) :: Γ3, C)]
      ((Γ0 ++ A :: B :: x) ++ Imp (And A0 B0) C0 :: Γ3, C)). apply AndImpLRule_I. repeat rewrite <- app_assoc in H0.
       assert (J4: AndLRule [(Γ0 ++ A :: B :: x ++ Imp (And A0 B0) C0 :: Γ3, C)] (Γ0 ++ And A B :: x ++ Imp (And A0 B0) C0 :: Γ3, C)). apply AndLRule_I.
       repeat rewrite <- app_assoc in J4. simpl in J4.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
       assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s ((Γ0 ++ A :: B :: x) ++ Imp A0 (Imp B0 C0) :: Γ3, C)).
       assert (AndLRule [((Γ0 ++ A :: B :: x) ++ Imp A0 (Imp B0 C0) :: Γ3, C)] ((Γ0 ++ And A B :: x) ++ Imp A0 (Imp B0 C0) :: Γ3, C)).
       repeat rewrite <- app_assoc. apply AndLRule_I. apply s0 in H1. destruct H1.
       pose (dlCons x1 DersNilF). apply AndImpL in H0.
       assert (Γ0 ++ (A :: B :: x) ++ Imp A0 (Imp B0 C0) :: Γ3 =(Γ0 ++ A :: B :: x) ++ Imp A0 (Imp B0 C0) :: Γ3).
       repeat rewrite <- app_assoc. auto. rewrite H1 in H0.
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[((Γ0 ++ A :: B :: x) ++ Imp A0 (Imp B0 C0) :: Γ3, C)])
       (Γ0 ++ A :: B :: x ++ Imp (And A0 B0) C0 :: Γ3, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0.
   + destruct x. { inversion e0. }
      { inversion e0.  subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
        - assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
          assert (OrImpLRule [((Γ2 ++ Imp A0 C0 :: Γ3) ++ Imp B0 C0 :: A :: B :: Γ1, C)]
          ((Γ2 ++ Imp (Or A0 B0) C0 :: Γ3) ++ A :: B :: Γ1, C)). repeat rewrite <- app_assoc.
          simpl. apply OrImpLRule_I. simpl. repeat rewrite <- app_assoc. simpl.
          assert (J4: AndLRule [((Γ2 ++ Imp A0 C0 :: Γ3 ++ [Imp B0 C0]) ++ A :: B :: Γ1, C)]
          ((Γ2 ++ Imp A0 C0 :: Γ3 ++ [Imp B0 C0]) ++ And A B :: Γ1, C)).
          apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
          assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
          pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
          pose (dlCons x1 DersNilF). apply OrImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
          repeat rewrite <- app_assoc in H0. simpl in H0.  pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
          (ps:=[(Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: A :: B :: Γ1, C)]) (Γ2 ++ Imp (Or A0 B0) C0 :: Γ3 ++ A :: B :: Γ1, C) H0 d0).
          repeat rewrite <- app_assoc. exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        - assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
          assert (OrImpLRule [(Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: x0 ++ A :: B :: Γ1, C)]
          (Γ2 ++ Imp (Or A0 B0) C0 :: Γ3 ++ x0 ++ A :: B :: Γ1, C)). apply OrImpLRule_I.
          assert (J4: AndLRule [((Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: x0) ++ A :: B :: Γ1, C)] ((Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: x0) ++ And A B :: Γ1, C)).
          apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
          assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
          pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
          pose (dlCons x1 DersNilF). apply OrImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
          pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: x0 ++ A :: B :: Γ1, C)])
          (Γ2 ++ Imp (Or A0 B0) C0 :: Γ3 ++ x0 ++ A :: B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1.
          simpl. rewrite dersrec_height_nil. lia. reflexivity.
        - destruct x0.
            + simpl in e1. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
               pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl. repeat rewrite <- app_assoc. simpl.
               assert (OrImpLRule [(Γ2 ++ Imp A0 C0 :: x ++ Imp B0 C0 :: A :: B :: Γ1, C)]
               (Γ2 ++ Imp (Or A0 B0) C0 :: x ++ A :: B :: Γ1, C)). apply OrImpLRule_I.
               assert (J4: AndLRule [((Γ2 ++ Imp A0 C0 :: x ++ [Imp B0 C0]) ++ A :: B :: Γ1, C)] ((Γ2 ++ Imp A0 C0 :: x ++ [Imp B0 C0]) ++ And A B :: Γ1, C)).
               apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4. repeat rewrite <- app_assoc in J4. simpl in J4.
               assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
               pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s (Γ2 ++ Imp A0 C0 :: x ++ Imp B0 C0 :: A :: B :: Γ1, C)).
               assert (AndLRule [(Γ2 ++ Imp A0 C0 :: x ++ Imp B0 C0 :: A :: B :: Γ1, C)]
               (Γ2 ++ Imp A0 C0 :: (x ++ []) ++ Imp B0 C0 :: And A B :: Γ1, C)). repeat rewrite <- app_assoc. simpl. auto.
               apply s0 in H1. destruct H1. clear s0. clear s. pose (dlCons x1 DersNilF). apply OrImpL in H0.
               pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ Imp A0 C0 :: x ++ Imp B0 C0 :: A :: B :: Γ1, C)])
              (Γ2 ++ Imp (Or A0 B0) C0 :: x ++ A :: B :: Γ1, C) H0 d0). repeat rewrite <- app_assoc. exists d1.
               simpl. rewrite dersrec_height_nil. lia. reflexivity.
            +  inversion e1. subst. simpl. repeat rewrite <- app_assoc. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
                pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. clear e0. clear e1.
                assert (OrImpLRule [(Γ2 ++ Imp A0 C0 :: (x ++ A :: B :: x0) ++ Imp B0 C0 :: Γ4, C)]
                (Γ2 ++ Imp (Or A0 B0) C0 :: (x ++ A :: B :: x0) ++ Γ4, C)). apply OrImpLRule_I.
                assert (J4: AndLRule [((Γ2 ++ Imp A0 C0 :: x) ++ A :: B :: x0 ++ Imp B0 C0 :: Γ4, C)] ((Γ2 ++ Imp A0 C0 :: x) ++ And A B :: x0 ++ Imp B0 C0 :: Γ4, C)).
                apply AndLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
                assert (J5: derrec_height x1 < S (dersrec_height d)). lia. assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
                pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s (Γ2 ++ Imp A0 C0 :: x ++ A :: B :: x0 ++ Imp B0 C0 :: Γ4, C)).
                assert (AndLRule [(Γ2 ++ Imp A0 C0 :: x ++ A :: B :: x0 ++ Imp B0 C0 :: Γ4, C)] (Γ2 ++ Imp A0 C0 :: (x ++ And A B :: x0) ++ Imp B0 C0 :: Γ4, C)).
                repeat rewrite <- app_assoc. simpl. auto. apply s0 in H1. destruct H1. clear s0. clear s.
                pose (dlCons x2 DersNilF). apply OrImpL in H0. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in H0. simpl in H0.
                pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ Imp A0 C0 :: x ++ A :: B :: x0 ++ Imp B0 C0 :: Γ4, C)])
                (Γ2 ++ Imp (Or A0 B0) C0 :: x ++ A :: B :: x0 ++ Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
                rewrite dersrec_height_nil. lia. reflexivity. }
    + destruct x. simpl in e0. inversion e0. inversion e0. subst. clear e0. assert (J30: dersrec_height d = dersrec_height d). reflexivity. simpl.
       pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
       assert (OrImpLRule [((Γ0 ++ A :: B :: x) ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)]
       ((Γ0 ++ A :: B :: x) ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (J4: AndLRule [(Γ0 ++ A :: B :: x ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)] (Γ0 ++ And A B :: x ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)). apply AndLRule_I.
       assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s (Γ0 ++ A :: B :: x ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)).
       assert (AndLRule [(Γ0 ++ A :: B :: x ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)] ((Γ0 ++ And A B :: x) ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)).
       repeat rewrite <- app_assoc. simpl ; auto. apply s0 in H1. destruct H1. pose (dlCons x1 DersNilF). apply OrImpL in H0.
       pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: B :: x ++ Imp A0 C0 :: Γ3 ++ Imp B0 C0 :: Γ4, C)])
       (Γ0 ++ A :: B :: x ++ Imp (Or A0 B0) C0 :: Γ3 ++ Γ4, C) H0 d0). repeat rewrite <- app_assoc. exists d1. simpl.
        rewrite dersrec_height_nil. lia. reflexivity.
  (* ImpImpL *)
 * inversion H. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0.
   + destruct x. { inversion e0. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. repeat rewrite <- app_assoc. simpl.
        assert (ImpImpLRule [(Γ2 ++ Imp B0 C0 :: x ++ A :: B :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x ++ A :: B :: Γ1, C)]
        (Γ2 ++ Imp (Imp A0 B0) C0 :: x ++ A :: B :: Γ1, C)). apply ImpImpLRule_I. apply ImpImpL in H0.
        assert (J4: AndLRule [((Γ2 ++ Imp B0 C0 :: x) ++ A :: B :: Γ1, Imp A0 B0)] ((Γ2 ++ Imp B0 C0 :: x) ++ And A B :: Γ1, Imp A0 B0)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J4. simpl in J4. assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x0 = derrec_height x0). reflexivity. pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
        assert (J7: AndLRule [((Γ2 ++ C0 :: x) ++ A :: B :: Γ1, C)] ((Γ2 ++ C0 :: x) ++ And A B :: Γ1, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J7. simpl in J7. assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity. pose (IH _ J8 _ _ J9). destruct p. clear s0. pose (s _ J7). destruct s0. clear s.
        pose (dlCons x3 DersNilF). pose (dlCons x2 d0). pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ Imp B0 C0 :: x ++ A :: B :: Γ1, Imp A0 B0); (Γ2 ++ C0 :: x ++ A :: B :: Γ1, C)])
        (Γ2 ++ Imp (Imp A0 B0) C0 :: x ++ A :: B :: Γ1, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
    + destruct x. { simpl in e0. inversion e0. }
       { inversion e0. subst. clear e0. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
          assert (ImpImpLRule [((Γ0 ++ A :: B :: x) ++ Imp B0 C0 :: Γ3, Imp A0 B0); ((Γ0 ++ A :: B :: x) ++ C0 :: Γ3, C)]
          ((Γ0 ++ A :: B :: x) ++ Imp (Imp A0 B0) C0 :: Γ3, C)). apply ImpImpLRule_I. apply ImpImpL in H0. repeat rewrite <- app_assoc in H0. simpl in H0.
          assert (J4: AndLRule [(Γ0 ++ A :: B :: x ++ Imp B0 C0 :: Γ3, Imp A0 B0)]
          ((Γ0 ++ And A B :: x) ++ Imp B0 C0 :: Γ3, Imp A0 B0)). repeat rewrite <- app_assoc. apply AndLRule_I. assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
          assert (J6: derrec_height x0 = derrec_height x0). reflexivity. pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
          assert (J7: AndLRule [(Γ0 ++ A :: B :: x ++ C0 :: Γ3, C)] ((Γ0 ++ And A B :: x) ++ C0 :: Γ3, C)). repeat rewrite <- app_assoc. apply AndLRule_I.
          assert (J8: derrec_height x1 < S (dersrec_height d)). lia. assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
          pose (IH _ J8 _ _ J9). destruct p. clear s0. pose (s _ J7). destruct s0. clear s. pose (dlCons x3 DersNilF). pose (dlCons x2 d0).
          pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: B :: x ++ Imp B0 C0 :: Γ3, Imp A0 B0); (Γ0 ++ A :: B :: x ++ C0 :: Γ3, C)])
         (Γ0 ++ A :: B :: x ++ Imp (Imp A0 B0) C0 :: Γ3, C) H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
  (* BoxImpL *)
 * inversion H ; subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0.
   + destruct x. { inversion e0. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. repeat rewrite <- app_assoc. simpl.
        assert (BoxImpLRule [((unBoxed_list Γ2 ++ B0 :: unBoxed_list x) ++ unBox_formula A :: unBox_formula B :: unBoxed_list Γ1 ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ A :: B :: Γ1, C)]
        (Γ2 ++ Box A0 → B0 :: x ++ A :: B :: Γ1, C)). epose (@BoxImpLRule_I _ _ _ Γ2 (x ++ A :: B :: Γ1)).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b. simpl in b.
        repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat (rewrite <- app_assoc in b ; simpl in b) ; apply b ; auto.
        assert (J4: AndLRule [(unBoxed_list Γ2 ++ B0 :: unBoxed_list x ++ A :: B :: unBoxed_list Γ1 ++ [Box A0], A0)] (unBoxed_list Γ2 ++ B0 :: unBoxed_list (x ++ A ∧ B :: Γ1) ++ [Box A0], A0)).
        repeat (rewrite unBox_app_distrib ; rewrite <- app_assoc ; simpl).
        epose (AndLRule_I _ _ A0 (unBoxed_list Γ2 ++ B0 :: unBoxed_list x) (unBoxed_list Γ1 ++ [Box A0])).
        repeat rewrite <- app_assoc in a ; simpl in a. apply a.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). destruct p. clear s0. repeat rewrite <- app_assoc in s. pose (s _ J4). destruct s0. clear s.
        assert (J7: AndLRule [((Γ2 ++ B0 :: x) ++ A :: B :: Γ1, C)] ((Γ2 ++ B0 :: x) ++ And A B :: Γ1, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J7. simpl in J7. assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity. pose (IH _ J8 _ _ J9). destruct p. clear s0. pose (s _ J7). destruct s0. clear s.
        pose (unBox_left_hpadm_gen A (unBoxed_list Γ2 ++ B0 :: unBoxed_list x) (B :: unBoxed_list Γ1 ++ [Box A0]) A0).
        repeat rewrite <- app_assoc in s ; simpl in s. pose (s x2). destruct s0.
        pose (unBox_left_hpadm_gen B (unBoxed_list Γ2 ++ B0 :: unBoxed_list x ++ [unBox_formula A]) (unBoxed_list Γ1 ++ [Box A0]) A0).
        repeat (repeat rewrite <- app_assoc in s0 ; simpl in s0). pose (s0 x4). destruct s1.
        pose (dlCons x3 DersNilF). pose (dlCons x5 d0). apply BoxImpL in H0. repeat rewrite <- app_assoc in H0 ; simpl in H0.
        pose (derI _ H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
    + destruct x. { simpl in e0. inversion e0. }
       { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. repeat rewrite <- app_assoc. simpl.
        assert (BoxImpLRule [(unBoxed_list Γ0 ++ unBox_formula A :: unBox_formula B :: unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0); (Γ0 ++ A :: B :: x ++ B0 :: Γ3, C)]
        (Γ0 ++ A :: B :: x ++ Box A0 → B0 :: Γ3, C)). epose (@BoxImpLRule_I _ _ _ (Γ0 ++ A :: B :: x) Γ3).
        repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        assert (J4: AndLRule [(unBoxed_list Γ0 ++ A :: B :: unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0)] (unBoxed_list (Γ0 ++ And A B :: x) ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0)).
        repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc. apply AndLRule_I.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
        assert (J7: AndLRule [(Γ0 ++ A :: B :: x ++ B0 :: Γ3, C)] ((Γ0 ++ And A B :: x) ++ B0 :: Γ3, C)). repeat rewrite <- app_assoc. apply AndLRule_I.
        assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity. pose (IH _ J8 _ _ J9). destruct p. clear s0. pose (s _ J7). destruct s0. clear s.
        pose (unBox_left_hpadm_gen _ _ _ _ x2). destruct s.
        pose (unBox_left_hpadm_gen B (unBoxed_list Γ0 ++ [unBox_formula A]) (unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0]) A0).
        repeat (repeat rewrite <- app_assoc in s ; simpl in s). pose (s x4). destruct s0.
        pose (dlCons x3 DersNilF). pose (dlCons x5 d0). apply BoxImpL in H0. pose (derI _ H0 d1). exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
  (* SLR *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity. pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (SLRRule [(unBoxed_list (Γ0 ++ A :: B :: Γ1) ++ [Box A0], A0)] (Γ0 ++ A :: B :: Γ1, Box A0)). apply SLRRule_I. apply SLR in H0.
    assert (J4: AndLRule [(unBoxed_list Γ0 ++ A :: B :: unBoxed_list Γ1 ++ [Box A0], A0)] (unBoxed_list (Γ0 ++ A ∧ B :: Γ1) ++ [Box A0], A0)).
    repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc ; simpl. apply AndLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
    pose (unBox_left_hpadm_gen A (unBoxed_list Γ0) (B :: unBoxed_list Γ1 ++ [Box A0]) A0).
    repeat rewrite <- app_assoc in s ; simpl in s. pose (s x0). destruct s0.
    pose (unBox_left_hpadm_gen B (unBoxed_list Γ0 ++ [unBox_formula A]) (unBoxed_list Γ1 ++ [Box A0]) A0).
    repeat (repeat rewrite <- app_assoc in s0 ; simpl in s0). pose (s0 x1). destruct s1.
    repeat rewrite unBox_app_distrib in H0 ; repeat rewrite <- app_assoc in H0.
    pose (dlCons x2 DersNilF). pose (derI _ H0 d0). exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }

(* Invertibility AndR *)
{ intros prem1 prem2 RA. inversion RA. subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H.
  (* BotL *)
  * inversion H. subst. simpl.
    assert (BotLRule [] (Γ0 ++ Bot :: Γ1, A)). apply BotLRule_I. apply BotL in H0.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[]) (Γ0 ++ Bot :: Γ1, A) H0 DersNilF). exists d0.
    assert (BotLRule [] (Γ0 ++ Bot :: Γ1, B)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (Γ0 ++ Bot :: Γ1, B) H1 DersNilF). exists d1. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
  (* AndR *)
  * inversion H. subst. assert (J0: (dersrec_height d) = (dersrec_height d)). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s. exists x. exists x0. simpl. split ; lia.
  (* AndL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (AndLRule [(Γ0 ++ A0 :: B0 :: Γ1, A)] (Γ0 ++ And A0 B0 :: Γ1, A)). apply AndLRule_I. apply AndL in H0.
    assert (AndLRule [(Γ0 ++ A0 :: B0 :: Γ1, B)] (Γ0 ++ And A0 B0 :: Γ1, B)). apply AndLRule_I. apply AndL in H1.
    assert (J4: AndRRule [(Γ0 ++ A0 :: B0 :: Γ1, A);(Γ0 ++ A0 :: B0 :: Γ1, B)] (Γ0 ++ A0 :: B0 :: Γ1, And A B)). apply AndRRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s. pose (s0 _ _ J4). destruct s. clear s0. destruct s. pose (dlCons x0 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A0 :: B0 :: Γ1, A)]) (Γ0 ++ And A0 B0 :: Γ1, A) H0 d0). exists d1.
    pose (dlCons x1 DersNilF). pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A0 :: B0 :: Γ1, B)]) (Γ0 ++ And A0 B0 :: Γ1, B) H1 d2). exists d3.
    simpl. rewrite dersrec_height_nil. simpl. split. simpl. destruct p. lia. destruct p. lia. reflexivity.
  (* OrR1 *)
  * inversion H.
  (* OrR2 *)
  * inversion H.
  (* OrL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    assert (OrLRule [(Γ0 ++ A0 :: Γ1, A);(Γ0 ++ B0 :: Γ1, A)] (Γ0 ++ Or A0 B0 :: Γ1, A)). apply OrLRule_I. apply OrL in H0.
    assert (OrLRule [(Γ0 ++ A0 :: Γ1, B);(Γ0 ++ B0 :: Γ1, B)] (Γ0 ++ Or A0 B0 :: Γ1, B)). apply OrLRule_I. apply OrL in H1.
    assert (J4: AndRRule [(Γ0 ++ A0 :: Γ1, A);(Γ0 ++ A0 :: Γ1, B)] (Γ0 ++ A0 :: Γ1, And A B)). apply AndRRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s. pose (s0 _ _ J4). destruct s. clear s0. destruct s. destruct p.
    assert (J7: AndRRule [(Γ0 ++ B0 :: Γ1, A);(Γ0 ++ B0 :: Γ1, B)] (Γ0 ++ B0 :: Γ1, And A B)). apply AndRRule_I.
    assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J8 _ _ J9). destruct p. clear s. pose (s0 _ _ J7). destruct s. clear s0. destruct s. destruct p. pose (dlCons x3 DersNilF).  pose (dlCons x1 d0).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A0 :: Γ1, A); (Γ0 ++ B0 :: Γ1, A)]) (Γ0 ++ Or A0 B0 :: Γ1, A) H0 d1). exists d2.
    pose (dlCons x4 DersNilF).  pose (dlCons x2 d3). pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A0 :: Γ1, B); (Γ0 ++ B0 :: Γ1, B)]) (Γ0 ++ Or A0 B0 :: Γ1, B) H1 d4). exists d5.
    simpl. rewrite dersrec_height_nil. simpl. split. simpl. lia. lia. reflexivity.
  (* ImpR *)
  * inversion H.
  (* AtomImpL1 *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (AtomImpL1Rule [(Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, A)] (Γ0 ++ # P :: Γ1 ++ Imp # P A0 :: Γ2, A)). apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
    assert (AtomImpL1Rule [(Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, B)] (Γ0 ++ # P :: Γ1 ++ Imp # P A0 :: Γ2, B)). apply AtomImpL1Rule_I. apply AtomImpL1 in H1.
    assert (J4: AndRRule [(Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, A);(Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, B)] (Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, And A B)). apply AndRRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s. pose (s0 _ _ J4). destruct s. clear s0. destruct s. destruct p. pose (dlCons x0 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, A)]) (Γ0 ++ # P :: Γ1 ++ Imp # P A0 :: Γ2, A) H0 d0). exists d1.  pose (dlCons x1 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ # P :: Γ1 ++ A0 :: Γ2, B)]) (Γ0 ++ # P :: Γ1 ++ Imp # P A0 :: Γ2, B) H1 d2). exists d3.
    simpl. rewrite dersrec_height_nil. simpl. split. simpl. lia. lia. reflexivity.
  (* AtomImpL2 *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (AtomImpL2Rule [(Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, A)] (Γ0 ++ Imp # P A0 :: Γ1 ++ # P :: Γ2, A)).
    apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
    assert (AtomImpL2Rule [(Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, B)] (Γ0 ++ Imp # P A0 :: Γ1 ++ # P :: Γ2, B)).
    apply AtomImpL2Rule_I. apply AtomImpL2 in H1.
    assert (J4: AndRRule [(Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, A);(Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, B)]
    (Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, And A B)). apply AndRRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s. pose (s0 _ _ J4). destruct s. clear s0. destruct s. destruct p.
    pose (dlCons x0 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, A)]) (Γ0 ++ Imp # P A0 :: Γ1 ++ # P :: Γ2, A) H0 d0). exists d1.
    pose (dlCons x1 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ A0 :: Γ1 ++ # P :: Γ2, B)]) (Γ0 ++ Imp # P A0 :: Γ1 ++ # P :: Γ2, B) H1 d2). exists d3.
    simpl. rewrite dersrec_height_nil. simpl. split. simpl. lia. lia. reflexivity.
  (* AndImpL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (AndImpLRule [(Γ0 ++ Imp A0 (Imp B0 C) :: Γ1, A)] (Γ0 ++ Imp (And A0 B0) C :: Γ1, A)).
    apply AndImpLRule_I. apply AndImpL in H0.
    assert (AndImpLRule [(Γ0 ++ Imp A0 (Imp B0 C) :: Γ1, B)] (Γ0 ++ Imp (And A0 B0) C :: Γ1, B)).
    apply AndImpLRule_I. apply AndImpL in H1.
    assert (J4: AndRRule [(Γ0 ++ Imp A0 (Imp B0 C) :: Γ1, A);(Γ0 ++ Imp A0 (Imp B0 C) :: Γ1, B)]
    (Γ0 ++ Imp A0 (Imp B0 C) :: Γ1, And A B)). apply AndRRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s. pose (s0 _ _ J4). destruct s. clear s0. destruct s. destruct p.
    pose (dlCons x0 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ Imp A0 (Imp B0 C) :: Γ1, A)]) (Γ0 ++ Imp (And A0 B0) C :: Γ1, A) H0 d0). exists d1.
    pose (dlCons x1 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ Imp A0 (Imp B0 C) :: Γ1, B)]) (Γ0 ++ Imp (And A0 B0) C :: Γ1, B) H1 d2). exists d3.
    simpl. rewrite dersrec_height_nil. simpl. split. simpl. lia. lia. reflexivity.
  (* OrImpL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (OrImpLRule [(Γ0 ++ Imp A0 C :: Γ1 ++ Imp B0 C ::Γ2, A)] (Γ0 ++ Imp (Or A0 B0) C :: Γ1 ++ Γ2, A)).
    apply OrImpLRule_I. apply OrImpL in H0.
    assert (OrImpLRule [(Γ0 ++ Imp A0 C :: Γ1 ++ Imp B0 C ::Γ2, B)] (Γ0 ++ Imp (Or A0 B0) C :: Γ1 ++ Γ2, B)).
    apply OrImpLRule_I. apply OrImpL in H1.
    assert (J4: AndRRule [(Γ0 ++ Imp A0 C :: Γ1 ++ Imp B0 C :: Γ2, A);(Γ0 ++ Imp A0 C :: Γ1 ++ Imp B0 C :: Γ2, B)]
    (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B0 C :: Γ2, And A B)). apply AndRRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia.
    assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s. pose (s0 _ _ J4). destruct s. clear s0. destruct s. destruct p.
    pose (dlCons x0 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ Imp A0 C :: Γ1 ++ Imp B0 C :: Γ2, A)]) (Γ0 ++ Imp (Or A0 B0) C :: Γ1 ++ Γ2, A) H0 d0). exists d1.
    pose (dlCons x1 DersNilF).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ Imp A0 C :: Γ1 ++ Imp B0 C :: Γ2, B)]) (Γ0 ++ Imp (Or A0 B0) C :: Γ1 ++ Γ2, B) H1 d2). exists d3.
    simpl. rewrite dersrec_height_nil. simpl. split. simpl. lia. lia. reflexivity.
  (* ImpImpL *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    assert (ImpImpLRule [(Γ0 ++ Imp B0 C :: Γ1, Imp A0 B0);(Γ0 ++ C :: Γ1, A)] (Γ0 ++ Imp (Imp A0 B0) C :: Γ1, A)).
    apply ImpImpLRule_I. apply ImpImpL in H0.
    assert (ImpImpLRule [(Γ0 ++ Imp B0 C :: Γ1, Imp A0 B0);(Γ0 ++ C :: Γ1, B)] (Γ0 ++ Imp (Imp A0 B0) C :: Γ1, B)).
    apply ImpImpLRule_I. apply ImpImpL in H1.
    assert (J4: AndRRule [(Γ0 ++ C :: Γ1, A);(Γ0 ++ C :: Γ1, B)]
    (Γ0 ++ C :: Γ1, And A B)). apply AndRRule_I.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s. pose (s0 _ _ J4). destruct s. clear s0. destruct s. destruct p.
    pose (dlCons x1 DersNilF). pose (dlCons x d0).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ Imp B0 C :: Γ1, Imp A0 B0); (Γ0 ++ C :: Γ1, A)]) (Γ0 ++ Imp (Imp A0 B0) C :: Γ1, A) H0 d1). exists d2.
    pose (dlCons x2 DersNilF). pose (dlCons x d3).
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[(Γ0 ++ Imp B0 C :: Γ1, Imp A0 B0); (Γ0 ++ C :: Γ1, B)]) (Γ0 ++ Imp (Imp A0 B0) C :: Γ1, B) H1 d4). exists d5.
    simpl. rewrite dersrec_height_nil. simpl. split. simpl. lia. lia. reflexivity.
  (* BoxImpL *)
  * inversion H ; subst ; simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    assert (BoxImpLRule [(unBoxed_list Γ0 ++ B0 :: unBoxed_list Γ1 ++ [Box A0], A0); (Γ0 ++ B0 :: Γ1, A)] (Γ0 ++ Imp (Box A0) B0 :: Γ1, A)).
    apply BoxImpLRule_I ; auto. apply BoxImpL in H0.
    assert (BoxImpLRule [(unBoxed_list Γ0 ++ B0 :: unBoxed_list Γ1 ++ [Box A0], A0); (Γ0 ++ B0 :: Γ1, B)] (Γ0 ++ Imp (Box A0) B0 :: Γ1, B)).
    apply BoxImpLRule_I ; auto. apply BoxImpL in H1.
    assert (J4: AndRRule [(Γ0 ++ B0 :: Γ1, A);(Γ0 ++ B0 :: Γ1, B)] (Γ0 ++ B0 :: Γ1, And A B)). apply AndRRule_I.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s. pose (s0 _ _ J4). destruct s. clear s0. destruct s. destruct p.
    pose (dlCons x1 DersNilF). pose (dlCons x d0).
    pose (derI _ H0 d1). exists d2. pose (dlCons x2 DersNilF). pose (dlCons x d3).
    pose (derI _ H1 d4). exists d5. simpl. rewrite dersrec_height_nil. simpl. split. simpl. lia. lia. reflexivity.
  (* SLR *)
  * inversion H. }
Qed.

Theorem AndL_inv : forall concl prem, (derrec G4iSLT_rules (fun _ => False) concl) ->
                                      (AndLRule [prem] concl) ->
                                      (derrec G4iSLT_rules (fun _ => False) prem).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (AndR_AndL_hpinv _  _ X J1). destruct p. pose (s _ H). destruct s1. assumption.
Qed.

Theorem AndR_inv : forall concl prem1 prem2, (derrec G4iSLT_rules (fun _ => False) concl) ->
                                      (AndRRule [prem1;prem2] concl) ->
                                      (derrec G4iSLT_rules (fun _ => False) prem1) *
                                      (derrec G4iSLT_rules (fun _ => False) prem2).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (AndR_AndL_hpinv _ _ X J1). destruct p. pose (s0 _ _ H). repeat destruct s1. auto.
Qed.















