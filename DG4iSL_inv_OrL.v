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

Theorem OrL_hpinv : forall (k : nat) concl
        (D0 : derrec G4iSL_rules (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem1 prem2, ((OrLRule [prem1;prem2] concl) ->
          existsT2 (D1 : derrec G4iSL_rules (fun _ => False) prem1)
                   (D2 : derrec G4iSL_rules (fun _ => False) prem2),
          (derrec_height D1 <= k) * (derrec_height D2 <= k)))).
Proof.
assert (DersNilF: dersrec G4iSL_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0 : derrec G4iSL_rules (fun _ : Seq => False) concl),
x = derrec_height D0 ->
((forall prem1 prem2, ((OrLRule [prem1;prem2] concl) ->
existsT2 (D1 : derrec G4iSL_rules (fun _ => False) prem1)
                   (D2 : derrec G4iSL_rules (fun _ => False) prem2),
          (derrec_height D1 <= x) * (derrec_height D2 <= x)))))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. intros prem1 prem2 RA. inversion RA. subst. simpl.
  inversion g ; subst.
  (* IdP *)
  * inversion H. subst. assert (InT # P (Γ0 ++ Or A B :: Γ1)). rewrite <- H2. apply InT_or_app. right. apply InT_eq.
    assert (InT # P (Γ0 ++ A :: Γ1)). apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. inversion i. subst. inversion H1. auto. apply InT_split in H1. destruct H1.
    destruct s. rewrite e.     assert (InT # P (Γ0 ++ B :: Γ1)). apply InT_app_or in H0. destruct H0. apply InT_or_app. auto.
    apply InT_or_app. right. apply InT_cons. inversion i. subst. inversion H1. auto. apply InT_split in H1. destruct H1.
    destruct s. rewrite e0. assert (IdPRule [] (x ++ # P :: x0, # P)). apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[]) (x ++ # P :: x0, # P) H1 DersNilF). exists d0.
    assert (IdPRule [] (x1 ++ # P :: x2, # P)). apply IdPRule_I. apply IdP in H3.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[]) (x1 ++ # P :: x2, # P) H3 DersNilF). exists d1.
    simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
  (* BotL *)
  * inversion H. subst. assert (InT (Bot) (Γ0 ++ Γ1)).
    assert (InT (Bot) (Γ0 ++ A ∨ B :: Γ1)). rewrite <- H2. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right. inversion i.
    inversion H1. auto. assert (InT (Bot) (Γ0 ++ A :: Γ1)). apply InT_app_or in H0. destruct H0. apply InT_or_app. auto.
    apply InT_or_app. right. apply InT_cons ; auto. assert (InT (Bot) (Γ0 ++ B :: Γ1)). apply InT_app_or in H0. destruct H0.
    apply InT_or_app. auto. apply InT_or_app. right. apply InT_cons ; auto.
    apply InT_split in H1. destruct H1. destruct s. rewrite e. apply InT_split in H3. destruct H3. destruct s. rewrite e0.
    assert (BotLRule [] (x ++ ⊥ :: x0, C)). apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[]) (x ++ ⊥ :: x0, C) H1 DersNilF). exists d0.
    assert (BotLRule [] (x1 ++ ⊥ :: x2, C)). apply BotLRule_I. apply BotL in H3.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[]) (x1 ++ ⊥ :: x2, C) H3 DersNilF). exists d1.
    simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    assert (AndRRule [(Γ0 ++ A :: Γ1, A0);(Γ0 ++ A :: Γ1, B0)] (Γ0 ++ A :: Γ1, A0 ∧ B0)). apply AndRRule_I. apply AndR in H0.
    assert (AndRRule [(Γ0 ++ B :: Γ1, A0);(Γ0 ++ B :: Γ1, B0)] (Γ0 ++ B :: Γ1, A0 ∧ B0)). apply AndRRule_I. apply AndR in H1.
    assert (J4: OrLRule [(Γ0 ++ A :: Γ1, A0);(Γ0 ++ B :: Γ1, A0)] (Γ0 ++ A ∨ B :: Γ1, A0)). apply OrLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p.
    assert (J7: OrLRule [(Γ0 ++ A :: Γ1, B0);(Γ0 ++ B :: Γ1, B0)] (Γ0 ++ A ∨ B :: Γ1, B0)). apply OrLRule_I.
    assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J8 _ _ J9 _ _ J7). repeat destruct s. repeat destruct p. pose (dlCons x4 DersNilF). pose (dlCons x2 d0).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ B :: Γ1, A0); (Γ0 ++ B :: Γ1, B0)]) (Γ0 ++ B :: Γ1, A0 ∧ B0) H1 d1).
    pose (dlCons x3 DersNilF). pose (dlCons x1 d3).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: Γ1, A0); (Γ0 ++ A :: Γ1, B0)]) (Γ0 ++ A :: Γ1, A0 ∧ B0) H0 d4).
    exists d5. exists d2. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
  (* AndL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndLRule  [((Γ0 ++ A :: x0) ++ A0 :: B0 :: Γ3, C)] ((Γ0 ++ A :: x0) ++ A0 ∧ B0 :: Γ3, C)). apply AndLRule_I. apply AndL in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (AndLRule  [((Γ0 ++ B :: x0) ++ A0 :: B0 :: Γ3, C)] ((Γ0 ++ B :: x0) ++ A0 ∧ B0 :: Γ3, C)). apply AndLRule_I. apply AndL in H1.
      repeat rewrite <- app_assoc in H1. simpl in H1.
      assert (J4: OrLRule [(Γ0 ++ A :: x0 ++ A0 :: B0 :: Γ3, C);(Γ0 ++ B :: x0 ++ A0 :: B0 :: Γ3, C)]
      (((Γ0 ++ [A ∨ B]) ++ x0) ++ A0 :: B0 :: Γ3, C)). repeat rewrite <- app_assoc. apply OrLRule_I.
      assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x1 DersNilF).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:= [(Γ0 ++ A :: x0 ++ A0 :: B0 :: Γ3, C)]) (Γ0 ++ A :: x0 ++ And A0 B0 :: Γ3, C) H0 d0).
      pose (dlCons x2 DersNilF).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:= [(Γ0 ++ B :: x0 ++ A0 :: B0 :: Γ3, C)]) (Γ0 ++ B :: x0 ++ And A0 B0 :: Γ3, C) H1 d2).
      exists d1. exists d3. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
   + repeat destruct s. repeat destruct p. subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (AndLRule  [(Γ2 ++ A0 :: B0 :: x ++ A :: Γ1, C)] ((Γ2 ++ A0 ∧ B0 :: x) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. apply AndLRule_I. apply AndL in H0.
      assert (AndLRule  [(Γ2 ++ A0 :: B0 :: x ++ B :: Γ1, C)] ((Γ2 ++ A0 ∧ B0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply AndLRule_I. apply AndL in H1.
      assert (J4: OrLRule [((Γ2 ++ A0 :: B0 :: x) ++ A :: Γ1, C);((Γ2 ++ A0 :: B0 :: x) ++ B :: Γ1, C)]
      ((Γ2 ++ A0 :: B0 :: x) ++ A ∨ B :: Γ1, C)). apply OrLRule_I. repeat rewrite <- app_assoc in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x1 DersNilF).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:= [(Γ2 ++ (A0 :: B0 :: x) ++ A :: Γ1, C)]) ((Γ2 ++ A0 ∧ B0 :: x) ++ A :: Γ1, C) H0 d0).
      pose (dlCons x2 DersNilF).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:= [(Γ2 ++ (A0 :: B0 :: x) ++ B :: Γ1, C)]) ((Γ2 ++ A0 ∧ B0 :: x) ++ B :: Γ1, C) H1 d2).
      exists d1. exists d3. cbn. rewrite dersrec_height_nil ; auto. repeat rewrite Nat.max_0_r. rewrite <- e.
      split ; apply le_n_S ; auto.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (OrR1Rule [(Γ0 ++ A :: Γ1, A0)] (Γ0 ++ A :: Γ1, A0 ∨ B0)). apply OrR1Rule_I. apply OrR1 in H0.
    assert (OrR1Rule [(Γ0 ++ B :: Γ1, A0)] (Γ0 ++ B :: Γ1, A0 ∨ B0)). apply OrR1Rule_I. apply OrR1 in H1.
    assert (J4: OrLRule [(Γ0 ++ A :: Γ1, A0);(Γ0 ++ B :: Γ1, A0)] (Γ0 ++ A ∨ B :: Γ1, A0)). apply OrLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: Γ1, A0)]) (Γ0 ++ A :: Γ1, A0 ∨ B0) H0 d0).
    pose (dlCons x1 DersNilF).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ B :: Γ1, A0)]) (Γ0 ++ B :: Γ1, A0 ∨ B0) H1 d2).
    exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (OrR2Rule [(Γ0 ++ A :: Γ1, B0)] (Γ0 ++ A :: Γ1, A0 ∨ B0)). apply OrR2Rule_I. apply OrR2 in H0.
    assert (OrR2Rule [(Γ0 ++ B :: Γ1, B0)] (Γ0 ++ B :: Γ1, A0 ∨ B0)). apply OrR2Rule_I. apply OrR2 in H1.
    assert (J4: OrLRule [(Γ0 ++ A :: Γ1, B0);(Γ0 ++ B :: Γ1, B0)] (Γ0 ++ A ∨ B :: Γ1, B0)). apply OrLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: Γ1, B0)]) (Γ0 ++ A :: Γ1, A0 ∨ B0) H0 d0).
    pose (dlCons x1 DersNilF).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ B :: Γ1, B0)]) (Γ0 ++ B :: Γ1, A0 ∨ B0) H1 d2).
    exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
  (* OrL *)
  * inversion H. subst. apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e0. subst.
      assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. exists x. exists x0.
      rewrite e. simpl. split ; lia.
   + assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (OrLRule [((Γ0 ++ A :: x0) ++ A0 :: Γ3, C);((Γ0 ++ A :: x0) ++ B0 :: Γ3, C)]
      ((Γ0 ++ A :: x0) ++ A0 ∨ B0 :: Γ3, C)). apply OrLRule_I. apply OrL in H0. repeat rewrite <- app_assoc in H0.
      assert (OrLRule [((Γ0 ++ B :: x0) ++ A0 :: Γ3, C);((Γ0 ++ B :: x0) ++ B0 :: Γ3, C)]
      ((Γ0 ++ B :: x0) ++ A0 ∨ B0 :: Γ3, C)). apply OrLRule_I. apply OrL in H1. repeat rewrite <- app_assoc in H1.
      assert (J4: OrLRule [(Γ0 ++ A :: x0 ++ A0 :: Γ3, C);(Γ0 ++ B :: x0 ++ A0 :: Γ3, C)]
      (((Γ0 ++ [A ∨ B]) ++ x0) ++ A0 :: Γ3, C)). repeat rewrite <- app_assoc. simpl. apply OrLRule_I.
      assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p.
      assert (J7: OrLRule [(Γ0 ++ A :: x0 ++ B0 :: Γ3, C);(Γ0 ++ B :: x0 ++ B0 :: Γ3, C)]
      (((Γ0 ++ [A ∨ B]) ++ x0) ++ B0 :: Γ3, C)). repeat rewrite <- app_assoc. simpl. apply OrLRule_I.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia. assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). repeat destruct s. repeat destruct p. pose (dlCons x4 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ0 ++ A :: x0 ++ A0 :: Γ3, C); (Γ0 ++ A :: x0 ++ B0 :: Γ3, C)]) (Γ0 ++ A :: x0 ++ A0 ∨ B0 :: Γ3, C) H0 d1).
      pose (dlCons x5 DersNilF). pose (dlCons x3 d3).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:= [(Γ0 ++ B :: x0 ++ A0 :: Γ3, C); (Γ0 ++ B :: x0 ++ B0 :: Γ3, C)]) (Γ0 ++ B :: x0 ++ A0 ∨ B0 :: Γ3, C) H1 d4).
      exists d2. exists d5. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (OrLRule [(Γ2 ++ A0 :: x ++ A :: Γ1, C);(Γ2 ++ B0 :: x ++ A :: Γ1, C)]
      ((Γ2 ++ A0 ∨ B0 :: x) ++ A :: Γ1, C)). repeat rewrite <- app_assoc; apply OrLRule_I. apply OrL in H0.
      assert (OrLRule [(Γ2 ++ A0 :: x ++ B :: Γ1, C);(Γ2 ++ B0 :: x ++ B :: Γ1, C)]
      ((Γ2 ++ A0 ∨ B0 :: x) ++ B :: Γ1, C)). repeat rewrite <- app_assoc; apply OrLRule_I. apply OrL in H1.
      assert (J4: OrLRule [((Γ2 ++ A0 :: x) ++ A :: Γ1, C);((Γ2 ++ A0 :: x) ++ B :: Γ1, C)]
      ((Γ2 ++ A0 :: x) ++ A ∨ B :: Γ1, C)). apply OrLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
      assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p.
      assert (J7: OrLRule [((Γ2 ++ B0 :: x) ++ A :: Γ1, C);((Γ2 ++ B0 :: x) ++ B :: Γ1, C)]
      ((Γ2 ++ B0 :: x) ++ A ∨ B :: Γ1, C)). apply OrLRule_I. repeat rewrite <- app_assoc in J7. simpl in J7.
      assert (J8: derrec_height x1 < S (dersrec_height d)). lia. assert (J9: derrec_height x1 = derrec_height x1). reflexivity.
      pose (IH _ J8 _ _ J9 _ _ J7). repeat destruct s. repeat destruct p. pose (dlCons x4 DersNilF). pose (dlCons x2 d0).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:=[(Γ2 ++ A0 :: x ++ A :: Γ1, C); (Γ2 ++ B0 :: x ++ A :: Γ1, C)]) ((Γ2 ++ A0 ∨ B0 :: x) ++ A :: Γ1, C) H0 d1).
      pose (dlCons x5 DersNilF). pose (dlCons x3 d3).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:= [(Γ2 ++ A0 :: x ++ B :: Γ1, C); (Γ2 ++ B0 :: x ++ B :: Γ1, C)]) ((Γ2 ++ A0 ∨ B0 :: x) ++ B :: Γ1, C) H1 d4).
      exists d2. exists d5. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
  (* ImpR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    assert (J50: list_exch_L (Γ2 ++ A0 :: Γ3, B0) (A0 :: Γ0 ++ A ∨ B :: Γ1, B0)). rewrite <- H2.
    assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). auto. rewrite H0.
    assert (A0 :: Γ2 ++ Γ3 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). auto. rewrite H1. apply list_exch_LI.
    assert (J51: derrec_height x = derrec_height x). auto. pose (G4iSL_hpadm_list_exch_L (derrec_height x) _ x J51 _ J50). destruct s.
    assert (ImpRRule [([] ++ A0 :: Γ0 ++ A :: Γ1, B0)] ([] ++ Γ0 ++ A :: Γ1, A0 → B0)). apply ImpRRule_I. apply ImpR in H0. simpl in H0.
    assert (ImpRRule [([] ++ A0 :: Γ0 ++ B :: Γ1, B0)] ([] ++ Γ0 ++ B :: Γ1, A0 → B0)). apply ImpRRule_I. apply ImpR in H1. simpl in H1.
    assert (J4: OrLRule [((A0 :: Γ0) ++ A :: Γ1, B0);((A0 :: Γ0) ++ B :: Γ1, B0)] ((A0 :: Γ0) ++ A ∨ B :: Γ1, B0)). apply OrLRule_I. repeat rewrite <- app_assoc in J4. simpl in J4.
    assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x1 DersNilF).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(A0 :: Γ0 ++ A :: Γ1, B0)]) (Γ0 ++ A :: Γ1, A0 → B0) H0 d0).
    pose (dlCons x2 DersNilF).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(A0 :: Γ0 ++ B :: Γ1, B0)]) (Γ0 ++ B :: Γ1, A0 → B0) H1 d2).
    exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + assert (AtomImpL1Rule  [((Γ0 ++ A :: x1) ++ # P :: Γ3 ++ A0 :: Γ4, C)]
       ((Γ0 ++ A :: x1) ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)). apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
       repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (AtomImpL1Rule  [((Γ0 ++ B :: x1) ++ # P :: Γ3 ++ A0 :: Γ4, C)] ((Γ0 ++ B :: x1) ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)). apply AtomImpL1Rule_I. apply AtomImpL1 in H1.
       repeat rewrite <- app_assoc in H1. simpl in H1.
      assert (J4: OrLRule [(Γ0 ++ A :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C);(Γ0 ++ B :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)]
      (((Γ0 ++ [A ∨ B]) ++ x1) ++ # P :: Γ3 ++ A0 :: Γ4, C)). repeat rewrite <- app_assoc. apply OrLRule_I.
      assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:= [(Γ0 ++ A :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)]) (Γ0 ++ A :: x1 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C) H0 d0).
      pose (dlCons x2 DersNilF).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
      (ps:= [(Γ0 ++ B :: x1 ++ # P :: Γ3 ++ A0 :: Γ4, C)]) (Γ0 ++ B :: x1 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C) H1 d2).
      exists d1. exists d3. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
   + repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
      { inversion e1. }
      { assert (AtomImpL1Rule  [(Γ2 ++ # P :: (x0 ++ A :: x2) ++ A0 :: Γ4, C)] ((Γ2 ++ # P :: x0) ++ A :: x2 ++ # P → A0 :: Γ4, C)).
        assert ((Γ2 ++ # P :: x0) ++ A :: x2 ++ # P → A0 :: Γ4 = Γ2 ++ # P :: (x0 ++ A :: x2) ++ # P → A0 :: Γ4).
        repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
        assert (AtomImpL1Rule  [(Γ2 ++ # P :: (x0 ++ B :: x2) ++ A0 :: Γ4, C)] ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4, C)).
        assert ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4 = Γ2 ++ # P :: (x0 ++ B :: x2) ++ # P → A0 :: Γ4).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply AtomImpL1Rule_I. apply AtomImpL1 in H1.
        assert (J4: OrLRule [(Γ2 ++ # P :: (x0 ++ A :: x2) ++ A0 :: Γ4, C);(Γ2 ++ # P :: (x0 ++ B :: x2) ++ A0 :: Γ4, C)] (Γ2 ++ # P :: ((x0 ++ [A ∨ B]) ++ x2) ++ A0 :: Γ4, C)).
        assert (Γ2 ++ # P :: ((x0 ++ [A ∨ B]) ++ x2) ++ A0 :: Γ4 = (Γ2 ++ # P :: x0) ++ A ∨ B :: x2 ++ A0 :: Γ4).
        repeat rewrite <- app_assoc ; auto. rewrite H2.
        assert (Γ2 ++ # P :: (x0 ++ A :: x2) ++ A0 :: Γ4 = (Γ2 ++ # P :: x0) ++ A :: x2 ++ A0 :: Γ4).
        repeat rewrite <- app_assoc ; auto. rewrite H3.
        assert (Γ2 ++ # P :: (x0 ++ B :: x2) ++ A0 :: Γ4 = (Γ2 ++ # P :: x0) ++ B :: x2 ++ A0 :: Γ4).
        repeat rewrite <- app_assoc ; auto. rewrite H4. apply OrLRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia.  assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x1 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: (x0 ++ A :: x2) ++ A0 :: Γ4, C)]) ((Γ2 ++ # P :: x0) ++ A :: x2 ++ # P → A0 :: Γ4, C) H0 d0).
        pose (dlCons x3 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
        (ps:= [(Γ2 ++ # P :: (x0 ++ B :: x2) ++ A0 :: Γ4, C)]) ((Γ2 ++ # P :: x0) ++ B :: x2 ++ # P → A0 :: Γ4, C) H1 d2).
        exists d1. exists d3. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity. }
      { repeat destruct s. repeat destruct p ; subst.
        assert (AtomImpL1Rule  [(Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ A :: Γ1, C)]
        ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ A :: Γ1, C)). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. apply AtomImpL1Rule_I. apply AtomImpL1 in H0.
        assert (AtomImpL1Rule  [(Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ B :: Γ1, C)]
        ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. apply AtomImpL1Rule_I. apply AtomImpL1 in H1.
        assert (J4: OrLRule [(Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ A :: Γ1, C);(Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ B :: Γ1, C)] (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ A ∨ B :: Γ1, C)).
        assert (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ A ∨ B :: Γ1 = (Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ A ∨ B :: Γ1).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2.
        assert (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ A :: Γ1 = (Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ A :: Γ1).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H3.
        assert (Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ B :: Γ1 = (Γ2 ++ # P :: Γ3 ++ A0 :: x1) ++ B :: Γ1).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H4. apply OrLRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ A :: Γ1, C)]) ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ A :: Γ1, C) H0 d0).
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
        (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: x1 ++ B :: Γ1, C)]) ((Γ2 ++ # P :: Γ3 ++ # P → A0 :: x1) ++ B :: Γ1, C) H1 d2).
        exists d1. exists d3. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity. }
 (* AtomImpL2 *)
   * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
     pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
     apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst. { inversion e1. }
    { assert (AtomImpL2Rule  [((Γ0 ++ A :: x1) ++ A0 :: Γ3 ++ # P :: Γ4, C)] ((Γ0 ++ A :: x1) ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
      repeat rewrite <- app_assoc in H0. simpl in H0.
      assert (AtomImpL2Rule  [((Γ0 ++ B :: x1) ++A0 :: Γ3 ++ # P :: Γ4, C)] ((Γ0 ++ B :: x1) ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I. apply AtomImpL2 in H1.
      repeat rewrite <- app_assoc in H1. simpl in H1.
      assert (J4: OrLRule [(Γ0 ++ A :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C);(Γ0 ++ B :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)]
      (((Γ0 ++ [A ∨ B]) ++ x1) ++ A0 :: Γ3 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc. apply OrLRule_I.
      assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
      pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:= [(Γ0 ++ A :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)]) (Γ0 ++ A :: x1 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C) H0 d0).
      pose (dlCons x2 DersNilF). pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:= [(Γ0 ++ B :: x1 ++ A0 :: Γ3 ++ # P :: Γ4, C)]) (Γ0 ++ B :: x1 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C) H1 d2).
      exists d1. exists d3. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity. }
   { repeat destruct s. repeat destruct p ; subst.
      apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst. { inversion e1. }
      { assert (AtomImpL2Rule  [(Γ2 ++ A0 :: (x0 ++ A :: x2) ++ # P :: Γ4, C)] ((Γ2 ++ # P → A0 :: x0) ++ A :: x2 ++ # P :: Γ4, C)).
        assert ((Γ2 ++ # P → A0 :: x0) ++ A :: x2 ++ # P :: Γ4 = Γ2 ++ # P → A0 :: (x0 ++ A :: x2) ++ # P :: Γ4).
        repeat rewrite <- app_assoc ; auto. rewrite H0. apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
        assert (AtomImpL2Rule  [(Γ2 ++ A0 :: (x0 ++ B :: x2) ++ # P :: Γ4, C)] ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C)).
        assert ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P :: Γ4 = Γ2 ++ # P → A0 :: (x0 ++ B :: x2) ++ # P :: Γ4).
        repeat rewrite <- app_assoc ; auto. rewrite H1. apply AtomImpL2Rule_I. apply AtomImpL2 in H1.
        assert (J4: OrLRule [(Γ2 ++ A0 :: (x0 ++ A :: x2) ++ # P :: Γ4, C);(Γ2 ++ A0 :: (x0 ++ B :: x2) ++ # P :: Γ4, C)] (Γ2 ++ A0 :: ((x0 ++ [A ∨ B]) ++ x2) ++ # P :: Γ4, C)).
        assert (Γ2 ++ A0 :: ((x0 ++ [A ∨ B]) ++ x2) ++ # P :: Γ4 = (Γ2 ++ A0 :: x0) ++ A ∨ B :: x2 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto. rewrite H2.
        assert (Γ2 ++ A0 :: (x0 ++ A :: x2) ++ # P :: Γ4 = (Γ2 ++ A0 :: x0) ++ A :: x2 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto. rewrite H3.
        assert (Γ2 ++ A0 :: (x0 ++ B :: x2) ++ # P :: Γ4 = (Γ2 ++ A0 :: x0) ++ B :: x2 ++ # P :: Γ4). repeat rewrite <- app_assoc ; auto. rewrite H4. apply OrLRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x1 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 :: (x0 ++ A :: x2) ++ # P :: Γ4, C)]) ((Γ2 ++ # P → A0 :: x0) ++ A :: x2 ++ # P :: Γ4, C) H0 d0).
        pose (dlCons x3 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:= [(Γ2 ++A0 :: (x0 ++ B :: x2) ++ # P :: Γ4, C)]) ((Γ2 ++ # P → A0 :: x0) ++ B :: x2 ++ # P :: Γ4, C) H1 d2).
        exists d1. exists d3. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity. }
      { repeat destruct s. repeat destruct p ; subst.
        assert (AtomImpL2Rule  [(Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ A :: Γ1, C)] ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ A :: Γ1, C)). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. apply AtomImpL2Rule_I. apply AtomImpL2 in H0.
        assert (AtomImpL2Rule  [(Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ B :: Γ1, C)] ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc.
        simpl. repeat rewrite <- app_assoc. apply AtomImpL2Rule_I. apply AtomImpL2 in H1.
        assert (J4: OrLRule [(Γ2 ++A0 :: Γ3 ++ # P :: x1 ++ A :: Γ1, C);(Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ B :: Γ1, C)] (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ A ∨ B :: Γ1, C)).
        assert (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ A ∨ B :: Γ1 = (Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ A ∨ B :: Γ1). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2.
        assert (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ A :: Γ1 = (Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ A :: Γ1). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H3.
        assert (Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ B :: Γ1 = (Γ2 ++ A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H4. apply OrLRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 :: Γ3 ++ # P :: x1 ++ A :: Γ1, C)]) ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ A :: Γ1, C) H0 d0).
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++A0 :: Γ3 ++ # P :: x1 ++ B :: Γ1, C)]) ((Γ2 ++ # P → A0 :: Γ3 ++ # P :: x1) ++ B :: Γ1, C) H1 d2).
        exists d1. exists d3. simpl. rewrite dersrec_height_nil. split ; lia. reflexivity. } }
 (* AndImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    +  assert (AndImpLRule [((Γ0 ++ A :: x1) ++ A0 → B0 → C0 :: Γ3, C)] ((Γ0 ++ A :: x1) ++ (A0 ∧ B0) → C0 :: Γ3, C)). apply AndImpLRule_I. apply AndImpL in H0.
        repeat rewrite <- app_assoc in H0 ; simpl in H0.
        assert (AndImpLRule [((Γ0 ++ B :: x1) ++ A0 → B0 → C0 :: Γ3, C)] ((Γ0 ++ B :: x1) ++ (A0 ∧ B0) → C0 :: Γ3, C)). apply AndImpLRule_I. apply AndImpL in H1.
        repeat rewrite <- app_assoc in H1 ; simpl in H1.
        assert (J4: OrLRule [(Γ0 ++ A :: x1 ++ A0 → B0 → C0 :: Γ3, C);(Γ0 ++ B :: x1 ++ A0 → B0 → C0 :: Γ3, C)]
        (((Γ0 ++ [A ∨ B]) ++ x1) ++ A0 → B0 → C0 :: Γ3, C)). repeat rewrite <- app_assoc ; simpl. apply OrLRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: x1 ++ A0 → B0 → C0 :: Γ3, C)]) (Γ0 ++ A :: x1 ++ (A0 ∧ B0) → C0 :: Γ3, C) H0 d0).
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ B :: x1 ++ A0 → B0 → C0 :: Γ3, C)]) (Γ0 ++ B :: x1 ++ (A0 ∧ B0) → C0 :: Γ3, C) H1 d2).
        exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
    +  repeat destruct s. repeat destruct p ; subst.
        assert (AndImpLRule [(Γ2 ++ A0 → B0 → C0 :: x0 ++ A :: Γ1, C)] ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. apply AndImpLRule_I. apply AndImpL in H0.
        assert (AndImpLRule [(Γ2 ++ A0 → B0 → C0 :: x0 ++ B :: Γ1, C)] ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply AndImpLRule_I. apply AndImpL in H1.
        assert (J4: OrLRule [(Γ2 ++ A0 → B0 → C0 :: x0 ++ A :: Γ1, C);(Γ2 ++ A0 → B0 → C0 :: x0 ++ B :: Γ1, C)] (Γ2 ++ A0 → B0 → C0 :: x0 ++ A ∨ B :: Γ1, C)).
        assert (Γ2 ++ A0 → B0 → C0 :: x0 ++ A ∨ B :: Γ1 = (Γ2 ++ A0 → B0 → C0 :: x0) ++ A ∨ B :: Γ1). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H2.
        assert (Γ2 ++ A0 → B0 → C0 :: x0 ++ A :: Γ1 = (Γ2 ++ A0 → B0 → C0 :: x0) ++ A :: Γ1). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H3.
        assert (Γ2 ++ A0 → B0 → C0 :: x0 ++ B :: Γ1 = (Γ2 ++ A0 → B0 → C0 :: x0) ++ B :: Γ1). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. rewrite H4. apply OrLRule_I.
        assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x1 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → B0 → C0 :: x0 ++ A :: Γ1, C)]) ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ A :: Γ1, C) H0 d0).
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → B0 → C0 :: x0 ++ B :: Γ1, C)]) ((Γ2 ++ (A0 ∧ B0) → C0 :: x0) ++ B :: Γ1, C) H1 d2).
        exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
 (* OrImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
   + inversion e1.
   +  assert (OrImpLRule [((Γ0 ++ A :: x1) ++ A0 → C0 :: Γ3 ++  B0 → C0 :: Γ4, C)] ((Γ0 ++ A :: x1) ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I. apply OrImpL in H0.
        repeat rewrite <- app_assoc in H0 ; simpl in H0.
        assert (OrImpLRule [((Γ0 ++ B :: x1) ++ A0 → C0 :: Γ3 ++  B0 → C0 :: Γ4, C)] ((Γ0 ++ B :: x1) ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I. apply OrImpL in H1.
        repeat rewrite <- app_assoc in H1 ; simpl in H1.
        assert (J4: OrLRule [(Γ0 ++ A :: x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C);(Γ0 ++ B:: x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)]
        (((Γ0 ++ [A ∨ B]) ++ x1) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)). repeat rewrite <- app_assoc ; simpl.
        apply OrLRule_I. assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)]) (Γ0 ++ A :: x1 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C) H0 d0).
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ B :: x1 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)]) (Γ0 ++ B :: x1 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C) H1 d2).
        exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
   +   repeat destruct s. repeat destruct p ; subst. apply app2_find_hole in e1. destruct e1. repeat destruct s ; destruct p ; subst.
        {   assert (OrImpLRule [(Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: A :: Γ1, C)]
            ((Γ2 ++ (A0 ∨ B0) → C0 :: Γ3) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. apply OrImpLRule_I. apply OrImpL in H0.
            assert (OrImpLRule [(Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: B :: Γ1, C)]
            ((Γ2 ++ (A0 ∨ B0) → C0 :: Γ3) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply OrImpLRule_I. apply OrImpL in H1.
            assert (J4: OrLRule [((Γ2 ++ A0 → C0 :: Γ3 ++ [B0 → C0]) ++ A :: Γ1, C);((Γ2 ++ A0 → C0 :: Γ3 ++ [B0 → C0]) ++ B :: Γ1, C)]
            ((Γ2 ++ A0 → C0 :: Γ3 ++ [B0 → C0]) ++ A ∨ B :: Γ1, C)). apply OrLRule_I. repeat rewrite <- app_assoc in J4 ; simpl in J4 ; repeat rewrite <- app_assoc in J4.
            assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
            pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
            pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: A :: Γ1, C)]) ((Γ2 ++ (A0 ∨ B0) → C0 :: Γ3) ++ A :: Γ1, C) H0 d0).
            pose (dlCons x2 DersNilF).
            pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → C0 :: Γ3 ++ [B0 → C0] ++ B :: Γ1, C)]) ((Γ2 ++ (A0 ∨ B0) → C0 :: Γ3) ++ B :: Γ1, C) H1 d2).
            exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; rewrite Nat.max_0_r ; apply le_n_S ; rewrite <- e ; auto. }
        {   assert (OrImpLRule [(Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: x1 ++ A :: Γ1, C)] ((Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ x1) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
            apply OrImpLRule_I. apply OrImpL in H0.
            assert (OrImpLRule [(Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: x1 ++ B :: Γ1, C)] ((Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
            apply OrImpLRule_I. apply OrImpL in H1.
            assert (J4: OrLRule [((Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: x1) ++ A :: Γ1, C);((Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: x1) ++ B :: Γ1, C)]
            ((Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: x1) ++ A ∨ B :: Γ1, C)). apply OrLRule_I.  repeat rewrite <- app_assoc in J4 ; simpl in J4 ; repeat rewrite <- app_assoc in J4.
            assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
            pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x0 DersNilF).
            pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → C0 :: Γ3 ++ (B0 → C0 :: x1) ++ A :: Γ1, C)]) ((Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ x1) ++ A :: Γ1, C) H0 d0).
            pose (dlCons x2 DersNilF).
            pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → C0 :: Γ3 ++ (B0 → C0 :: x1) ++ B :: Γ1, C)]) ((Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ x1) ++ B :: Γ1, C) H1 d2).
            exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; rewrite Nat.max_0_r ; apply le_n_S ; rewrite <- e ; auto. }
        {   destruct x1.
            -  simpl in e1. subst. assert (OrImpLRule [(Γ2 ++ A0 → C0 :: x0 ++ B0 → C0 :: A :: Γ1, C)]
              ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.  apply OrImpLRule_I. apply OrImpL in H0.
              assert (OrImpLRule [(Γ2 ++ A0 → C0 :: x0 ++ B0 → C0 :: B :: Γ1, C)]  ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc.
              apply OrImpLRule_I. apply OrImpL in H1.
              assert (J4: OrLRule [(Γ2 ++ A0 → C0 :: x0 ++ B0 → C0 :: A :: Γ1, C);(Γ2 ++ A0 → C0 :: x0 ++ B0 → C0 :: B :: Γ1, C)] (Γ2 ++ A0 → C0 :: (x0 ++ []) ++ B0 → C0 :: A ∨ B :: Γ1, C)).
              assert (Γ2 ++ A0 → C0 :: x0 ++ B0 → C0 :: A :: Γ1 = (Γ2 ++ A0 → C0 :: x0 ++ [B0 → C0]) ++ A :: Γ1).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.
              assert (Γ2 ++ A0 → C0 :: x0 ++ B0 → C0 :: B :: Γ1 = (Γ2 ++ A0 → C0 :: x0 ++ [B0 → C0]) ++ B :: Γ1).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H3.
              assert (Γ2 ++ A0 → C0 :: (x0 ++ []) ++ B0 → C0 :: A ∨ B :: Γ1 = (Γ2 ++ A0 → C0 :: x0 ++ [B0 → C0]) ++ A ∨ B :: Γ1).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H4.
              apply OrLRule_I. assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
              pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p. pose (dlCons x1 DersNilF).
              pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → C0 :: x0 ++ B0 → C0 :: A :: Γ1, C)]) ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ A :: Γ1, C) H0 d0).
              pose (dlCons x2 DersNilF).
              pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → C0 :: x0 ++ B0 → C0 :: B :: Γ1, C)]) ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: Γ1, C) H1 d2).
              exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
            -  inversion e1. subst. assert (OrImpLRule [(Γ2 ++ A0 → C0 :: x0 ++ A :: x1 ++ B0 → C0 :: Γ4, C)] ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ A :: x1 ++ Γ4, C)).
              assert (Γ2 ++ A0 → C0 :: x0 ++ A :: x1 ++ B0 → C0 :: Γ4 = Γ2 ++ A0 → C0 :: (x0 ++ A :: x1) ++ B0 → C0 :: Γ4).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H0.
              assert ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ A :: x1 ++ Γ4 = Γ2 ++ (A0 ∨ B0) → C0 :: (x0 ++ A :: x1) ++ Γ4).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1. apply OrImpLRule_I. apply OrImpL in H0.
              assert (OrImpLRule [(Γ2 ++ A0 → C0 :: x0 ++ B :: x1 ++ B0 → C0 :: Γ4, C)] ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: x1 ++ Γ4, C)).
              assert (Γ2 ++ A0 → C0 :: x0 ++ B :: x1 ++ B0 → C0 :: Γ4 = Γ2 ++ A0 → C0 :: (x0 ++ B :: x1) ++ B0 → C0 :: Γ4).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H1.
              assert ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: x1 ++ Γ4 = Γ2 ++ (A0 ∨ B0) → C0 :: (x0 ++ B :: x1) ++ Γ4).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2. apply OrImpLRule_I. apply OrImpL in H1.
              assert (J4: OrLRule [(Γ2 ++ A0 → C0 :: x0 ++ A :: x1 ++ B0 → C0 :: Γ4, C);(Γ2 ++ A0 → C0 :: x0 ++ B :: x1 ++ B0 → C0 :: Γ4, C)]  (Γ2 ++ A0 → C0 :: (x0 ++ A ∨ B :: x1) ++ B0 → C0 :: Γ4, C)).
              assert (Γ2 ++ A0 → C0 :: x0 ++ A :: x1 ++ B0 → C0 :: Γ4 = (Γ2 ++ A0 → C0 :: x0) ++ A :: x1 ++ B0 → C0 :: Γ4).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H2.
              assert (Γ2 ++ A0 → C0 :: x0 ++ B :: x1 ++ B0 → C0 :: Γ4 = (Γ2 ++ A0 → C0 :: x0) ++ B :: x1 ++ B0 → C0 :: Γ4).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H3.
              assert (Γ2 ++ A0 → C0 :: (x0 ++ A ∨ B :: x1) ++ B0 → C0 :: Γ4 = (Γ2 ++ A0 → C0 :: x0) ++ A ∨ B :: x1 ++ B0 → C0 :: Γ4).
              repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. auto. rewrite H4.  apply OrLRule_I.
              assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
              pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p.  pose (dlCons x2 DersNilF).
              pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → C0 :: x0 ++ A :: x1 ++ B0 → C0 :: Γ4, C)]) ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ A :: x1 ++ Γ4, C) H0 d0).
              pose (dlCons x3 DersNilF).
              pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ A0 → C0 :: x0 ++ B :: x1 ++ B0 → C0 :: Γ4, C)]) ((Γ2 ++ (A0 ∨ B0) → C0 :: x0) ++ B :: x1 ++ Γ4, C) H1 d2).
              exists d1. exists d3. simpl. rewrite dersrec_height_nil ; auto. split ; lia. }
  (* ImpImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
    apply list_split_form in H2. destruct H2. repeat destruct s ; repeat destruct p ; subst.
    + inversion e1.
    + assert (ImpImpLRule [((Γ0 ++ A :: x2) ++ B0 → C0 :: Γ3, A0 → B0);((Γ0 ++ A :: x2) ++ C0 :: Γ3, C)]
       ((Γ0 ++ A :: x2) ++ (A0 → B0) → C0 :: Γ3, C)). apply ImpImpLRule_I. apply ImpImpL in H0. repeat rewrite <- app_assoc in H0. simpl in H0.
       assert (ImpImpLRule [((Γ0 ++ B :: x2) ++ B0 → C0 :: Γ3, A0 → B0);((Γ0 ++ B :: x2) ++ C0 :: Γ3, C)]
       ((Γ0 ++ B :: x2) ++ (A0 → B0) → C0 :: Γ3, C)). apply ImpImpLRule_I. apply ImpImpL in H1. repeat rewrite <- app_assoc in H1. simpl in H1.
       assert (J4: OrLRule [(Γ0 ++ A :: x2 ++ B0 → C0 :: Γ3, A0 → B0);(Γ0 ++ B :: x2 ++ B0 → C0 :: Γ3, A0 → B0)]
       (((Γ0 ++ [A ∨ B]) ++ x2) ++ B0 → C0 :: Γ3, A0 → B0)). repeat rewrite <- app_assoc. simpl. apply OrLRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p.
       assert (J7: OrLRule [(Γ0 ++ A :: x2 ++ C0 :: Γ3, C);(Γ0 ++ B :: x2 ++ C0 :: Γ3, C)] (((Γ0 ++ [A ∨ B]) ++ x2) ++ C0 :: Γ3, C)). repeat rewrite <- app_assoc. simpl. apply OrLRule_I.
       assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J8 _ _ J9 _ _ J7). repeat destruct s. repeat destruct p. pose (dlCons x4 DersNilF). pose (dlCons x1 d0).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A :: x2 ++ B0 → C0 :: Γ3, A0 → B0); (Γ0 ++ A :: x2 ++ C0 :: Γ3, C)]) (Γ0 ++ A :: x2 ++ (A0 → B0) → C0 :: Γ3, C) H0 d1).
       pose (dlCons x5 DersNilF). pose (dlCons x3 d3).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:= [(Γ0 ++ B :: x2 ++ B0 → C0 :: Γ3, A0 → B0); (Γ0 ++ B :: x2 ++ C0 :: Γ3, C)]) (Γ0 ++ B :: x2 ++ (A0 → B0) → C0 :: Γ3, C) H1 d4).
       exists d2. exists d5. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
    + repeat destruct s. repeat destruct p ; subst.
       assert (ImpImpLRule [(Γ2 ++ B0 → C0 :: x1 ++ A :: Γ1, A0 → B0);(Γ2 ++ C0 :: x1 ++ A :: Γ1, C)]
       ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ A :: Γ1, C)). repeat rewrite <- app_assoc. apply ImpImpLRule_I. apply ImpImpL in H0.
       assert (ImpImpLRule [(Γ2 ++ B0 → C0 :: x1 ++ B :: Γ1, A0 → B0);(Γ2 ++ C0 :: x1 ++ B :: Γ1, C)]
       ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ B :: Γ1, C)). repeat rewrite <- app_assoc. apply ImpImpLRule_I. apply ImpImpL in H1.
       assert (J4: OrLRule [(Γ2 ++ B0 → C0 :: x1 ++ A :: Γ1, A0 → B0);(Γ2 ++ B0 → C0 :: x1 ++ B :: Γ1, A0 → B0)] (Γ2 ++ B0 → C0 :: x1 ++ A ∨ B :: Γ1, A0 → B0)).
       assert (Γ2 ++ B0 → C0 :: x1 ++ A :: Γ1 = (Γ2 ++ B0 → C0 :: x1) ++ A :: Γ1). repeat rewrite <- app_assoc ; auto. rewrite H2.
       assert (Γ2 ++ B0 → C0 :: x1 ++ B :: Γ1 = (Γ2 ++ B0 → C0 :: x1) ++ B :: Γ1). repeat rewrite <- app_assoc ; auto. rewrite H3.
       assert (Γ2 ++ B0 → C0 :: x1 ++ A ∨ B :: Γ1 = (Γ2 ++ B0 → C0 :: x1) ++ A ∨ B :: Γ1).
       repeat rewrite <- app_assoc ; auto. rewrite H4. apply OrLRule_I.
       assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
       pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. repeat destruct p.
       assert (J7: OrLRule [(Γ2 ++ C0 :: x1 ++ A :: Γ1, C);(Γ2 ++ C0 :: x1 ++ B :: Γ1, C)] (Γ2 ++ C0 :: x1 ++ A ∨ B :: Γ1, C)).
       assert (Γ2 ++ C0 :: x1 ++ A :: Γ1 = (Γ2 ++ C0 :: x1) ++ A :: Γ1). repeat rewrite <- app_assoc ; auto. rewrite H2.
       assert (Γ2 ++ C0 :: x1 ++ B :: Γ1 = (Γ2 ++ C0 :: x1) ++ B :: Γ1). repeat rewrite <- app_assoc ; auto. rewrite H3.
       assert (Γ2 ++ C0 :: x1 ++ A ∨ B :: Γ1 = (Γ2 ++ C0 :: x1) ++ A ∨ B :: Γ1). repeat rewrite <- app_assoc ; auto. rewrite H4.
       apply OrLRule_I. assert (J8: derrec_height x0 < S (dersrec_height d)). lia. assert (J9: derrec_height x0 = derrec_height x0). reflexivity.
       pose (IH _ J8 _ _ J9 _ _ J7). repeat destruct s. repeat destruct p. pose (dlCons x4 DersNilF). pose (dlCons x2 d0).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ B0 → C0 :: x1 ++ A :: Γ1, A0 → B0); (Γ2 ++ C0 :: x1 ++ A :: Γ1, C)]) ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ A :: Γ1, C) H0 d1).
       pose (dlCons x5 DersNilF). pose (dlCons x3 d3).
       pose (derI (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ2 ++ B0 → C0 :: x1 ++ B :: Γ1, A0 → B0); (Γ2 ++ C0 :: x1 ++ B :: Γ1, C)]) ((Γ2 ++ (A0 → B0) → C0 :: x1) ++ B :: Γ1, C) H1 d4).
       exists d2. exists d5. simpl. rewrite dersrec_height_nil ; auto. split ; lia.
  (* BoxImpL *)
 * inversion H ; subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + inversion e0.
   + destruct x. { inversion e0. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. repeat rewrite <- app_assoc. simpl.
        assert (J4: OrLRule [((unBoxed_list Γ2 ++ B0 :: unBoxed_list x) ++ A :: unBoxed_list Γ1 ++ [Box A0], A0);((unBoxed_list Γ2 ++ B0 :: unBoxed_list x) ++ B :: unBoxed_list Γ1 ++ [Box A0], A0)]
        (unBoxed_list Γ2 ++ B0 :: unBoxed_list (x ++ A ∨ B :: Γ1) ++ [Box A0], A0)).
        repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl. epose (OrLRule_I A B A0 (unBoxed_list Γ2 ++ B0 :: unBoxed_list x) (unBoxed_list Γ1 ++ [Box A0])). repeat rewrite <- app_assoc in o ; simpl in o ; apply o.
        assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
        pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s. destruct p.
        assert (J7: OrLRule [((Γ2 ++ B0 :: x) ++ A :: Γ1, C);((Γ2 ++ B0 :: x) ++ B :: Γ1, C)] ((Γ2 ++ B0 :: x) ++ Or A B :: Γ1, C)). apply OrLRule_I.
        repeat rewrite <- app_assoc in J7. simpl in J7. assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J9: derrec_height x1 = derrec_height x1). reflexivity. pose (IH _ J8 _ _ J9 _ _ J7). repeat destruct s. destruct p.
        assert (BoxImpLRule [((unBoxed_list Γ2 ++ B0 :: unBoxed_list x) ++ unBox_formula A :: unBoxed_list Γ1 ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ A :: Γ1, C)]
        (Γ2 ++ Box A0 → B0 :: x ++ A :: Γ1, C)). epose (@BoxImpLRule_I _ _ _ Γ2 (x ++ A :: Γ1)).
        repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b. apply b ; auto.
        assert (BoxImpLRule [((unBoxed_list Γ2 ++ B0 :: unBoxed_list x) ++ unBox_formula B :: unBoxed_list Γ1 ++ [Box A0], A0); (Γ2 ++ B0 :: x ++ B :: Γ1, C)]
        (Γ2 ++ Box A0 → B0 :: x ++ B :: Γ1, C)). epose (@BoxImpLRule_I _ _ _ Γ2 (x ++ B :: Γ1)).
        repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b. apply b ; auto.
        apply BoxImpL in H0. apply BoxImpL in H1.
        pose (unBox_left_hpadm_gen A (unBoxed_list Γ2 ++ B0 :: unBoxed_list x) (unBoxed_list Γ1 ++ [Box A0]) A0 x2).
        destruct s. pose (dlCons x4 DersNilF). pose (dlCons x6 d0). pose (derI _ H0 d1). exists d2.
        pose (unBox_left_hpadm_gen B (unBoxed_list Γ2 ++ B0 :: unBoxed_list x) (unBoxed_list Γ1 ++ [Box A0]) A0 x3).
        destruct s. pose (dlCons x5 DersNilF). pose (dlCons x7 d3). pose (derI _ H1 d4). exists d5.
        simpl. rewrite dersrec_height_nil. simpl. split ;lia. reflexivity. }
    + destruct x. { simpl in e0. inversion e0. }
       { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
          pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. repeat rewrite <- app_assoc. simpl.
          assert (J4: OrLRule [(unBoxed_list Γ0 ++ A :: unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0);(unBoxed_list Γ0 ++ B :: unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0)]
          (unBoxed_list (Γ0 ++ A ∨ B :: x) ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0)). repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc. apply OrLRule_I.
          assert (J5: derrec_height x0 < S (dersrec_height d)). lia. assert (J6: derrec_height x0 = derrec_height x0). reflexivity.
          pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s ; destruct p.
          assert (J7: OrLRule [(Γ0 ++ A :: x ++ B0 :: Γ3, C);(Γ0 ++ B :: x ++ B0 :: Γ3, C)] ((Γ0 ++ Or A B :: x) ++ B0 :: Γ3, C)). repeat rewrite <- app_assoc. simpl. apply OrLRule_I.
          assert (J8: derrec_height x1 < S (dersrec_height d)). lia.
          assert (J9: derrec_height x1 = derrec_height x1). reflexivity. pose (IH _ J8 _ _ J9 _ _ J7). repeat destruct s ; destruct p.
          assert (BoxImpLRule [(unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0);(Γ0 ++ A :: x ++ B0 :: Γ3, C)]
          (Γ0 ++ A :: x ++ Box A0 → B0 :: Γ3, C)). epose (@BoxImpLRule_I _ _ _ (Γ0 ++ A :: x) Γ3).
          repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b. apply b ; auto.
          assert (BoxImpLRule [(unBoxed_list Γ0 ++ unBox_formula B :: unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0); (Γ0 ++ B :: x ++ B0 :: Γ3, C)]
          (Γ0 ++ B :: x ++ Box A0 → B0 :: Γ3, C)). epose (@BoxImpLRule_I _ _ _ (Γ0 ++ B :: x) Γ3).
          repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in b ; simpl in b. apply b ; auto.
          apply BoxImpL in H0. apply BoxImpL in H1.
          pose (unBox_left_hpadm_gen A (unBoxed_list Γ0) (unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0]) A0 x2).
          destruct s. pose (dlCons x4 DersNilF). pose (dlCons x6 d0). pose (derI _ H0 d1). exists d2.
          pose (unBox_left_hpadm_gen B (unBoxed_list Γ0) (unBoxed_list x ++ B0 :: unBoxed_list Γ3 ++ [Box A0]) A0 x3).
          destruct s. pose (dlCons x5 DersNilF). pose (dlCons x7 d3). pose (derI _ H1 d4). exists d5.
          simpl. rewrite dersrec_height_nil. simpl. split ;lia. reflexivity. }
  (* SLR *)
  * inversion H. subst. simpl. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
    assert (SLRRule [(unBoxed_list (Γ0 ++ A :: Γ1) ++ [Box A0], A0)] (Γ0 ++ A :: Γ1, Box A0)). apply SLRRule_I ; auto.
    apply SLR in H0. repeat rewrite unBox_app_distrib in H0 ; simpl in H0. repeat rewrite <- app_assoc in H0 ; simpl in H0.
    assert (SLRRule [(unBoxed_list (Γ0 ++ B :: Γ1) ++ [Box A0], A0)] (Γ0 ++ B :: Γ1, Box A0)). apply SLRRule_I ; auto.
    apply SLR in H1. repeat rewrite unBox_app_distrib in H1 ; simpl in H1. repeat rewrite <- app_assoc in H1 ; simpl in H1.
    assert (J4: OrLRule [(unBoxed_list Γ0 ++ A :: unBoxed_list Γ1 ++ [Box A0], A0);(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0)] (unBoxed_list (Γ0 ++ A ∨ B :: Γ1) ++ [Box A0], A0)).
    repeat rewrite unBox_app_distrib ; repeat rewrite <- app_assoc. apply OrLRule_I.
    assert (J5: derrec_height x < S (dersrec_height d)). lia. assert (J6: derrec_height x = derrec_height x). reflexivity.
    pose (IH _ J5 _ _ J6 _ _ J4). repeat destruct s ; destruct p.
    pose (unBox_left_hpadm_gen A (unBoxed_list Γ0) (unBoxed_list Γ1 ++ [Box A0]) A0 x0).
    destruct s. pose (dlCons x2 DersNilF). pose (derI _ H0 d0). exists d1.
    pose (unBox_left_hpadm_gen B (unBoxed_list Γ0) (unBoxed_list Γ1 ++ [Box A0]) A0 x1).
    destruct s. pose (dlCons x3 DersNilF). pose (derI _ H1 d2). exists d3.
    simpl. rewrite dersrec_height_nil. simpl. split ;lia. reflexivity.
Qed.

Theorem OrL_inv : forall concl prem1 prem2, (derrec G4iSL_rules (fun _ => False) concl) ->
                                      (OrLRule [prem1;prem2] concl) ->
                                      ((derrec G4iSL_rules (fun _ => False) prem1) * (derrec G4iSL_rules (fun _ => False) prem2)).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (OrL_hpinv _  _ X J1). pose (s _ _ H). destruct s0. destruct s0. auto.
Qed.



