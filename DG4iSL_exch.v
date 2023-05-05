Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.
Require Export DG4iSL_exch_prelims1.
Require Import DG4iSL_exch_prelims2.
Require Import DG4iSL_exch_prelims3.
Require Import DG4iSL_exch_prelims4.
Require Import DG4iSL_exch_prelims5.

Theorem G4iSL_hpadm_list_exch_L : forall (k : nat) s
                                  (D0: derrec G4iSL_rules (fun _ => False) s),
        k = (derrec_height D0) ->
        (forall se, (list_exch_L s se) ->
        (existsT2 (D1 : derrec G4iSL_rules (fun _ => False) se),
          derrec_height D1 <=k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s : list (MPropF) * (MPropF))
  (D0 : derrec G4iSL_rules (fun _ : list (MPropF) * (MPropF) => False) s),
x = derrec_height D0 ->
(forall se,
(list_exch_L s se) ->
(existsT2
  D1 : derrec G4iSL_rules
         (fun _ : list (MPropF) * (MPropF) => False) se,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.
(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 ip a leaf *)
- inversion f.
(* D0 is ends with an application of rule *)
- intros hei se exch. inversion exch.
  assert (DersNil: dersrec G4iSL_rules (fun _ : list (MPropF) * (MPropF) => False) []).
  apply dersrec_nil. inversion g.
  (* IdP *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In # P (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). assert (In # P (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4)).
    rewrite <- H0. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (IdPRule [] (x ++ # P :: x0, # P)). apply IdPRule_I. apply IdP in H.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[]) (x ++ # P :: x0, # P) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
  (* BotL *)
  * inversion H1. subst. inversion H5. subst. simpl.
    assert (In (Bot) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4)). assert (In (Bot) (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4)).
    rewrite <- H0. apply in_or_app. right. apply in_eq. apply in_app_or in H. apply in_or_app.
    destruct H. auto. apply in_app_or in H. right. apply in_or_app. destruct H. right. apply in_or_app.
    right. apply in_or_app. auto. apply in_app_or in H. destruct H. right. apply in_or_app. auto.
    apply in_app_or in H. destruct H. auto. right. apply in_or_app. right. apply in_or_app. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e.
    assert (BotLRule [] (x ++ Bot :: x0, A)). apply BotLRule_I. apply BotL in H.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[]) (x ++ Bot :: x0, A) H DersNil). exists d0. simpl. rewrite dersrec_height_nil.
    lia. reflexivity.
 (* AndR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AndR_app_list_exchL _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply AndR in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, A0) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, B) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A0 ∧ B) a d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* AndL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AndL_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply AndL in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 :: B :: Γ6, A) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* OrR1 *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (OrR1_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply OrR1 in o. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, A0) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A0 ∨ B) o d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* OrR2 *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (OrR2_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply OrR2 in o. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, B) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A0 ∨ B) o d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* OrL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (OrL_app_list_exchL _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply OrL in o. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ5 ++ A0 :: Γ6, A) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ5 ++ B :: Γ6, A) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) o d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpR_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply ImpR in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 :: Γ6, B) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Imp A0 B) i d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* AtomImpL1 *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AtomImpL1_app_list_exchL _ _ _ exch H1). destruct s. destruct p. destruct s.
   + apply AtomImpL1 in  a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J0). destruct s.
      assert (E: derrec_height x0 < S (dersrec_height d)). lia.
      assert (E1: derrec_height x0 = derrec_height x0). auto.
      pose (IH (derrec_height x0) E (Γ5 ++ # P :: Γ6 ++ A0 :: Γ7, A) x0 E1 x l).
      destruct s. pose (dlCons x1 DersNil).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
      (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
   + apply AtomImpL2 in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J0). destruct s.
      assert (E: derrec_height x0 < S (dersrec_height d)). lia.
      assert (E1: derrec_height x0 = derrec_height x0). auto.
      pose (IH (derrec_height x0) E (Γ5 ++ # P :: Γ6 ++ A0 :: Γ7, A) x0 E1 x l).
      destruct s. pose (dlCons x1 DersNil).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
      (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* AtomImpL2 *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AtomImpL2_app_list_exchL _ _ _ exch H1). destruct s. destruct p. destruct s.
   + apply AtomImpL2 in  a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J0). destruct s.
      assert (E: derrec_height x0 < S (dersrec_height d)). lia.
      assert (E1: derrec_height x0 = derrec_height x0). auto.
      pose (IH (derrec_height x0) E (Γ5 ++ A0 :: Γ6 ++ # P :: Γ7, A) x0 E1 x l).
      destruct s. pose (dlCons x1 DersNil).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
      (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
   + apply AtomImpL1 in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
      pose (dersrec_derrec_height d J0). destruct s.
      assert (E: derrec_height x0 < S (dersrec_height d)). lia.
      assert (E1: derrec_height x0 = derrec_height x0). auto.
      pose (IH (derrec_height x0) E (Γ5 ++ A0 :: Γ6 ++ # P :: Γ7, A)x0 E1 x l).
      destruct s. pose (dlCons x1 DersNil).
      pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
      (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
      rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* AndImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (AndImpL_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply AndImpL in a. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 → B → C :: Γ6, A) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) a d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* OrImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (OrImpL_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply OrImpL in o. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s0.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    destruct s.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 → C :: Γ6 ++ B → C :: Γ7, A) x0 E1 x l).
    destruct s. pose (dlCons x1 DersNil).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) o d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
    destruct s. destruct p.
    pose (IH (derrec_height x0) E (Γ5 ++ A0 → C :: Γ6 ++ B → C :: Γ7, A) x0 E1 x1 l). destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 x1 x2 E3 x l0).
    destruct s. pose (dlCons x3 DersNil).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) o d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (ImpImpL_app_list_exchL _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply ImpImpL in i. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E (Γ5 ++ B → C :: Γ6, A0 → B) x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ5 ++ C :: Γ6, A) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) i d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* BoxImpL *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (BoxImpL_app_list_exchL _ _ _ _ exch H1). repeat destruct s. repeat destruct p.
    apply BoxImpL in b. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec2_height d J0). repeat destruct s.
    assert (E: derrec_height x1 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x1 = derrec_height x1). auto.
    pose (IH (derrec_height x1) E _ x1 E1 x l0).
    destruct s.
    assert (E2: derrec_height x2 < S (dersrec_height d)). lia.
    assert (E3: derrec_height x2 = derrec_height x2). auto.
    pose (IH (derrec_height x2) E2 (Γ5 ++ B :: Γ6, A) x2 E3 x0 l).
    destruct s. pose (dlCons x4 DersNil). pose (dlCons x3 d0).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A) b d1). exists d2. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
  (* SLR *)
  * inversion H1. subst. inversion H5. subst. simpl. simpl in IH.
    pose (SLR_app_list_exchL _ _ _ exch H1). destruct s. destruct p.
    apply SLR in s. assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s0.
    assert (E: derrec_height x0 < S (dersrec_height d)). lia.
    assert (E1: derrec_height x0 = derrec_height x0). auto.
    pose (IH (derrec_height x0) E _ x0 E1 x l).
    destruct s0. pose (dlCons x1 DersNil).
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : list (MPropF) * (MPropF) => False)
    (ps:=[x]) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, Box A0) s d0). exists d1. simpl.
    rewrite dersrec_height_nil. rewrite Nat.max_0_r. lia. reflexivity.
Qed.

Theorem G4iSL_adm_list_exch_L : forall s,
        (derrec G4iSL_rules (fun _ => False) s) ->
        (forall se, (@list_exch_L s se) ->
        (derrec G4iSL_rules (fun _ => False) se)).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). auto.
pose (G4iSL_hpadm_list_exch_L (derrec_height X) s X J1 se H). destruct s0. auto.
Qed.

Definition exch s se := @list_exch_L s se.

Lemma G4iSL_adm_exch : forall s,
        (G4iSL_prv s) ->
        (forall se, (exch s se) ->
        (G4iSL_prv se)).
Proof.
unfold exch. unfold G4iSL_prv. apply G4iSL_adm_list_exch_L.
Qed.
