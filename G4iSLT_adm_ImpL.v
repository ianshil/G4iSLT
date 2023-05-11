Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import G4iSLT_calc.
Require Import G4iSLT_list_lems.
Require Import G4iSLT_exch.
Require Import G4iSLT_wkn.
Require Import G4iSLT_remove_list.
Require Import G4iSLT_dec.
Require Import G4iSLT_inv_AndR_AndL.
Require Import G4iSLT_inv_OrL.
Require Import G4iSLT_inv_AtomImpL.
Require Import G4iSLT_inv_AndImpL.
Require Import G4iSLT_inv_OrImpL.
Require Import G4iSLT_inv_ImpImpL_R.
Require Import G4iSLT_inv_BoxImpL_R.

Theorem ImpL_adm : forall n s (D0:derrec G4iSLT_rules (fun _ => False) s) A B Γ0 Γ1 C,
                                n = derrec_height D0 ->
                               (s = (Γ0 ++ Γ1, A)) ->
                               derrec G4iSLT_rules (fun _ => False) (Γ0 ++ B :: Γ1, C) ->
                               derrec G4iSLT_rules (fun _ => False) (Γ0 ++ Imp A B :: Γ1, C).
Proof.
assert (DersNilF: dersrec G4iSLT_rules (fun _ : Seq  => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : Seq)
  (D0:derrec G4iSLT_rules (fun _ => False) concl) A B Γ0 Γ1 C,
                                x = derrec_height D0 ->
                               (concl = (Γ0 ++ Γ1, A)) ->
                               derrec G4iSLT_rules (fun _ => False) (Γ0 ++ B :: Γ1, C) ->
                               derrec G4iSLT_rules (fun _ => False) (Γ0 ++ Imp A B :: Γ1, C))).
apply d. intros n IH. clear d.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros A B Γ0 Γ1 C hei eq D1. subst.
  inversion g ; subst.
  (* IdP *)
  * inversion H ; subst.
    assert (J1: derrec_height D1 = derrec_height D1). auto.
    assert (J2: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ # P :: Γ3, C)).
    assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). auto. rewrite H0.
    assert (B :: Γ2 ++ # P :: Γ3 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
    pose (G4iSLT_hpadm_list_exch_L _ _ _ J1 _ J2). destruct s.
    apply G4iSLT_adm_list_exch_L with (s:=(# P → B :: Γ2 ++ # P :: Γ3, C)).
    apply derI with (ps:=[(B :: Γ2 ++ # P :: Γ3, C)]) ; auto. apply AtomImpL2.
    assert (B :: Γ2 ++ # P :: Γ3 = [] ++ B :: Γ2 ++ # P :: Γ3). auto. rewrite H0.
    assert (# P → B :: Γ2 ++ # P :: Γ3 = [] ++ # P → B :: Γ2 ++ # P :: Γ3). auto. rewrite H1. apply AtomImpL2Rule_I.
    apply dlCons ; auto.
    assert (Γ0 ++ # P → B :: Γ1 = [] ++ [] ++ Γ0 ++ [# P → B] ++ Γ1). auto. rewrite H0.
    assert (# P → B :: Γ2 ++ # P :: Γ3 = [] ++ [# P → B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
  (* BotL *)
  * inversion H. subst. assert (InT (⊥) (Γ0 ++ A → B :: Γ1)). assert (InT (⊥) (Γ0 ++ Γ1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq.
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. auto. apply InT_split in H0. destruct H0. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ⊥ :: x0, C)). apply BotLRule_I. apply BotL in H0.
    pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
    (ps:=[]) (x ++ ⊥ :: x0, C) H0 DersNilF). auto.
   (* AndR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl in IH.
    assert (J1: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J2: derrec_height x0 = derrec_height x0). auto.
    assert (J3: (Γ0 ++ Γ1, B0) =(Γ0 ++ Γ1, B0)). auto.
    pose (IH _ J1 _ _ _ _ _ _ _ J2 J3 D1).
    assert (J4: derrec_height x < S (dersrec_height d)). lia.
    assert (J5: derrec_height x = derrec_height x). auto.
    assert (J6: (Γ0 ++ Γ1, A0) =(Γ0 ++ Γ1, A0)). auto.
    pose (IH _ J4 _ _ _ _ _ _ _ J5 J6 d0). apply derI with (ps:=[(Γ0 ++ A0 → B0 → B :: Γ1, C)]).
    apply AndImpL. apply AndImpLRule_I. apply dlCons ; auto.
  (* AndL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply G4iSLT_adm_list_exch_L with (s:=(A → B :: Γ2 ++ A0 ∧ B0 :: Γ3, C)).
    assert (J1: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ A0 ∧ B0 :: Γ3, C)).
    assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). auto. rewrite H0.
    assert (B :: Γ2 ++ A0 ∧ B0 :: Γ3 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
    pose (G4iSLT_adm_list_exch_L _ D1 _ J1).
    assert (J2: AndLRule [((B :: Γ2) ++ A0 :: B0 :: Γ3, C)] ((B :: Γ2) ++ A0 ∧ B0 :: Γ3, C)). apply AndLRule_I.
    repeat rewrite <- app_assoc in J2 ; simpl in J2.
    pose (AndL_inv _ _ d0 J2).
    assert (J3: derrec_height x < S (dersrec_height d)). lia.
    assert (J4: derrec_height x = derrec_height x). auto.
    assert (J5: (Γ2 ++ A0 :: B0 :: Γ3, A) = ([] ++ Γ2 ++ A0 :: B0 :: Γ3, A)). auto.
    pose (IH _ J3 _ _ _ _ _ _ _ J4 J5 d1). simpl in d2.
    apply derI with (ps:=[(A → B :: Γ2 ++ A0 :: B0 :: Γ3, C)]).
    assert (A → B :: Γ2 ++ A0 :: B0 :: Γ3 = (A → B :: Γ2) ++ A0 :: B0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (A → B :: Γ2 ++ A0 ∧ B0 :: Γ3 = (A → B :: Γ2) ++ A0 ∧ B0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply AndL. apply AndLRule_I. apply dlCons ; auto.
    assert (Γ0 ++ A → B :: Γ1 = [] ++ [] ++ Γ0 ++ [A → B] ++ Γ1). auto. rewrite H0.
    assert (A → B :: Γ2 ++ A0 ∧ B0 :: Γ3 = [] ++ [A → B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
  (* OrR1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    assert (J1: derrec_height x < S (dersrec_height d)). lia.
    assert (J2: derrec_height x = derrec_height x). auto.
    assert (J3: (Γ0 ++ Γ1, A0) =(Γ0 ++ Γ1, A0)). auto.
    pose (IH _ J1 _ _ _ _ _ _ _ J2 J3 D1).
    assert (J4: wkn_L (B0 → B) ((Γ0 ++ [A0 → B]) ++ Γ1, C) ((Γ0 ++ [A0 → B]) ++ B0 → B :: Γ1, C)).
    simpl. apply wkn_LI. repeat rewrite <- app_assoc in J4 ; simpl in J4.
    pose (@G4iSLT_adm_wkn_L _ d0 _ _ J4). apply derI with (ps:=[(Γ0 ++ A0 → B :: B0 → B :: Γ1, C)]).
    apply OrImpL.
    assert (Γ0 ++ A0 → B :: B0 → B :: Γ1 = Γ0 ++ A0 → B :: [] ++ B0 → B :: Γ1). auto. rewrite H0.
    assert (Γ0 ++ (A0 ∨ B0) → B :: Γ1 = Γ0 ++ (A0 ∨ B0) → B  :: [] ++ Γ1). auto. rewrite H1.
    apply OrImpLRule_I. apply dlCons ; auto.
  (* OrR2 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    assert (J1: derrec_height x < S (dersrec_height d)). lia.
    assert (J2: derrec_height x = derrec_height x). auto.
    assert (J3: (Γ0 ++ Γ1, B0) =(Γ0 ++ Γ1, B0)). auto.
    pose (IH _ J1 _ _ _ _ _ _ _ J2 J3 D1).
    assert (J4: wkn_L (A0 → B) (Γ0 ++ B0 → B :: Γ1, C) (Γ0 ++ A0 → B :: B0 → B :: Γ1, C)).
    simpl. apply wkn_LI.
    pose (@G4iSLT_adm_wkn_L _ d0 _ _ J4). apply derI with (ps:=[(Γ0 ++ A0 → B :: B0 → B :: Γ1, C)]).
    apply OrImpL.
    assert (Γ0 ++ A0 → B :: B0 → B :: Γ1 = Γ0 ++ A0 → B :: [] ++ B0 → B :: Γ1). auto. rewrite H0.
    assert (Γ0 ++ (A0 ∨ B0) → B :: Γ1 = Γ0 ++ (A0 ∨ B0) → B  :: [] ++ Γ1). auto. rewrite H1.
    apply OrImpLRule_I. apply dlCons ; auto.
  (* OrL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply G4iSLT_adm_list_exch_L with (s:=(A → B :: Γ2 ++ A0 ∨ B0 :: Γ3, C)).
    assert (J1: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ A0 ∨ B0 :: Γ3, C)).
    assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). auto. rewrite H0.
    assert (B :: Γ2 ++ A0 ∨ B0 :: Γ3 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
    pose (G4iSLT_adm_list_exch_L _ D1 _ J1).
    assert (J2: OrLRule [((B :: Γ2) ++ A0 :: Γ3, C);((B :: Γ2) ++ B0 :: Γ3, C)] ((B :: Γ2) ++ A0 ∨ B0 :: Γ3, C)). apply OrLRule_I.
    repeat rewrite <- app_assoc in J2 ; simpl in J2.
    pose (OrL_inv _ _ _ d0 J2). destruct p.
    assert (J3: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J4: derrec_height x0 = derrec_height x0). auto.
    assert (J5: (Γ2 ++ B0 :: Γ3, A) = ([] ++ Γ2 ++ B0 :: Γ3, A)). auto.
    pose (IH _ J3 _ _ _ _ _ _ _ J4 J5 d2). simpl in d3.
    assert (J6: derrec_height x < S (dersrec_height d)). lia.
    assert (J7: derrec_height x = derrec_height x). auto.
    assert (J8: (Γ2 ++ A0 :: Γ3, A) =([] ++ Γ2 ++ A0 :: Γ3, A)). auto.
    pose (IH _ J6 _ _ _ _ _ _ _ J7 J8 d1). simpl in d4. pose (dlCons d3 DersNilF). pose (dlCons d4 d5).
    apply derI with (ps:=[(A → B :: Γ2 ++ A0 :: Γ3, C); (A → B :: Γ2 ++ B0 :: Γ3, C)]).
    apply OrL.
    assert (A → B :: Γ2 ++ A0 :: Γ3 = (A → B :: Γ2) ++ A0 :: Γ3). repeat rewrite <- app_assoc ; auto. rewrite H0.
    assert (A → B :: Γ2 ++ B0 :: Γ3 = (A → B :: Γ2) ++ B0 :: Γ3). repeat rewrite <- app_assoc ; auto. rewrite H1.
    assert (A → B :: Γ2 ++ A0 ∨ B0 :: Γ3 = (A → B :: Γ2) ++ A0 ∨ B0 :: Γ3). auto. rewrite H3.
    apply OrLRule_I. apply dlCons ; auto.
    assert (Γ0 ++ A → B :: Γ1 = [] ++ [] ++ Γ0 ++ [A → B] ++ Γ1). auto. rewrite H0.
    assert (A → B :: Γ2 ++ A0 ∨ B0 :: Γ3 = [] ++ [A → B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
  (* ImpR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply derI with (ps:=[(Γ0 ++ B0 → B :: Γ1, A0 → B0);(Γ0 ++ B :: Γ1, C)]). apply ImpImpL.
    apply ImpImpLRule_I. apply dlCons. apply G4iSLT_adm_wkn_L with (s:=(Γ0 ++ Γ1, A0 → B0)) (A:=B0 → B) ; auto.
    2: apply wkn_LI. apply derI with (ps:=[(Γ2 ++ A0 :: Γ3, B0)]). apply ImpR. rewrite <- H2. apply ImpRRule_I.
    apply dlCons ; auto. apply dlCons ; auto.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply G4iSLT_adm_list_exch_L with (s:=(A → B :: Γ2 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)).
    assert (J1: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)).
    assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). auto. rewrite H0.
    assert (B :: Γ2 ++ # P :: Γ3 ++ # P → A0 :: Γ4 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
    pose (G4iSLT_adm_list_exch_L _ D1 _ J1).
    assert (J2: AtomImpL1Rule [((B :: Γ2) ++ # P :: Γ3 ++ A0 :: Γ4, C)] ((B :: Γ2) ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)). apply AtomImpL1Rule_I.
    repeat rewrite <- app_assoc in J2 ; simpl in J2.
    pose (AtomImpL_inv P A0 (B :: Γ2 ++ # P :: Γ3) Γ4 C). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
    simpl in d1. apply d1 in d0. clear d1.
    assert (J3: derrec_height x < S (dersrec_height d)). lia.
    assert (J4: derrec_height x = derrec_height x). auto.
    assert (J5: (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, A) = ([] ++ Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, A)). auto.
    pose (IH _ J3 _ _ _ _ _ _ _ J4 J5 d0). simpl in d1.
    apply derI with (ps:=[(A → B :: Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)]).
    assert (A → B ::Γ2 ++ # P :: Γ3 ++ # P → A0 :: Γ4 = (A → B :: Γ2) ++ # P :: Γ3 ++ # P → A0 :: Γ4). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (A → B :: Γ2 ++ # P :: Γ3 ++ A0 :: Γ4 = (A → B :: Γ2) ++ # P :: Γ3 ++ A0 :: Γ4). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply AtomImpL1. apply AtomImpL1Rule_I. apply dlCons ; auto.
    assert (Γ0 ++ A → B :: Γ1 = [] ++ [] ++ Γ0 ++ [A → B] ++ Γ1). auto. rewrite H0.
    assert (A → B :: Γ2 ++ # P :: Γ3 ++ # P → A0 :: Γ4 = [] ++ [A → B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
  (* AtomImpL1 *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply G4iSLT_adm_list_exch_L with (s:=(A → B :: Γ2 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)).
    assert (J1: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)).
    assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). auto. rewrite H0.
    assert (B :: Γ2 ++ # P → A0 :: Γ3 ++ # P :: Γ4 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
    pose (G4iSLT_adm_list_exch_L _ D1 _ J1).
    assert (J2: AtomImpL2Rule [((B :: Γ2) ++ A0 :: Γ3 ++ # P :: Γ4, C)] ((B :: Γ2) ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
    repeat rewrite <- app_assoc in J2 ; simpl in J2.
    pose (AtomImpL_inv P A0 (B :: Γ2) (Γ3 ++ # P :: Γ4) C). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
    simpl in d1. apply d1 in d0. clear d1.
    assert (J3: derrec_height x < S (dersrec_height d)). lia.
    assert (J4: derrec_height x = derrec_height x). auto.
    assert (J5: (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, A) = ([] ++ Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, A)). auto.
    pose (IH _ J3 _ _ _ _ _ _ _ J4 J5 d0). simpl in d1.
    apply derI with (ps:=[(A → B :: Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C)]).
    assert (A → B ::Γ2 ++ # P → A0 :: Γ3 ++ # P :: Γ4 = (A → B :: Γ2) ++ # P → A0 :: Γ3 ++ # P :: Γ4). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (A → B :: Γ2 ++ A0 :: Γ3 ++ # P :: Γ4 = (A → B :: Γ2) ++ A0 :: Γ3 ++ # P :: Γ4). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply AtomImpL2. apply AtomImpL2Rule_I. apply dlCons ; auto.
    assert (Γ0 ++ A → B :: Γ1 = [] ++ [] ++ Γ0 ++ [A → B] ++ Γ1). auto. rewrite H0.
    assert (A → B :: Γ2 ++ # P → A0 :: Γ3 ++ # P :: Γ4 = [] ++ [A → B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
 (* AndImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply G4iSLT_adm_list_exch_L with (s:=(A → B :: Γ2 ++ (A0 ∧ B0) → C0 :: Γ3, C)).
    assert (J1: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ (A0 ∧ B0) → C0 :: Γ3, C)).
    assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). auto. rewrite H0.
    assert (B :: Γ2 ++ (A0 ∧ B0) → C0 :: Γ3 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
    pose (G4iSLT_adm_list_exch_L _ D1 _ J1).
    assert (J2: AndImpLRule [((B :: Γ2) ++ (A0 → B0 → C0) :: Γ3, C)] ((B :: Γ2) ++ (A0 ∧ B0) → C0 :: Γ3, C)). apply AndImpLRule_I.
    repeat rewrite <- app_assoc in J2 ; simpl in J2.
    pose (AndImpL_inv _ _ d0 J2).
    assert (J3: derrec_height x < S (dersrec_height d)). lia.
    assert (J4: derrec_height x = derrec_height x). auto.
    assert (J5: (Γ2 ++ A0 → B0 → C0 :: Γ3, A) = ([] ++ Γ2 ++ A0 → B0 → C0 :: Γ3, A)). auto.
    pose (IH _ J3 _ _ _ _ _ _ _ J4 J5 d1). simpl in d2.
    apply derI with (ps:=[(A → B :: Γ2 ++ A0 → B0 → C0 :: Γ3, C)]).
    assert (A → B ::Γ2 ++ (A0 ∧ B0) → C0 :: Γ3 = (A → B :: Γ2) ++ (A0 ∧ B0) → C0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (A → B :: Γ2 ++ A0 → B0 → C0 :: Γ3= (A → B :: Γ2) ++ A0 → B0 → C0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply AndImpL. apply AndImpLRule_I. apply dlCons ; auto.
    assert (Γ0 ++ A → B :: Γ1 = [] ++ [] ++ Γ0 ++ [A → B] ++ Γ1). auto. rewrite H0.
    assert (A → B :: Γ2 ++ (A0 ∧ B0) → C0 :: Γ3 = [] ++ [A → B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
  (* OrImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply G4iSLT_adm_list_exch_L with (s:=(A → B :: Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C)).
    assert (J1: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C)).
    assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). auto. rewrite H0.
    assert (B :: Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
    pose (G4iSLT_adm_list_exch_L _ D1 _ J1).
    assert (J2: OrImpLRule [((B :: Γ2) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)] ((B :: Γ2) ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
    repeat rewrite <- app_assoc in J2 ; simpl in J2.
    pose (OrImpL_inv _ _ d0 J2).
    assert (J3: derrec_height x < S (dersrec_height d)). lia.
    assert (J4: derrec_height x = derrec_height x). auto.
    assert (J5: (Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, A) = ([] ++ Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, A)). auto.
    pose (IH _ J3 _ _ _ _ _ _ _ J4 J5 d1). simpl in d2.
    apply derI with (ps:=[(A → B :: Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4, C)]).
    assert (A → B :: Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4 = (A → B :: Γ2) ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (A → B :: Γ2 ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4 = (A → B :: Γ2) ++ A0 → C0 :: Γ3 ++ B0 → C0 :: Γ4). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply OrImpL. apply OrImpLRule_I. apply dlCons ; auto.
    assert (Γ0 ++ A → B :: Γ1 = [] ++ [] ++ Γ0 ++ [A → B] ++ Γ1). auto. rewrite H0.
    assert (A → B :: Γ2 ++ (A0 ∨ B0) → C0 :: Γ3 ++ Γ4 = [] ++ [A → B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
  (* ImpImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply G4iSLT_adm_list_exch_L with (s:=(A → B :: Γ2 ++ (A0 → B0) → C0 :: Γ3, C)).
    assert (J1: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ (A0 → B0) → C0 :: Γ3, C)).
    assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). auto. rewrite H0.
    assert (B ::Γ2 ++ (A0 → B0) → C0 :: Γ3 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
    pose (G4iSLT_adm_list_exch_L _ D1 _ J1).
    assert (J2: ImpImpLRule [((B :: Γ2) ++ B0 → C0 :: Γ3, A0 → B0);((B :: Γ2) ++ C0 :: Γ3, C)] ((B :: Γ2) ++ (A0 → B0) → C0 :: Γ3, C)). apply ImpImpLRule_I.
    repeat rewrite <- app_assoc in J2 ; simpl in J2.
    pose (ImpImpL_inv_R _ _ _ d0 J2).
    assert (J3: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J4: derrec_height x0 = derrec_height x0). auto.
    assert (J5: (Γ2 ++ C0 :: Γ3, A) = ([] ++ Γ2 ++ C0 :: Γ3, A)). auto.
    pose (IH _ J3 _ _ _ _ _ _ _ J4 J5 d1). simpl in d2.
    apply derI with (ps:=[(A → B :: Γ2 ++ B0 → C0 :: Γ3, A0 → B0);(A → B :: Γ2 ++ C0 :: Γ3, C)]).
    assert (A → B :: Γ2 ++ B0 → C0 :: Γ3 = (A → B :: Γ2) ++ B0 → C0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert (A → B :: Γ2 ++ C0 :: Γ3 = (A → B :: Γ2) ++ C0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H1.
    assert (A → B :: Γ2 ++ (A0 → B0) → C0 :: Γ3 = (A → B :: Γ2) ++ (A0 → B0) → C0 :: Γ3). repeat rewrite <- app_assoc. auto. rewrite H3.
    apply ImpImpL. apply ImpImpLRule_I. apply dlCons ; auto.
    apply G4iSLT_adm_wkn_L with (s:=(Γ2 ++ B0 → C0 :: Γ3, A0 → B0)) (A:=A → B) ; auto.
    assert ((Γ2 ++ B0 → C0 :: Γ3, A0 → B0) = ([] ++ Γ2 ++ B0 → C0 :: Γ3, A0 → B0)). repeat rewrite <- app_assoc. auto. rewrite H0.
    assert ((A → B :: Γ2 ++ B0 → C0 :: Γ3, A0 → B0) = ([] ++ A → B :: Γ2 ++ B0 → C0 :: Γ3, A0 → B0)). repeat rewrite <- app_assoc. auto. rewrite H1.
    apply wkn_LI. apply dlCons ; auto.
    assert (Γ0 ++ A → B :: Γ1 = [] ++ [] ++ Γ0 ++ [A → B] ++ Γ1). auto. rewrite H0.
    assert (A → B :: Γ2 ++ (A0 → B0) → C0 :: Γ3 = [] ++ [A → B] ++ Γ0 ++ [] ++ Γ1). rewrite H2 ; auto. rewrite H1. apply list_exch_LI.
  (* BoxImpL *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply G4iSLT_adm_list_exch_L with (s:=(A → B :: Γ2 ++ Box A0 → B0 :: Γ3, C)).
    assert (J1: list_exch_L (Γ0 ++ B :: Γ1, C) (B :: Γ2 ++ Box A0 → B0 :: Γ3, C)).
    pose (list_exch_LI [] [] Γ0 [B] Γ1 C). simpl in l ; rewrite <- H2 in l ; auto.
    pose (G4iSLT_adm_list_exch_L _ D1 _ J1).
    assert (J2: BoxImpLRule [(unBox_formula B :: unBoxed_list Γ2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0);(B :: Γ2 ++ B0 :: Γ3, C)] (B :: Γ2 ++ Box A0 → B0 :: Γ3, C)).
    pose (@BoxImpLRule_I A0 B0 C (B :: Γ2) Γ3).
    repeat rewrite <- app_assoc in b ;  repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
    repeat rewrite <- app_assoc ; simpl ; apply b. pose (BoxImpL_inv_R _ _ _ d0 J2).
    assert (J3: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J4: derrec_height x0 = derrec_height x0). auto.
    assert (J5: (Γ2 ++ B0 :: Γ3, A) = ([] ++ Γ2 ++ B0 :: Γ3, A)). auto.
    pose (IH _ J3 _ _ _ _ _ _ _ J4 J5 d1). simpl in d2.
    apply derI with (ps:=[(A → B :: unBoxed_list Γ2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0], A0);(A → B :: Γ2 ++ B0 :: Γ3, C)]).
    apply BoxImpL. pose (@BoxImpLRule_I A0 B0 C (A → B :: Γ2) Γ3).
    repeat rewrite <- app_assoc in b ;  repeat rewrite <- app_assoc in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ;
    repeat rewrite <- app_assoc ; simpl ; apply b. apply dlCons ; auto.
    pose (wkn_LI (A → B) [] (unBoxed_list Γ2 ++ B0 :: unBoxed_list Γ3 ++ [Box A0]) A0). simpl in w. pose (G4iSLT_adm_wkn_L x w). auto. apply dlCons ; auto.
    pose (list_exch_LI [] [A → B] Γ0 [] Γ1 C). rewrite H2. simpl in l ; apply l.
  (* GLR *)
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). repeat destruct s. simpl in IH.
    apply derI with (ps:=[(unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0);(Γ0 ++ B :: Γ1, C)]).
    apply BoxImpL. pose (@BoxImpLRule_I A0 B C Γ0 Γ1). apply b.
    apply dlCons ; auto. 2: apply dlCons ; auto. assert (wkn_L B ((unBoxed_list Γ0 ++ unBoxed_list Γ1) ++ [Box A0], A0) (unBoxed_list Γ0 ++ B :: unBoxed_list Γ1 ++ [Box A0], A0)).
    pose (wkn_LI B (unBoxed_list Γ0) (unBoxed_list Γ1 ++ [Box A0]) A0). simpl in w. rewrite <- app_assoc ; auto.
    clear e. rewrite unBox_app_distrib in x. pose (G4iSLT_adm_wkn_L x H0). auto.
Qed.


