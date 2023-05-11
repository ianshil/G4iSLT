Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import G4iSLT_calc.
Require Import G4iSLT_list_lems.
Require Import G4iSLT_remove_list.
Require Import G4iSLT_dec.
Require Import G4iSLT_termination_measure.
Require Import G4iSLT_termination_measure_All.
Require Import G4iSLT_exch.
Require Import G4iSLT_wkn.
Require Import G4iSLT_Id.
Require Import G4iSLT_inv_ImpL_R.
Require Import G4iSLT_inv_AndImpL.
Require Import G4iSLT_inv_OrImpL.
Require Import G4iSLT_inv_AndR_AndL.
Require Import G4iSLT_inv_AtomImpL.
Require Import G4iSLT_inv_ImpImpL_R.
Require Import G4iSLT_inv_ImpImpL_L.
Require Import G4iSLT_inv_ImpR.
Require Import G4iSLT_inv_OrL.
Require Import G4iSLT_adm_unBox_L.
Require Import G4iSLT_ctr.

Theorem G4iSLT_cut_adm_main : forall n A s Γ0 Γ1 C,
                      n = weight_form A ->
                      (s = (Γ0 ++ Γ1, C)) ->
                      (derrec G4iSLT_rules (fun _ => False) (Γ0 ++ Γ1, A)) ->
                      (derrec G4iSLT_rules (fun _ => False) (Γ0 ++ A :: Γ1, C)) ->
                      (derrec G4iSLT_rules (fun _ => False) s).
Proof.
(* The proof is by induction on, first, size_form of the cut formula and on, second, the mhd
   of the sequent-conclusion. *)
(* We set up the strong induction on n properly first. *)
pose (strong_inductionT (fun (x:nat) => forall A s Γ0 Γ1 C,
                      x = weight_form A ->
                      (s = (Γ0 ++ Γ1, C)) ->
                      ((derrec G4iSLT_rules (fun _ => False) (Γ0 ++ Γ1, A)) ->
                      (derrec G4iSLT_rules (fun _ => False) (Γ0 ++ A :: Γ1, C)) ->
                      (derrec G4iSLT_rules (fun _ => False) s)))).
apply d. clear d. intros n PIH.
pose (less_thanS_strong_inductionT (fun s => forall A (Γ0 Γ1 : list MPropF) (C : MPropF),
                  n = weight_form A ->
                  s = (Γ0 ++ Γ1, C) ->
                  derrec G4iSLT_rules (fun _ : Seq => False) (Γ0 ++ Γ1, A) ->
                  derrec G4iSLT_rules (fun _ : Seq => False) (Γ0 ++ A :: Γ1, C) -> derrec G4iSLT_rules (fun _ : Seq => False) s)).
intros A s. revert A. revert s. apply d. clear d. intros s SIH.

(* Now we do the actual proof-theoretical work. *)
assert (DersNilF: dersrec G4iSLT_rules (fun _ : Seq   => False) []).
apply dersrec_nil.
assert (DersNilT: dersrec G4iSLT_rules (fun _ : Seq => True) []).
apply dersrec_nil.

intros A Γ0 Γ1 C weight E D0 D1. subst.

inversion D0. inversion H.
inversion D1. inversion H1.

(* We focus on the left rule. *)
inversion H ; subst.

(* Left rule is IdP *)
- inversion H3. subst.
  pose (list_exch_LI [] [] Γ0  [# P] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  pose (ctr_LI (# P) [] Γ2 Γ3 C). simpl in c. pose (G4iSLT_adm_ctr_L d c).
  pose (list_exch_LI [] [# P] Γ2  [] Γ3 C). simpl in l0. pose (G4iSLT_adm_list_exch_L _ d0 _ l0). auto.

(* Left rule is BotL *)
- inversion H3. subst. assert (BotLRule [] (Γ2 ++ ⊥ :: Γ3, C)). apply BotLRule_I. apply BotL in H0.
  pose (derI _ H0 DersNilF). assumption.

(* Left rule is AndR *)
- inversion H3. subst.
  assert (J0: AndLRule [(Γ0 ++ A0 :: B :: Γ1, C)] (Γ0 ++ A0 ∧ B :: Γ1, C)). apply AndLRule_I.
  pose (AndL_inv (Γ0 ++ A0 ∧ B :: Γ1, C) (Γ0 ++ A0 :: B :: Γ1, C) D1 J0).
  inversion X. subst. inversion X2. subst. clear X4. clear X2.
  assert (J1: wkn_L B (Γ0 ++ Γ1, A0) (Γ0 ++B :: Γ1, A0)). apply wkn_LI.
  pose (G4iSLT_adm_wkn_L X1 J1).
  assert (J2: weight_form A0 < weight_form (A0 ∧ B)). simpl. lia.
  assert (J3: weight_form A0 = weight_form A0). auto.
  assert (J5: (Γ0 ++ B :: Γ1, C) = (Γ0 ++ B :: Γ1, C)). auto.
  pose (PIH _ J2 A0 (Γ0 ++ B :: Γ1, C) Γ0 (B :: Γ1) C J3 J5 d0 d).
  assert (J6: weight_form B < weight_form (A0 ∧ B)). simpl. lia.
  assert (J7: weight_form B = weight_form B). auto.
  assert (J9: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
  pose (PIH _ J6 B (Γ0 ++ Γ1, C) Γ0 Γ1 C J7 J9 X3 d1). assumption.

(* Left rule is AndL *)
- inversion H3. subst. inversion X. subst. clear X2. clear X0.
  pose (list_exch_LI [] [] Γ0  [A] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  assert (J0: AndLRule [((A :: Γ2) ++ A0 :: B :: Γ3, C)] ((A :: Γ2) ++ A0 ∧ B :: Γ3, C)). apply AndLRule_I.
  repeat rewrite <- app_assoc in J0. simpl in J0.
  pose (AndL_inv (A :: Γ2 ++ A0 ∧ B :: Γ3, C) (A :: Γ2 ++ A0 :: B :: Γ3, C) d J0).
  assert (J1: AndLRule  [(Γ2 ++ A0 :: B :: Γ3, C)] (Γ2 ++ A0 ∧ B :: Γ3, C)). apply AndLRule_I. apply AndL in J1.
  assert (J2: InT (Γ2 ++ A0 :: B :: Γ3, C) [(Γ2 ++ A0 :: B :: Γ3, C)]). apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J2). rewrite <- H4 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J5: (Γ2 ++ A0 :: B :: Γ3, C) = ([] ++ Γ2 ++ A0 :: B :: Γ3, C)). auto.
  pose (SIH _ l0 A _ _ _ J3 J5). simpl in d1.
  pose (d1 X1 d0). apply derI with (ps:=[(Γ2 ++ A0 :: B :: Γ3, C)]). apply AndL. apply AndLRule_I.
  apply dlCons ; auto.

(* Left rule is OrR1 *)
- inversion H3. subst.
  assert (J0: OrLRule [(Γ0 ++ A0 :: Γ1, C);(Γ0 ++ B :: Γ1, C)] (Γ0 ++ A0 ∨ B :: Γ1, C)). apply OrLRule_I.
  pose (OrL_inv (Γ0 ++ A0 ∨ B :: Γ1, C) (Γ0 ++ A0 :: Γ1, C) (Γ0 ++ B :: Γ1, C) D1 J0). destruct p.
  inversion X. subst. clear X2. clear X.
  assert (J2: weight_form A0 < weight_form (A0 ∨ B)). simpl. lia.
  assert (J3: weight_form A0 = weight_form A0). auto.
  assert (J5: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
  pose (PIH _ J2 A0 (Γ0 ++ Γ1, C) Γ0 Γ1 C J3 J5 X1 d). auto.

(* Left rule is OrR2 *)
- inversion H3. subst.
  assert (J0: OrLRule [(Γ0 ++ A0 :: Γ1, C);(Γ0 ++ B :: Γ1, C)] (Γ0 ++ A0 ∨ B :: Γ1, C)). apply OrLRule_I.
  pose (OrL_inv (Γ0 ++ A0 ∨ B :: Γ1, C) (Γ0 ++ A0 :: Γ1, C) (Γ0 ++ B :: Γ1, C) D1 J0). destruct p.
  inversion X. subst. clear X2. clear X.
  assert (J2: weight_form B < weight_form (A0 ∨ B)). simpl. lia.
  assert (J3: weight_form B = weight_form B). auto.
  assert (J5: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
  pose (PIH _ J2 B (Γ0 ++ Γ1, C) Γ0 Γ1 C J3 J5 X1 d0). auto.

(* Left rule is OrL *)
- inversion H3. subst. inversion X. subst. inversion X2. subst. clear X4. clear X2. clear X. clear X0.
  pose (list_exch_LI [] [] Γ0  [A] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  assert (J0: OrLRule [((A :: Γ2) ++ A0 :: Γ3, C);((A :: Γ2) ++ B :: Γ3, C)] ((A :: Γ2) ++ A0 ∨ B :: Γ3, C)). apply OrLRule_I.
  repeat rewrite <- app_assoc in J0. simpl in J0.
  pose (OrL_inv (A :: Γ2 ++ A0 ∨ B :: Γ3, C) (A :: Γ2 ++ A0 :: Γ3, C) (A :: Γ2 ++  B :: Γ3, C) d J0). destruct p.
  assert (J1: OrLRule  [(Γ2 ++ A0 :: Γ3, C);(Γ2 ++ B :: Γ3, C)] (Γ2 ++ A0 ∨ B :: Γ3, C)). apply OrLRule_I. apply OrL in J1.
  assert (J2: InT (Γ2 ++ A0 :: Γ3, C) [(Γ2 ++ A0 :: Γ3, C); (Γ2 ++ B :: Γ3, C)]). apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J2). rewrite <- H4 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J5: (Γ2 ++ A0 :: Γ3, C) = ([] ++ Γ2 ++ A0 :: Γ3, C)). auto.
  pose (SIH _ l0 A _ _ _ J3 J5). simpl in d2. pose (d2 X1 d0).
  assert (J6: InT (Γ2 ++ B :: Γ3, C) [(Γ2 ++ A0 :: Γ3, C); (Γ2 ++ B :: Γ3, C)]). apply InT_cons. apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J6).
  assert (J7: weight_form A = weight_form A). auto.
  assert (J9: (Γ2 ++ B :: Γ3, C) = ([] ++ Γ2 ++ B :: Γ3, C)). auto.
  pose (SIH _ l1 A _ _ _ J7 J9). simpl in d4. pose (d4 X3 d1).
  apply derI with (ps:=[(Γ2 ++ A0 :: Γ3, C); (Γ2 ++ B :: Γ3, C)]). apply OrL. apply OrLRule_I.
  apply dlCons ; auto. apply dlCons ; auto.


(* Left rule is ImpR *)
- inversion H3. subst. inversion X. subst. clear X2. clear X. inversion H1. simpl.
      (* Right rule is IdP *)
      { inversion H0. subst. assert (J0 : InT (# P) (Γ2 ++ Γ3)). rewrite H4. apply InT_or_app.
        assert (InT (# P) (Γ0 ++ A0 → B :: Γ1)). rewrite <- H8. apply InT_or_app ; right ; apply InT_eq.
        apply InT_app_or in H2 ; destruct H2 ; auto. inversion i ; subst; auto. inversion H5. apply InT_split in J0.
        destruct J0. destruct s ; subst. rewrite e. apply derI with (ps:=[]) ; auto. apply IdP. apply IdPRule_I. }
      (* Right rule is BotL *)
      { inversion H0. subst. assert (J0 : InT ⊥ (Γ2 ++ Γ3)). rewrite H4. apply InT_or_app.
        assert (InT ⊥ (Γ0 ++ A0 → B :: Γ1)). rewrite <- H8. apply InT_or_app ; right ; apply InT_eq.
        apply InT_app_or in H2 ; destruct H2 ; auto. inversion i ; subst; auto. inversion H5. apply InT_split in J0.
        destruct J0. destruct s ; subst. rewrite e. apply derI with (ps:=[]) ; auto. apply BotL. apply BotLRule_I. }
    (* Right rule is AndR *)
    { inversion H0. subst. inversion X0. subst. inversion X2. subst. rewrite H4. clear X4. clear X2.
      assert (AndRRule [(Γ0 ++ Γ1, A);(Γ0 ++ Γ1, B0)] (Γ0 ++ Γ1, A ∧ B0)). apply AndRRule_I. apply AndR in H2.
      assert (J21: InT (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B0)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J21).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, A) = (Γ0 ++ Γ1, A)). reflexivity. pose (SIH _ l (A0 → B) _ _ _ J5 J7).
      assert (J31: InT (Γ0 ++ Γ1, B0) [(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B0)]). apply InT_cons. apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J31).
      assert (J10 : (Γ0 ++ Γ1, B0) = (Γ0 ++ Γ1, B0)). reflexivity. pose (SIH _ l0 (A0 → B) _ _ _ J5 J10).
      apply derI with (ps:=[(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B0)]). apply AndR. apply AndRRule_I. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is AndL *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H8. destruct H8 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst. rewrite H4.
        assert (AndLRule [((Γ0 ++ x0) ++ A :: B0 :: Γ5, C)] ((Γ0 ++ x0) ++ A ∧ B0 :: Γ5, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc in H2. apply AndL in H2.
        assert (J21: InT (Γ0 ++ x0 ++ A :: B0 :: Γ5, C) [(Γ0 ++ x0 ++ A :: B0 :: Γ5, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: B0 :: Γ5, C) = (Γ0 ++ x0 ++ A :: B0 :: Γ5, C)). reflexivity.
        assert (J01: AndLRule [((Γ0 ++ x0) ++ A :: B0 :: Γ5, A0 → B)] ((Γ0 ++ x0) ++ A ∧ B0 :: Γ5, A0 → B)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in X.
        pose (AndL_inv(Γ0 ++ x0 ++ A ∧ B0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ A :: B0 :: Γ5, A0 → B) D0 J01).
        pose (SIH _ l (A0 → B) _ _ _ J5 J7). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: B0 :: Γ5, C)]).
        apply AndL. pose (AndLRule_I A B0 C (Γ0 ++ x0) Γ5). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc in f. rewrite H4.
        assert (AndLRule [(Γ4 ++ A :: B0 :: x ++ Γ1, C)] (Γ4 ++ A ∧ B0 :: x ++ Γ1, C)). apply AndLRule_I. apply AndL in H2.
        assert (J21: InT (Γ4 ++ A :: B0 :: x ++ Γ1, C) [(Γ4 ++ A :: B0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ4 ++ A :: B0 :: x ++ Γ1, C) = ((Γ4 ++ A :: B0 :: x) ++ Γ1, C)). rewrite <- app_assoc ; reflexivity.
        repeat rewrite <- app_assoc in X. simpl in X. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: AndLRule [(Γ4 ++ A :: B0 :: x ++ Γ1, A0 → B)] (Γ4 ++ A ∧ B0 :: x ++ Γ1, A0 → B)). apply AndLRule_I.
        pose (AndL_inv (Γ4 ++ A ∧ B0 :: x ++ Γ1, A0 → B) (Γ4 ++ A :: B0 :: x ++ Γ1, A0 → B) D0 J01).
        repeat rewrite <- app_assoc in SIH. pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d0.
        pose (d0 d X). apply derI with (ps:=[(Γ4 ++ A :: B0 :: x ++ Γ1, C)]).
        apply AndL. repeat rewrite <- app_assoc. apply AndLRule_I. apply dlCons ; auto. }
    (* Right rule is OrR1 *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0.
      assert (OrR1Rule [(Γ0 ++ Γ1, A)] (Γ0 ++ Γ1, A ∨ B0)). apply OrR1Rule_I. apply OrR1 in H2.
      assert (J21: InT (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J21).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, A) = (Γ0 ++ Γ1, A)). reflexivity.
      pose (SIH _ l (A0 → B) _ _ _ J5 J7). apply derI with (ps:=[(Γ0 ++ Γ1, A)]).
      apply OrR1. rewrite H4. apply OrR1Rule_I. apply dlCons ; auto. }
    (* Right rule is OrR2 *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0.
      assert (OrR2Rule [(Γ0 ++ Γ1, B0)] (Γ0 ++ Γ1, A ∨ B0)). apply OrR2Rule_I. apply OrR2 in H2.
      assert (J21: InT (Γ0 ++ Γ1, B0) [(Γ0 ++ Γ1, B0)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J21).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, B0) = (Γ0 ++ Γ1, B0)). reflexivity. rewrite H4.
      pose (SIH _ l (A0 → B) _ _ _ J5 J7). apply derI with (ps:=[(Γ0 ++ Γ1, B0)]).
      apply OrR2. apply OrR2Rule_I. apply dlCons ; auto. }
    (* Right rule is OrL *)
    { inversion H0. subst. inversion X0. subst. inversion X2. subst. clear X4. clear X2. clear X0.
      rewrite H4. apply list_split_form in H8. destruct H8 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (OrLRule [((Γ0 ++ x0) ++ A :: Γ5, C);((Γ0 ++ x0) ++ B0 :: Γ5, C)] ((Γ0 ++ x0) ++ A ∨ B0 :: Γ5, C)). apply OrLRule_I.
        repeat rewrite <- app_assoc in H2. apply OrL in H2.
        repeat rewrite <- app_assoc in X3. simpl in X3. repeat rewrite <- app_assoc in X. simpl in X.
        assert (J01: OrLRule [((Γ0 ++ x0) ++ A :: Γ5, A0 → B);((Γ0 ++ x0) ++ B0 :: Γ5, A0 → B)] ((Γ0 ++ x0) ++ A ∨ B0 :: Γ5, A0 → B)). apply OrLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (OrL_inv (Γ0 ++ x0 ++ A ∨ B0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ A :: Γ5, A0 → B) (Γ0 ++ x0 ++ B0 :: Γ5, A0 → B) D0 J01).
        destruct p.
        assert (J21: InT (Γ0 ++ x0 ++ A :: Γ5, C) [(Γ0 ++ x0 ++ A :: Γ5, C); (Γ0 ++ x0 ++ B0 :: Γ5, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: Γ5, C) = (Γ0 ++ x0 ++ A :: Γ5, C)). reflexivity.
        pose (SIH _ l (A0 → B) _ _ _ J5 J7 d X).
        assert (J22: InT (Γ0 ++ x0 ++ B0 :: Γ5, C) [(Γ0 ++ x0 ++ A :: Γ5, C); (Γ0 ++ x0 ++ B0 :: Γ5, C)]). apply InT_cons. apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J22).
        assert (J10 : (Γ0 ++ x0 ++ B0 :: Γ5, C) = (Γ0 ++ x0 ++ B0 :: Γ5, C)). reflexivity.
        pose (SIH _ l0 (A0 → B) _ _ _ J5 J10 d0 X3). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: Γ5, C); (Γ0 ++ x0 ++ B0 :: Γ5, C)]).
        apply OrL.  pose (OrLRule_I A B0 C (Γ0 ++ x0) Γ5). repeat rewrite <- app_assoc in o ; simpl in o ; auto. apply dlCons ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
        assert (OrLRule [(Γ4 ++ A :: x ++ Γ1, C);(Γ4 ++ B0 :: x ++ Γ1, C)] (Γ4 ++ A ∨ B0 :: x ++ Γ1, C)). apply OrLRule_I.
        apply OrL in H2. repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: OrLRule [(Γ4 ++ A :: x ++ Γ1, A0 → B);(Γ4 ++ B0 :: x ++ Γ1, A0 → B)] (Γ4 ++ A ∨ B0 :: x ++ Γ1, A0 → B)). apply OrLRule_I.
        pose (OrL_inv (Γ4 ++ A ∨ B0 :: x ++ Γ1, A0 → B) (Γ4 ++ A :: x ++ Γ1, A0 → B) (Γ4 ++ B0 :: x ++ Γ1, A0 → B) D0 J01). destruct p.
        assert (J21: InT (Γ4 ++ A :: x ++ Γ1, C) [(Γ4 ++ A :: x ++ Γ1, C); (Γ4 ++ B0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ4 ++ A :: x ++ Γ1, C) = ((Γ4 ++ A :: x) ++ Γ1, C)). rewrite <- app_assoc ; reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. pose (d1 d X).
        assert (J22: InT (Γ4 ++ B0 :: x ++ Γ1, C) [(Γ4 ++ A :: x ++ Γ1, C); (Γ4 ++ B0 :: x ++ Γ1, C)]). apply InT_cons. apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J22).
        assert (J10 : (Γ4 ++ B0 :: x ++ Γ1, C) = ((Γ4 ++ B0 :: x) ++ Γ1, C)). rewrite <- app_assoc ; reflexivity.
        pose (SIH _ l0 (A0 → B) _ _ _ J5 J10). repeat rewrite <- app_assoc in d3. pose (d3 d0 X3).
        apply derI with (ps:=[(Γ4 ++ A :: x ++ Γ1, C); (Γ4 ++ B0 :: x ++ Γ1, C)]).
        apply OrL. apply OrLRule_I. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is ImpR *)
    { inversion H0. subst. inversion X0. subst. clear X2. rewrite <- H8 in D1. rewrite H4.
      pose (list_exch_LI [] [] Γ4 [A] Γ5 B0). simpl in l. rewrite H8 in l. pose (G4iSLT_adm_list_exch_L _ X _ l).
      assert (ImpRRule [([] ++ A :: Γ0 ++ Γ1, B0)] ([] ++ Γ0 ++ Γ1, A → B0)). apply ImpRRule_I. simpl in H2. apply ImpR in H2.
      assert (J21: InT (A :: Γ0 ++ Γ1, B0) [(A :: Γ0 ++ Γ1, B0)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J21).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J7 : (A :: Γ0 ++ Γ1, B0) = ((A :: Γ0) ++ Γ1, B0)). reflexivity.
      pose (SIH _ l0 (A0 → B) _ _ _ J5 J7). simpl in d0.
      assert (wkn_L A ([] ++ Γ0 ++ Γ1, A0 → B) ([] ++ A :: Γ0 ++ Γ1, A0 → B)). apply wkn_LI. simpl in H4.
      pose (@G4iSLT_adm_wkn_L (Γ0 ++ Γ1, A0 → B) D0 (A :: Γ0 ++ Γ1, A0 → B) A H5).
      pose (d0 d1 d). pose (dlCons d2 DersNilF). pose (derI _ H2 d3). assumption. }
    (* Right rule is AtomImpL1 *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H8. destruct H8 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst. rewrite H4.
        assert (AtomImpL1Rule [((Γ0 ++ x0) ++ # P :: Γ5 ++ A :: Γ6, C)] ((Γ0 ++ x0) ++ # P :: Γ5 ++ # P → A :: Γ6, C)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc in H2. apply AtomImpL1 in H2.
        assert (J21: InT (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C) [(Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C) = (Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)). reflexivity.
        repeat rewrite <- app_assoc in X. simpl in X.
        assert (J01: AtomImpL1Rule [((Γ0 ++ x0) ++ # P :: Γ5 ++ A :: Γ6,A0 → B)] ((Γ0 ++ x0) ++ # P :: Γ5 ++ # P → A :: Γ6, A0 → B)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AtomImpL_inv P A (Γ0 ++ x0 ++ # P :: Γ5) Γ6 (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d. pose (d D0).
        pose (SIH _ l (A0 → B) _ _ _ J5 J7 d0 X). apply derI with (ps:=[(Γ0 ++ x0 ++ # P :: Γ5 ++ A :: Γ6, C)]).
        apply AtomImpL1. pose (AtomImpL1Rule_I P A C (Γ0 ++ x0) Γ5 Γ6). repeat rewrite <- app_assoc in a ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. rewrite H4.
        apply list_split_form in e0. destruct e0 ; subst. destruct s.
        + repeat destruct p. inversion e0. subst.
           pose (list_exch_LI [] [] Γ2 [# P] Γ3 B). simpl in l. rewrite H4 in l.
           pose (G4iSLT_adm_list_exch_L (Γ2 ++ # P :: Γ3, B) X1 (# P :: (Γ4 ++ # P :: x) ++ Γ1, B) l).
           repeat rewrite <- app_assoc in d. simpl in d.
           assert (J1: ctr_L (# P) ([] ++ # P :: Γ4 ++ # P :: x ++ Γ1, B) ([] ++ # P :: Γ4 ++ x ++ Γ1, B)). apply ctr_LI. simpl in J1.
           pose (G4iSLT_adm_ctr_L d J1).
           assert (J3: list_exch_L ([] ++ [# P] ++ Γ4 ++ [] ++ x ++ Γ1, B) ([] ++ [] ++ Γ4 ++ [# P] ++ x ++ Γ1, B)). apply list_exch_LI.
           simpl in J3. pose (G4iSLT_adm_list_exch_L _ d0 _ J3). repeat rewrite <- app_assoc. simpl.
           assert (J4: weight_form B < weight_form (# P → B)). simpl ; lia.
           assert (J5: weight_form B = weight_form B). auto.
           assert (J7: (Γ4 ++ # P :: x ++ Γ1, C) = (Γ4 ++ # P :: x ++ Γ1, C)). auto.
           pose (PIH (weight_form B) J4 B (Γ4 ++ # P :: x ++ Γ1, C) (Γ4 ++ # P :: x) Γ1 C J5).
           repeat rewrite <- app_assoc in d2. simpl in d2. pose (d2 J7 d1 X). auto.
        +  repeat destruct s. repeat destruct p. subst.
            assert (AtomImpL1Rule [(Γ4 ++ # P :: (x ++ x1) ++ A :: Γ6, C)] (Γ4 ++ # P :: (x ++ x1) ++ # P → A :: Γ6, C)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in H2. apply AtomImpL1 in H2.
            assert (J21: InT (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C) [(Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)]). apply InT_eq.
            pose (G4iSLT_less_thanS _ _ H2 _ J21).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J7 : (Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C) = ((Γ4 ++ # P :: x) ++ x1 ++ A :: Γ6, C)). repeat rewrite <- app_assoc ; simpl ; reflexivity.
            repeat rewrite <- app_assoc in X. simpl in X.
            assert (J01: AtomImpL1Rule [(Γ4 ++ # P :: (x ++ x1) ++ A :: Γ6, A0 → B)] (Γ4 ++ # P :: (x ++ x1) ++ # P → A :: Γ6, A0 → B)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A (Γ4 ++ # P :: x ++ x1) Γ6 (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH.
            pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. pose (d1 d0 X).
            apply derI with (ps:=[(Γ4 ++ # P :: x ++ x1 ++ A :: Γ6, C)]). apply AtomImpL1. repeat rewrite <- app_assoc. simpl.
            pose (AtomImpL1Rule_I P A C Γ4 (x ++ x1) Γ6) ; repeat rewrite <- app_assoc in a ; auto. apply dlCons ; auto.
        +  repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
            assert (AtomImpL1Rule [(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)] (Γ4 ++ # P :: Γ5 ++ # P → A :: x0 ++ Γ1, C)). apply AtomImpL1Rule_I.
            apply AtomImpL1 in H2.
            assert (J21: InT (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C) [(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)]). apply InT_eq.
            pose (G4iSLT_less_thanS _ _ H2 _ J21).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J7 : (Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C) = ((Γ4 ++ # P :: Γ5 ++ A :: x0) ++ Γ1, C)). repeat rewrite <- app_assoc ; simpl ;  repeat rewrite <- app_assoc ; simpl ; reflexivity.
            assert (J01: AtomImpL1Rule [(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, A0 → B)] (Γ4 ++ # P :: Γ5 ++ # P → A :: x0 ++ Γ1, A0 → B)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in D0. simpl in D0. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A (Γ4 ++ # P :: Γ5) (x0 ++ Γ1) (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH. simpl in SIH. repeat rewrite <- app_assoc in SIH.
            pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
            simpl in d1. pose (d1 d0 X).
            apply derI with (ps:=[(Γ4 ++ # P :: Γ5 ++ A :: x0 ++ Γ1, C)]). apply AtomImpL1. apply AtomImpL1Rule_I. apply dlCons ; auto. }
    (* Right rule is AtomImpL2 *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H8. destruct H8 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst. rewrite H4.
        pose (list_exch_LI [] [] Γ2 [# P] Γ3 B). simpl in l. rewrite H4 in l.
        pose (G4iSLT_adm_list_exch_L (Γ2 ++ # P :: Γ3, B) X1 (# P :: Γ0 ++ Γ5 ++ # P :: Γ6, B) l).
        repeat rewrite <- app_assoc in d. simpl in d.
        assert (J1: ctr_L (# P) ([] ++ # P :: (Γ0 ++ Γ5) ++ # P :: Γ6, B) ([] ++ # P :: (Γ0 ++ Γ5) ++ Γ6, B)). apply ctr_LI. simpl in J1.
        repeat rewrite <- app_assoc in J1. pose (G4iSLT_adm_ctr_L d J1).
        pose (list_exch_LI [] [# P] (Γ0 ++ Γ5) [] Γ6 B). simpl in l0. simpl in l0. repeat rewrite <- app_assoc in l0.
        pose (G4iSLT_adm_list_exch_L _ d0 _ l0).
        assert (J4: weight_form B < weight_form (# P → B)). simpl ; lia.
        assert (J5: weight_form B = weight_form B). auto.
        assert (J7:(Γ0 ++ Γ5 ++ # P :: Γ6, C) = (Γ0 ++ Γ5 ++ # P :: Γ6, C)). auto.
        pose (PIH (weight_form B) J4 B (Γ0 ++ Γ5 ++ # P :: Γ6, C) Γ0 (Γ5 ++ # P :: Γ6) C J5). repeat rewrite <- app_assoc in d2. simpl in d2. pose (d2 J7 d1 X). auto.
      - repeat destruct s. repeat destruct p. subst.
        assert (AtomImpL2Rule [((Γ0 ++ x0) ++ A :: Γ5 ++ # P :: Γ6, C)] ((Γ0 ++ x0) ++ # P → A :: Γ5 ++ # P :: Γ6, C)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc in H2. rewrite H4. apply AtomImpL2 in H2.
        assert (J21: InT (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C) [(Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C) = (Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)). reflexivity.
        repeat rewrite <- app_assoc in X. simpl in X.
        assert (J01: AtomImpL2Rule [((Γ0 ++ x0) ++ A :: Γ5 ++ # P :: Γ6,A0 → B)] ((Γ0 ++ x0) ++ # P → A :: Γ5 ++ # P :: Γ6, A0 → B)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AtomImpL_inv P A (Γ0 ++ x0) (Γ5 ++ # P :: Γ6) (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d. pose (d D0).
        pose (SIH _ l (A0 → B) _ _ _ J5 J7 d0 X). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: Γ5 ++ # P :: Γ6, C)]).
        apply AtomImpL2. pose( AtomImpL2Rule_I P A C (Γ0 ++ x0) Γ5 Γ6). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. apply list_split_form in e0. destruct e0 ; subst. destruct s.
        + repeat destruct p. inversion e0.
        +  repeat destruct s. repeat destruct p. subst. rewrite H4.
            assert (AtomImpL2Rule [(Γ4 ++ A :: (x ++ x1) ++ # P :: Γ6, C)] (Γ4 ++ # P → A :: (x ++ x1) ++ # P :: Γ6, C)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in H2. apply AtomImpL2 in H2.
            assert (J21: InT (Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C) [(Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)]). apply InT_eq.
            pose (G4iSLT_less_thanS _ _ H2 _ J21).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J7 : (Γ4 ++  A :: x ++ x1 ++ # P :: Γ6, C) = ((Γ4 ++ A :: x) ++ x1 ++ # P :: Γ6, C)). repeat rewrite <- app_assoc ; simpl ; reflexivity.
            repeat rewrite <- app_assoc in X. simpl in X.
            assert (J01: AtomImpL2Rule [(Γ4 ++ A :: (x ++ x1) ++ # P :: Γ6, A0 → B)] (Γ4 ++ # P → A :: (x ++ x1) ++ # P :: Γ6, A0 → B)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A Γ4 (x ++ x1 ++ # P :: Γ6) (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH.
            pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. pose (d1 d0 X).
            apply derI with (ps:=[(Γ4 ++ A :: x ++ x1 ++ # P :: Γ6, C)]). apply AtomImpL2. pose (AtomImpL2Rule_I P A C Γ4 (x ++ x1) Γ6).
            repeat rewrite <-app_assoc ; simpl ; repeat rewrite <-app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
        +  repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. rewrite H4.
            assert (AtomImpL2Rule [(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)] (Γ4 ++ # P → A :: Γ5 ++ # P :: x0 ++ Γ1, C)). apply AtomImpL2Rule_I.
            apply AtomImpL2 in H2.
            assert (J21: InT (Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C) [(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)]). apply InT_eq.
            pose (G4iSLT_less_thanS _ _ H2 _ J21).
            assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
            assert (J7 : (Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C) = ((Γ4 ++  A :: Γ5 ++ # P :: x0) ++ Γ1, C)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; reflexivity.
            assert (J01: AtomImpL2Rule [(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, A0 → B)] (Γ4 ++ # P → A :: Γ5 ++ # P :: x0 ++ Γ1, A0 → B)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in D0. simpl in D0. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A Γ4 (Γ5 ++  # P :: x0 ++ Γ1) (A0 → B)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH. simpl in SIH. repeat rewrite <- app_assoc in SIH.
            pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
            simpl in d1. pose (d1 d0 X).
            apply derI with (ps:=[(Γ4 ++ A :: Γ5 ++ # P :: x0 ++ Γ1, C)]). apply AtomImpL2. repeat rewrite <- app_assoc. simpl.
            repeat rewrite <- app_assoc. apply AtomImpL2Rule_I. apply dlCons ; auto. }
    (* Right rule is AndImpL *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H8. destruct H8 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst. rewrite H4.
        pose (list_exch_LI [] [] Γ2 [A ∧ B0] Γ3 B). simpl in l. pose (G4iSLT_adm_list_exch_L _ X1 _ l). rewrite H4 in d.
        assert (J1: AndLRule [([] ++ A :: B0 :: Γ0 ++ Γ1, B)] ([] ++ A ∧ B0 :: Γ0 ++ Γ1, B)). apply AndLRule_I. simpl in J1. pose (AndL_inv _ _ d J1).
        assert (derrec G4iSLT_rules (fun _ : list (MPropF) * MPropF => False) ([] ++ Γ0 ++ Γ1, A → B0 → B)).
        apply derI with (ps:=[([] ++ A :: Γ0 ++ Γ1, B0 → B)]). apply ImpR. apply ImpRRule_I. apply dlCons ; auto.
        simpl. apply derI with (ps:=[([A] ++ B0 :: Γ0 ++ Γ1, B)]). apply ImpR. assert (A :: Γ0 ++ Γ1 = [A] ++ Γ0 ++ Γ1). auto.
        rewrite H2. apply ImpRRule_I. simpl. apply dlCons ; auto. simpl in X0.
        assert (J2: weight_form (A → B0 → B) < weight_form ((A ∧ B0) → B)). simpl. lia.
        assert (J3: weight_form (A → B0 → B) = weight_form (A → B0 → B)). auto.
        assert (J5: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
        pose (PIH (weight_form (A → B0 → B)) J2 (A → B0 → B) (Γ0 ++ Γ1, C) Γ0 Γ1 C J3 J5 X0 X).  auto.
      - repeat destruct s. repeat destruct p. subst. rewrite H4.
        assert (AndImpLRule [((Γ0 ++ x0) ++ A → B0 → C0 :: Γ5, C)] ((Γ0 ++ x0) ++ (A ∧ B0) → C0 :: Γ5, C)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in H2. apply AndImpL in H2.
        assert (J21: InT  (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C) [(Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C) = (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)). reflexivity.
        repeat rewrite <- app_assoc in X. simpl in X.
        assert (J01: AndImpLRule [((Γ0 ++ x0) ++ A → B0 → C0 :: Γ5, A0 → B)] ((Γ0 ++ x0) ++ (A ∧ B0) → C0 :: Γ5, A0 → B)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AndImpL_inv (Γ0 ++ x0 ++ (A ∧ B0) → C0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, A0 → B) D0 J01).
        pose (SIH _ l (A0 → B) _ _ _ J5 J7 d X). apply derI with (ps:=[(Γ0 ++ x0 ++ A → B0 → C0 :: Γ5, C)]).
        apply AndImpL. pose (AndImpLRule_I A B0 C0 C (Γ0 ++ x0) Γ5). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. rewrite H4.
        assert (AndImpLRule [(Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)] (Γ4 ++ (A ∧ B0) → C0 :: x ++ Γ1, C)). apply AndImpLRule_I. apply AndImpL in H2.
        assert (J21: InT  (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C) [(Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ4 ++ A → B0 → C0 :: x ++ Γ1, C) = ((Γ4 ++ A → B0 → C0 :: x) ++ Γ1, C)). repeat rewrite <- app_assoc ; simpl ; reflexivity.
        repeat rewrite <- app_assoc in X. simpl in X. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: AndImpLRule [(Γ4 ++ A → B0 → C0 :: x ++ Γ1, A0 → B)] (Γ4 ++ (A ∧ B0) → C0 :: x ++ Γ1, A0 → B)). apply AndImpLRule_I.
        pose (AndImpL_inv (Γ4 ++ (A ∧ B0) → C0 :: x ++ Γ1, A0 → B) (Γ4 ++ A → B0 → C0 :: x ++ Γ1, A0 → B) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d0. pose (d0 d X). apply derI with (ps:=[(Γ4 ++ A → B0 → C0 :: x ++ Γ1, C)]).
        apply AndImpL. repeat rewrite <- app_assoc. apply AndImpLRule_I. apply dlCons ; auto. }
    (* Right rule is OrImpL *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H8. destruct H8 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst. rewrite H4.
        pose (list_exch_LI [] [] Γ2 [A ∨  B0] Γ3 B). simpl in l. rewrite H4 in l. pose (G4iSLT_adm_list_exch_L _ X1 _ l).
        assert (J1: OrLRule [([] ++ A :: Γ0 ++ Γ5 ++ Γ6, B);([] ++ B0 :: Γ0 ++ Γ5 ++ Γ6, B)] ([] ++ A ∨  B0 :: Γ0 ++ Γ5 ++ Γ6, B)). apply OrLRule_I. simpl in J1.
        pose (OrL_inv _ _ _ d J1). destruct p.
        assert (derrec G4iSLT_rules (fun _ : list (MPropF) * MPropF => False) ([] ++ Γ0 ++ Γ5 ++ Γ6, A → B)).
        apply derI with (ps:=[([] ++ A :: Γ0 ++ Γ5 ++ Γ6, B)]). apply ImpR. apply ImpRRule_I. apply dlCons ; auto. simpl in X0.
        assert (derrec G4iSLT_rules (fun _ : list (MPropF) * MPropF => False) ([] ++ Γ0 ++ Γ5 ++ Γ6, B0 → B)).
        apply derI with (ps:=[([] ++ B0 :: Γ0 ++ Γ5 ++ Γ6, B)]). apply ImpR. apply ImpRRule_I. apply dlCons ; auto. simpl in X2.
        assert (J10: wkn_L (B0 → B) ((Γ0 ++ Γ5) ++ Γ6, A → B) ((Γ0 ++ Γ5) ++ B0 → B :: Γ6, A → B)). apply wkn_LI. repeat rewrite <- app_assoc in J10.
        pose (G4iSLT_adm_wkn_L X0 J10).
        assert (J2: weight_form (A → B) < weight_form ((A ∨  B0) → B)). simpl. lia.
        assert (J3: weight_form (A → B) = weight_form (A → B)). auto.
        assert (J5: (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C) = (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C)). auto.
        pose (PIH (weight_form (A → B)) J2 (A → B) (Γ0 ++ Γ5 ++ B0 → B :: Γ6,C) Γ0 (Γ5 ++ B0 → B :: Γ6) C J3 J5 d2 X).
        assert (J6: weight_form (B0 → B) < weight_form ((A ∨  B0) → B)). simpl. lia.
        assert (J7: weight_form (B0 → B) = weight_form (B0 → B)). auto.
        assert (J9: (Γ0 ++ Γ5 ++ Γ6,C) = ((Γ0 ++ Γ5) ++ Γ6,C)). repeat rewrite <- app_assoc. auto.
        pose (PIH (weight_form (B0 → B)) J6 (B0 → B) (Γ0 ++ Γ5 ++ Γ6,C) (Γ0 ++ Γ5) Γ6 C J7 J9). repeat rewrite <- app_assoc in d4. pose (d4 X2 d3). auto.
      - repeat destruct s. repeat destruct p. subst. rewrite H4.
        assert (OrImpLRule [((Γ0 ++ x0) ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6 , C)] ((Γ0 ++ x0) ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6, C)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in H2. apply OrImpL in H2.
        assert (J21: InT  (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C) [(Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C) = (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)). reflexivity.
        repeat rewrite <- app_assoc in X. simpl in X.
        assert (J01: OrImpLRule [((Γ0 ++ x0) ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, A0 → B)] ((Γ0 ++ x0) ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6, A0 → B)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (OrImpL_inv (Γ0 ++ x0 ++ (A ∨ B0) → C0 :: Γ5 ++ Γ6, A0 → B) (Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, A0 → B) D0 J01).
        pose (SIH _ l (A0 → B) _ _ _ J5 J7 d X). apply derI with (ps:=[(Γ0 ++ x0 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C)]).
        apply OrImpL. pose (OrImpLRule_I A B0 C0 C (Γ0 ++ x0) Γ5 Γ6). repeat rewrite <- app_assoc in o ; simpl in o ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. rewrite H4. repeat rewrite <- app_assoc. simpl.
        assert (OrImpLRule [(Γ4 ++ A → C0 :: [] ++  B0 → C0 :: x ++ Γ1, C)] (Γ4 ++ (A ∨ B0) → C0 :: [] ++ x ++ Γ1, C)). apply OrImpLRule_I.
        simpl in H2. apply OrImpL in H2.
        assert (J21: InT  (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C) [(Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C) = (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)). reflexivity.
        repeat rewrite <- app_assoc in X. simpl in X. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: OrImpLRule [(Γ4 ++ A → C0 :: [] ++ B0 → C0 :: x ++ Γ1, A0 → B)] (Γ4 ++ (A ∨ B0) → C0 :: [] ++ x ++ Γ1, A0 → B)). apply OrImpLRule_I.
        simpl in J01.
        pose (OrImpL_inv (Γ4 ++ (A ∨ B0) → C0 :: x ++ Γ1, A0 → B) (Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, A0 → B) D0 J01).
        repeat rewrite <- app_assoc in SIH. pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d0. simpl in d0. pose (d0 d).
        pose (list_exch_LI (Γ4 ++ [A → C0]) Γ5 [B0 → C0] [] Γ6 C). simpl in l0. repeat rewrite <- app_assoc in l0. rewrite e0 in l0.
        pose (G4iSLT_adm_list_exch_L (Γ4 ++ A → C0 :: Γ5 ++ B0 → C0 :: Γ6, C) X (Γ4 ++ A → C0 :: B0 → C0 :: x ++ A0 → B :: Γ1, C) l0).
        pose (list_exch_LI Γ4 [] (A → C0 :: B0 → C0 :: x) [A0 → B] Γ1 C). simpl in l1. repeat rewrite <- app_assoc in l1. simpl in l1.
        pose (G4iSLT_adm_list_exch_L _ d2 _ l1). pose (d1 d3). apply derI with (ps:=[(Γ4 ++ A → C0 :: B0 → C0 :: x ++ Γ1, C)]).
        apply OrImpL. pose (OrImpLRule_I A B0 C0 C Γ4 [] (x ++ Γ1)). simpl in o ; auto. apply dlCons ; auto. }
    (* Right rule is ImpImpL *)
    { inversion H0. subst. inversion X0. subst. inversion X2. subst. clear X4. clear X2. clear X0.
      apply list_split_form in H8. destruct H8 ; subst. destruct s.
      - repeat destruct p. inversion e0. subst. rewrite H4.
        pose (list_exch_LI [] [] Γ2 [A →  B0] Γ3 B). simpl in l. rewrite H4 in l. pose (G4iSLT_adm_list_exch_L _ X1 _ l).
        pose (ImpL_inv_R A B0 [] (Γ0 ++ Γ1) B d).
        assert (derrec G4iSLT_rules (fun _ : list (MPropF) * MPropF => False) ([] ++ Γ0 ++ Γ1, B0 → B)).
        apply derI with (ps:=[([] ++ B0 :: Γ0 ++ Γ1, B)]). apply ImpR. apply ImpRRule_I. apply dlCons ; auto. simpl in X0. clear d0.
        assert (J2: weight_form (B0 → B) < weight_form ((A →  B0) → B)). simpl. lia.
        assert (J3: weight_form (B0 → B) = weight_form (B0 → B)). auto.
        assert (J5: (Γ0 ++ Γ1, A → B0) = (Γ0 ++ Γ1, A → B0)). auto.
        pose (PIH (weight_form (B0 → B)) J2 (B0 → B) (Γ0 ++ Γ1, A → B0) Γ0 Γ1 (A → B0) J3 J5 X0 X).
        assert (J6: weight_form (A → B0) < weight_form ((A →  B0) → B)). simpl. lia.
        assert (J7: weight_form (A → B0) = weight_form (A → B0)). auto.
        assert (J9: (Γ0 ++ Γ1,B) = (Γ0 ++ Γ1,B)). auto.
        pose (PIH (weight_form (A → B0)) J6 (A → B0) (Γ0 ++ Γ1,B) [] (Γ0 ++ Γ1) B J7 J9). simpl in d1. pose (d1 d0 d).
        assert (J10: weight_form B < weight_form ((A →  B0) → B)). simpl. lia.
        assert (J11: weight_form B = weight_form B). auto.
        assert (J13: (Γ0 ++ Γ1,C) = (Γ0 ++ Γ1,C)). auto.
        pose (PIH (weight_form B) J10 B (Γ0 ++ Γ1,C) Γ0 Γ1 C J11 J13). simpl in d3. pose (d3 d2 X3). auto.
      - repeat destruct s. repeat destruct p. subst. rewrite H4.
        assert (ImpImpLRule [((Γ0 ++ x0) ++ B0 → C0 :: Γ5, A → B0);((Γ0 ++ x0) ++ C0 :: Γ5, C)] ((Γ0 ++ x0) ++ (A → B0) → C0 :: Γ5, C)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in H2. apply ImpImpL in H2.
        repeat rewrite <- app_assoc in X3. simpl in X3. repeat rewrite <- app_assoc in X1. simpl in X1.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5, A0 → B) = ((Γ0 ++ x0) ++ (A → B0) → C0 :: Γ5, A0 → B)).
        repeat rewrite <- app_assoc ; simpl ; auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J60 J61).
        pose (ctr_LI (B0 → C0) ((Γ0 ++ x0) ++ [A]) [] Γ5 (A0 → B)). repeat rewrite <- app_assoc in c. simpl in c. repeat rewrite <- app_assoc in d.
        pose (@G4iSLT_adm_ctr_L _ d _ _ c).
        assert (J01: ImpImpLRule [((Γ0 ++ x0) ++ B0 → C0 :: Γ5, A → B0);((Γ0 ++ x0) ++ C0 :: Γ5, A0 → B)] ((Γ0 ++ x0) ++ (A → B0) → C0 :: Γ5, A0 → B)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (ImpImpL_inv_R (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5, A0 → B) (Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0) (Γ0 ++ x0 ++ C0 :: Γ5, A0 → B) D0 J01).
        assert (J22: InT (Γ0 ++ x0 ++ C0 :: Γ5, C) [(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0); (Γ0 ++ x0 ++ C0 :: Γ5, C)]). apply InT_cons. apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J22).
        assert (J8: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J10 : (Γ0 ++ x0 ++ C0 :: Γ5, C) = (Γ0 ++ x0 ++ C0 :: Γ5, C)). reflexivity.
        pose (SIH _ l (A0 → B) _ _ _ J8 J10 d1 X3).
        assert (J32: ImpRRule [((Γ0 ++ A0 → B :: x0) ++ A :: B0 → C0 :: Γ5, B0)] ((Γ0 ++ A0 → B :: x0) ++ B0 → C0 :: Γ5, A → B0)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J32. simpl in J32. repeat rewrite <- app_assoc in X.
        pose (ImpR_inv (Γ0 ++ A0 → B :: x0 ++ B0 → C0 :: Γ5, A → B0) (Γ0 ++ A0 → B :: x0 ++ A:: B0 → C0 :: Γ5, B0) X J32).
        assert (J21: InT (Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0) [(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0); (Γ0 ++ x0 ++ C0 :: Γ5, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J33: ImpRRule [((Γ0 ++ x0) ++ A :: B0 → C0 :: Γ5, B0)] ((Γ0 ++ x0) ++ B0 → C0 :: Γ5, A → B0)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J33. simpl in J33. apply ImpR in J33.
        assert (J34: InT (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0) [(Γ0 ++ x0 ++ A:: B0 → C0 :: Γ5, B0)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ J33 _ J34).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0)= (Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0)). reflexivity.
        assert ((Γ0 ++ x0 ++ A :: B0 → C0 :: Γ5, B0) << (Γ0 ++ x0 ++ (A → B0) → C0 :: Γ5, C)). apply less_thanS_trans with (m:=(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0)) ; auto.
        pose (SIH _ H5 (A0 → B) _ _ _ J5 J7 d0 d3).
        apply derI with (ps:=[(Γ0 ++ x0 ++ B0 → C0 :: Γ5, A → B0); (Γ0 ++ x0 ++ C0 :: Γ5, C)]).
        apply ImpImpL. pose (ImpImpLRule_I A B0 C0 C (Γ0 ++ x0) Γ5). repeat rewrite <- app_assoc in i ; simpl in i ; auto. apply dlCons ; auto.
        apply derI with (ps:=[(Γ0 ++ x0 ++ A:: B0 → C0 :: Γ5, B0)]). apply ImpR. pose (ImpRRule_I A B0 (Γ0 ++ x0) (B0 → C0 :: Γ5)). repeat rewrite <- app_assoc in i ; simpl in i ; auto.
        apply dlCons ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl. rewrite H4.
        assert (ImpImpLRule [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0);(Γ4 ++ C0 :: x ++ Γ1, C)] (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, C)). apply ImpImpLRule_I.
        apply ImpImpL in H2. repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, A0 → B) = (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, A0 → B)).
        repeat rewrite <- app_assoc ; simpl ; auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J60 J61).
        pose (ctr_LI (B0 → C0) (Γ4 ++ [A]) [] (x ++ Γ1) (A0 → B)). simpl in c. repeat rewrite <- app_assoc in c ; simpl in c. pose (@G4iSLT_adm_ctr_L _ d _ _ c).
        assert (J01: ImpImpLRule [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0);(Γ4 ++ C0 :: x ++ Γ1, A0 → B)] (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, A0 → B)). apply ImpImpLRule_I.
        pose (ImpImpL_inv_R (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, A0 → B) (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0) (Γ4 ++ C0 :: x ++ Γ1, A0 → B) D0 J01).
        assert (J22: InT  (Γ4 ++ C0 :: x ++ Γ1, C) [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0); (Γ4 ++ C0 :: x ++ Γ1, C)]). apply InT_cons. apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J22).
        assert (J8: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J10 : (Γ4 ++ C0 :: x ++ Γ1, C) = ((Γ4 ++ C0 :: x) ++ Γ1, C)). repeat rewrite <- app_assoc ; reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (A0 → B) _ _ _ J8 J10). repeat rewrite <- app_assoc in d2. simpl in d2. pose (d2 d1 X3).
        assert (J32: ImpRRule [(Γ4 ++ A :: B0 → C0 :: x ++ A0 → B :: Γ1, B0)] (Γ4 ++ B0 → C0 :: x ++ A0 → B :: Γ1, A → B0)). apply ImpRRule_I.
        pose (ImpR_inv (Γ4 ++ B0 → C0 :: x ++ A0 → B :: Γ1, A → B0) (Γ4 ++ A :: B0 → C0 :: x ++ A0 → B :: Γ1, B0) X J32).
        assert (J21: InT (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0) [(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0); (Γ4 ++ C0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J33: ImpRRule [(Γ4 ++ A :: B0 → C0 :: x ++ Γ1,  B0)] (Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J33. simpl in J33. apply ImpR in J33.
        assert (J34: InT (Γ4 ++ A :: B0 → C0 :: x ++ Γ1,  B0) [(Γ4 ++ A :: B0 → C0 :: x ++ Γ1,  B0)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ J33 _ J34).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0) = ((Γ4 ++ A :: B0 → C0 :: x) ++ Γ1, B0)). repeat rewrite <- app_assoc ; simpl ; reflexivity.
        assert ((Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0) << (Γ4 ++ (A → B0) → C0 :: x ++ Γ1, C)). apply less_thanS_trans with (m:=(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0)) ; auto.
        pose (SIH _ H5 (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d5. pose (d5 d0 d4).
        apply derI with (ps:=[(Γ4 ++ B0 → C0 :: x ++ Γ1, A → B0); (Γ4 ++ C0 :: x ++ Γ1, C)]).
        apply ImpImpL. repeat rewrite <- app_assoc. apply ImpImpLRule_I. apply dlCons ; auto.
        apply derI with (ps:=[(Γ4 ++ A :: B0 → C0 :: x ++ Γ1, B0)]). apply ImpR. pose (ImpRRule_I A B0 Γ4 (B0 → C0 :: x ++ Γ1)). repeat rewrite <- app_assoc in i ; simpl in i ; auto.
        apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is BoxImpL *)
    { inversion H0 ; subst. inversion X0 ; subst. inversion X2 ; subst. clear X4. clear X2. clear X0. rewrite H4.
      apply list_split_form in H8. destruct H8 ; subst. destruct s.
      - repeat destruct p ; subst. inversion e0 ; subst.
        assert (J50: weight_form B < weight_form (Box A → B)). simpl. lia.
        assert (J51: weight_form B = weight_form B). auto.
        assert (J53: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). auto.
        pose (PIH _ J50 _ _ _ _ _ J51 J53). apply d ; auto.
        assert (J54: weight_form (Box A) < weight_form (Box A → B)). simpl. lia.
        assert (J55: weight_form (Box A) = weight_form (Box A)). auto.
        assert (J56: (Γ0 ++ Γ1, B) = (Γ0 ++ Γ1, B)). auto.
        pose (PIH _ J54 _ _ _ _ _ J55 J56). clear d. apply d0 ; auto ; clear d0.
        apply derI with (ps:=[(unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)]). apply SLR. pose (@SLRRule_I A (Γ0 ++ Γ1)).
        repeat rewrite unBox_app_distrib in s ; repeat rewrite <- app_assoc in s ; simpl in s ; apply s. apply dlCons ; auto.
        assert (J57: (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A) = (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)). auto.
        pose (PIH _ J50 _ _ _ _ _ J51 J57). apply d ; auto ; clear d.
        pose (list_exch_LI [] [] Γ2 [Box A] Γ3 B). simpl in l. rewrite H4 in l. pose (G4iSLT_adm_list_exch_L _ X1 _ l).
        pose (list_exch_LI [] [Box A] (Γ0 ++ Γ1) [] [] B). simpl in l0. repeat rewrite <- app_assoc in l0. rewrite <- app_nil_end in l0.
        pose (G4iSLT_adm_list_exch_L _ d _ l0). auto.
        pose (unBoxed_list_left_adm_gen (Γ0 ++ Γ1) [] [Box A] B).
        simpl in g ; repeat rewrite unBox_app_distrib in g ; repeat rewrite <- app_assoc in g. apply g ; auto.
        pose (list_exch_LI [] [] Γ2 [Box A] Γ3 B). simpl in l. rewrite H4 in l. pose (G4iSLT_adm_list_exch_L _ X1 _ l).
        pose (list_exch_LI [] [Box A] Γ0 [] Γ1 B). simpl in l0. pose (G4iSLT_adm_list_exch_L _ d _ l0). auto.
      - repeat destruct s ; repeat destruct p ; subst. repeat rewrite <- app_assoc in X3 ; simpl in X3.
        assert (J0: BoxImpLRule [(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B0 :: unBoxed_list Γ5 ++ [Box A], A);(Γ0 ++ x0 ++ B0 :: Γ5, C)] (Γ0 ++ x0 ++ Box A → B0 :: Γ5, C)).
        pose (@BoxImpLRule_I A B0 C (Γ0 ++ x0) Γ5). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        apply BoxImpL in J0.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ0 ++ x0 ++ Box A → B0 :: Γ5, A0 → B) = ((Γ0 ++ x0) ++ Box A → B0 :: Γ5, A0 → B)).
        repeat rewrite <- app_assoc ; simpl ; auto.
        assert (J70: weight_form (Box A → B0) = weight_form (Box A → B0)). auto.
        pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J70 J60 J61).
        assert (J21: InT ((Γ0 ++ x0) ++ B0 :: Γ5, C) [(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B0 :: unBoxed_list Γ5 ++ [Box A], A); (Γ0 ++ x0 ++ B0 :: Γ5, C)]). apply InT_cons.
        repeat rewrite <- app_assoc ; apply InT_eq. pose (G4iSLT_less_thanS _ _ J0 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : ((Γ0 ++ x0) ++ B0 :: Γ5, C) = (Γ0 ++ x0 ++ B0 :: Γ5, C)). rewrite <- app_assoc. reflexivity.
        pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d. pose (d0 d X3). repeat rewrite <- app_assoc in d1.
        apply derI with (ps:=[(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B0 :: unBoxed_list Γ5 ++ [Box A], A); (Γ0 ++ x0 ++ B0 :: Γ5, C)]) ; auto.
        apply dlCons ; auto. 2: apply dlCons ; auto.
        assert (J22: InT (unBoxed_list Γ0 ++ unBoxed_list x0 ++ B0 :: unBoxed_list Γ5 ++ [Box A], A) [(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B0 :: unBoxed_list Γ5 ++ [Box A], A); (Γ0 ++ x0 ++ B0 :: Γ5, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ J0 _ J22).
        assert (J9: (unBoxed_list Γ0 ++ unBoxed_list x0 ++ B0 :: unBoxed_list Γ5 ++ [Box A], A) = (unBoxed_list Γ0 ++ unBoxed_list x0 ++ B0 :: unBoxed_list Γ5 ++ [Box A], A)). auto.
        pose (SIH _ l0 (A0 → B) _ _ _ J5 J9). apply d2 ; auto. clear d2.
        apply derI with (ps:=[(A0 :: unBoxed_list Γ0 ++ unBoxed_list x0 ++ B0 :: unBoxed_list Γ5 ++ [Box A], B)]). apply ImpR. epose (ImpRRule_I _ _ []). simpl in i ; apply i.
        apply dlCons ; auto. pose (list_exch_LI [] [] Γ2 [A0] Γ3 B). simpl in l1. rewrite H4 in l1. pose (G4iSLT_adm_list_exch_L _ X1 _ l1).
        assert (J80: derrec_height d2 = derrec_height d2). auto.
        assert (J81: (A0 :: Γ0 ++ x0 ++ Box A → B0 :: Γ5, B) = ((A0 :: Γ0 ++ x0) ++ Box A → B0 :: Γ5, B)).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto.
        assert (J90: weight_form (Box A → B0) = weight_form (Box A → B0)). auto.
        pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J90 J80 J81). simpl in d3. repeat rewrite <- app_assoc in d3.
        pose (wkn_LI (Box A) (A0 :: Γ0 ++ x0 ++ B0 :: Γ5) [] B). rewrite <- app_nil_end in w.
        pose (G4iSLT_adm_wkn_L d3 w). simpl in d4 ; repeat rewrite <- app_assoc in d4.
        pose (unBoxed_list_left_adm_gen (Γ0 ++ x0) [A0] (B0 :: Γ5 ++ [Box A]) B).
        simpl in g ; repeat rewrite unBox_app_distrib in g ; repeat rewrite <- app_assoc in g. apply g in d4. clear g.
        pose (unBoxed_list_left_adm_gen Γ5 (A0 :: unBoxed_list Γ0 ++ unBoxed_list x0 ++ [B0]) [Box A] B).
        simpl in g ; repeat rewrite unBox_app_distrib in g ; repeat rewrite <- app_assoc in g. apply g in d4. clear g. auto.
        repeat rewrite unBox_app_distrib in X ; repeat rewrite <- app_assoc in X ; simpl in X ; auto.
      - repeat destruct s ; repeat destruct p ; subst. repeat rewrite <- app_assoc. simpl.
        assert (J0: BoxImpLRule [(unBoxed_list Γ4 ++ B0 :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A);(Γ4 ++ B0 :: x ++ Γ1, C)] (Γ4 ++ Box A → B0 :: x ++ Γ1, C)).
        pose (@BoxImpLRule_I A B0 C Γ4 (x ++ Γ1)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
        apply BoxImpL in J0.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: ((Γ4 ++ Box A → B0 :: x) ++ Γ1, A0 → B) = (Γ4 ++ Box A → B0 :: x ++ Γ1, A0 → B)).
        repeat rewrite <- app_assoc ; simpl ; auto.
        assert (J70: weight_form (Box A → B0) = weight_form (Box A → B0)). auto.
        pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J70 J60 J61).
        assert (J21: InT (Γ4 ++ B0 :: x ++ Γ1, C) [(unBoxed_list Γ4 ++ B0 :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A); (Γ4 ++ B0 :: x ++ Γ1, C)]). apply InT_cons.
        repeat rewrite <- app_assoc ; apply InT_eq. pose (G4iSLT_less_thanS _ _ J0 _ J21).
        assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
        assert (J7 : (Γ4 ++ B0 :: x ++ Γ1, C) = ((Γ4 ++ B0 :: x) ++ Γ1, C)). rewrite <- app_assoc. reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (A0 → B) _ _ _ J5 J7). repeat rewrite <- app_assoc in d0. pose (d0 d X3).
        apply derI with (ps:=[(unBoxed_list Γ4 ++ B0 :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A); (Γ4 ++ B0 :: x ++ Γ1, C)]) ; auto.
        apply dlCons ; auto. 2: apply dlCons ; auto. repeat rewrite unBox_app_distrib in X ; repeat rewrite <- app_assoc in X ; simpl in X.
        assert (J22: InT (unBoxed_list Γ4 ++ B0 :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A) [(unBoxed_list Γ4 ++ B0 :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A); (Γ4 ++ B0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ J0 _ J22).
        assert (J9: (unBoxed_list Γ4 ++ B0 :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A) = ((unBoxed_list Γ4 ++ B0 :: unBoxed_list x) ++ unBoxed_list Γ1 ++ [Box A], A)). repeat rewrite <- app_assoc ; auto.
        pose (SIH _ l0 (A0 → B) _ _ _ J5 J9). repeat rewrite <- app_assoc in d2 ; apply d2 ; clear d2 ; simpl ; auto. simpl.
        apply derI with (ps:=[(A0 :: unBoxed_list Γ4 ++ B0 :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], B)]). apply ImpR. epose (ImpRRule_I _ _ []). simpl in i ; apply i. apply dlCons ; auto.
        pose (list_exch_LI [] [] Γ2 [A0] Γ3 B). simpl in l1. rewrite H4 in l1. pose (G4iSLT_adm_list_exch_L _ X1 _ l1). repeat rewrite <- app_assoc in d2. simpl in d2.
        assert (J80: derrec_height d2 = derrec_height d2). auto.
        assert (J81: (A0 :: Γ4 ++ Box A → B0 :: x ++ Γ1, B) = ((A0 :: Γ4) ++ Box A → B0 :: x ++ Γ1, B)).
        repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; auto.
        assert (J90: weight_form (Box A → B0) = weight_form (Box A → B0)). auto.
        pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J90 J80 J81). simpl in d3.
        pose (wkn_LI (Box A) (A0 :: Γ4 ++ B0 :: x ++ Γ1) [] B). rewrite <- app_nil_end in w.
        pose (G4iSLT_adm_wkn_L d3 w). simpl in d4; repeat rewrite <- app_assoc in d4 ; simpl in d4 ; repeat rewrite <- app_assoc in d4 ; auto.
        pose (unBoxed_list_left_adm_gen Γ4 [A0] (B0 :: x ++ Γ1 ++ [Box A]) B).
        simpl in g ; repeat rewrite unBox_app_distrib in g ; repeat rewrite <- app_assoc in g. apply g in d4. clear g.
        pose (unBoxed_list_left_adm_gen (x ++ Γ1) (A0 :: unBoxed_list Γ4 ++ [B0]) [Box A] B).
        simpl in g ; repeat rewrite unBox_app_distrib in g ; repeat rewrite <- app_assoc in g. apply g in d4 ; auto. }
    (* Right rule is SLR *)
    { inversion H0. subst. rewrite H4. inversion X0. subst. clear X2. clear X0.
      assert (J0: SLRRule [(unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)] (Γ0 ++ Γ1, Box A)).
      pose (@SLRRule_I A (Γ0 ++ Γ1)). repeat rewrite unBox_app_distrib in s ; repeat rewrite <- app_assoc in s ; simpl in s ; apply s. apply SLR in J0.
      apply derI with (ps:=[(unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)]) ; auto. apply dlCons ; auto.
      assert (J22: InT (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A) [(unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ J0 _ J22).
      assert (J5: weight_form (A0 → B) = weight_form (A0 → B)). reflexivity.
      assert (J7 : (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A) = (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)). auto.
      pose (SIH _ l (A0 → B) _ _ _ J5 J7). apply d ; auto. 2: repeat rewrite unBox_app_distrib in X ; repeat rewrite <- app_assoc in X ; auto.
      pose (list_exch_LI [] [] Γ2 [A0] Γ3 B). simpl in l0. rewrite H4 in l0. pose (G4iSLT_adm_list_exch_L _ X1 _ l0).
      apply derI with (ps:=[(A0 :: unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], B)]). apply ImpR. epose (ImpRRule_I A0 B []). simpl in i ; apply i.
      pose (wkn_LI (Box A) (A0 :: unBoxed_list Γ0 ++ unBoxed_list Γ1) [] B). rewrite <- app_nil_end in w. apply dlCons.
      pose (unBoxed_list_left_adm_gen (Γ0 ++ Γ1) [A0] [] B). repeat rewrite <- app_nil_end in g. simpl in g.
      repeat rewrite unBox_app_distrib in g. pose (g d0).
      epose (G4iSLT_adm_wkn_L g0 w). simpl in d1 ; repeat rewrite <- app_assoc in d1 ; auto.
      apply DersNilF. }


(* Left rule is AtomImpL1 *)
- inversion H3. subst. inversion X. subst. clear X2. clear X.
  pose (list_exch_LI [] [] Γ0  [A] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  pose (AtomImpL_inv P A0 (A :: Γ2 ++ # P :: Γ3) Γ4 C). repeat rewrite <- app_assoc in d0. simpl in d0.
  repeat rewrite <- app_assoc in d0. simpl in d0. pose (d0 d).
  assert (J1: AtomImpL1Rule  [(Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)] (Γ2 ++ # P :: Γ3 ++ # P → A0 :: Γ4, C)).
  apply AtomImpL1Rule_I. apply AtomImpL1 in J1.
  assert (J2: InT (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C) [(Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)]). apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J2). rewrite <- H4 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J5: (Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C) = ([] ++ Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)). auto.
  pose (SIH _ l0 A _ _ _ J3 J5). simpl in d2. pose (d2 X1 d1).
  apply derI with (ps:=[(Γ2 ++ # P :: Γ3 ++ A0 :: Γ4, C)]). apply AtomImpL1. apply AtomImpL1Rule_I.
  apply dlCons ; auto.

(* Left rule is AtomImpL2 *)
- inversion H3. subst. inversion X. subst. clear X2. clear X.
  pose (list_exch_LI [] [] Γ0  [A] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  pose (AtomImpL_inv P A0 (A :: Γ2) (Γ3 ++ # P :: Γ4) C). repeat rewrite <- app_assoc in d0. simpl in d0. pose (d0 d).
  assert (J1: AtomImpL2Rule  [(Γ2 ++A0  :: Γ3 ++ # P :: Γ4, C)] (Γ2 ++ # P → A0 :: Γ3 ++ # P :: Γ4, C)).
  apply AtomImpL2Rule_I. apply AtomImpL2 in J1.
  assert (J2: InT (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C) [(Γ2 ++ A0:: Γ3 ++ # P  :: Γ4, C)]). apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J2). rewrite <- H4 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J5: (Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C) = ([] ++ Γ2 ++  A0:: Γ3 ++ # P :: Γ4, C)). auto.
  pose (SIH _ l0 A _ _ _ J3 J5). simpl in d2. pose (d2 X1 d1).
  apply derI with (ps:=[(Γ2 ++ A0 :: Γ3 ++ # P :: Γ4, C)]). apply AtomImpL2. apply AtomImpL2Rule_I.
  apply dlCons ; auto.

(* Left rule is AndImpL *)
- inversion H3. subst. inversion X. subst. clear X2. clear X.
  pose (list_exch_LI [] [] Γ0  [A] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  assert (J01: AndImpLRule [((A :: Γ2) ++ A0 → B → C0 :: Γ3, C)] ((A :: Γ2) ++ (A0 ∧ B) → C0 :: Γ3, C)). apply AndImpLRule_I.
  pose (AndImpL_inv ((A :: Γ2) ++ (A0 ∧ B) → C0 :: Γ3, C) ((A :: Γ2) ++ A0 → B → C0 :: Γ3, C) d J01).
  repeat rewrite <- app_assoc in d0. simpl in d0.
  assert (J1: AndImpLRule  [(Γ2 ++ A0 → B → C0 :: Γ3, C)] (Γ2 ++ (A0 ∧ B) → C0 :: Γ3, C)).
  apply AndImpLRule_I. apply AndImpL in J1.
  assert (J2: InT (Γ2 ++ A0 → B → C0 :: Γ3, C) [(Γ2 ++ A0 → B → C0 :: Γ3, C)]). apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J2). rewrite <- H4 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J5: (Γ2 ++ A0 → B → C0 :: Γ3, C) = ([] ++ Γ2 ++ A0 → B → C0 :: Γ3, C)). auto.
  pose (SIH _ l0 A _ _ _ J3 J5). simpl in d1. pose (d1 X1 d0).
  apply derI with (ps:=[(Γ2 ++ A0 → B → C0 :: Γ3, C)]). apply AndImpL. apply AndImpLRule_I.
  apply dlCons ; auto.

(* Left rule is OrImpL *)
- inversion H3. subst. inversion X. subst. clear X2. clear X.
  pose (list_exch_LI [] [] Γ0  [A] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  assert (J01: OrImpLRule [((A :: Γ2) ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)] ((A :: Γ2) ++ (A0 ∨ B) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
  pose (OrImpL_inv ((A :: Γ2) ++ (A0 ∨ B) → C0 :: Γ3 ++ Γ4, C) ((A :: Γ2) ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) d J01).
  repeat rewrite <- app_assoc in d0. simpl in d0.
  assert (J1: OrImpLRule  [(Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)] (Γ2 ++ (A0 ∨ B) → C0 :: Γ3 ++ Γ4, C)).
  apply OrImpLRule_I. apply OrImpL in J1.
  assert (J2: InT (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) [(Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)]). apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J2). rewrite <- H4 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J5: (Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C) = ([] ++ Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)). auto.
  pose (SIH _ l0 A _ _ _ J3 J5). simpl in d1. pose (d1 X1 d0).
  apply derI with (ps:=[(Γ2 ++ A0 → C0 :: Γ3 ++ B → C0 :: Γ4, C)]). apply OrImpL. apply OrImpLRule_I.
  apply dlCons ; auto.

(* Left rule is ImpImpL *)
- inversion H3. subst. inversion X. subst. inversion X2. subst. clear X2. clear X4. clear X.
  pose (list_exch_LI [] [] Γ0  [A] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  assert (J01: ImpImpLRule [((A :: Γ2) ++ B → C0 :: Γ3, A0 → B);((A :: Γ2) ++ C0 :: Γ3, C)] ((A :: Γ2) ++ (A0 → B) → C0 :: Γ3, C)). apply ImpImpLRule_I.
  pose (ImpImpL_inv_R ((A :: Γ2) ++ (A0 → B) → C0 :: Γ3, C) ((A :: Γ2) ++ B → C0 :: Γ3, A0 → B) ((A :: Γ2) ++ C0 :: Γ3, C) d J01).
  repeat rewrite <- app_assoc in d0. simpl in d0.
  assert (J1: ImpImpLRule  [(Γ2 ++ B → C0 :: Γ3, (A0 → B));(Γ2 ++ C0 :: Γ3, C)] (Γ2 ++ (A0 → B) → C0 :: Γ3, C)).
  apply ImpImpLRule_I. apply ImpImpL in J1.
  assert (J2: InT (Γ2 ++ C0 :: Γ3, C) [(Γ2 ++ B → C0 :: Γ3, A0 → B); (Γ2 ++ C0 :: Γ3, C)]). apply InT_cons. apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J2). rewrite <- H4 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J5: (Γ2 ++ C0 :: Γ3, C) = ([] ++ Γ2 ++ C0 :: Γ3, C)). auto.
  pose (SIH _ l0 A _ _ _ J3 J5). simpl in d1. pose (d1 X3 d0).
  apply derI with (ps:=[(Γ2 ++ B → C0 :: Γ3, A0 → B); (Γ2 ++ C0 :: Γ3, C)]). apply ImpImpL. apply ImpImpLRule_I.
  apply dlCons ; auto. apply dlCons ; auto.

(* Left rule is BoxImpL *)
- inversion H3 ; subst. inversion X. subst. inversion X2 ; subst. clear X4. clear X2.
  pose (list_exch_LI [] [] Γ0  [A] Γ1 C). simpl in l. rewrite <- H4 in l. pose (G4iSLT_adm_list_exch_L _ D1 _ l).
  assert (J01: BoxImpLRule [(unBox_formula A :: unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ [Box A0], A0);(A :: Γ2 ++ B :: Γ3, C)] (A :: Γ2 ++ Box A0 → B :: Γ3, C)).
  pose (@BoxImpLRule_I A0 B C (A :: Γ2) Γ3). simpl in b ; repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
  assert (J02: derrec_height d = derrec_height d). auto.
  pose (ImpL_inv_R (Box A0) B (A :: Γ2) Γ3 C d). simpl in d0.
  assert (J1: BoxImpLRule [(unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ [Box A0], A0); (Γ2 ++ B :: Γ3, C)] (Γ2 ++ Box A0 → B :: Γ3, C)).
  pose (@BoxImpLRule_I A0 B C Γ2 Γ3). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
  apply BoxImpL in J1.
  assert (J2: InT (Γ2 ++ B :: Γ3, C) [(unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ [Box A0], A0); (Γ2 ++ B :: Γ3, C)]). apply InT_cons. apply InT_eq.
  pose (G4iSLT_less_thanS _ _ J1 _ J2). rewrite <- H4 in SIH.
  assert (J3: weight_form A = weight_form A). auto.
  assert (J5: (Γ2 ++ B :: Γ3, C) = ([] ++ Γ2 ++ B :: Γ3, C)). auto.
  pose (SIH _ l0 A _ _ _ J3 J5). simpl in d1. pose (d1 X3 d0).
  apply derI with (ps:=[(unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ [Box A0], A0); (Γ2 ++ B :: Γ3, C)]). apply BoxImpL. apply BoxImpLRule_I ; auto.
  apply dlCons ; auto. apply dlCons ; auto.

(* Left rule is SLR *)
- inversion H3. subst. inversion H1.
    (* Right rule is IdP *)
    { inversion H0. subst. assert (J0 : InT (# P) (Γ0 ++ Γ1)). apply InT_or_app.
      assert (InT (# P) (Γ0 ++ Box A0 :: Γ1)). rewrite <- H7. apply InT_or_app ; right ; apply InT_eq.
      apply InT_app_or in H2 ; destruct H2 ; auto. inversion i ; subst; auto. inversion H4. apply InT_split in J0.
      destruct J0. destruct s ; subst. rewrite e. apply derI with (ps:=[]) ; auto. apply IdP. apply IdPRule_I. }
    (* Right rule is BotL *)
    { inversion H0. subst. assert (J0 : InT ⊥ (Γ0 ++ Γ1)). apply InT_or_app.
      assert (InT ⊥ (Γ0 ++ Box A0 :: Γ1)). rewrite <- H7. apply InT_or_app ; right ; apply InT_eq.
      apply InT_app_or in H2 ; destruct H2 ; auto. inversion i ; subst; auto. inversion H4. apply InT_split in J0.
      destruct J0. destruct s ; subst. rewrite e. apply derI with (ps:=[]) ; auto. apply BotL. apply BotLRule_I. }
    (* Right rule is AndR *)
    { inversion H0. subst. inversion X0. subst. inversion X2. subst. clear X2. clear X4.
      assert (AndRRule [(Γ0 ++ Γ1, A);(Γ0 ++ Γ1, B)] (Γ0 ++ Γ1, A ∧ B)). apply AndRRule_I. apply AndR in H2.
      assert (J21: InT (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, A) = (Γ0 ++ Γ1, A)). reflexivity.
      pose (SIH _ l (Box A0) _ _ _ J5 J7 D0 X1).
      assert (J31: InT  (Γ0 ++ Γ1, B) [(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B)]). apply InT_cons. apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J31).
      assert (J10 : (Γ0 ++ Γ1, B) = (Γ0 ++ Γ1, B)). reflexivity.
      pose (SIH _ l0 (Box A0) _ _ _ J5 J10 D0 X3). apply derI with (ps:=[(Γ0 ++ Γ1, A); (Γ0 ++ Γ1, B)]).
      apply AndR. apply AndRRule_I. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is AndL *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H7. destruct H7 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (AndLRule [((Γ0 ++ x0) ++ A :: B :: Γ3, C)] ((Γ0 ++ x0) ++ A ∧ B :: Γ3, C)). apply AndLRule_I.
        repeat rewrite <- app_assoc in H2. apply AndL in H2.
        assert (J21: InT  (Γ0 ++ x0 ++ A :: B :: Γ3, C) [(Γ0 ++ x0 ++ A :: B :: Γ3, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: B :: Γ3, C) = (Γ0 ++ x0 ++ A :: B :: Γ3, C)). reflexivity.
        repeat rewrite <- app_assoc in X1. simpl in X1.
        assert (J01: AndLRule [((Γ0 ++ x0) ++ A :: B :: Γ3, Box A0)] ((Γ0 ++ x0) ++ A ∧ B :: Γ3, Box A0)). apply AndLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AndL_inv(Γ0 ++ x0 ++ A ∧ B :: Γ3, Box A0) (Γ0 ++ x0 ++ A :: B :: Γ3, Box A0) D0 J01).
        pose (SIH _ l (Box A0) _ _ _ J5 J7 d X1). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: B :: Γ3, C)]).
        apply AndL. pose (AndLRule_I A B C (Γ0 ++ x0) Γ3). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
        assert (AndLRule [(Γ2 ++ A :: B :: x ++ Γ1, C)] (Γ2 ++ A ∧ B :: x ++ Γ1, C)). apply AndLRule_I. apply AndL in H2.
        assert (J21: InT  (Γ2 ++ A :: B :: x ++ Γ1, C) [(Γ2 ++ A :: B :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ2 ++ A :: B :: x ++ Γ1, C) = ((Γ2 ++ A :: B :: x) ++ Γ1, C)). repeat rewrite <- app_assoc ; simpl ; reflexivity.
        repeat rewrite <- app_assoc in X1. simpl in X1. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: AndLRule [(Γ2 ++ A :: B :: x ++ Γ1, Box A0)] (Γ2 ++ A ∧ B :: x ++ Γ1, Box A0)). apply AndLRule_I.
        pose (AndL_inv (Γ2 ++ A ∧ B :: x ++ Γ1, Box A0) (Γ2 ++ A :: B :: x ++ Γ1, Box A0) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d0. pose (d0 d X1). apply derI with (ps:=[(Γ2 ++ A :: B :: x ++ Γ1, C)]).
        apply AndL. apply AndLRule_I. apply dlCons ; auto. }
    (* Right rule is OrR1 *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X.
      assert (OrR1Rule [(Γ0 ++ Γ1, A)] (Γ0 ++ Γ1, A ∨ B)). apply OrR1Rule_I. apply OrR1 in H2.
      assert (J21: InT  (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, A) = (Γ0 ++ Γ1, A)). reflexivity.
      pose (SIH _ l (Box A0) _ _ _ J5 J7 D0 X1). apply derI with (ps:=[(Γ0 ++ Γ1, A)]).
      apply OrR1. apply OrR1Rule_I. apply dlCons ; auto. }
    (* Right rule is OrR2 *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X.
      assert (OrR2Rule [(Γ0 ++ Γ1, B)] (Γ0 ++ Γ1, A ∨ B)). apply OrR2Rule_I. apply OrR2 in H2.
      assert (J21: InT  (Γ0 ++ Γ1, B) [(Γ0 ++ Γ1, B)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J7 : (Γ0 ++ Γ1, B) = (Γ0 ++ Γ1, B)). reflexivity.
      pose (SIH _ l (Box A0) _ _ _ J5 J7 D0 X1). apply derI with (ps:=[(Γ0 ++ Γ1, B)]).
      apply OrR2. apply OrR2Rule_I. apply dlCons ; auto. }
    (* Right rule is OrL *)
    { inversion H0. subst. inversion X0. subst. inversion X2. subst. clear X4. clear X2. clear X0.
      apply list_split_form in H7. destruct H7 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (OrLRule [((Γ0 ++ x0) ++ A :: Γ3, C);((Γ0 ++ x0) ++ B :: Γ3, C)] ((Γ0 ++ x0) ++ A ∨ B :: Γ3, C)). apply OrLRule_I.
        repeat rewrite <- app_assoc in H2. apply OrL in H2.
        repeat rewrite <- app_assoc in X3. simpl in X3. repeat rewrite <- app_assoc in X1. simpl in X1.
        assert (J01: OrLRule [((Γ0 ++ x0) ++ A :: Γ3, Box A0);((Γ0 ++ x0) ++ B :: Γ3, Box A0)] ((Γ0 ++ x0) ++ A ∨ B :: Γ3, Box A0)). apply OrLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (OrL_inv (Γ0 ++ x0 ++ A ∨ B :: Γ3, Box A0) (Γ0 ++ x0 ++ A :: Γ3, Box A0) (Γ0 ++ x0 ++ B :: Γ3, Box A0) D0 J01).
        destruct p.
        assert (J21: InT (Γ0 ++ x0 ++ A :: Γ3, C) [(Γ0 ++ x0 ++ A :: Γ3, C); (Γ0 ++ x0 ++ B :: Γ3, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: Γ3, C) = (Γ0 ++ x0 ++ A :: Γ3, C)). reflexivity.
        pose (SIH _ l (Box A0) _ _ _ J5 J7 d X1).
        assert (J22: InT (Γ0 ++ x0 ++ B :: Γ3, C) [(Γ0 ++ x0 ++ A :: Γ3, C); (Γ0 ++ x0 ++ B :: Γ3, C)]). apply InT_cons. apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J22).
        assert (J8: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J10 : (Γ0 ++ x0 ++ B :: Γ3, C) = (Γ0 ++ x0 ++ B :: Γ3, C)). reflexivity.
        pose (SIH _ l0 (Box A0) _ _ _ J5 J10 d0 X3).
        apply derI with (ps:=[(Γ0 ++ x0 ++ A :: Γ3, C); (Γ0 ++ x0 ++ B :: Γ3, C)]).
        apply OrL. pose (OrLRule_I A B C (Γ0 ++ x0) Γ3). repeat rewrite <- app_assoc in o ; simpl in o ; auto. apply dlCons ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
        assert (OrLRule [(Γ2 ++ A :: x ++ Γ1, C);(Γ2 ++ B :: x ++ Γ1, C)] (Γ2 ++ A ∨ B :: x ++ Γ1, C)). apply OrLRule_I.
        apply OrL in H2. repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: OrLRule [(Γ2 ++ A :: x ++ Γ1, Box A0);(Γ2 ++ B :: x ++ Γ1, Box A0)] (Γ2 ++ A ∨ B :: x ++ Γ1, Box A0)). apply OrLRule_I.
        pose (OrL_inv (Γ2 ++ A ∨ B :: x ++ Γ1, Box A0) (Γ2 ++ A :: x ++ Γ1, Box A0) (Γ2 ++ B :: x ++ Γ1, Box A0) D0 J01).
        destruct p.
        assert (J21: InT (Γ2 ++ A :: x ++ Γ1, C) [(Γ2 ++ A :: x ++ Γ1, C); (Γ2 ++ B :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ2 ++ A :: x ++ Γ1, C) = ((Γ2 ++ A :: x) ++ Γ1, C)). repeat rewrite <- app_assoc ; reflexivity. repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. pose (d1 d X1).
        assert (J22: InT  (Γ2 ++ B :: x ++ Γ1, C) [(Γ2 ++ A :: x ++ Γ1, C); (Γ2 ++ B :: x ++ Γ1, C)]). apply InT_cons. apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J22).
        assert (J10 : (Γ2 ++ B :: x ++ Γ1, C) = ((Γ2 ++ B :: x) ++ Γ1, C)). repeat rewrite <- app_assoc ; reflexivity.
        pose (SIH _ l0 (Box A0) _ _ _ J5 J10). repeat rewrite <- app_assoc in d3. pose (d3 d0 X3).
        apply derI with (ps:=[(Γ2 ++ A :: x ++ Γ1, C); (Γ2 ++ B :: x ++ Γ1, C)]).
        apply OrL. apply OrLRule_I. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is ImpR *)
    { inversion H0. subst. inversion X0. subst. clear X2. rewrite <- H7 in D1.
      pose (list_exch_LI [] [] Γ2 [A] Γ3 B). simpl in l. rewrite H7 in l. pose (G4iSLT_adm_list_exch_L _ X1 _ l).
      assert (ImpRRule [([] ++ A :: Γ0 ++ Γ1, B)] ([] ++ Γ0 ++ Γ1, A → B)). apply ImpRRule_I. simpl in H2. apply ImpR in H2.
      assert (J21: InT (A :: Γ0 ++ Γ1, B) [(A :: Γ0 ++ Γ1, B)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ H2 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J7 : (A :: Γ0 ++ Γ1, B) = ((A :: Γ0) ++ Γ1, B)). reflexivity.
      pose (SIH _ l0 (Box A0) _ _ _ J5 J7). simpl in d0.
      assert (wkn_L A ([] ++ Γ0 ++ Γ1, Box A0) ([] ++ A :: Γ0 ++ Γ1, Box A0)). apply wkn_LI. simpl in H4.
      pose (@G4iSLT_adm_wkn_L (Γ0 ++ Γ1, Box A0) D0 (A :: Γ0 ++ Γ1, Box A0) A H4).
      pose (d0 d1 d). pose (dlCons d2 DersNilF).
      pose (derI (rules:=G4iSLT_rules) (prems:=fun _ : Seq => False)
      (ps:=[(A :: Γ0 ++ Γ1, B)]) (Γ0 ++ Γ1, A → B) H2 d3). assumption. }
    (* Right rule is AtomImpL1 *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H7. destruct H7 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (AtomImpL1Rule [((Γ0 ++ x0) ++ # P :: Γ3 ++ A :: Γ4, C)] ((Γ0 ++ x0) ++ # P :: Γ3 ++ # P → A :: Γ4, C)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc in H2. apply AtomImpL1 in H2.
        assert (J21: InT  (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C) [(Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C) = (Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)). reflexivity.
        repeat rewrite <- app_assoc in X1. simpl in X1.
        assert (J01: AtomImpL1Rule [((Γ0 ++ x0) ++ # P :: Γ3 ++ A :: Γ4,Box A0)] ((Γ0 ++ x0) ++ # P :: Γ3 ++ # P → A :: Γ4, Box A0)). apply AtomImpL1Rule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AtomImpL_inv P A (Γ0 ++ x0 ++ # P :: Γ3) Γ4 (Box A0)). repeat rewrite <- app_assoc in d. simpl in d. pose (d D0).
        pose (SIH _ l (Box A0) _ _ _ J5 J7 d0 X1). apply derI with (ps:=[(Γ0 ++ x0 ++ # P :: Γ3 ++ A :: Γ4, C)]).
        apply AtomImpL1. pose (AtomImpL1Rule_I P A C (Γ0 ++ x0) Γ3 Γ4). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
        apply list_split_form in e0. destruct e0 ; subst. destruct s.
        + repeat destruct p. inversion e0.
        +  repeat destruct s. repeat destruct p. subst.
            assert (AtomImpL1Rule [(Γ2 ++ # P :: (x ++ x1) ++ A :: Γ4, C)] (Γ2 ++ # P :: (x ++ x1) ++ # P → A :: Γ4, C)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in H2. apply AtomImpL1 in H2.
            assert (J21: InT  (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C) [(Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)]). apply InT_eq.
            pose (G4iSLT_less_thanS _ _ H2 _ J21).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J7 : (Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C) = ((Γ2 ++ # P :: x) ++ x1 ++ A :: Γ4, C)). repeat rewrite <- app_assoc ; reflexivity.
            repeat rewrite <- app_assoc in X1. simpl in X1.
            assert (J01: AtomImpL1Rule [(Γ2 ++ # P :: (x ++ x1) ++ A :: Γ4, Box A0)] (Γ2 ++ # P :: (x ++ x1) ++ # P → A :: Γ4, Box A0)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A (Γ2 ++ # P :: x ++ x1) Γ4 (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH.
            pose (SIH _ l (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. pose (d1 d0 X1).
            apply derI with (ps:=[(Γ2 ++ # P :: x ++ x1 ++ A :: Γ4, C)]). apply AtomImpL1.
            pose (AtomImpL1Rule_I P A C Γ2 (x ++ x1) Γ4). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
        +  repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
            assert (AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)] (Γ2 ++ # P :: Γ3 ++ # P → A :: x0 ++ Γ1, C)). apply AtomImpL1Rule_I. apply AtomImpL1 in H2.
            assert (J21: InT  (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C) [(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)]). apply InT_eq.
            pose (G4iSLT_less_thanS _ _ H2 _ J21).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J7 : (Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C) = ((Γ2 ++ # P :: Γ3 ++ A :: x0) ++ Γ1, C)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; reflexivity.
            assert (J01: AtomImpL1Rule [(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, Box A0)] (Γ2 ++ # P :: Γ3 ++ # P → A :: x0 ++ Γ1, Box A0)). apply AtomImpL1Rule_I.
            repeat rewrite <- app_assoc in D0. simpl in D0. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A (Γ2 ++ # P :: Γ3) (x0 ++ Γ1) (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH. simpl in SIH. repeat rewrite <- app_assoc in SIH.
            pose (SIH _ l (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
            simpl in d1. pose (d1 d0 X1).
            apply derI with (ps:=[(Γ2 ++ # P :: Γ3 ++ A :: x0 ++ Γ1, C)]). apply AtomImpL1. apply AtomImpL1Rule_I. apply dlCons ; auto. }
    (* Right rule is AtomImpL2 *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H7. destruct H7 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (AtomImpL2Rule [((Γ0 ++ x0) ++ A :: Γ3 ++ # P :: Γ4, C)] ((Γ0 ++ x0) ++ # P → A :: Γ3 ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc in H2. apply AtomImpL2 in H2.
        assert (J21: InT  (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C) [(Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C) = (Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)). reflexivity.
        repeat rewrite <- app_assoc in X1. simpl in X1.
        assert (J01: AtomImpL2Rule [((Γ0 ++ x0) ++ A :: Γ3 ++ # P :: Γ4,Box A0)] ((Γ0 ++ x0) ++ # P → A :: Γ3 ++ # P :: Γ4, Box A0)). apply AtomImpL2Rule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AtomImpL_inv P A (Γ0 ++ x0) (Γ3 ++ # P :: Γ4) (Box A0)). repeat rewrite <- app_assoc in d. simpl in d. pose (d D0).
        pose (SIH _ l (Box A0) _ _ _ J5 J7 d0 X1). apply derI with (ps:=[(Γ0 ++ x0 ++ A :: Γ3 ++ # P :: Γ4, C)]).
        apply AtomImpL2. pose (AtomImpL2Rule_I P A C (Γ0 ++ x0) Γ3 Γ4). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
        apply list_split_form in e0. destruct e0 ; subst. destruct s.
        + repeat destruct p. inversion e0.
        +  repeat destruct s. repeat destruct p. subst.
            assert (AtomImpL2Rule [(Γ2 ++ A :: (x ++ x1) ++ # P :: Γ4, C)] (Γ2 ++ # P → A :: (x ++ x1) ++ # P :: Γ4, C)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in H2. apply AtomImpL2 in H2.
            assert (J21: InT  (Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C) [(Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)]). apply InT_eq.
            pose (G4iSLT_less_thanS _ _ H2 _ J21).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J7 : (Γ2 ++  A :: x ++ x1 ++ # P :: Γ4, C) = ((Γ2 ++ A :: x) ++ x1 ++ # P :: Γ4, C)). repeat rewrite <- app_assoc ; simpl ; auto.
            repeat rewrite <- app_assoc in X1. simpl in X1.
            assert (J01: AtomImpL2Rule [(Γ2 ++ A :: (x ++ x1) ++ # P :: Γ4, Box A0)] (Γ2 ++ # P → A :: (x ++ x1) ++ # P :: Γ4, Box A0)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in J01. simpl in J01. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A Γ2 (x ++ x1 ++ # P :: Γ4) (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH.
            pose (SIH _ l (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. pose (d1 d0 X1).
            apply derI with (ps:=[(Γ2 ++ A :: x ++ x1 ++ # P :: Γ4, C)]). apply AtomImpL2.
            pose (AtomImpL2Rule_I P A C Γ2 (x ++ x1) Γ4). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
        +  repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
            assert (AtomImpL2Rule [(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)] (Γ2 ++ # P → A :: Γ3 ++ # P :: x0 ++ Γ1, C)). apply AtomImpL2Rule_I. apply AtomImpL2 in H2.
            assert (J21: InT  (Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C) [(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)]). apply InT_eq.
            pose (G4iSLT_less_thanS _ _ H2 _ J21).
            assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
            assert (J7 : (Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C) = ((Γ2 ++  A :: Γ3 ++ # P :: x0) ++ Γ1, C)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; reflexivity.
            assert (J01: AtomImpL2Rule [(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, Box A0)] (Γ2 ++ # P → A :: Γ3 ++ # P :: x0 ++ Γ1, Box A0)). apply AtomImpL2Rule_I.
            repeat rewrite <- app_assoc in D0. simpl in D0. repeat rewrite <- app_assoc in D0. simpl in D0.
            pose (AtomImpL_inv P A Γ2 (Γ3 ++  # P :: x0 ++ Γ1) (Box A0)). repeat rewrite <- app_assoc in d. simpl in d.
            repeat rewrite <- app_assoc in d. pose (d D0). repeat rewrite <- app_assoc in SIH. simpl in SIH. repeat rewrite <- app_assoc in SIH.
            pose (SIH _ l (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d1. simpl in d1. repeat rewrite <- app_assoc in d1.
            simpl in d1. pose (d1 d0 X1).
            apply derI with (ps:=[(Γ2 ++ A :: Γ3 ++ # P :: x0 ++ Γ1, C)]). apply AtomImpL2. apply AtomImpL2Rule_I. apply dlCons ; auto. }
    (* Right rule is AndImpL *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H7. destruct H7 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (AndImpLRule [((Γ0 ++ x0) ++ A → B → C0 :: Γ3, C)] ((Γ0 ++ x0) ++ (A ∧ B) → C0 :: Γ3, C)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in H2. apply AndImpL in H2.
        assert (J21: InT  (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C) [(Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C) = (Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)). reflexivity.
        repeat rewrite <- app_assoc in X1. simpl in X1.
        assert (J01: AndImpLRule [((Γ0 ++ x0) ++ A → B → C0 :: Γ3, Box A0)] ((Γ0 ++ x0) ++ (A ∧ B) → C0 :: Γ3, Box A0)). apply AndImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (AndImpL_inv (Γ0 ++ x0 ++ (A ∧ B) → C0 :: Γ3, Box A0) (Γ0 ++ x0 ++ A → B → C0 :: Γ3, Box A0) D0 J01).
        pose (SIH _ l (Box A0) _ _ _ J5 J7 d X1). apply derI with (ps:=[(Γ0 ++ x0 ++ A → B → C0 :: Γ3, C)]).
        apply AndImpL. pose (AndImpLRule_I A B C0 C (Γ0 ++ x0) Γ3). repeat rewrite <- app_assoc in a ; simpl in a ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
        assert (AndImpLRule [(Γ2 ++ A → B → C0 :: x ++ Γ1, C)] (Γ2 ++ (A ∧ B) → C0 :: x ++ Γ1, C)). apply AndImpLRule_I. apply AndImpL in H2.
        assert (J21: InT  (Γ2 ++ A → B → C0 :: x ++ Γ1, C) [(Γ2 ++ A → B → C0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ2 ++ A → B → C0 :: x ++ Γ1, C) = ((Γ2 ++ A → B → C0 :: x) ++ Γ1, C)). repeat rewrite <- app_assoc ; simpl ; reflexivity.
        repeat rewrite <- app_assoc in X1. simpl in X1. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: AndImpLRule [(Γ2 ++ A → B → C0 :: x ++ Γ1, Box A0)] (Γ2 ++ (A ∧ B) → C0 :: x ++ Γ1, Box A0)). apply AndImpLRule_I.
        pose (AndImpL_inv (Γ2 ++ (A ∧ B) → C0 :: x ++ Γ1, Box A0) (Γ2 ++ A → B → C0 :: x ++ Γ1, Box A0) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d0. 
        pose (d0 d X1). apply derI with (ps:=[(Γ2 ++ A → B → C0 :: x ++ Γ1, C)]).
        apply AndImpL. apply AndImpLRule_I. apply dlCons ; auto. }
    (* Right rule is OrImpL *)
    { inversion H0. subst. inversion X0. subst. clear X2. clear X0. apply list_split_form in H7. destruct H7 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (OrImpLRule [((Γ0 ++ x0) ++ A → C0 :: Γ3 ++ B → C0 :: Γ4 , C)] ((Γ0 ++ x0) ++ (A ∨ B) → C0 :: Γ3 ++ Γ4, C)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in H2. apply OrImpL in H2.
        assert (J21: InT  (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C) [(Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C) = (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)). reflexivity.
        repeat rewrite <- app_assoc in X1. simpl in X1.
        assert (J01: OrImpLRule [((Γ0 ++ x0) ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, Box A0)] ((Γ0 ++ x0) ++ (A ∨ B) → C0 :: Γ3 ++ Γ4, Box A0)). apply OrImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (OrImpL_inv (Γ0 ++ x0 ++ (A ∨ B) → C0 :: Γ3 ++ Γ4, Box A0) (Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, Box A0) D0 J01).
        pose (SIH _ l (Box A0) _ _ _ J5 J7 d X1). apply derI with (ps:=[(Γ0 ++ x0 ++ A → C0 :: Γ3 ++ B → C0 :: Γ4, C)]).
        apply OrImpL. pose (OrImpLRule_I A B C0 C (Γ0 ++ x0) Γ3 Γ4). repeat rewrite <- app_assoc in o ; simpl in o ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
        assert (OrImpLRule [(Γ2 ++ A → C0 :: [] ++  B → C0 :: x ++ Γ1, C)] (Γ2 ++ (A ∨ B) → C0 :: [] ++ x ++ Γ1, C)). apply OrImpLRule_I.
        simpl in H2. apply OrImpL in H2.
        assert (J21: InT  (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C) [(Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C) = ((Γ2 ++ A → C0 :: B → C0 :: x) ++ Γ1, C)). repeat rewrite <- app_assoc ; simpl ; reflexivity.
        repeat rewrite <- app_assoc in X1. simpl in X1. rewrite <- app_assoc in D0. simpl in D0.
        assert (J01: OrImpLRule [(Γ2 ++ A → C0 :: [] ++ B → C0 :: x ++ Γ1, Box A0)] (Γ2 ++ (A ∨ B) → C0 :: [] ++ x ++ Γ1, Box A0)). apply OrImpLRule_I.
        simpl in J01.
        pose (OrImpL_inv (Γ2 ++ (A ∨ B) → C0 :: x ++ Γ1, Box A0) (Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, Box A0) D0 J01).
        repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d0. simpl in d0. pose (d0 d).
        pose (list_exch_LI (Γ2 ++ [A → C0]) Γ3 [] [B → C0] Γ4 C). simpl in l0. repeat rewrite <- app_assoc in l0. simpl in l0. rewrite e0 in l0.
        pose (G4iSLT_adm_list_exch_L _ X1 _ l0). pose (d1 d2). apply derI with (ps:=[(Γ2 ++ A → C0 :: B → C0 :: x ++ Γ1, C)]).
        apply OrImpL. pose (OrImpLRule_I A B C0 C Γ2 [] (x ++ Γ1)). repeat rewrite <- app_assoc in o ; simpl in o ; auto. apply dlCons ; auto. }
    (* Right rule is ImpImpL *)
    { inversion H0. subst. inversion X0. subst. inversion X2. subst. clear X4. clear X2. clear X0. apply list_split_form in H7. destruct H7 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s. repeat destruct p. subst.
        assert (ImpImpLRule [((Γ0 ++ x0) ++ B → C0 :: Γ3, A → B);((Γ0 ++ x0) ++ C0 :: Γ3, C)] ((Γ0 ++ x0) ++ (A → B) → C0 :: Γ3, C)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in H2. apply ImpImpL in H2.
        repeat rewrite <- app_assoc in X1. simpl in X1. repeat rewrite <- app_assoc in X3. simpl in X3.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ0 ++ x0 ++ (A → B) → C0 :: Γ3, Box A0) = ((Γ0 ++ x0) ++ (A → B) → C0 :: Γ3, Box A0)). rewrite <- app_assoc ; auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J60 J61).
        pose (ctr_LI (B → C0) (Γ0 ++ x0 ++ [A]) [] Γ3 (Box A0)). simpl in c. repeat rewrite <- app_assoc in c ; simpl in c. repeat rewrite <- app_assoc in d.
        pose (@G4iSLT_adm_ctr_L _ d _ (B → C0) c).
        assert (J01: ImpImpLRule [((Γ0 ++ x0) ++ B → C0 :: Γ3, A → B);((Γ0 ++ x0) ++ C0 :: Γ3, Box A0)] ((Γ0 ++ x0) ++ (A → B) → C0 :: Γ3, Box A0)). apply ImpImpLRule_I.
        repeat rewrite <- app_assoc in J01. simpl in J01.
        pose (ImpImpL_inv_R (Γ0 ++ x0 ++ (A → B) → C0 :: Γ3, Box A0) (Γ0 ++ x0 ++ B → C0 :: Γ3, A → B) (Γ0 ++ x0 ++ C0 :: Γ3, Box A0) D0 J01).
        assert (J22: InT (Γ0 ++ x0 ++ C0 :: Γ3, C) [(Γ0 ++ x0 ++ B → C0 :: Γ3, A → B); (Γ0 ++ x0 ++ C0 :: Γ3, C)]). apply InT_cons. apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J22).
        assert (J8: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J10 : (Γ0 ++ x0 ++ C0 :: Γ3, C) = (Γ0 ++ x0 ++ C0 :: Γ3, C)). reflexivity.
        pose (SIH _ l (Box A0) _ _ _ J8 J10 d1 X3).
        assert (J32: ImpRRule [((Γ0 ++ Box A0 :: x0) ++ A :: B → C0 :: Γ3, B)] ((Γ0 ++ Box A0 :: x0) ++ B → C0 :: Γ3, A → B)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J32. simpl in J32.
        pose (ImpR_inv (Γ0 ++ Box A0 :: x0 ++ B → C0 :: Γ3, A → B) (Γ0 ++ Box A0 :: x0 ++ A:: B → C0 :: Γ3, B) X1 J32).
        assert (J21: InT (Γ0 ++ x0 ++ B → C0 :: Γ3, A → B) [(Γ0 ++ x0 ++ B → C0 :: Γ3, A → B); (Γ0 ++ x0 ++ C0 :: Γ3, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J33: ImpRRule [((Γ0 ++ x0) ++ A :: B → C0 :: Γ3, B)] ((Γ0 ++ x0) ++ B → C0 :: Γ3, A → B)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J33. simpl in J33. apply ImpR in J33.
        assert (J34: InT (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B) [(Γ0 ++ x0 ++ A:: B → C0 :: Γ3, B)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ J33 _ J34).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B)= (Γ0 ++ x0 ++ A :: B → C0 :: Γ3, B)). reflexivity.
        pose (less_thanS_trans l1 l0). pose (SIH _ l2 (Box A0) _ _ _ J5 J7 d0 d3).
        apply derI with (ps:=[(Γ0 ++ x0 ++ B → C0 :: Γ3, A → B); (Γ0 ++ x0 ++ C0 :: Γ3, C)]).
        apply ImpImpL. pose (ImpImpLRule_I A B C0 C (Γ0 ++ x0) Γ3). repeat rewrite <- app_assoc in i ; simpl in i ; auto. apply dlCons ; auto.
        apply derI with (ps:=[(Γ0 ++ x0 ++ A:: B → C0 :: Γ3, B)]). apply ImpR. pose (ImpRRule_I A B (Γ0 ++ x0) (B → C0 :: Γ3)).
        repeat rewrite <- app_assoc in i ; simpl in i ; auto. apply dlCons ; auto. apply dlCons ; auto.
      - repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. simpl.
        assert (ImpImpLRule [(Γ2 ++ B → C0 :: x ++ Γ1, A → B);(Γ2 ++ C0 :: x ++ Γ1, C)] (Γ2 ++ (A → B) → C0 :: x ++ Γ1, C)). apply ImpImpLRule_I.
        apply ImpImpL in H2. repeat rewrite <- app_assoc in D0. simpl in D0.
        assert (J60: derrec_height D0 = derrec_height D0). auto.
        assert (J61: (Γ2 ++ (A → B) → C0 :: x ++ Γ1, Box A0) = (Γ2 ++ (A → B) → C0 :: x ++ Γ1, Box A0)). auto.
        pose (ImpImpL_inv_L _ _ _ _ _ _ _ _ _ J60 J61).
        pose (ctr_LI (B → C0) (Γ2 ++ [A]) [] (x ++ Γ1) (Box A0)). simpl in c. repeat rewrite <- app_assoc in c ; simpl in c. pose (@G4iSLT_adm_ctr_L _ d _ _ c).
        assert (J01: ImpImpLRule [(Γ2 ++ B → C0 :: x ++ Γ1, A → B);(Γ2 ++ C0 :: x ++ Γ1, Box A0)] (Γ2 ++ (A → B) → C0 :: x ++ Γ1, Box A0)). apply ImpImpLRule_I.
        pose (ImpImpL_inv_R (Γ2 ++ (A → B) → C0 :: x ++ Γ1, Box A0) (Γ2 ++ B → C0 :: x ++ Γ1, A → B) (Γ2 ++ C0 :: x ++ Γ1, Box A0) D0 J01).
        assert (J22: InT  (Γ2 ++ C0 :: x ++ Γ1, C) [(Γ2 ++ B → C0 :: x ++ Γ1, A → B); (Γ2 ++ C0 :: x ++ Γ1, C)]). apply InT_cons. apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J22).
        assert (J8: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J10 : (Γ2 ++ C0 :: x ++ Γ1, C) = ((Γ2 ++ C0 :: x) ++ Γ1, C)). rewrite <- app_assoc ; auto. repeat rewrite <- app_assoc in SIH.
        pose (SIH _ l (Box A0) _ _ _ J8 J10). repeat rewrite <- app_assoc in d2. simpl in d2. pose (d2 d1 X3).
        assert (J32: ImpRRule [(Γ2 ++ A :: B → C0 :: x ++ Box A0 :: Γ1, B)] (Γ2 ++ B → C0 :: x ++ Box A0 :: Γ1, A → B)). apply ImpRRule_I.
        pose (ImpR_inv (Γ2 ++ B → C0 :: x ++ Box A0 :: Γ1, A → B) (Γ2 ++ A :: B → C0 :: x ++ Box A0 :: Γ1, B) X1 J32).
        assert (J21: InT (Γ2 ++ B → C0 :: x ++ Γ1, A → B) [(Γ2 ++ B → C0 :: x ++ Γ1, A → B); (Γ2 ++ C0 :: x ++ Γ1, C)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ H2 _ J21).
        assert (J33: ImpRRule [(Γ2 ++ A :: B → C0 :: x ++ Γ1,  B)] (Γ2 ++ B → C0 :: x ++ Γ1, A → B)). apply ImpRRule_I.
        repeat rewrite <- app_assoc in J33. simpl in J33. apply ImpR in J33.
        assert (J34: InT (Γ2 ++ A :: B → C0 :: x ++ Γ1,  B) [(Γ2 ++ A :: B → C0 :: x ++ Γ1,  B)]). apply InT_eq.
        pose (G4iSLT_less_thanS _ _ J33 _ J34).
        assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
        assert (J7 : (Γ2 ++ A :: B → C0 :: x ++ Γ1, B) = ((Γ2 ++ A :: B → C0 :: x) ++ Γ1, B)). rewrite <- app_assoc ; auto.
        pose (less_thanS_trans l1 l0). pose (SIH _ l2 (Box A0) _ _ _ J5 J7). repeat rewrite <- app_assoc in d5. pose (d5 d0 d4).
        apply derI with (ps:=[(Γ2 ++ B → C0 :: x ++ Γ1, A → B); (Γ2 ++ C0 :: x ++ Γ1, C)]).
        apply ImpImpL. apply ImpImpLRule_I. apply dlCons ; auto.
        apply derI with (ps:=[(Γ2 ++ A :: B → C0 :: x ++ Γ1, B)]). apply ImpR. pose (ImpRRule_I A B Γ2 (B → C0 :: x ++ Γ1)).
        repeat rewrite <- app_assoc in i ; simpl in i ; auto. apply dlCons ; auto. apply dlCons ; auto. }
    (* Right rule is BoxImpL *)
    { inversion H0. subst. inversion X0. subst. clear X0. inversion X2. subst. inversion X. subst. clear X5. clear X3. clear X.
      apply list_split_form in H7. destruct H7 ; subst. destruct s.
      - repeat destruct p. inversion e0.
      - repeat destruct s ; repeat destruct p ; subst. rewrite <- app_assoc in X0 ; simpl in X0.
         assert (J0: BoxImpLRule [(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A);(Γ0 ++ x0 ++ B :: Γ3, C)] (Γ0 ++ x0 ++ Box A → B :: Γ3, C)).
         pose (@BoxImpLRule_I A B C (Γ0 ++ x0) Γ3). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
         apply BoxImpL in J0.
         apply derI with (ps:=[(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A); (Γ0 ++ x0 ++ B :: Γ3, C)]) ; auto. apply dlCons. 2: apply dlCons ; auto.
         assert (J21: InT (unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A) [(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A); (Γ0 ++ x0 ++ B :: Γ3, C)]). apply InT_eq.
         pose (G4iSLT_less_thanS _ _ J0 _ J21).
         assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
         assert (J7 : (unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A) = (unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A)). reflexivity.
         pose (SIH _ l (Box A0) _ _ _ J5 J7). apply d ; clear d.
         assert (J70: derrec_height D0 = derrec_height D0). auto.
         assert (J71: (Γ0 ++ x0 ++ Box A → B :: Γ3, Box A0) = ((Γ0 ++ x0) ++ Box A → B :: Γ3, Box A0)). rewrite <- app_assoc ; auto.
         assert (J80: weight_form (Box A → B) = weight_form (Box A → B)). auto.
         pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J80 J70 J71). repeat rewrite <- app_assoc in d.
         pose (wkn_LI (Box A) (Γ0 ++ x0 ++ B :: Γ3) [] (Box A0)). rewrite <- app_nil_end in w.
         pose (G4iSLT_adm_wkn_L d w). simpl in d0 ; repeat rewrite <- app_assoc in d0 ; simpl in d0 ; auto.
         pose (unBoxed_list_left_adm_gen (Γ0 ++ x0) [] (B :: Γ3 ++ [Box A]) (Box A0)).
         simpl in g ; repeat rewrite unBox_app_distrib in g ; repeat rewrite <- app_assoc in g. pose (g d0).
         pose (unBoxed_list_left_adm_gen Γ3 (unBoxed_list Γ0 ++ unBoxed_list x0 ++ [B]) [Box A] (Box A0)).
         simpl in g1 ; repeat rewrite unBox_app_distrib in g1 ; repeat rewrite <- app_assoc in g1. pose (g1 g0). simpl in g0 ; auto.
         assert (J50: weight_form A0 < weight_form (Box A0)). simpl. lia.
         assert (J51: weight_form A0 = weight_form A0). auto.
         assert (J53: (unBoxed_list Γ0 ++ Box A0 :: unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A) = (unBoxed_list Γ0 ++ Box A0 :: unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A)). auto.
         pose (PIH _ J50 _ _ _ _ _ J51 J53). apply d ; clear d ; auto.
         assert (J90: derrec_height X4 = derrec_height X4). auto.
         assert (J91: (unBoxed_list (Γ0 ++ x0 ++ Box A → B :: Γ3) ++ [Box A0], A0) = ((unBoxed_list Γ0 ++ unBoxed_list x0) ++ Box A → B :: unBoxed_list Γ3 ++ [Box A0], A0)).
         repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; auto.
         assert (J100: weight_form (Box A → B) = weight_form (Box A → B)). auto.
         pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J100 J90 J91). repeat rewrite <- app_assoc in d.
         pose (wkn_LI (Box A) (unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A0]) [] A0).
         simpl in w ; repeat rewrite <- app_nil_end in w ; repeat rewrite <- app_assoc in w ; simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w.
         pose (G4iSLT_adm_wkn_L d w).
         pose (list_exch_LI (unBoxed_list Γ0) [] (unBoxed_list x0 ++ B :: unBoxed_list Γ3) [Box A0] [Box A] A0). simpl in l0 ; repeat rewrite <- app_assoc in l0 ; simpl in l0.
         apply G4iSLT_adm_list_exch_L with (s:=(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A0; Box A], A0)) ; auto.
         repeat rewrite unBox_app_distrib in X1 ; repeat rewrite <- app_assoc in X1 ; simpl in X1.
         pose (wkn_LI (Box A0) (unBoxed_list Γ0 ++ [A0]) (unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A]) A).
         simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w.
         apply G4iSLT_adm_wkn_L with (A:=Box A0) (s:=(unBoxed_list Γ0 ++ A0 :: unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A)) ; auto.
         assert (J21: InT (Γ0 ++ x0 ++ B :: Γ3, C) [(unBoxed_list Γ0 ++ unBoxed_list x0 ++ B :: unBoxed_list Γ3 ++ [Box A], A); (Γ0 ++ x0 ++ B :: Γ3, C)]). apply InT_cons. apply InT_eq.
         pose (G4iSLT_less_thanS _ _ J0 _ J21).
         assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
         assert (J7 : (Γ0 ++ x0 ++ B :: Γ3, C) = (Γ0 ++ x0 ++ B :: Γ3, C)). reflexivity.
         pose (SIH _ l (Box A0) _ _ _ J5 J7). apply d ; clear d.
         assert (J70: derrec_height D0 = derrec_height D0). auto.
         assert (J71: (Γ0 ++ x0 ++ Box A → B :: Γ3, Box A0) = ((Γ0 ++ x0) ++ Box A → B :: Γ3, Box A0)). rewrite <- app_assoc ; auto.
         assert (J80: weight_form (Box A → B) = weight_form (Box A → B)). auto.
         pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J80 J70 J71). repeat rewrite <- app_assoc in d. auto.
         repeat rewrite <- app_assoc in X0 ; simpl in X0 ; auto.
      - repeat destruct s ; repeat destruct p ; subst. rewrite <- app_assoc. simpl.
         assert (J0: BoxImpLRule [(unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A);(Γ2 ++ B :: x ++ Γ1, C)] (Γ2 ++ Box A → B :: x ++ Γ1, C)).
         pose (@BoxImpLRule_I A B C Γ2 (x ++ Γ1)). repeat rewrite unBox_app_distrib in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
         apply BoxImpL in J0. simpl in SIH. repeat rewrite <- app_assoc in SIH. simpl in SIH.
         apply derI with (ps:=[(unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A); (Γ2 ++ B :: x ++ Γ1, C)]) ; auto. apply dlCons. 2: apply dlCons ; auto.
         assert (J21: InT (unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A) [(unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A); (Γ2 ++ B :: x ++ Γ1, C)]). apply InT_eq.
         pose (G4iSLT_less_thanS _ _ J0 _ J21).
         assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
         assert (J7 : (unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A) = (unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A)). reflexivity.
         pose (SIH _ l (Box A0) _ _ _ J5 J7). apply d ; clear d.
         assert (J70: derrec_height D0 = derrec_height D0). auto.
         assert (J71: ((Γ2 ++ Box A → B :: x) ++ Γ1, Box A0) = (Γ2 ++ Box A → B :: x ++ Γ1, Box A0)). repeat rewrite <- app_assoc ; auto.
         assert (J80: weight_form (Box A → B) = weight_form (Box A → B)). auto.
         pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J80 J70 J71). repeat rewrite <- app_assoc in d.
         pose (wkn_LI (Box A) (Γ2 ++ B :: x ++ Γ1) [] (Box A0)). rewrite <- app_nil_end in w.
         pose (G4iSLT_adm_wkn_L d w). simpl in d0 ; repeat rewrite <- app_assoc in d0 ; simpl in d0 ; auto. repeat rewrite <- app_assoc in d0.
         pose (unBoxed_list_left_adm_gen Γ2 [] (B :: x ++ Γ1 ++ [Box A]) (Box A0)).
         simpl in g ; repeat rewrite unBox_app_distrib in g ; repeat rewrite <- app_assoc in g. pose (g d0).
         pose (unBoxed_list_left_adm_gen (x ++ Γ1) (unBoxed_list Γ2 ++ [B]) [Box A] (Box A0)).
         simpl in g1 ; repeat rewrite unBox_app_distrib in g1 ; repeat rewrite <- app_assoc in g1. pose (g1 g0). simpl in g2 ; auto.
         assert (J50: weight_form A0 < weight_form (Box A0)). simpl. lia.
         assert (J51: weight_form A0 = weight_form A0). auto.
         assert (J53: (unBoxed_list Γ2 ++ Box A0 :: B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A) = (unBoxed_list Γ2 ++ Box A0 :: B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A)). auto.
         pose (PIH _ J50 _ _ _ _ _ J51 J53). apply d ; clear d ; auto.
         assert (J90: derrec_height X4 = derrec_height X4). auto.
         assert (J91: (unBoxed_list ((Γ2 ++ Box A → B :: x) ++ Γ1) ++ [Box A0], A0) = (unBoxed_list Γ2 ++ Box A → B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A0], A0)).
         repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; auto.
         assert (J100: weight_form (Box A → B) = weight_form (Box A → B)). auto.
         pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J100 J90 J91). repeat rewrite <- app_assoc in d.
         pose (wkn_LI (Box A) (unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A0]) [] A0).
         simpl in w ; repeat rewrite <- app_nil_end in w ; repeat rewrite <- app_assoc in w ; simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w.
         pose (G4iSLT_adm_wkn_L d w).
         pose (list_exch_LI (unBoxed_list Γ2) [] (B :: unBoxed_list x ++ unBoxed_list Γ1) [Box A0] [Box A] A0). simpl in l0 ; repeat rewrite <- app_assoc in l0 ; simpl in l0.
         apply G4iSLT_adm_list_exch_L with (s:=(unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A0; Box A], A0)) ; auto.
         repeat rewrite unBox_app_distrib in X1 ; repeat rewrite <- app_assoc in X1 ; simpl in X1.
         pose (wkn_LI (Box A0) (unBoxed_list Γ2 ++ [A0]) (B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A]) A).
         simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w.
         apply G4iSLT_adm_wkn_L with (A:=Box A0) (s:=(unBoxed_list Γ2 ++ A0 :: B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A)) ; auto.
         pose (list_exch_LI (unBoxed_list Γ2) [] (B :: unBoxed_list x) [A0] (unBoxed_list Γ1 ++ [Box A])  A). simpl in l0 ; repeat rewrite <- app_assoc in l0 ; simpl in l0.
         apply G4iSLT_adm_list_exch_L with (s:=(unBoxed_list Γ2 ++ B :: unBoxed_list x ++ A0 :: unBoxed_list Γ1 ++ [Box A], A)) ; auto.
         assert (J21: InT (Γ2 ++ B :: x ++ Γ1, C) [(unBoxed_list Γ2 ++ B :: unBoxed_list x ++ unBoxed_list Γ1 ++ [Box A], A); (Γ2 ++ B :: x ++ Γ1, C)]). apply InT_cons. apply InT_eq.
         pose (G4iSLT_less_thanS _ _ J0 _ J21).
         assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
         assert (J7 : (Γ2 ++ B :: x ++ Γ1, C) = (Γ2 ++ B :: x ++ Γ1, C)). reflexivity.
         pose (SIH _ l (Box A0) _ _ _ J5 J7). apply d ; clear d.
         assert (J70: derrec_height D0 = derrec_height D0). auto.
         assert (J71: ((Γ2 ++ Box A → B :: x) ++ Γ1, Box A0) = (Γ2 ++ Box A → B :: x ++ Γ1, Box A0)). repeat rewrite <- app_assoc ; auto.
         assert (J80: weight_form (Box A → B) = weight_form (Box A → B)). auto.
         pose (@ImpL_hpinv_R _ _ _ _ _ _ _ _ _ J80 J70 J71). repeat rewrite <- app_assoc in d. auto.
         repeat rewrite <- app_assoc in X0 ; simpl in X0 ; auto.
         pose (list_exch_LI Γ2 [] (B :: x) [Box A0] Γ1 C). simpl in l0 ; repeat rewrite <- app_assoc in l0 ; simpl in l0.
         apply G4iSLT_adm_list_exch_L with (s:=(Γ2 ++ B :: x ++ Box A0 :: Γ1, C)) ; auto. }
   (* Right rule is SLR *)
    { inversion H0 ; subst. inversion X0. subst. clear X2. inversion X. subst. clear X3. clear X0. clear X.
      assert (J0: SLRRule [(unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)] (Γ0 ++ Γ1, Box A)). pose (@SLRRule_I A (Γ0 ++ Γ1)).
      repeat rewrite unBox_app_distrib in s ; repeat rewrite <- app_assoc in s ; simpl in s ; apply s. apply SLR in J0.
      apply derI with (ps:=[(unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)]) ; auto. apply dlCons ; auto.
      assert (J21: InT (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A) [(unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)]). apply InT_eq.
      pose (G4iSLT_less_thanS _ _ J0 _ J21).
      assert (J5: weight_form (Box A0) = weight_form (Box A0)). reflexivity.
      assert (J7: (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A) = (unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A], A)). repeat rewrite <- app_assoc ; reflexivity.
      pose (SIH _ l (Box A0) _ _ _ J5 J7). apply d ; clear d.
      pose (wkn_LI (Box A) (unBoxed_list Γ0 ++ unBoxed_list Γ1) [] (Box A0)). simpl in w ; repeat rewrite <- app_nil_end in w ; repeat rewrite <- app_assoc in w.
      apply G4iSLT_adm_wkn_L with (A:=Box A) (s:=(unBoxed_list Γ0 ++ unBoxed_list Γ1, Box A0)) ; auto.
      apply derI with (ps:=[(unBoxed_list (unBoxed_list Γ0) ++ unBoxed_list (unBoxed_list Γ1) ++ [Box A0], A0)]). apply SLR. pose (@SLRRule_I A0 (unBoxed_list Γ0 ++ unBoxed_list Γ1)).
      repeat rewrite unBox_app_distrib in s ; repeat rewrite <- app_assoc in s ; simpl in s ; apply s.
      repeat rewrite unBox_app_distrib in X2 ; repeat rewrite <- app_assoc in X2 ; simpl in X2 ; auto. apply dlCons ; auto.
      pose (unBoxed_list_left_adm_gen (unBoxed_list Γ0 ++ unBoxed_list Γ1) [] [Box A0] A0).
      simpl in g ; repeat rewrite unBox_app_distrib in g ; repeat rewrite <- app_assoc in g ; simpl in g. apply g ; auto.
      repeat rewrite unBox_app_distrib in X1 ; simpl in X1 ; repeat rewrite <- app_assoc in X1 ; simpl in X1.
      assert (J50: weight_form A0 < weight_form (Box A0)). simpl. lia.
      assert (J51: weight_form A0 = weight_form A0). auto.
      assert (J53: (unBoxed_list Γ0 ++ Box A0 :: unBoxed_list Γ1 ++ [Box A], A) =(unBoxed_list Γ0 ++ Box A0 :: unBoxed_list Γ1 ++ [Box A], A)). repeat rewrite <- app_assoc ; auto.
      pose (PIH _ J50 _ _ _ _ _ J51 J53). apply d ; clear d ; auto.
      pose (list_exch_LI (unBoxed_list Γ0) [Box A] (unBoxed_list Γ1) [Box A0] [] A0). simpl in l0.
      apply G4iSLT_adm_list_exch_L with (s:=(unBoxed_list Γ0 ++ Box A :: unBoxed_list Γ1 ++ [Box A0], A0)) ; auto.
      pose (wkn_LI (Box A) (unBoxed_list Γ0) (unBoxed_list Γ1 ++ [Box A0]) A0). simpl in w ; repeat rewrite <- app_assoc in w.
      apply G4iSLT_adm_wkn_L with (A:=Box A) (s:=(unBoxed_list Γ0 ++ unBoxed_list Γ1 ++ [Box A0], A0)) ; auto.
      repeat rewrite unBox_app_distrib in X2 ; repeat rewrite <- app_assoc in X2 ; simpl in X2 ; auto.
      pose (wkn_LI (Box A0) (unBoxed_list Γ0 ++ [A0]) (unBoxed_list Γ1 ++ [Box A]) A). simpl in w ; repeat rewrite <- app_assoc in w ; simpl in w.
      apply G4iSLT_adm_wkn_L with (A:=Box A0) (s:=(unBoxed_list Γ0 ++ A0 :: unBoxed_list Γ1 ++ [Box A], A)) ; auto. }
Qed.

Theorem G4iSLT_cut_adm0 : forall A Γ0 Γ1 C,
                      G4iSLT_prv (Γ0 ++ Γ1, A) ->
                      G4iSLT_prv (Γ0 ++ A :: Γ1, C) ->
                      G4iSLT_prv (Γ0 ++ Γ1, C).
Proof.
intros.
assert (J1: weight_form A = weight_form A). reflexivity.
assert (J3: (Γ0 ++ Γ1, C) = (Γ0 ++ Γ1, C)). reflexivity.
pose (@G4iSLT_cut_adm_main (weight_form A) A
(Γ0 ++ Γ1, C) Γ0 Γ1 C J1 J3). unfold G4iSLT_prv. auto.
Qed.

Theorem G4iSLT_cut_adm : forall A Γ0 Γ1 C,
                      (G4iSLT_prv (Γ0 ++ Γ1, A) * G4iSLT_prv (Γ0 ++ A :: Γ1, C)) ->
                      G4iSLT_prv (Γ0 ++ Γ1, C).
Proof.
intros. destruct X. apply G4iSLT_cut_adm0 with (A:=A) ; auto.
Qed.