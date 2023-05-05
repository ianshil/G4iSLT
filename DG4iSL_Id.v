Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_exch.
Require Import DG4iSL_wkn.
Require Import DG4iSL_inv_ImpR.

(* We can show that identities on formulae of all complexities are derivable in G4iSL. *)

Lemma Id_all_form0 : forall n (A : MPropF) Γ0 Γ1,
          (n = weight_form A) ->
          derrec G4iSL_rules (fun _ => False) (Γ0 ++ A :: Γ1, A).
Proof.
pose (strong_inductionT (fun (x:nat) => forall A Γ0 Γ1,
                      x = weight_form A ->
                      derrec G4iSL_rules (fun _ => False) (Γ0 ++ A :: Γ1, A))).
apply d. clear d. intros n IH. destruct A.
- intros. assert (IdPRule [] (Γ0 ++ # n0 :: Γ1, # n0)). apply IdPRule_I. apply IdP in H0.
  apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[]).
  assumption. apply dersrec_nil.
- intros. assert (BotLRule [] (Γ0 ++ ⊥ :: Γ1, ⊥)). apply BotLRule_I. apply BotL in H0.
  apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[]).
  assumption. apply dersrec_nil.
- intros.  assert (AndLRule [(Γ0 ++ A1 :: A2 :: Γ1, And A1 A2)]  (Γ0 ++ And A1 A2 :: Γ1, And A1 A2)).
  apply AndLRule_I. apply AndL in H0.
  assert (AndRRule [(Γ0 ++ A1 :: A2 :: Γ1, A1) ; (Γ0 ++ A1 :: A2 :: Γ1, A2)] (Γ0 ++ A1 :: A2 :: Γ1, And A1 A2)).
  apply AndRRule_I. apply AndR in H1.
  assert (J1: weight_form A1 < n). subst. simpl. lia.
  pose (IH (weight_form A1) J1 A1 Γ0 (A2 :: Γ1)).
  assert (J2 : weight_form A2 < n). subst. simpl. lia.
  pose (IH (weight_form A2) J2 A2 (Γ0 ++ [A1]) Γ1). repeat rewrite <- app_assoc in d0. simpl in d0.
  apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A1 :: A2 :: Γ1, And A1 A2)]) ; auto.
  apply dlCons. 2 : apply dersrec_nil.
  apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(Γ0 ++ A1 :: A2 :: Γ1, A1); (Γ0 ++ A1 :: A2 :: Γ1, A2)]).
  assumption. apply dlCons. auto. apply dlCons. auto. apply dersrec_nil.
- intros.
  apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
  (ps:=[(Γ0 ++ A1 :: Γ1, Or A1 A2) ; (Γ0 ++ A2 :: Γ1, Or A1 A2)]).
  apply OrL. apply OrLRule_I. apply dlCons.
  apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
  (ps:=[(Γ0 ++ A1 :: Γ1, A1)]). apply OrR1. apply OrR1Rule_I. apply dlCons. 2: apply dersrec_nil.
  assert (J1: weight_form A1 < n). subst. simpl. lia. pose (IH (weight_form A1) J1 A1 Γ0 Γ1). auto.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
  (ps:=[(Γ0 ++ A2 :: Γ1, A2)]). apply OrR2. apply OrR2Rule_I. apply dlCons.
  assert (J2: weight_form A2 < n). subst. simpl. lia. pose (IH (weight_form A2) J2 A2 Γ0 Γ1). auto.
  apply dersrec_nil.
- intros. apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
  (ps:=[(Γ0 ++ A1 :: Imp A1 A2 :: Γ1, A2)]). apply ImpR. apply ImpRRule_I. apply dlCons. 2: apply dersrec_nil.
  destruct A1 ; intros.
  + apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ # n0 :: A2 :: Γ1, A2)]). apply AtomImpL1. assert (Γ0 ++ # n0 :: Imp # n0 A2 :: Γ1 = Γ0 ++ # n0 :: [] ++ Imp # n0 A2 :: Γ1).
     auto. rewrite H0. assert (Γ0 ++ # n0 :: A2 :: Γ1 = Γ0 ++ # n0 :: [] ++ A2 :: Γ1). auto. rewrite H1. apply AtomImpL1Rule_I.
     apply dlCons. 2: apply dersrec_nil. assert (J1: (weight_form A2) < n). subst. simpl. lia. pose (IH (weight_form A2) J1 A2 (Γ0 ++ [# n0]) Γ1).
     rewrite <- app_assoc in d. simpl in d. apply d. auto.
  + apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
     (ps:=[]). apply BotL. apply BotLRule_I. apply dersrec_nil.
  + apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ A1_1 :: A1_2 :: Imp (And A1_1 A1_2) A2 :: Γ1, A2)]). apply AndL. apply AndLRule_I.
     apply dlCons. 2: apply dersrec_nil.
     apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ A1_1 :: A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1, A2)]). apply AndImpL.
     assert (Γ0 ++ A1_1 :: A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1 = (Γ0 ++ A1_1 :: [A1_2]) ++ Imp A1_1 (Imp A1_2 A2) :: Γ1).
     repeat rewrite <- app_assoc. auto. rewrite H0.
     assert (Γ0 ++ A1_1 :: A1_2 :: Imp (And A1_1 A1_2) A2 :: Γ1 = (Γ0 ++ A1_1 :: [A1_2]) ++ Imp (And A1_1 A1_2) A2 :: Γ1).
     repeat rewrite <- app_assoc. auto. rewrite H1. apply AndImpLRule_I. apply dlCons. 2: apply dersrec_nil.
     assert (J1: weight_form (Imp A1_1 (Imp A1_2 A2)) < n). simpl. simpl in H. lia.
     assert (J2: weight_form (Imp A1_1 (Imp A1_2 A2)) = weight_form (Imp A1_1 (Imp A1_2 A2))). auto.
     pose (IH (weight_form (Imp A1_1 (Imp A1_2 A2))) J1 (Imp A1_1 (Imp A1_2 A2)) Γ0 Γ1 J2).
     assert (ImpRRule [(Γ0 ++ A1_1 :: Imp A1_1 (Imp A1_2 A2) :: Γ1, Imp A1_2 A2)] (Γ0 ++ Imp A1_1 (Imp A1_2 A2) :: Γ1, Imp A1_1 (Imp A1_2 A2))).
     apply ImpRRule_I. assert (J3: derrec_height d = derrec_height d). auto.
      pose (@ImpR_hpinv (derrec_height d) _ d J3 _ H0). destruct s. clear l.
     assert (ImpRRule [(Γ0 ++ A1_1 :: A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1, A2)] (Γ0 ++ A1_1 :: Imp A1_1 (Imp A1_2 A2) :: Γ1, Imp A1_2 A2)).
     assert (Γ0 ++ A1_1 :: A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1 = (Γ0 ++ [A1_1]) ++ A1_2 :: Imp A1_1 (Imp A1_2 A2) :: Γ1).
     repeat rewrite <- app_assoc ; auto. rewrite H1.
     assert (Γ0 ++ A1_1 :: Imp A1_1 (Imp A1_2 A2) :: Γ1 = (Γ0 ++ [A1_1]) ++ Imp A1_1 (Imp A1_2 A2) :: Γ1).
     repeat rewrite <- app_assoc ; auto. rewrite H2. apply ImpRRule_I.
     assert (J4: derrec_height x = derrec_height x). auto.
     pose (@ImpR_hpinv (derrec_height x) _ x J4 _ H1). destruct s. auto.
  + apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
     (ps:=[((Γ0 ++ [Or A1_1 A1_2]) ++ Imp A1_1 A2 :: [] ++ Imp A1_2 A2 :: Γ1, A2)]). apply OrImpL.
     assert (Γ0 ++ Or A1_1 A1_2 :: Imp (Or A1_1 A1_2) A2 :: Γ1 = (Γ0 ++ [Or A1_1 A1_2]) ++ Imp (Or A1_1 A1_2) A2 :: [] ++ Γ1).
     repeat rewrite <- app_assoc. auto. rewrite H0. apply OrImpLRule_I. apply dlCons. simpl. 2: apply dersrec_nil.
     subst. repeat rewrite <- app_assoc. simpl.
     apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
     (ps:=[(Γ0 ++ A1_1 :: Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, A2);(Γ0 ++ A1_2 :: Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, A2)]).
     apply OrL. apply OrLRule_I. apply dlCons. 2: apply dlCons. 3: apply dersrec_nil.
     assert (J1: weight_form (Imp A1_1 A2) < weight_form (Imp (Or A1_1 A1_2) A2)). simpl. lia.
     assert (J2: weight_form (Imp A1_1 A2) = weight_form (Imp A1_1 A2)). auto.
     pose (IH (weight_form (Imp A1_1 A2)) J1 (Imp A1_1 A2) Γ0 (Imp A1_2 A2 :: Γ1) J2).
     assert (ImpRRule [(Γ0 ++ A1_1 :: Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, A2)] (Γ0 ++ Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, Imp A1_1 A2)).
     apply ImpRRule_I. assert (J3: derrec_height d = derrec_height d). auto.
     pose (@ImpR_hpinv (derrec_height d) _ d J3 _ H). destruct s. clear l. auto.
     assert (J1: weight_form (Imp A1_2 A2) < weight_form (Imp (Or A1_1 A1_2) A2)). simpl. lia.
     assert (J2: weight_form (Imp A1_2 A2) = weight_form (Imp A1_2 A2)). auto.
     pose (IH (weight_form (Imp A1_2 A2)) J1 (Imp A1_2 A2) (Γ0 ++ [Imp A1_1 A2]) Γ1 J2). repeat rewrite <- app_assoc in d.
     simpl in d.
     assert (ImpRRule [(Γ0 ++ A1_2 :: Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, A2)] (Γ0 ++ Imp A1_1 A2 :: Imp A1_2 A2 :: Γ1, Imp A1_2 A2)).
     apply ImpRRule_I. assert (J3: derrec_height d = derrec_height d). auto.
     pose (@ImpR_hpinv (derrec_height d) _ d J3 _ H). destruct s. clear l. auto.
  + apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
     (ps:=[((Γ0 ++ [Imp A1_1 A1_2]) ++ Imp A1_2 A2 :: Γ1, Imp A1_1 A1_2);((Γ0 ++ [Imp A1_1 A1_2]) ++ A2 :: Γ1, A2)]).
     apply ImpImpL.
     assert (Γ0 ++ Imp A1_1 A1_2 :: Imp (Imp A1_1 A1_2) A2 :: Γ1 = (Γ0 ++ [Imp A1_1 A1_2]) ++ Imp (Imp A1_1 A1_2) A2 :: Γ1).
     repeat rewrite <- app_assoc. auto. rewrite H0. apply ImpImpLRule_I. repeat rewrite <- app_assoc. simpl. subst.
     apply dlCons. 2: apply dlCons. 3: apply dersrec_nil.
     assert (J1: weight_form (Imp A1_1 A1_2) < weight_form (Imp (Imp A1_1 A1_2) A2)). simpl. lia.
     assert (J2: weight_form (Imp A1_1 A1_2) = weight_form (Imp A1_1 A1_2)). auto.
     pose (IH (weight_form (Imp A1_1 A1_2)) J1 (Imp A1_1 A1_2) Γ0 (Imp A1_2 A2 :: Γ1) J2). auto.
     assert (J1: weight_form A2 < weight_form (Imp (Imp A1_1 A1_2) A2)). simpl. lia.
     assert (J2: weight_form A2 = weight_form A2). auto.
     pose (IH (weight_form A2) J1 A2 (Γ0 ++ [Imp A1_1 A1_2]) Γ1 J2). repeat rewrite <- app_assoc in d.
     simpl in d. auto.
  + apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False)
     (ps:=[(unBoxed_list Γ0 ++ A1 :: A2 :: unBoxed_list Γ1 ++ [Box A1], A1) ; (Γ0 ++ Box A1 :: A2 :: Γ1, A2)]). apply BoxImpL.
     pose (@BoxImpLRule_I A1 A2 A2 (Γ0 ++ [Box A1]) Γ1).
     repeat rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; apply b.
     assert (J1: (weight_form A1) < n). subst. simpl. lia.
     pose (IH _ J1 A1 (unBoxed_list Γ0) (A2 :: unBoxed_list Γ1 ++ [Box A1])). apply dlCons. 2: apply dlCons. 3: apply dlNil. apply d ; auto.
     assert (J2: (weight_form A2) < n). subst ; simpl ; lia. pose (IH _ J2 A2 (Γ0 ++ [Box A1]) Γ1). rewrite <- app_assoc in d0. simpl in d0. apply d0 ; auto.
- intros. assert (SLRRule [(unBoxed_list Γ0 ++ A :: unBoxed_list Γ1 ++ [Box A], A)] (Γ0 ++ Box A :: Γ1, Box A)).
  pose (@SLRRule_I A (Γ0 ++ Box A :: Γ1)). repeat rewrite unBox_app_distrib in s ; repeat rewrite <- app_assoc in s ; apply s.
  assert (J: (weight_form A) < n). subst ; simpl ; lia.
  pose (IH _ J A (unBoxed_list Γ0) (unBoxed_list Γ1 ++ [Box A])). apply SLR in H0.
  apply derI with (rules:=G4iSL_rules) (prems:=fun _ : Seq => False) (ps:=[(unBoxed_list Γ0 ++ A :: unBoxed_list Γ1 ++ [Box A], A)]) ; auto.
  apply dlCons. 2: apply dersrec_nil. apply d ; auto.
Qed.

Lemma Id_all_form : forall (A : MPropF) Γ0 Γ1,
          derrec G4iSL_rules (fun _ => False) (Γ0 ++ A :: Γ1, A).
Proof.
intros.
pose (@Id_all_form0 (weight_form A) A Γ0 Γ1). apply d ; auto.
Qed.

Lemma ModusPonens : forall A B Γ0 Γ1 Γ2, derrec G4iSL_rules (fun _ => False) (Γ0 ++ A :: Γ1 ++ (Imp A B) :: Γ2, B).
Proof.
intros.
pose (Id_all_form (Imp A B) (Γ0 ++ Γ1) Γ2). rewrite <- app_assoc in d.
assert (ImpRRule [(Γ0 ++ A :: Γ1 ++ Imp A B :: Γ2, B)] (Γ0 ++ Γ1 ++ Imp A B :: Γ2, Imp A B)). apply ImpRRule_I.
assert (J3: derrec_height d = derrec_height d). auto.
pose (@ImpR_hpinv (derrec_height d) _ d J3 _ H). destruct s. auto.
Qed.
