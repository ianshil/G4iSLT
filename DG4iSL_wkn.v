Require Import List.
Export ListNotations.
Require Import Lia.
Require Import PeanoNat.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.
Require Import DG4iSL_dec.

Set Implicit Arguments.

(* We define the relation which takes care of the notion of weakening on the left. *)

Inductive wkn_L (fml : MPropF) : relationT Seq :=
  | wkn_LI Γ0 Γ1 A : wkn_L fml
        (Γ0 ++ Γ1, A) (Γ0 ++ fml :: Γ1, A).

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent sw which is a weakened
version of s, with some premises psw that are such that they are either the same premises
(in case the weakened formula is weakened in the rule) or weakened versions of ps. *)

Lemma AndR_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (AndRRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (AndRRule [psw1;psw2] sw) * (@wkn_L A ps1 psw1) * (@wkn_L A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1, A0). exists (Γ0 ++ A :: Γ1, B). repeat split.
Qed.

Lemma AndL_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (AndLRule [ps] s) ->
  (existsT2 psw, (AndLRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H ; subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: A0 :: B :: Γ1, C). repeat split ; try assumption.
  epose (AndLRule_I _ _ _ (Γ2 ++ [A]) Γ1). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
- exists (Γ2 ++ A :: x ++ A0 :: B :: Γ1, C). split ; auto.
  epose (AndLRule_I _ _ _ (Γ2 ++ A :: x) Γ1). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
  repeat rewrite <- app_assoc. apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r ; simpl in e0 ; subst.
  + exists (Γ0 ++ A :: A0 :: B :: Γ1, C). repeat split ; try assumption.
     epose (AndLRule_I _ _ _ (Γ0 ++ [A]) Γ1). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
  + inversion e0 ; subst. exists (Γ0 ++ A0 :: B :: x ++ A :: Γ3, C). split ; try assumption.
     repeat rewrite <- app_assoc ; apply AndLRule_I. epose (wkn_LI A (Γ0 ++ A0 :: B :: x) _ C).
     repeat rewrite <- app_assoc in w ; simpl in w. apply w.
Qed.

Lemma OrR1_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (OrR1Rule [ps] s) ->
  (existsT2 psw, (OrR1Rule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1, A0). repeat split.
Qed.

Lemma OrR2_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (OrR2Rule [ps] s) ->
  (existsT2 psw, (OrR2Rule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1, B). repeat split.
Qed.

Lemma OrL_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (OrLRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (OrLRule [psw1;psw2] sw) * (@wkn_L A ps1 psw1) * (@wkn_L A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: A0 :: Γ1, C). exists (Γ2 ++ A :: B :: Γ1, C). repeat split ; try assumption.
  epose (OrLRule_I _ _ _ (Γ2 ++ [A]) Γ1). repeat rewrite <- app_assoc in o ; simpl in o ; apply o.
- exists ((Γ2 ++ A :: x) ++ A0 :: Γ1, C). exists ((Γ2 ++ A :: x) ++ B :: Γ1, C). repeat split ; auto.
  epose (OrLRule_I _ _ _ (Γ2 ++ A :: x) Γ1). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; apply o.
  1-2: repeat rewrite <- app_assoc ; apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r ; simpl in e0 ; subst.
  + exists (Γ0 ++ A :: A0 :: Γ1, C). exists (Γ0 ++ A :: B :: Γ1, C). repeat split ; try assumption.
     epose (OrLRule_I _ _ _ (Γ0 ++ [A]) Γ1). repeat rewrite <- app_assoc in o ; simpl in o ; apply o.
  + inversion e0 ; subst. exists (Γ0 ++ A0 :: x ++ A :: Γ3, C). exists (Γ0 ++ B :: x ++ A :: Γ3, C). repeat split ; try assumption.
     repeat rewrite <- app_assoc ; apply OrLRule_I.
     1-2: epose (wkn_LI A (Γ0 ++ _ :: x) _ C) ; repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
Qed.

Lemma ImpR_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (ImpRRule [ps] s) ->
  (existsT2 psw, (ImpRRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A0 :: A :: Γ3, B). repeat split ; try assumption. epose (wkn_LI A (Γ2 ++ [A0]) _ B).
  simpl in w ; repeat rewrite <- app_assoc in w ; apply w.
- exists ((Γ2 ++ A :: x) ++ A0 :: Γ1, B). split ; auto.
  epose (ImpRRule_I _ _ (Γ2 ++ A :: x) Γ1). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in i ; simpl in i ; apply i.
  repeat rewrite <- app_assoc. apply wkn_LI.
- exists (Γ0 ++ A0 :: x ++ A :: Γ3, B). repeat split ; try assumption.
  epose (ImpRRule_I _ _ Γ0 (x ++ A:: Γ3)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in i ; simpl in i ; apply i.
  epose (wkn_LI A (Γ0 ++ A0 :: x) _ B). repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
Qed.

Lemma AtomImpL1_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (AtomImpL1Rule [ps] s) ->
  (existsT2 psw, (AtomImpL1Rule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ3 ++ A :: # P :: Γ1 ++ A0 :: Γ2, C). repeat split ; try assumption.
  epose (AtomImpL1Rule_I _ _ _ (Γ3 ++ [A]) Γ1 Γ2). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
- exists ((Γ3 ++ A :: x) ++ # P :: Γ1 ++ A0 :: Γ2, C). split ; repeat rewrite <- app_assoc ; simpl ; auto. 2: apply wkn_LI.
  epose (AtomImpL1Rule_I _ _ _ (Γ3 ++ A :: x) Γ1 Γ2). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
- destruct x ; subst ; repeat rewrite app_nil_r ; simpl in e0 ; subst.
  + exists (Γ0 ++ A :: # P :: Γ1 ++ A0 :: Γ2, C). repeat split ; try assumption.
     epose (AtomImpL1Rule_I _ _ _ (Γ0 ++ [A]) Γ1 Γ2). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
  + inversion e0 ; subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    * exists (Γ0 ++ # P :: (Γ1 ++ [A]) ++ A0 :: Γ2, C). repeat split ; try assumption ; repeat rewrite <- app_assoc ; simpl.
      epose (AtomImpL1Rule_I _ _ _ Γ0 (Γ1 ++ [A]) Γ2). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
      epose (wkn_LI A (Γ0 ++ # P :: Γ1) _ C). repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
    * destruct x0 ;  subst ; repeat rewrite app_nil_r ; simpl in e1 ; subst ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc.
      -- exists (Γ0 ++ # P :: Γ1 ++ A :: A0 :: Γ2, C). repeat split ; try assumption.
         epose (AtomImpL1Rule_I _ _ _ Γ0 (Γ1 ++ [A]) Γ2). simpl in a ; repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
         epose (wkn_LI A (Γ0 ++ # P :: Γ1) _ C). repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
      -- inversion e1 ; subst. exists (Γ0 ++ # P :: Γ1 ++ A0 :: x0 ++ A :: Γ4, C). repeat split ; try assumption.
         epose (wkn_LI A (Γ0 ++ # P :: Γ1 ++ A0 :: x0) Γ4 C).
          repeat rewrite <- app_assoc in w ; simpl in w ; simpl in w ; repeat rewrite <- app_assoc in w ; apply w.
    * exists (Γ0 ++ # P :: (x ++ A :: x0) ++ A0 :: Γ2, C). repeat split ; try assumption.
      epose (AtomImpL1Rule_I _ _ _ Γ0 (x ++ A :: x0) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
      epose (wkn_LI A (Γ0 ++ # P :: x) _ C). repeat rewrite <- app_assoc ; simpl in w ; repeat rewrite <- app_assoc in w ; apply w.
Qed.

Lemma AtomImpL2_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (AtomImpL2Rule [ps] s) ->
  (existsT2 psw, (AtomImpL2Rule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ3 ++ A :: A0 :: Γ1 ++ # P :: Γ2, C). repeat split ; try assumption.
  epose (AtomImpL2Rule_I _ _ _ (Γ3 ++ [A]) Γ1 Γ2). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
- exists ((Γ3 ++ A :: x) ++ A0 :: Γ1 ++ # P :: Γ2, C). split ; repeat rewrite <- app_assoc ; simpl ; auto. 2: apply wkn_LI.
  epose (AtomImpL2Rule_I _ _ _ (Γ3 ++ A :: x) Γ1 Γ2). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
- destruct x ; subst ; repeat rewrite app_nil_r ; simpl in e0 ; subst.
  + exists (Γ0 ++ A :: A0 :: Γ1 ++ # P :: Γ2, C). repeat split ; try assumption.
     epose (AtomImpL2Rule_I _ _ _ (Γ0 ++ [A]) Γ1 Γ2). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
  + inversion e0 ; subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    * exists (Γ0 ++ A0 :: (Γ1 ++ [A]) ++ # P :: Γ2, C). repeat split ; try assumption ; repeat rewrite <- app_assoc ; simpl.
      epose (AtomImpL2Rule_I _ _ _ Γ0 (Γ1 ++ [A]) Γ2). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
      epose (wkn_LI A (Γ0 ++ A0 :: Γ1) _ C). repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
    * destruct x0 ;  subst ; repeat rewrite app_nil_r ; simpl in e1 ; subst ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc.
      -- exists (Γ0 ++ A0 :: (Γ1 ++ [A]) ++ # P :: Γ2, C). repeat split ; try assumption ; repeat rewrite <- app_assoc ; simpl.
         epose (AtomImpL2Rule_I _ _ _ Γ0 (Γ1 ++ [A]) Γ2). simpl in a ; repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
         epose (wkn_LI A (Γ0 ++ A0 :: Γ1) _ C). repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
      -- inversion e1 ; subst. exists (Γ0 ++ A0 :: Γ1 ++ # P :: x0 ++ A :: Γ4, C). repeat split ; try assumption.
         epose (wkn_LI A (Γ0 ++ A0 :: Γ1 ++ # P :: x0) Γ4 C).
          repeat rewrite <- app_assoc in w ; simpl in w ; simpl in w ; repeat rewrite <- app_assoc in w ; apply w.
    * exists (Γ0 ++ A0 :: (x ++ A :: x0) ++ # P :: Γ2, C). repeat split ; try assumption.
      epose (AtomImpL2Rule_I _ _ _ Γ0 (x ++ A :: x0) Γ2). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
      epose (wkn_LI A (Γ0 ++ A0 :: x) _ C). repeat rewrite <- app_assoc ; simpl in w ; repeat rewrite <- app_assoc in w ; apply w.
Qed.

Lemma AndImpL_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (AndImpLRule [ps] s) ->
  (existsT2 psw, (AndImpLRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: (Imp A0 (Imp B C)) :: Γ1, D). repeat split ; try assumption.
  epose (AndImpLRule_I _ _ _ _ (Γ2 ++ [A]) Γ1). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
- exists ((Γ2 ++ A :: x) ++ (Imp A0 (Imp B C)) :: Γ1, D). repeat split ; auto ; repeat rewrite <- app_assoc ; simpl.
  epose (AndImpLRule_I _ _ _ _ (Γ2 ++ A :: x) Γ1). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
  repeat rewrite <- app_assoc ; apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r ; simpl in e0 ; subst.
  + exists (Γ0 ++ A :: (Imp A0 (Imp B C)) :: Γ1, D). repeat split ; try assumption.
     epose (AndImpLRule_I _ _ _ _ (Γ0 ++ [A]) Γ1). repeat rewrite <- app_assoc in a ; simpl in a ; apply a.
  + inversion e0 ; subst. exists (Γ0 ++ (Imp A0 (Imp B C)) :: x ++ A :: Γ3, D). repeat split ; try assumption.
     repeat rewrite <- app_assoc ; apply AndImpLRule_I.
     epose (wkn_LI A (Γ0 ++ _ :: x) _ D) ; repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
Qed.

Lemma OrImpL_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (OrImpLRule [ps] s) ->
  (existsT2 psw, (OrImpLRule [psw] sw) * (@wkn_L A ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ3 ++ A :: (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2, D). repeat split ; try assumption.
  epose (OrImpLRule_I _ _ _ _ (Γ3 ++ [A]) Γ1 Γ2). repeat rewrite <- app_assoc in o ; simpl in o ; apply o.
- exists ((Γ3 ++ A :: x) ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2, D). repeat split ; auto ; repeat rewrite <- app_assoc ; simpl.
  epose (OrImpLRule_I _ _ _ _ (Γ3 ++ A :: x) Γ1 Γ2). repeat rewrite <- app_assoc in o ; simpl in o ; apply o.
  repeat rewrite <- app_assoc ; apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r ; simpl in e0 ; subst.
  + exists (Γ0 ++ A :: (Imp A0 C) :: Γ1 ++ (Imp B C) :: Γ2, D). repeat split ; try assumption.
     epose (OrImpLRule_I _ _ _ _ (Γ0 ++ [A]) Γ1 Γ2). repeat rewrite <- app_assoc in o ; simpl in o ; apply o.
  + inversion e0 ; subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    * exists (Γ0 ++ (Imp A0 C) :: Γ1 ++ (Imp B C) :: A :: Γ2, D). repeat split ; try assumption ; repeat rewrite <- app_assoc ; simpl.
      apply OrImpLRule_I. epose (wkn_LI A (Γ0 ++ A0 → C :: Γ1 ++ [B → C])  Γ2 D) ; simpl in w ; repeat rewrite <- app_assoc in w ;
      simpl in w ; repeat rewrite <- app_assoc in w ; apply w.
    * exists (Γ0 ++ (Imp A0 C) :: Γ1 ++  (Imp B C) :: x0 ++ A :: Γ4, D). repeat split ; auto ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc.
      apply OrImpLRule_I. epose (wkn_LI A (Γ0 ++ A0 → C :: Γ1 ++ B → C :: x0) Γ4 D) ; simpl in w ; repeat rewrite <- app_assoc in w ;
      simpl in w ; repeat rewrite <- app_assoc in w ; apply w.
    * exists (Γ0 ++ (Imp A0 C) :: (x ++ A :: x0) ++ (Imp B C) :: Γ2, D). repeat split ; auto ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc.
      epose (OrImpLRule_I _ _ _ _ Γ0 (x ++ A :: x0) Γ2). repeat rewrite <- app_assoc in o ; simpl in o ; apply o.
      epose (wkn_LI A (Γ0 ++ A0 → C :: x) _ D) ; simpl in w ; repeat rewrite <- app_assoc in w ;
      simpl in w ; repeat rewrite <- app_assoc in w ; apply w.
Qed.

Lemma ImpImpL_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (ImpImpLRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (ImpImpLRule [psw1;psw2] sw) * (@wkn_L A ps1 psw1) * (@wkn_L A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A :: (Imp B C) :: Γ1, (Imp A0 B)). exists (Γ2 ++ A :: C :: Γ1, D). repeat split ; try assumption.
  epose (ImpImpLRule_I _ _ _ _ (Γ2 ++ [A]) Γ1). repeat rewrite <- app_assoc in i ; simpl in i ; apply i.
- exists ((Γ2 ++ A :: x) ++ (Imp B C) :: Γ1, (Imp A0 B)). exists ((Γ2 ++ A :: x) ++ C :: Γ1, D). repeat split ; auto.
  epose (ImpImpLRule_I _ _ _ _ (Γ2 ++ A :: x) Γ1). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in i ; simpl in i ; apply i.
  1-2: repeat rewrite <- app_assoc ; apply wkn_LI.
- destruct x ; subst ; repeat rewrite app_nil_r ; simpl in e0 ; subst.
  + exists ((Γ0 ++ [A]) ++ (Imp B C) :: Γ1, (Imp A0 B)) . exists ((Γ0 ++ [A]) ++ C :: Γ1, D). repeat split ; try assumption.
     epose (ImpImpLRule_I _ _ _ _ (Γ0 ++ [A]) Γ1). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in i ; simpl in i ; apply i.
     1-2: repeat rewrite <- app_assoc ; simpl ; apply wkn_LI.
  + inversion e0 ; subst. exists (Γ0 ++ (Imp B C) :: x ++ A :: Γ3, (Imp A0 B)). exists (Γ0 ++ C :: x ++ A :: Γ3, D). repeat split ; try assumption.
     repeat rewrite <- app_assoc ; apply ImpImpLRule_I.
     1-2: epose (wkn_LI A (Γ0 ++ _ :: x) _ _) ; repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
Qed.

Lemma BoxImpL_app_wkn_L : forall s sw A ps1 ps2,
  (@wkn_L A s sw) ->
  (BoxImpLRule [ps1;ps2] s) ->
  (existsT2 psw1 psw2, (BoxImpLRule [psw1;psw2] sw) * (@wkn_L (unBox_formula A) ps1 psw1) * (@wkn_L A ps2 psw2)).
Proof.
intros s sw A ps1 ps2 wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (unBoxed_list Γ2 ++ (unBox_formula A) :: B :: unBoxed_list Γ1 ++ [Box A0], A0). exists (Γ2 ++ A :: B :: Γ1, C). repeat split ; try assumption.
  epose (@BoxImpLRule_I A0 B C (Γ2 ++ [A]) Γ1).
  simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; rewrite unBox_app_distrib in b ; simpl in b. rewrite <- app_assoc in b ; simpl in b. apply b ; auto.
- exists (unBoxed_list (Γ2 ++ A :: x) ++ B :: unBoxed_list Γ1 ++ [Box A0], A0). exists ((Γ2 ++ A :: x) ++ B :: Γ1, C). repeat split ; auto.
  3: repeat rewrite <- app_assoc ; apply wkn_LI.
  2: repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; apply wkn_LI.
  epose (@BoxImpLRule_I A0 B C (Γ2 ++ A :: x) Γ1).
  rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
- destruct x ; subst ; repeat rewrite app_nil_r ; simpl in e0 ; subst.
  + exists (unBoxed_list (Γ0 ++ [A]) ++ B :: unBoxed_list Γ1 ++ [Box A0], A0). exists (Γ0 ++ A :: B :: Γ1, C). repeat split ; auto.
     epose (@BoxImpLRule_I _ _ _ (Γ0 ++ [A]) Γ1).
     rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
     rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ; apply wkn_LI.
  + inversion e0 ; subst.
     exists (unBoxed_list Γ0 ++ B :: unBoxed_list (x ++ A :: Γ3) ++ [Box A0], A0). exists (Γ0 ++ B :: x ++ A :: Γ3, C). repeat split ; auto.
     epose (@BoxImpLRule_I _ _ _ Γ0 (x ++ A :: Γ3)).
     rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; rewrite unBox_app_distrib in b ; simpl in b ; repeat rewrite <- app_assoc in b ; simpl in b ; apply b.
     2: epose (wkn_LI A (Γ0 ++ _ :: x) _ _) ; repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
     epose (wkn_LI (unBox_formula A) (unBoxed_list Γ0 ++ B :: unBoxed_list x) _ _).
     repeat rewrite unBox_app_distrib ; simpl ; simpl in w ; repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in w ; simpl in w ; apply w.
Qed.

Lemma SLR_app_wkn_L : forall s sw A ps,
  (@wkn_L A s sw) ->
  (SLRRule [ps] s) ->
   (existsT2 psw, (SLRRule [psw] sw) * (@wkn_L (unBox_formula A) ps psw)).
Proof.
intros s sw A ps wkn RA. inversion RA. inversion wkn. subst.
inversion H. subst. repeat rewrite unBox_app_distrib.
repeat rewrite <- app_assoc. exists (unBoxed_list Γ0 ++ (unBox_formula A) :: unBoxed_list Γ1 ++ [Box A0], A0).
repeat split ; try assumption.
epose (@SLRRule_I _ (Γ0 ++ A :: Γ1)). repeat rewrite unBox_app_distrib in s ; simpl in s ; repeat rewrite <- app_assoc in s ; simpl in s ; apply s ; auto.
Qed.

(* Now we can prove that weakening is height-preserving admissible. *)

Theorem G4iSL_wkn_L : forall (k : nat) s
        (D0 : derrec G4iSL_rules (fun _ => False) s),
        k = (derrec_height D0) ->
          (forall sw A, ((@wkn_L A s sw) ->
          existsT2 (D1 : derrec G4iSL_rules (fun _ => False) sw),
          derrec_height D1 <= k)).
Proof.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (s :(list (MPropF) * MPropF))
  (D0 : derrec G4iSL_rules (fun _ : (list (MPropF) * MPropF) => False) s),
x = derrec_height D0 ->
(forall sw A,
wkn_L A s sw ->
(existsT2
  D1 : derrec G4iSL_rules
         (fun _ : (list (MPropF) * MPropF) => False) sw,
  derrec_height D1 <= x)))).
apply s. intros n IH. clear s.

assert (DersNil: dersrec (G4iSL_rules) (fun _ : (list (MPropF) * MPropF) => False) []). apply dersrec_nil.

(* Now we do the actual proof-theoretical work. *)
intros s0 D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- intros hei sw A wkn. inversion f.
(* D0 ends with an application of rule *)
- intros hei sw A wkn. inversion wkn. inversion g ; simpl.
  (* IdP *)
  * inversion H1 ; subst. inversion H5 ; subst. simpl. assert (InT (# P) (Γ0 ++ A :: Γ1)).
    assert (InT (# P) (Γ0 ++ Γ1)). rewrite <- H0 ; apply InT_or_app ; right ; apply InT_eq.
    apply InT_or_app. apply InT_app_or in H ; destruct H ; auto ; right ; apply InT_cons ; auto.
    apply InT_split in H. destruct H. destruct s ; subst. rewrite e. pose (IdPRule_I P x x0). apply IdP in i.
    epose (@derI _ _ _ _ _ i d). exists d0. simpl. lia.
  (* BotL *)
  * inversion H1 ; subst. inversion H5 ; subst. simpl. assert (InT ⊥ (Γ0 ++ A :: Γ1)).
    assert (InT ⊥ (Γ0 ++ Γ1)). rewrite <- H0 ; apply InT_or_app ; right ; apply InT_eq.
    apply InT_or_app. apply InT_app_or in H ; destruct H ; auto ; right ; apply InT_cons ; auto.
    apply InT_split in H. destruct H. destruct s ; subst. rewrite e. pose (BotLRule_I x x0 A0). apply BotL in b.
    epose (@derI _ _ _ _ _ b d). exists d0. simpl. lia.
  (* AndR *)
  * inversion H1 ; subst. inversion H5 ; subst. pose (AndR_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. inversion d ; subst. remember[(Γ0 ++ Γ1, A1); (Γ0 ++ Γ1, B)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. remember [(Γ0 ++ Γ1, B)] as ps''. destruct d0.
    inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ0 ++ Γ1, A1) d E1 x A w0).
    destruct s.
    assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E3: derrec_height d0 = derrec_height d0). auto.
    pose (IH (derrec_height d0) E2 (Γ0 ++ Γ1, B) d0 E3 x0 A w).
    destruct s.
    pose (dlCons x2 d1). pose (dlCons x1 d2). apply AndR in a.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1, And A1 B) a).
    pose (d4 d3). exists d5.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia.
    reflexivity.
  (* AndL *)
  * inversion H1. subst. inversion H5. subst. pose (AndL_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. remember [(Γ2 ++ A1 :: B :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (derrec_height d)). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ A1 :: B :: Γ3, A0) d E1 x A w).
    destruct s.
    pose (dlCons x0 d0). apply AndL in a.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0) a).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia.
    reflexivity.
  (* OrR1 *)
  * inversion H1. subst. inversion H5. subst. pose (OrR1_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. remember[(Γ0 ++ Γ1, A1)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (derrec_height d)). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ0 ++ Γ1, A1) d E1 x A w).
    destruct s.
    pose (dlCons x0 d0). apply OrR1 in o.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, Or A1 B) o).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia.
    reflexivity.
  (* OrR2 *)
  * inversion H1. subst. inversion H5. subst. pose (OrR2_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. remember[(Γ0 ++ Γ1, B)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (derrec_height d)). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ0 ++ Γ1, B) d E1 x A w).
    destruct s.
    pose (dlCons x0 d0). apply OrR2 in o.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, Or A1 B) o).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia.
    reflexivity.
  (* OrL *)
  * inversion H1. subst. inversion H5. subst. pose (OrL_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. inversion d. remember [(Γ2 ++ A1 :: Γ3, A0); (Γ2 ++ B :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. remember [(Γ2 ++ B :: Γ3, A0)] as ps''. destruct d0.
    inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E(Γ2 ++ A1 :: Γ3, A0) d E1 x A w0).
    destruct s.
    assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E3: derrec_height d0 = derrec_height d0). auto.
    pose (IH (derrec_height d0) E2(Γ2 ++ B :: Γ3, A0) d0 E3 x0 A w).
    destruct s.
    pose (dlCons x2 d1). pose (dlCons x1 d2). apply OrL in o.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1, A0) o).
    pose (d4 d3). exists d5.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia.
    reflexivity.
  (* ImpR *)
  * inversion H1. subst. inversion H5. subst. pose (ImpR_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember[(Γ2 ++ A1 :: Γ3, B)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ A1 :: Γ3, B) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply ImpR in i.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, Imp A1 B) i).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia.  reflexivity.
  (* AtomImpL1 *)
  * inversion H1. subst. inversion H5. subst. pose (AtomImpL1_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ # P :: Γ3 ++ A1 :: Γ4, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ # P :: Γ3 ++ A1 :: Γ4, A0) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply AtomImpL1 in a.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0)  a).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia. reflexivity.
  (* AtomImpL2 *)
  * inversion H1. subst. inversion H5. subst. pose (AtomImpL2_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ A1 :: Γ3 ++ # P :: Γ4, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ A1 :: Γ3 ++ # P :: Γ4, A0) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply AtomImpL2 in a.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0)  a).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia. reflexivity.
  (* AndImpL *)
  * inversion H1. subst. inversion H5. subst. pose (AndImpL_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ Imp A1 (Imp B C) :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ Imp A1 (Imp B C) :: Γ3, A0) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply AndImpL in a.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0)  a).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia. reflexivity.
  (* OrImpL *)
  * inversion H1. subst. inversion H5. subst. pose (OrImpL_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(Γ2 ++ Imp A1 C :: Γ3 ++ Imp B C :: Γ4, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ Imp A1 C :: Γ3 ++ Imp B C :: Γ4, A0) d E1 x A w).
    destruct s. pose (dlCons x0 d0). apply OrImpL in o.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, A0)  o).
    pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia. reflexivity.
  (* ImpImpL *)
  * inversion H1. subst. inversion H5. subst. pose (ImpImpL_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. inversion d. remember [(Γ2 ++ Imp B C :: Γ3, Imp A1 B); (Γ2 ++ C :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. remember [(Γ2 ++ C :: Γ3, A0)] as ps''. destruct d0.
    inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (Γ2 ++ Imp B C :: Γ3, Imp A1 B) d E1 x A w0).
    destruct s.
    assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E3: derrec_height d0 = derrec_height d0). auto.
    pose (IH (derrec_height d0) E2 (Γ2 ++ C :: Γ3, A0) d0 E3 x0 A w).
    destruct s.
    pose (dlCons x2 d1). pose (dlCons x1 d2). apply ImpImpL in i.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1, A0) i).
    pose (d4 d3). exists d5.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia.
    reflexivity.
  (* BoxImpL *)
  * inversion H1 ; subst. inversion H5 ; subst. pose (BoxImpL_app_wkn_L wkn H1). repeat destruct s.
    repeat destruct p. remember [(unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ [Box A1], A1); (Γ2 ++ B :: Γ3, A0)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst. remember [(Γ2 ++ B :: Γ3, A0)] as ps''. destruct d0.
    inversion Heqps''. inversion Heqps''. subst. simpl. simpl in IH.
    assert (E: derrec_height d < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E1: derrec_height d = derrec_height d). auto.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (unBoxed_list Γ2 ++ B :: unBoxed_list Γ3 ++ [Box A1], A1) d E1 x (unBox_formula A) w0).
    destruct s.
    assert (E2: derrec_height d0 < S (Init.Nat.max (derrec_height d) (derrec_height d0))). lia.
    assert (E3: derrec_height d0 = derrec_height d0). auto.
    pose (IH (derrec_height d0) E2 (Γ2 ++ B :: Γ3, A0) d0 E3 x0 A w).
    destruct s.
    pose (dlCons x2 d1). pose (dlCons x1 d2). apply BoxImpL in b.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x;x0]) (Γ0 ++ A :: Γ1, A0) b).
    pose (d4 d3). exists d5.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia.
    reflexivity.
  (* SLR *)
  * inversion H1. subst. inversion H5 ; subst. pose (SLR_app_wkn_L wkn H1). destruct s.
    repeat destruct p. remember [(unBoxed_list (Γ0 ++ Γ1) ++ [Box A1], A1)] as ps'. destruct d.
    inversion Heqps'. inversion Heqps'. subst.
    assert (E: derrec_height d < S (derrec_height d)). auto.
    assert (E1: derrec_height d = derrec_height d). auto. simpl in IH.
    rewrite dersrec_height_nil in IH. 2: reflexivity. rewrite Nat.max_0_r in IH.
    pose (IH (derrec_height d) E (unBoxed_list (Γ0 ++ Γ1) ++ [Box A1], A1) d E1 x (unBox_formula A) w).
    destruct s0. pose (dlCons x0 d0). apply SLR in s.
    pose (derI (rules:=G4iSL_rules) (prems:=fun _ : (list (MPropF) * MPropF) => False)
    (ps:=[x]) (Γ0 ++ A :: Γ1, Box A1) s). pose (d2 d1). exists d3.
    simpl. repeat rewrite dersrec_height_nil. repeat rewrite Nat.max_0_r. lia. reflexivity.
Qed.

Theorem G4iSL_adm_wkn_L :  forall s, (derrec G4iSL_rules (fun _ => False) s) ->
          (forall sw A, (@wkn_L A s sw) ->
           (derrec G4iSL_rules (fun _ => False) sw)).
Proof.
intros.
assert (J0: derrec_height X = derrec_height X). auto.
pose (G4iSL_wkn_L X J0 H). destruct s0. auto.
Qed.


Theorem G4iSL_list_wkn_L : forall (k : nat) Γ0 Γ1 A
        (D0 : derrec G4iSL_rules (fun _ => False) (Γ0 ++ Γ1, A)),
        k = (derrec_height D0) ->
          (forall l, existsT2 (D1 : derrec G4iSL_rules (fun _ => False) (Γ0 ++ l ++ Γ1,A)),
          derrec_height D1 <= k).
Proof.
intros. induction l.
- simpl. exists D0. lia.
- simpl. destruct IHl.
  assert (E: derrec_height x = derrec_height x). reflexivity.
  assert (H0: wkn_L a (Γ0 ++ l ++ Γ1, A) (Γ0 ++ a :: l ++ Γ1, A)). apply wkn_LI.
  pose (@G4iSL_wkn_L (derrec_height x) (Γ0 ++ l ++ Γ1, A) x E (Γ0 ++ a :: l ++ Γ1, A) a H0).
  destruct s. exists x0. lia.
Qed.

