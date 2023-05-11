Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import G4iSLT_calc.
Require Import G4iSLT_list_lems.
Require Import G4iSLT_dec.
Require Import G4iSLT_exch.
Require Import G4iSLT_wkn.
Require Import G4iSLT_inv_AndR_AndL.
Require Import G4iSLT_inv_OrL.
Require Import G4iSLT_inv_AtomImpL.
Require Import G4iSLT_inv_AndImpL.
Require Import G4iSLT_inv_OrImpL.
Require Import G4iSLT_inv_ImpImpL_R.
Require Import G4iSLT_inv_ImpImpL_L.
Require Import G4iSLT_inv_ImpR.
Require Import G4iSLT_inv_BoxImpL_R.

Set Implicit Arguments.

(* Next is the definition for contraction of one formula on the left.
Note that while the leftmost occurrence of the formula is kept,
if we have exchange for our calculus it amounts to the same to keep
the rightmost formula. *)

Inductive ctr_L (fml : MPropF) : relationT Seq :=
  | ctr_LI Γ0 Γ1 Γ2 A : ctr_L fml
        (Γ0 ++ fml :: Γ1 ++ fml :: Γ2, A) (Γ0 ++ fml :: Γ1 ++ Γ2, A).

(* The following lemmas make sure that if a rule is applied on a sequent s with
premises ps, then the same rule is applicable on a sequent sc which is a contracted
version of s, with some premises psc that are such that they are either the same premises
(in case the contracted formula was weakened) or contracted versions of ps. *)

Lemma AndR_app_ctr_L : forall s sc A ps1 ps2,
  (@ctr_L A s sc) ->
  (AndRRule [ps1;ps2] s) ->
  (existsT2 psc1 psc2, (AndRRule [psc1;psc2] sc) * (@ctr_L A ps1 psc1) * (@ctr_L A ps2 psc2)).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1 ++ Γ2, A0). exists (Γ0 ++ A :: Γ1 ++ Γ2, B). repeat split.
Qed.

Lemma AndL_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (AndLRule [ps] s) ->
  ((existsT2 psc, (AndLRule [psc] sc) * (@ctr_L A ps psc))
  +
  (existsT2 B C invps invpsc1 invpsc2,
                       (A = And B C) *
                       (AndLRule [invps] ps) *
                       (@ctr_L B invps invpsc1) *
                       (@ctr_L C invpsc1 invpsc2) *
                       (AndLRule [invpsc2] sc))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B. exists (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4, C).
  exists (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: B :: Γ3 ++ Γ4, C). repeat split.
  pose (AndLRule_I A0 B  C (Γ2 ++ A0 :: B :: Γ3) Γ4). repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
  pose (ctr_LI A0 Γ2 (B :: Γ3) (B :: Γ4) C). simpl in c ; auto.
  pose (ctr_LI B (Γ2 ++ [A0]) Γ3 Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right.
    exists A0. exists B. exists (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4, C).
    exists (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: B :: Γ3 ++ Γ4, C). repeat split.
    pose (AndLRule_I A0 B  C (Γ2 ++ A0 :: B :: Γ3) Γ4). repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
    pose (ctr_LI A0 Γ2 (B :: Γ3) (B :: Γ4) C). simpl in c ; auto.
    pose (ctr_LI B (Γ2 ++ [A0]) Γ3 Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. right.
       exists A0. exists B. exists (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4, C).
       exists (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: B :: Γ3 ++ Γ4, C).
       repeat split.
       pose (ctr_LI A0 Γ2 (B :: Γ3) (B :: Γ4) C). simpl in c ; auto.
       pose (ctr_LI B (Γ2 ++ [A0]) Γ3 Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists (Γ2 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ1, C).
         exists (Γ2 ++ A0 :: B :: Γ3 ++ B :: Γ1, C). exists (Γ2 ++ A0 :: B :: Γ3 ++ Γ1, C).
         repeat split.
         pose (AndLRule_I A0 B  C (Γ2 ++ A0 :: B :: Γ3) Γ1). repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
         pose (ctr_LI A0 Γ2 (B :: Γ3) (B :: Γ1) C). simpl in c ; auto.
         pose (ctr_LI B (Γ2 ++ [A0]) Γ3 Γ1 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: B :: Γ1, C). repeat split.
         pose (AndLRule_I A0 B  C (Γ2 ++ m0 :: Γ3 ++ x0) Γ1).
         repeat rewrite <- app_assoc in a ; simpl in a ;  repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists (Γ2 ++ A0 :: B :: x ++ A0 :: B :: Γ4, C).
         exists (Γ2 ++ A0 :: B :: x ++ B :: Γ4, C). exists (Γ2 ++ A0 :: B :: x ++ Γ4, C).
         repeat split.
         pose (ctr_LI A0 Γ2 (B :: x) (B :: Γ4) C). simpl in c ; auto.
         pose (ctr_LI B (Γ2 ++ [A0]) x Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: x ++ A0 :: B :: x0 ++ Γ4, C). repeat split.
         pose (AndLRule_I A0 B  C (Γ2 ++ m :: x) (x0 ++ Γ4)). repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
         pose (ctr_LI m Γ2 (x ++ A0 :: B :: x0) Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
- destruct x.
  * simpl in e0. inversion e0. subst. right.
    exists A0. exists B. exists (Γ0 ++ A0 :: B :: Γ3 ++ A0 :: B :: Γ4, C).
    exists (Γ0 ++ A0 :: B :: Γ3 ++ B :: Γ4, C). exists (Γ0 ++ A0 :: B :: Γ3 ++ Γ4, C).
    repeat split.
    pose (AndLRule_I A0 B  C (Γ0 ++ A0 :: B :: Γ3) Γ4). repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
    pose (ctr_LI A0 Γ0 (B :: Γ3) (B :: Γ4) C). simpl in c ; auto.
    pose (ctr_LI B (Γ0 ++ [A0]) Γ3 Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    repeat rewrite <- app_assoc. simpl. apply AndLRule_I.
  * simpl in e0. inversion e0. subst. left. repeat rewrite <- app_assoc. simpl.
    exists (Γ0 ++ A0 :: B :: x ++ A :: Γ3 ++ Γ4, C). repeat split.
    pose (ctr_LI A (Γ0 ++ A0 :: B :: x) Γ3 Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
Qed.

Lemma OrR1_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (OrR1Rule [ps] s) ->
  (existsT2 psc, (OrR1Rule [psc] sc) * (@ctr_L A ps psc)).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1 ++ Γ2, A0). repeat split.
Qed.

Lemma OrR2_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (OrR2Rule [ps] s) ->
  (existsT2 psc, (OrR2Rule [psc] sc) * (@ctr_L A ps psc)).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. exists (Γ0 ++ A :: Γ1 ++ Γ2, B). repeat split.
Qed.

Lemma OrL_app_ctr_L : forall s sc A ps1 ps2,
  (@ctr_L A s sc) ->
  (OrLRule [ps1;ps2] s) ->
  ((existsT2 psc1 psc2, (OrLRule [psc1;psc2] sc) *
                       (@ctr_L A ps1 psc1) *
                       (@ctr_L A ps2 psc2))
  +
  (existsT2 B C invps11 invps12 invps21 invps22 invpsc11 invpsc22,
                       (A = Or B C) *
                       (OrLRule [invps11;invps12] ps1) *
                       (OrLRule [invps21;invps22] ps2) *
                       (@ctr_L B invps11 invpsc11) *
                       (@ctr_L C invps22 invpsc22) *
                       (OrLRule [invpsc11;invpsc22] sc))).
Proof.
intros s sc A ps1 ps2 ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B. exists (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ4, C).
  exists (Γ2 ++ A0 :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ B :: Γ3 ++ A0 :: Γ4, C).
  exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: Γ3 ++  Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
  repeat split.
  pose (OrLRule_I A0 B  C (Γ2 ++ A0 :: Γ3) Γ4). repeat rewrite <- app_assoc in o ; simpl in o ;  auto.
  pose (OrLRule_I A0 B  C (Γ2 ++ B :: Γ3) Γ4). repeat rewrite <- app_assoc in o ; simpl in o ;  auto.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right.
    exists A0. exists B. exists (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ4, C).
    exists (Γ2 ++ A0 :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ B :: Γ3 ++ A0 :: Γ4, C).
    exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: Γ3 ++  Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
    repeat split.
    pose (OrLRule_I A0 B  C (Γ2 ++ A0 :: Γ3) Γ4). repeat rewrite <- app_assoc in o ; simpl in o ;  auto.
    pose (OrLRule_I A0 B  C (Γ2 ++ B :: Γ3) Γ4). repeat rewrite <- app_assoc in o ; simpl in o ;  auto.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. right.
       exists A0. exists B. exists (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ4, C).
       exists (Γ2 ++ B :: Γ3 ++ A0 :: Γ4, C). exists (Γ2 ++ A0 :: Γ3 ++ B :: Γ4, C).
       exists (Γ2 ++ B :: Γ3 ++ B :: Γ4, C). exists (Γ2 ++ A0 :: Γ3 ++  Γ4, C). exists (Γ2 ++ B :: Γ3 ++ Γ4, C).
       repeat split.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists (Γ2 ++ A0 :: Γ3 ++ A0 :: Γ1, C). exists (Γ2 ++ B :: Γ3 ++ A0 :: Γ1, C).
         exists (Γ2 ++ A0 :: Γ3 ++ B :: Γ1, C). exists (Γ2 ++ B :: Γ3 ++ B :: Γ1, C).
         exists (Γ2 ++ A0 :: Γ3 ++  Γ1, C). exists (Γ2 ++ B :: Γ3 ++ Γ1, C). repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: Γ1, C).  exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ B :: Γ1, C). repeat split.
           pose (OrLRule_I A0 B C (Γ2 ++ m0 :: Γ3 ++ x0) Γ1). repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists (Γ2 ++ A0 :: x ++ A0 :: Γ4, C).
         exists (Γ2 ++ B :: x ++ A0 :: Γ4, C). exists (Γ2 ++ A0 :: x ++ B :: Γ4, C).
         exists (Γ2 ++ B :: x ++ B :: Γ4, C). exists (Γ2 ++ A0 :: x ++  Γ4, C). exists (Γ2 ++ B :: x ++ Γ4, C). repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: x ++ A0 :: x0 ++ Γ4, C).  exists (Γ2 ++ m :: x ++ B :: x0 ++ Γ4, C). repeat split.
         pose (OrLRule_I A0 B  C (Γ2 ++ m :: x) (x0 ++ Γ4)). repeat rewrite <- app_assoc in o ; simpl in o ;  auto.
         pose (ctr_LI m Γ2 (x ++ A0 :: x0) Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
         pose (ctr_LI m Γ2 (x ++ B :: x0) Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
- destruct x.
  * simpl in e0. inversion e0. subst. right. repeat rewrite <- app_assoc. simpl.
    exists A0. exists B. exists (Γ0 ++ A0 :: Γ3 ++ A0 :: Γ4, C).
    exists (Γ0 ++ A0 :: Γ3 ++ B :: Γ4, C). exists (Γ0 ++ B :: Γ3 ++ A0 :: Γ4, C).
    exists (Γ0 ++ B :: Γ3 ++ B :: Γ4, C). exists(Γ0 ++ A0 :: Γ3 ++ Γ4, C). exists(Γ0 ++ B :: Γ3 ++ Γ4, C).
    repeat split.
    pose (OrLRule_I A0 B  C (Γ0 ++ A0 :: Γ3) Γ4). repeat rewrite <- app_assoc in o ; simpl in o ;  auto.
    pose (OrLRule_I A0 B  C (Γ0 ++ B :: Γ3) Γ4). repeat rewrite <- app_assoc in o ; simpl in o ;  auto.
  * simpl in e0. inversion e0. subst. left. repeat rewrite <- app_assoc. simpl.
    exists (Γ0 ++ A0 :: x ++ A :: Γ3 ++ Γ4, C). exists (Γ0 ++ B :: x ++ A :: Γ3 ++ Γ4, C). repeat split.
    pose (ctr_LI A (Γ0 ++ A0 :: x) Γ3 Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    pose (ctr_LI A (Γ0 ++ B :: x) Γ3 Γ4 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
Qed.

Lemma ImpR_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (ImpRRule [ps] s) ->
  (existsT2 psc, (ImpRRule [psc] sc) * (@ctr_L A ps psc)).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- exists (Γ2 ++ A0 :: A :: Γ3 ++ Γ4, B). repeat split ; try assumption.
  rewrite cons_single. rewrite cons_single with (v:=A0). rewrite app_assoc. rewrite app_assoc with (l:=Γ2). apply ctr_LI.
- destruct x ; subst.
  * simpl in e0. subst. repeat rewrite <- app_assoc. simpl.
     exists (Γ2 ++ A0 :: A :: Γ3 ++ Γ4, B). repeat split.
     pose (ctr_LI A (Γ2 ++ [A0]) Γ3 Γ4 B). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * simpl in e0. inversion e0. subst. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
    + repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ m :: Γ3 ++ A0 :: Γ4, B). repeat split.
       pose (ImpRRule_I A0 B (Γ2 ++ m :: Γ3) Γ4). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
       pose (ctr_LI m Γ2 (Γ3 ++[A0]) Γ4 B). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    + destruct x0.
       { simpl in e1. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: Γ3 ++ A0 :: Γ4, B). repeat split.
         pose (ImpRRule_I A0 B (Γ2 ++ m :: Γ3) Γ4). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
         pose (ctr_LI m Γ2 (Γ3 ++[A0]) Γ4 B). repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
       { simpl in e1. inversion e1. subst. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ A0 :: Γ1, B). repeat split.
         pose (ImpRRule_I A0 B (Γ2 ++ m0 :: Γ3 ++ x0) Γ1). repeat rewrite <- app_assoc in i ; simpl in i ; 
         repeat rewrite <- app_assoc in i ; simpl in i ;  auto. }
    + repeat rewrite <- app_assoc. simpl.
       exists (Γ2 ++ m :: x ++ A0 :: x0 ++ Γ4, B). split.
       pose (ImpRRule_I A0 B (Γ2 ++ m :: x) (x0 ++Γ4)). repeat rewrite <- app_assoc in i ; simpl in i ;  auto.
       pose (ctr_LI m Γ2 (x ++ A0 :: x0) Γ4 B). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
- repeat rewrite <- app_assoc. exists (Γ0 ++ A0 :: x ++ A :: Γ3 ++ Γ4, B). split. apply ImpRRule_I.
   pose (ctr_LI A (Γ0 ++ A0 ::x) Γ3 Γ4 B). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
Qed.

Lemma AtomImpL1_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (AtomImpL1Rule [ps] s) ->
  ((existsT2 psc, (AtomImpL1Rule [psc] sc) * (@ctr_L A ps psc))
  +
  (existsT2 P B invps invpsc,
                       (A = Imp (# P) B) *
                       ((AtomImpL1Rule [invps] ps) + (AtomImpL2Rule [invps] ps)) *
                       (@ctr_L B invps invpsc) *
                       ((AtomImpL1Rule [invpsc] sc) + (AtomImpL2Rule [invpsc] sc)))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply list_split_form in H1. destruct H1.
repeat destruct s ; repeat destruct p ; subst.
- apply list_split_form in e. destruct e. repeat destruct s ; repeat destruct p ; subst.
  * inversion e0.
  * left. exists (Γ0 ++ # P :: Γ1 ++ A0 :: x0 ++ Γ5, C). split. repeat rewrite <- app_assoc. simpl. apply AtomImpL1Rule_I.
    pose (ctr_LI (# P) Γ0 (Γ1 ++ A0 :: x0) Γ5 C). repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * repeat destruct s. repeat destruct p ; subst. left. exists (Γ0 ++ # P :: Γ4 ++ x ++ A0 :: Γ2, C). split.
    pose (AtomImpL1Rule_I P A0 C Γ0 (Γ4 ++ x) Γ2). repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
    pose (ctr_LI (# P) Γ0 Γ4 (x ++ A0 :: Γ2) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
- apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
  * right. exists P. exists A0. exists (Γ0 ++ # P :: Γ1 ++ A0 :: Γ4 ++ A0 :: Γ5, C). exists (Γ0 ++ # P :: Γ1 ++ A0 :: Γ4 ++ Γ5, C).
    repeat split ; repeat rewrite <- app_assoc ; simpl ; auto. left.
    pose (AtomImpL1Rule_I P A0 C Γ0 (Γ1 ++ A0 :: Γ4) Γ5). repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
    pose (ctr_LI A0 (Γ0 ++ # P :: Γ1) Γ4 Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    left. apply AtomImpL1Rule_I.
  * repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ # P :: Γ1 ++ A0 :: x1 ++ A :: Γ4 ++ Γ5, C). split.
    apply AtomImpL1Rule_I.
    pose (ctr_LI A (Γ0 ++ # P :: Γ1 ++ A0 :: x1) Γ4 Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * repeat destruct s ; repeat destruct p ; subst ; repeat rewrite <- app_assoc ; simpl.
     apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
    + right. exists P. exists A0. exists (Γ0 ++ # P :: x0 ++ A0 :: x ++ A0 :: Γ2, C). exists (Γ0 ++ # P :: x0 ++ A0 :: x ++ Γ2, C).
        repeat split ; repeat rewrite <- app_assoc ; simpl ; auto. left. apply AtomImpL1Rule_I.
        pose (ctr_LI A0 (Γ0 ++ # P :: x0) x Γ2 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
        left. apply AtomImpL1Rule_I.
    + repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ # P :: (x0 ++ A :: x) ++ A0 :: x2 ++ Γ5, C). split.
        pose (AtomImpL1Rule_I P A0 C Γ0 (x0 ++ A :: x) (x2 ++ Γ5)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
        pose (ctr_LI A (Γ0 ++ # P :: x0) (x ++ A0 :: x2) Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    +  repeat destruct s ; repeat destruct p ; subst. repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ # P :: (x0 ++ A :: Γ4 ++ x1) ++ A0 :: Γ2, C). split.
        pose (AtomImpL1Rule_I P A0 C Γ0 (x0 ++ A :: Γ4 ++ x1) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ; repeat rewrite <- app_assoc in a ; auto.
        pose (ctr_LI A (Γ0 ++ # P :: x0) Γ4 (x1 ++ A0 :: Γ2) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
- repeat destruct  s ; repeat destruct p ; subst. apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
  * left. exists (Γ3 ++ # P :: (x ++ Γ1) ++ A0 :: Γ2, C). repeat split.
    pose (AtomImpL1Rule_I P A0 C Γ3 (x ++ Γ1) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
    pose (ctr_LI (# P) Γ3 x (Γ1 ++ A0 :: Γ2) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * repeat rewrite <- app_assoc ; simpl. apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
    + right. exists P. exists A0. exists (Γ3 ++ A0 :: x ++ # P :: Γ1 ++ A0 :: Γ2, C). exists (Γ3 ++ A0 :: x ++ # P :: Γ1 ++ Γ2, C).
        repeat split ; repeat rewrite <- app_assoc ; simpl ; auto. right. apply AtomImpL2Rule_I.
        pose (ctr_LI A0 Γ3 (x ++ # P :: Γ1) Γ2 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
        right. apply AtomImpL2Rule_I.
    + repeat rewrite <- app_assoc ; simpl. left. exists ((Γ3 ++ A :: x) ++ # P :: Γ1 ++ A0 :: x2 ++ Γ5, C). split.
       pose (AtomImpL1Rule_I P A0 C (Γ3 ++ A :: x) Γ1 (x2 ++ Γ5)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
       pose (ctr_LI A Γ3 (x ++ # P :: Γ1 ++ A0 :: x2) Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    + repeat destruct s ; repeat destruct p ; subst. repeat rewrite <- app_assoc ; simpl. left. exists ((Γ3 ++ A :: x) ++ # P :: (x1 ++ x0) ++ A0 :: Γ2, C). split.
       pose (AtomImpL1Rule_I P A0 C (Γ3 ++ A :: x) (x1 ++ x0) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
       pose (ctr_LI A Γ3 (x ++ # P :: x1) (x0 ++ A0 :: Γ2) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * repeat destruct s ; repeat destruct p ; subst. left. exists ((Γ3 ++ A :: Γ4 ++ x0) ++ # P :: Γ1 ++ A0 :: Γ2, C). repeat split.
     pose (AtomImpL1Rule_I P A0 C (Γ3 ++ A :: Γ4 ++ x0) Γ1 Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
     pose (ctr_LI A Γ3 Γ4 (x0 ++ # P :: Γ1 ++ A0 :: Γ2) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
Qed.

Lemma AtomImpL2_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (AtomImpL2Rule [ps] s) ->
  ((existsT2 psc, ((AtomImpL1Rule [psc] sc) + (AtomImpL2Rule [psc] sc)) * (@ctr_L A ps psc))
  +
  (existsT2 P B invps invpsc,
                       (A = Imp (# P) B) *
                       ((AtomImpL1Rule [invps] ps) + (AtomImpL2Rule [invps] ps)) *
                       (@ctr_L B invps invpsc) *
                       ((AtomImpL1Rule [invpsc] sc) + (AtomImpL2Rule [invpsc] sc)))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst.
inversion H. subst. apply list_split_form in H1. destruct H1.
repeat destruct s ; repeat destruct p ; subst.
- apply list_split_form in e. destruct e. repeat destruct s ; repeat destruct p ; subst.
  * inversion e0.
  * right. exists P. exists A0. exists ((Γ0 ++ A0 :: Γ1) ++ # P :: x0 ++ A0 :: Γ5, C). exists (Γ0 ++ A0 :: Γ1 ++ # P :: x0 ++ Γ5, C).  repeat split.
    left. pose (AtomImpL1Rule_I P A0 C (Γ0 ++ A0 :: Γ1) x0 Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
    pose (ctr_LI A0 Γ0 (Γ1 ++ # P :: x0) Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    right. repeat rewrite <- app_assoc. apply AtomImpL2Rule_I.
  * repeat destruct s. repeat destruct p ; subst. right. exists P. exists A0. exists ((Γ0 ++ A0 :: Γ4) ++ A0 :: x ++ # P :: Γ2, C).
    exists (Γ0 ++ A0 :: (Γ4 ++ x) ++ # P :: Γ2, C).  repeat split. right.
    pose (AtomImpL2Rule_I P A0 C (Γ0 ++ A0 :: Γ4) x Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
    repeat rewrite <- app_assoc ; apply ctr_LI. right.
    pose (AtomImpL2Rule_I P A0 C Γ0 (Γ4 ++ x) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
- apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
  * left. repeat rewrite <- app_assoc ; simpl. exists (Γ0 ++ A0 :: Γ1 ++ # P :: Γ4 ++ Γ5, C). split. right. apply AtomImpL2Rule_I.
    pose (ctr_LI (# P) (Γ0 ++ A0 :: Γ1) Γ4 Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ A0 :: Γ1 ++ # P :: x1 ++ A :: Γ4 ++ Γ5, C). split. right. apply AtomImpL2Rule_I.
    pose (ctr_LI A (Γ0 ++ A0 :: Γ1 ++ # P :: x1) Γ4 Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * repeat destruct s ; repeat destruct p ; subst ; repeat rewrite <- app_assoc ; simpl.
     apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
    + left. exists (Γ0 ++ A0 :: x0 ++ # P :: x ++ Γ2, C). split. right. apply AtomImpL2Rule_I.
       pose (ctr_LI (# P) (Γ0 ++ A0 :: x0) x Γ2 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    + repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ A0 :: (x0 ++ A :: x) ++ # P :: x2 ++ Γ5, C). split. right.
       pose (AtomImpL2Rule_I P A0 C Γ0 (x0 ++ A :: x) (x2 ++ Γ5)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
       pose (ctr_LI A (Γ0 ++ A0 :: x0) (x ++ # P :: x2) Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    + repeat destruct s ; repeat destruct p ; subst. repeat rewrite <- app_assoc ; simpl. left. exists (Γ0 ++ A0 :: (x0 ++ A :: Γ4 ++ x1) ++ # P :: Γ2, C). split. right.
       pose (AtomImpL2Rule_I P A0 C Γ0 (x0 ++ A :: Γ4 ++ x1) Γ2). repeat rewrite <- app_assoc ; simpl  ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
       pose (ctr_LI A (Γ0 ++ A0 :: x0) Γ4 (x1 ++ # P :: Γ2) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
- repeat destruct  s ; repeat destruct p ; subst. apply list_split_form in e0. destruct e0. repeat destruct s ; repeat destruct p ; subst.
  * right. exists P. exists A0. repeat rewrite <- app_assoc ; simpl. exists (Γ3 ++ A0 :: (x ++ A0 :: Γ1) ++ # P :: Γ2, C). 
    exists (Γ3 ++ A0 :: (x ++ Γ1) ++ # P :: Γ2, C). repeat split. right.
    pose (AtomImpL2Rule_I P A0 C Γ3 (x ++ A0 :: Γ1) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
    repeat rewrite <- app_assoc ; apply ctr_LI. right.
    pose (AtomImpL2Rule_I P A0 C Γ3 (x ++ Γ1) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
  * repeat rewrite <- app_assoc ; simpl. apply list_split_form in e1. destruct e1. repeat destruct s ; repeat destruct p ; subst.
    +  left. exists (Γ3 ++ # P :: x ++ A0 :: Γ1 ++ Γ2, C). split. left. apply AtomImpL1Rule_I.
        pose (ctr_LI (# P) Γ3 (x ++ A0 :: Γ1) Γ2 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    +  repeat rewrite <- app_assoc ; simpl. left. exists ((Γ3 ++ A :: x) ++ A0 :: Γ1 ++ # P :: x2 ++ Γ5, C). split. right.
        pose (AtomImpL2Rule_I P A0 C (Γ3 ++ A :: x) Γ1 (x2 ++ Γ5)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
        pose (ctr_LI A Γ3 (x ++ A0 :: Γ1 ++ # P :: x2) Γ5 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    +  repeat destruct s ; repeat destruct p ; subst. repeat rewrite <- app_assoc ; simpl. left. exists ((Γ3 ++ A :: x) ++ A0 :: (x1 ++ x0) ++ # P :: Γ2, C). split. right.
        pose (AtomImpL2Rule_I P A0 C (Γ3 ++ A :: x) (x1 ++ x0) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
        pose (ctr_LI A Γ3 (x ++ A0 :: x1) (x0 ++ # P :: Γ2) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * repeat destruct s ; repeat destruct p ; subst. left. exists ((Γ3 ++ A :: Γ4 ++ x0) ++ A0 :: Γ1 ++ # P :: Γ2, C). split. right.
    pose (AtomImpL2Rule_I P A0 C (Γ3 ++ A :: Γ4 ++ x0) Γ1 Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
    repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc. apply ctr_LI.
Qed.

Lemma AndImpL_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (AndImpLRule [ps] s) ->
  ((existsT2 psc, (AndImpLRule [psc] sc) * (@ctr_L A ps psc))
  +
  (existsT2 B C D invps invpsc,
                       (A = Imp (And B C) D) *
                       (AndImpLRule [invps] ps) *
                       (@ctr_L (Imp B (Imp C D)) invps invpsc) *
                       (AndImpLRule [invpsc] sc))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst. inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. right. exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4, D).
  exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ4, D). repeat split.
  pose (AndImpLRule_I A0 B C D (Γ2 ++ A0 → B → C :: Γ3) Γ4). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. right. exists A0. exists B. exists C.
    exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4, D). exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ4, D). repeat split.
    pose (AndImpLRule_I A0 B C D (Γ2 ++ A0 → B → C :: Γ3) Γ4). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ;  auto.
  * inversion e0. subst. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e1 ; subst. repeat rewrite <- app_assoc. simpl. right.
       exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4, D).
       exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ4, D). repeat split.
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ1, D).
         exists (Γ2 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ1, D). repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m0 :: Γ3 ++ x0 ++ Imp A0 (Imp B C) :: Γ1, D). repeat split.
         pose (AndImpLRule_I A0 B C D (Γ2 ++ m0 :: Γ3 ++ x0) Γ1). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ; repeat rewrite <- app_assoc in a ; simpl in a ; auto. }
    + destruct x0.
      { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
         exists A0. exists B. exists C. exists (Γ2 ++ Imp A0 (Imp B C) :: x ++ Imp A0 (Imp B C) :: Γ4, D).
         exists (Γ2 ++ Imp A0 (Imp B C) :: x ++ Γ4, D). repeat split. }
      { simpl in e1. inversion e1. subst. left. repeat rewrite <- app_assoc. simpl.
         exists (Γ2 ++ m :: x ++ Imp A0 (Imp B C) :: x0 ++ Γ4, D). repeat split.
         pose (AndImpLRule_I A0 B C D (Γ2 ++ m :: x) (x0 ++ Γ4)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
         pose (ctr_LI m Γ2 ( x ++ A0 → B → C :: x0) Γ4 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
- destruct x.
  * simpl in e0. inversion e0. subst. right. repeat rewrite <- app_assoc. simpl. exists A0. exists B. exists C.
    exists (Γ0 ++ Imp A0 (Imp B C) :: Γ3 ++ Imp A0 (Imp B C) :: Γ4, D). exists (Γ0 ++ Imp A0 (Imp B C) :: Γ3 ++ Γ4, D). repeat split.
    pose (AndImpLRule_I A0 B C D (Γ0 ++ A0 → B → C :: Γ3) Γ4). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in a ; simpl in a ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
  * simpl in e0. inversion e0. subst. left. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Imp A0 (Imp B C) :: x ++ A :: Γ3 ++ Γ4, D). repeat split.
    pose (ctr_LI A (Γ0 ++ A0 → B → C :: x) Γ3 Γ4 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
Qed.

Lemma OrImpL_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (OrImpLRule [ps] s) ->
  ((existsT2 psc, (OrImpLRule [psc] sc) * (@ctr_L A ps psc))
  +
  (existsT2 B C D invps invpsc1 invpsc2,
                       (A = Imp (Or B C) D) *
                       (OrImpLRule [invps] ps) *
                       (@ctr_L (Imp B D) invps invpsc1) *
                       (@ctr_L (Imp C D) invpsc1 invpsc2) *
                       (OrImpLRule [invpsc2] sc))).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst. inversion H. subst. apply app2_find_hole in H1. destruct H1.
repeat destruct s ; destruct p ; subst.
- inversion e0. subst. apply app2_find_hole in H2. destruct H2.
  repeat destruct s ; destruct p ; subst.
  * right. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
    exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5, D). repeat split.
    pose (OrImpLRule_I A0 B C D (Γ3 ++ A0 → C :: Γ1 ++ [B → C]) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
    pose (ctr_LI (A0 → C) Γ3 (Γ1 ++ [B → C]) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    pose (ctr_LI (B → C) (Γ3 ++ A0 → C :: Γ1) [] Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * right. repeat rewrite <- app_assoc. simpl. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp A0 C :: Imp B C :: Γ5, D).
    exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ Γ5, D). repeat split.
    pose (OrImpLRule_I A0 B C D (Γ3 ++ A0 → C :: Γ1 ++ B → C :: x0) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
    pose (ctr_LI (A0 → C) Γ3 (Γ1 ++ B → C :: x0) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    pose (ctr_LI (B → C) (Γ3 ++ A0 → C :: Γ1) x0 Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * destruct x0.
    + simpl in e1. subst. right. repeat rewrite <- app_assoc. simpl. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
        exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5, D). repeat split.
        pose (OrImpLRule_I A0 B C D (Γ3 ++ A0 → C :: Γ4 ++ [B → C]) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
        pose (ctr_LI (A0 → C) Γ3 (Γ4 ++ [B → C]) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
        pose (ctr_LI (B → C) (Γ3 ++ A0 → C :: Γ4) [] Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    + simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
        exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++  Imp A0 C :: Imp B C :: x0 ++ Imp B C :: Γ2, D).
        exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x0 ++ Imp B C :: Γ2, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x0 ++ Γ2, D). repeat split.
        pose (OrImpLRule_I A0 B C D (Γ3 ++ A0 → C :: Γ4) [] (x0 ++ B → C :: Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
        pose (ctr_LI (B → C) (Γ3 ++ A0 → C :: Γ4) x0 Γ2 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
   + right. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
      exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5, D). repeat split.
      pose (OrImpLRule_I A0 B C D (Γ3 ++ A0 → C :: Γ4 ++ [B → C]) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
      pose (ctr_LI (A0 → C) Γ3 (Γ4 ++ [B → C]) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
      pose (ctr_LI (B → C) (Γ3 ++ A0 → C :: Γ4) [] Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    + destruct x.
        { simpl in e1. subst. right. repeat rewrite <- app_assoc. simpl. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
          exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5, D). repeat split.
          pose (OrImpLRule_I A0 B C D (Γ3 ++ A0 → C :: Γ4 ++ [B → C]) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          pose (ctr_LI (A0 → C) Γ3 (Γ4 ++ [B → C]) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
          pose (ctr_LI (B → C) (Γ3 ++ A0 → C :: Γ4) [] Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
        { simpl in e1.  inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
          exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp A0 C :: Imp B C :: x ++ Imp B C :: Γ2, D).
          exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Imp B C :: Γ2, D). exists (Γ3 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Γ2, D). repeat split.
          pose (OrImpLRule_I A0 B C D (Γ3 ++ A0 → C :: Γ4) [] (x ++ B → C :: Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          pose (ctr_LI (B → C) (Γ3 ++ A0 → C :: Γ4) x Γ2 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
    +  repeat rewrite <- app_assoc. simpl. right. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp A0 C :: Imp B C :: Γ5, D).
        exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp B C :: Γ5, D). exists (Γ3 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Γ5, D). repeat split.
      pose (OrImpLRule_I A0 B C D (Γ3 ++ A0 → C :: Γ1 ++ B → C :: x) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
      pose (ctr_LI (A0 → C) Γ3 (Γ1 ++ B → C :: x) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
      pose (ctr_LI (B → C) (Γ3 ++ A0 → C :: Γ1) x Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
  * inversion e0. subst.  repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
   + inversion e1. subst. right. exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2, D).
      exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Imp B C :: Γ2, D). exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Γ2, D). repeat split.
      pose (OrImpLRule_I A0 B C D Γ3 [] (Γ4 ++ A0 → C :: Γ1 ++ B → C :: Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
      pose (ctr_LI (A0 → C) Γ3 (B → C :: Γ4) (Γ1 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
      pose (ctr_LI (B → C) (Γ3 ++ [A0 → C]) (Γ4 ++ Γ1) Γ2 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
      pose (OrImpLRule_I A0 B C D Γ3 [] (Γ4 ++ Γ1 ++ Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
    + destruct x0.
        { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
          exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2, D).
          exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Imp B C :: Γ2, D). exists (Γ3 ++ Imp A0 C :: Imp B C :: Γ4 ++ Γ1 ++ Γ2, D). repeat split.
          pose (OrImpLRule_I A0 B C D Γ3 [] (Γ4 ++ A0 → C :: Γ1 ++ B → C :: Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          pose (ctr_LI (A0 → C) Γ3 (B → C :: Γ4) (Γ1 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
          pose (ctr_LI (B → C) (Γ3 ++ [A0 → C]) (Γ4 ++ Γ1) Γ2 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
          pose (OrImpLRule_I A0 B C D Γ3 [] (Γ4 ++ Γ1 ++ Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto. }
        { simpl in e1.  inversion e1. subst. left. exists (Γ3 ++ m0 :: Γ4 ++ x0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2, D). split.
          pose (OrImpLRule_I A0 B C D (Γ3 ++ m0 :: Γ4 ++ x0) Γ1 Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          pose (ctr_LI m0 Γ3 Γ4 (x0 ++ A0 → C :: Γ1 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
    +  repeat rewrite <- app_assoc. simpl. destruct x0.
        { simpl in e1. inversion e1. subst. right. repeat rewrite <- app_assoc. simpl.
          exists A0. exists B. exists C. exists (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ2, D).
          exists (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Γ1 ++ Imp B C :: Γ2, D). exists (Γ3 ++ Imp A0 C :: Imp B C :: x ++ Γ1 ++ Γ2, D). repeat split.
          pose (OrImpLRule_I A0 B C D Γ3 [] (x ++ A0 → C :: Γ1 ++ B → C :: Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          pose (ctr_LI (A0 → C) Γ3 (B → C :: x) (Γ1 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
          pose (ctr_LI (B → C) (Γ3 ++ [A0 → C]) (x ++ Γ1) Γ2 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
          pose (OrImpLRule_I A0 B C D Γ3 [] (x ++ Γ1 ++ Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto. }
        { simpl in e1.  inversion e1. subst. repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
           repeat destruct s ; destruct p ; subst.
          - left. exists (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5, D). split.
            pose (OrImpLRule_I A0 B C D (Γ3 ++ m :: x) Γ1 Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
            pose (ctr_LI m Γ3 (x ++ A0 → C :: Γ1 ++ [B → C]) Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ;  auto.
          - left. repeat rewrite <- app_assoc. exists (Γ3 ++ m :: x ++ Imp A0 C :: Γ1 ++ Imp B C :: x1 ++ Γ5, D). split.
            pose (OrImpLRule_I A0 B C D (Γ3 ++ m :: x) Γ1 (x1 ++ Γ5)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
            pose (ctr_LI m Γ3 (x ++ A0 → C :: Γ1 ++ B → C :: x1) Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ;  auto.
          - destruct x1.
            * simpl in e2. subst. left. repeat rewrite <- app_assoc. simpl. exists (Γ3 ++ m :: x ++ Imp A0 C :: x0 ++ Imp B C :: Γ5, D). split.
              pose (OrImpLRule_I A0 B C D (Γ3 ++ m :: x) x0 Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
              pose (ctr_LI m Γ3 (x ++ A0 → C :: x0 ++ [B → C]) Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ;  auto.
            * simpl in e2. inversion e2. subst. repeat rewrite <- app_assoc. simpl. left. exists (Γ3 ++ m0 :: x ++ Imp A0 C :: x0 ++ x1 ++ Imp B C :: Γ2, D). split.
              pose (OrImpLRule_I A0 B C D (Γ3 ++ m0 :: x) (x0 ++ x1) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
              pose (ctr_LI m0 Γ3 (x ++ A0 → C :: x0) (x1 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ;  auto. }
- destruct x.
  * simpl in e0. inversion e0 ; subst. repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2.
    repeat destruct s ; destruct p ; subst.
   + right. exists A0. exists B. exists C. exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
      exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: Γ5, D). repeat split.
      pose (OrImpLRule_I A0 B C D (Γ0 ++ A0 → C :: Γ1 ++ [B → C]) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
      pose (ctr_LI (A0 → C) Γ0 (Γ1 ++ [B → C]) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
      pose (ctr_LI (B → C) (Γ0 ++ A0 → C :: Γ1) [] Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    + right. repeat rewrite <- app_assoc. simpl.
        exists A0. exists B. exists C. exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp A0 C :: Imp B C :: Γ5, D).
        exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Imp B C :: Γ5, D). exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x ++ Γ5, D). repeat split.
        pose (OrImpLRule_I A0 B C D (Γ0 ++ A0 → C :: Γ1 ++ B → C :: x) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
        pose (ctr_LI (A0 → C) Γ0 (Γ1 ++ B → C :: x) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
        pose (ctr_LI (B → C) (Γ0 ++ A0 → C :: Γ1) x Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
    +  destruct x.
        { simpl in e1. subst. repeat rewrite <- app_assoc. simpl. right.
          exists A0. exists B. exists C. exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp A0 C :: Imp B C :: Γ5, D).
          exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Imp B C :: Γ5, D). exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: Γ5, D). repeat split.
          pose (OrImpLRule_I A0 B C D (Γ0 ++ A0 → C :: Γ4 ++ [B → C]) [] Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          pose (ctr_LI (A0 → C) Γ0 (Γ4 ++ [B → C]) (B → C :: Γ5) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
          pose (ctr_LI (B → C) (Γ0 ++ A0 → C :: Γ4) [] Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
        { simpl in e1. inversion e1. subst. repeat rewrite <- app_assoc. simpl. right.
          exists A0. exists B. exists C.  exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp A0 C :: Imp B C :: x ++ Imp B C :: Γ2, D).
          exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Imp B C :: Γ2, D). exists (Γ0 ++ Imp A0 C :: Γ4 ++ Imp B C :: x ++ Γ2, D). repeat split.
          pose (OrImpLRule_I A0 B C D (Γ0 ++ A0 → C :: Γ4) [] (x ++ B → C :: Γ2)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          pose (ctr_LI (B → C) (Γ0 ++ A0 → C :: Γ4) x Γ2 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
  * inversion e0. subst.  repeat rewrite <- app_assoc. simpl. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
   + left. exists(Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: A :: Γ4 ++ Γ5, D). repeat split.
      pose (ctr_LI A (Γ0 ++ A0 → C :: Γ1 ++ [B → C]) Γ4 Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ;  auto.
   + left. exists (Γ0 ++ Imp A0 C :: Γ1 ++ Imp B C :: x0 ++ A :: Γ4 ++ Γ5, D). repeat split.
      pose (OrImpLRule_I A0 B C D Γ0 Γ1 (x0 ++ A :: Γ4 ++ Γ5)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
      pose (ctr_LI A (Γ0 ++ A0 → C :: Γ1 ++ B → C :: x0) Γ4 Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
   + destruct x0.
       { simpl in e1. subst. repeat rewrite <- app_assoc. simpl. left. exists (Γ0 ++ Imp A0 C :: x ++ Imp B C :: A :: Γ4 ++ Γ5, D). repeat split.
         pose (ctr_LI A (Γ0 ++ A0 → C :: x ++ [B → C]) Γ4 Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
        { simpl in e1.  inversion e1. apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
          - left. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C ::  Γ5, D). repeat split.
            pose (OrImpLRule_I A0 B C D Γ0 (x ++ m :: Γ4) Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
            pose (ctr_LI m (Γ0 ++ A0 → C :: x) (Γ4 ++ [B → C]) Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
          - destruct x1.
            + simpl in e2. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
              exists (Γ0 ++ Imp A0 C :: x ++ m :: Γ4 ++ Imp B C ::  Γ5, D). repeat split.
              pose (OrImpLRule_I A0 B C D Γ0 (x ++ m :: Γ4) Γ5). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
              pose (ctr_LI m (Γ0 ++ A0 → C :: x) (Γ4 ++ [B → C]) Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
            + simpl in e2. inversion e2. subst. left. repeat rewrite <- app_assoc. simpl. repeat rewrite <- app_assoc. simpl.
                exists (Γ0 ++ Imp A0 C :: x ++ m0 :: Γ4 ++ x1 ++ Imp B C :: Γ2, D). repeat split.
                pose (OrImpLRule_I A0 B C D Γ0 (x ++ m0 :: Γ4 ++ x1) Γ2). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
                pose (ctr_LI m0 (Γ0 ++ A0 → C :: x) Γ4 (x1 ++ B → C :: Γ2) D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto.
          - left. repeat rewrite <- app_assoc. simpl. exists (Γ0 ++ Imp A0 C :: x ++ m :: x0 ++ Imp B C :: x1 ++ Γ5, D). repeat split.
            pose (OrImpLRule_I A0 B C D Γ0 (x ++ m :: x0) (x1 ++ Γ5)). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in o ; simpl in o ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
            pose (ctr_LI m (Γ0 ++ A0 → C :: x) (x0 ++ B → C :: x1) Γ5 D). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in c ; simpl in c ; repeat rewrite <- app_assoc in c ; simpl in c ; auto. }
Qed.

Lemma SLR_app_ctr_L : forall s sc A ps,
  (@ctr_L A s sc) ->
  (SLRRule [ps] s) ->
     (existsT2 psc, (SLRRule [psc] sc) * (@ctr_L (unBox_formula A) ps psc)).
Proof.
intros s sc A ps ctr RA. inversion RA. inversion ctr. subst. inversion H ; subst. clear H.
exists ((unBoxed_list Γ0 ++ unBox_formula A :: unBoxed_list Γ1 ++ unBoxed_list Γ2) ++ [Box A0], A0). repeat split ; auto.
pose (SLRRule_I A0 (Γ0 ++ A :: Γ1 ++ Γ2)).
repeat rewrite unBox_app_distrib in s ; simpl in s ; repeat rewrite <- app_assoc in s ; simpl in s ;
repeat rewrite unBox_app_distrib in s ; simpl in s ; repeat rewrite <- app_assoc in s ; simpl in s ;
repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto.
repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ;
repeat rewrite unBox_app_distrib ; simpl ; repeat rewrite <- app_assoc ; simpl ;
repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc ; auto. apply ctr_LI.
Qed.
