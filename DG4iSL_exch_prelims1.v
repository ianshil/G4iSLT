Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import general_export.

Require Import DiSL_calc.
Require Import DG4iSL_list_lems.


(* First, as we want to mimick sequents based on multisets of formulae we need to
obtain exchange. *)

(* Definition of exchange with lists of formulae directly. It is more general and should
make the proofs about exchange easier to handle. *) 

Inductive list_exch_L : relationT Seq  :=
  | list_exch_LI Γ0 Γ1 Γ2 Γ3 Γ4 A : list_exch_L
      (Γ0 ++ Γ1 ++ Γ2 ++ Γ3 ++ Γ4, A) (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A).

(* Some lemmas about In and exchange. *)

Lemma InT_list_exch_L : forall A l1 l2,
            (@list_exch_L (l1,A) (l2,A)) ->
            (forall x, (InT x l1 -> InT x l2) * (InT x l2 -> InT x l1)).
Proof.
intros A l1 l2 exch. inversion exch.
intro x. split ; intro ; apply InT_exch_list ; auto.
Qed.

(* Some useful lemmas about list exchange. *)

Lemma list_exch_L_id : forall s, (@list_exch_L s s).
Proof.
intros s. destruct s. pose (list_exch_LI l [] [] [] [] m). simpl in l0.
rewrite <- app_nil_end in l0 ; auto.
Qed.

Lemma list_exch_L_same_R : forall s se,
    (@list_exch_L s se) ->
    (forall Γ Γe A0 A1, (s = (Γ , A0)) ->
    (se = (Γe , A1)) ->
    (A0 = A1)).
Proof.
intros s se exch. induction exch. intros Γ Γe A0 A1 E1 E2.
inversion E1. inversion E2. rewrite H1 in H3. assumption.
Qed.

Lemma list_exch_L_permL : forall s se,
    (@list_exch_L s se) ->
      (forall Γ0 Γ1 A C, s = ((Γ0 ++ C :: Γ1), A) ->
      (existsT2 eΓ0 eΓ1, se = ((eΓ0 ++ C :: eΓ1), A))).
Proof.
intros s se exch. inversion exch ; subst. intros.
inversion H ; subst. apply partition_1_element in H1. destruct H1 ; repeat destruct s ; subst.
+ exists x. exists (x0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4). repeat rewrite <- app_assoc ; auto.
+ exists (Γ0 ++ Γ3 ++ Γ2 ++ x). exists (x0 ++ Γ4). repeat rewrite <- app_assoc ; auto.
+ exists (Γ0 ++ Γ3 ++ x). exists (x0 ++ Γ1 ++ Γ4). repeat rewrite <- app_assoc ; auto.
+ exists (Γ0 ++ x). exists (x0 ++ Γ2 ++ Γ1 ++ Γ4). repeat rewrite <- app_assoc ; auto.
+ exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ x). exists x0. repeat rewrite <- app_assoc ; auto.
Qed.

(* Some lemmas about nobox_gen_ext and exchange. *)

Lemma ND_Box_list_exch_L : forall l0 l1, (ND_Box_list l0 l1) ->
    forall A0 A1 l2, (list_exch_L (l1, A0) (l2,A0)) ->
    existsT2 l3, (ND_Box_list l3 l2) * (list_exch_L (l0,A1) (l3,A1)).
Proof.
intros l0 l1 X. induction X ; simpl ; intros ; subst.
- inversion H ; subst. exists [].
  destruct Γ0 ; destruct Γ1 ; destruct Γ2 ; destruct Γ3 ; destruct Γ4 ; simpl in H1 ; try inversion H1 ; simpl ; split.
  apply univ_gen_mod_nil. epose (list_exch_LI [] [] [] [] [] _). simpl in l ; apply l.
- inversion H ; subst. destruct Γ0 ; simpl in H1 ; simpl ; simpl in H ; subst.
  + destruct Γ1 ; simpl in H1 ; simpl ; simpl in H ; subst.
    * destruct Γ2 ; simpl in H1 ; simpl ; simpl in H ; subst.
      -- destruct Γ3 ; simpl in H1 ; simpl ; simpl in H ; subst.
        ++ exists (x :: l). split. apply univ_gen_mod_cons; auto. apply list_exch_L_id.
        ++ inversion H1 ; subst. exists (x :: l). split. apply univ_gen_mod_cons ; auto. apply list_exch_L_id.
      -- inversion H1 ; subst. apply univ_gen_mod_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
          apply univ_gen_mod_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst. exists (x2 ++ x :: x0 ++ x3).
          split. apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_cons ; auto ; apply univ_gen_mod_combine ; auto.
          pose (list_exch_LI [] (x :: x0) [] x2 x3 A1). simpl in l ; repeat rewrite <- app_nil_end in l ; auto.
    * inversion H1 ; subst. apply univ_gen_mod_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
      apply univ_gen_mod_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
      apply univ_gen_mod_splitR in u1. destruct u1. destruct s. repeat destruct p ; subst. exists (x1 ++ x2 ++ x :: x0 ++ x4).
      split. apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_cons ; auto ;
      apply univ_gen_mod_combine ; auto.
      pose (list_exch_LI [] (x :: x0) x2 x1 x4 A1). simpl in l ; repeat rewrite <- app_nil_end in l ; auto.
  + inversion H1 ; subst. apply univ_gen_mod_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
     apply univ_gen_mod_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
     apply univ_gen_mod_splitR in u1. destruct u1. destruct s. repeat destruct p ; subst.
     apply univ_gen_mod_splitR in u2. destruct u2. destruct s. repeat destruct p ; subst. exists (x :: x0 ++ x3 ++ x1 ++ x2 ++ x5).
     split. apply univ_gen_mod_cons ; auto ; apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_combine ; auto ;
     apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_combine ; auto.
     pose (list_exch_LI (x :: x0) x2 x1 x3 x5 A1). simpl in l ; repeat rewrite <- app_nil_end in l ; auto.
- inversion H ; subst. destruct Γ0 ; simpl in H1 ; simpl ; simpl in H ; subst.
  + destruct Γ1 ; simpl in H1 ; simpl ; simpl in H ; subst.
    * destruct Γ2 ; simpl in H1 ; simpl ; simpl in H ; subst.
      -- destruct Γ3 ; simpl in H1 ; simpl ; simpl in H ; subst.
        ++ exists (x :: l). split. apply univ_gen_mod_modif ; auto. apply list_exch_L_id.
        ++ inversion H1 ; subst. exists (x :: l). split. apply univ_gen_mod_modif ; auto. apply list_exch_L_id.
      -- inversion H1 ; subst. apply univ_gen_mod_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
          apply univ_gen_mod_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst. exists (x2 ++ x :: x0 ++ x3).
          split. apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_modif ; auto ; apply univ_gen_mod_combine ; auto.
          pose (list_exch_LI [] (x :: x0) [] x2 x3 A1). simpl in l ; repeat rewrite <- app_nil_end in l ; auto.
    * inversion H1 ; subst. apply univ_gen_mod_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
      apply univ_gen_mod_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
      apply univ_gen_mod_splitR in u1. destruct u1. destruct s. repeat destruct p ; subst. exists (x1 ++ x2 ++ x :: x0 ++ x4).
      split. apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_modif ; auto ;
      apply univ_gen_mod_combine ; auto.
      pose (list_exch_LI [] (x :: x0) x2 x1 x4 A1). simpl in l ; repeat rewrite <- app_nil_end in l ; auto.
  + inversion H1 ; subst. apply univ_gen_mod_splitR in X. destruct X. destruct s. repeat destruct p ; subst.
     apply univ_gen_mod_splitR in u0. destruct u0. destruct s. repeat destruct p ; subst.
     apply univ_gen_mod_splitR in u1. destruct u1. destruct s. repeat destruct p ; subst.
     apply univ_gen_mod_splitR in u2. destruct u2. destruct s. repeat destruct p ; subst. exists (x :: x0 ++ x3 ++ x1 ++ x2 ++ x5).
     split. apply univ_gen_mod_modif ; auto ; apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_combine ; auto ;
     apply univ_gen_mod_combine ; auto ; apply univ_gen_mod_combine ; auto.
     pose (list_exch_LI (x :: x0) x2 x1 x3 x5 A1). simpl in l ; repeat rewrite <- app_nil_end in l ; auto.
Qed.

(* Interactions between exchange and rules. *)

Lemma AndR_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (AndRRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (AndRRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1)  *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch RA. inversion RA. subst. inversion exch. subst. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A).
exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, B). repeat split.
Qed.

Lemma AndL_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (AndLRule [ps] s) ->
  (existsT2 pse,
    (AndLRule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A :: B :: Γ1, C). repeat split. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ0 ++ A :: B :: Γ5 ++ Γ6, C). repeat split. apply list_exch_L_id. }
      * simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ A :: B :: Γ4 ++ Γ6, C). repeat split.
        pose (AndLRule_I A B C (Γ0 ++ Γ5) (Γ4 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        pose (list_exch_LI Γ0 [] (A :: B :: Γ4) Γ5 Γ6 C). simpl in l ; auto.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ Γ4 ++ A :: B :: Γ3 ++ Γ6, C). repeat split.
      pose (AndLRule_I A B C (Γ0 ++ Γ5 ++ Γ4) (Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
      pose (list_exch_LI Γ0 (A :: B :: Γ3) Γ4 Γ5 Γ6 C). simpl in l ; auto.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. exists ((Γ0 ++ []) ++ A :: B :: Γ1, C). repeat split. rewrite <- app_assoc. apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ A :: B :: Γ4 ++ Γ6, C). repeat split.
          pose (AndLRule_I A B C (Γ0 ++ Γ5) (Γ4 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          pose (list_exch_LI Γ0 [] (A :: B :: Γ4) Γ5 Γ6 C). simpl in l ; auto. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ Γ4 ++ A :: B :: Γ3 ++ Γ6, C). repeat split.
        pose (AndLRule_I A B C (Γ0 ++ Γ5 ++ Γ4) (Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        pose (list_exch_LI Γ0 (A :: B :: Γ3) Γ4 Γ5 Γ6 C). simpl in l ; auto.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ A :: B :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat rewrite <- app_assoc. repeat split.
      pose (list_exch_LI (Γ0 ++ A :: B :: x) Γ3 Γ4 Γ5 Γ6 C). repeat rewrite <- app_assoc in l ; simpl in l ; auto.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ3) ++ A :: B :: Γ1, C). repeat split. 2: apply list_exch_L_id. rewrite app_assoc.
           apply AndLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A :: B :: Γ5 ++ Γ3 ++ Γ6, C). repeat split.
           pose (list_exch_LI Γ2 Γ3 [] (A :: B :: Γ5) Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5) ++ A :: B :: Γ4 ++ Γ3 ++ Γ6, C). repeat split.
        pose (AndLRule_I A B C (Γ2 ++ Γ5) (Γ4 ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
        pose (list_exch_LI Γ2 Γ3 (A :: B :: Γ4) Γ5 Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ4 ++ Γ3) ++ A :: B :: Γ1, C). repeat split.
           pose (AndLRule_I A B C (Γ2 ++ Γ4 ++ Γ3) Γ1). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
           pose (list_exch_LI Γ2 Γ3 Γ4 [] (A :: B :: Γ1) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A :: B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
           pose (list_exch_LI Γ2 Γ3 Γ4 (A :: B :: Γ5) Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A :: B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply AndLRule_I. }
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A :: B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply AndLRule_I. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ A :: B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply AndLRule_I.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ x) ++ A :: B :: x0 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
              pose (AndLRule_I A B C (Γ2 ++ x) (x0 ++ Γ4 ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
              pose (list_exch_LI Γ2 Γ3 Γ4 (x ++ A :: B :: x0) Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x0 ++ Γ3 ++ A :: B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply AndLRule_I.
              pose (list_exch_LI Γ2 Γ3 [] x0 (A :: B :: Γ1) C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A :: B :: Γ5 ++ x0 ++ Γ3 ++ Γ6, C). repeat split.
              pose (list_exch_LI Γ2 Γ3 x0 (A :: B :: Γ5) Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
        { simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5 ++ x0) ++ A :: B :: x ++ Γ3 ++ Γ6, C). split.
           pose (AndLRule_I A B C (Γ2 ++ Γ5 ++ x0) (x ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
           pose (list_exch_LI Γ2 Γ3 (x0 ++ A :: B :: x) Γ5 Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ A :: B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply AndLRule_I. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A :: B :: Γ5 ++ x ++ Γ6, C). repeat split.
              pose (list_exch_LI Γ2 x [] (A :: B :: Γ5) Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5) ++ A :: B :: Γ4 ++ x ++ Γ6, C). repeat split.
          pose (AndLRule_I A B C (Γ2 ++ Γ5) (Γ4 ++ x ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
          pose (list_exch_LI Γ2 x (A :: B :: Γ4) Γ5 Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: B :: x0 ++ Γ6, C). repeat split.
         pose (AndLRule_I A B C (Γ2 ++ Γ5 ++ Γ4 ++ x) (x0 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in a ; simpl in a ; auto.
         pose (list_exch_LI Γ2 (x ++ A :: B :: x0) Γ4 Γ5 Γ6 C). repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; auto.
Qed.

Lemma OrR1_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (OrR1Rule [ps] s) ->
  (existsT2 pse,
    (OrR1Rule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, A).
split ; auto. apply OrR1Rule_I. apply list_exch_LI.
Qed.

Lemma OrR2_app_list_exchL : forall s se ps,
  (@list_exch_L s se) ->
  (OrR2Rule [ps] s) ->
  (existsT2 pse,
    (OrR2Rule [pse] se) *
    (@list_exch_L ps pse)).
Proof.
intros s se ps exch RA. inversion RA. subst. inversion exch. subst. exists (Γ0 ++ Γ3 ++ Γ2 ++ Γ1 ++ Γ4, B).
split ; auto. apply OrR2Rule_I. apply list_exch_LI.
Qed.

Lemma OrL_app_list_exchL : forall s se ps1 ps2,
  (@list_exch_L s se) ->
  (OrLRule [ps1;ps2] s) ->
  (existsT2 pse1 pse2,
    (OrLRule [pse1;pse2] se) *
    (@list_exch_L ps1 pse1)  *
    (@list_exch_L ps2 pse2)).
Proof.
intros s se ps1 ps2 exch RA. inversion RA. subst. inversion exch. subst. symmetry in H0.
apply app2_find_hole in H0. destruct H0. repeat destruct s ; destruct p ; subst.
- destruct Γ3.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists (Γ0 ++ A :: Γ1, C). exists (Γ0 ++ B :: Γ1, C). repeat split ; try apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ0 ++ A :: Γ5 ++ Γ6, C). exists (Γ0 ++ B :: Γ5 ++ Γ6, C). repeat split ; try apply list_exch_L_id. }
      * simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ A :: Γ4 ++ Γ6, C). exists (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6, C). repeat split.
        pose (OrLRule_I A B C (Γ0 ++ Γ5) (Γ4 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
        1-2: epose (list_exch_LI Γ0 [] (_ :: Γ4) Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6, C). exists (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6, C). repeat split.
      pose (OrLRule_I A B C (Γ0 ++ Γ5 ++ Γ4) (Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
      1-2: epose (list_exch_LI Γ0 (_ :: Γ3) Γ4 Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
- destruct x.
  + simpl in e0. subst. simpl. destruct Γ3.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. subst. simpl. rewrite <- e0. exists ((Γ0 ++ []) ++ A :: Γ1, C). exists ((Γ0 ++ []) ++ B :: Γ1, C). repeat split ; rewrite <- app_assoc ; simpl ; try apply list_exch_L_id. }
        { simpl in e0. inversion e0. subst. simpl. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ A :: Γ4 ++ Γ6, C). exists (Γ0 ++ Γ5 ++ B :: Γ4 ++ Γ6, C). repeat split.
          pose (OrLRule_I A B C (Γ0 ++ Γ5) (Γ4 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          1-2: epose (list_exch_LI Γ0 (_ :: Γ4) [] Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
      * simpl in e0. inversion e0. subst. rewrite <- app_assoc ; simpl. exists (Γ0 ++ Γ5 ++ Γ4 ++ A :: Γ3 ++ Γ6, C). exists (Γ0 ++ Γ5 ++ Γ4 ++ B :: Γ3 ++ Γ6, C). repeat split.
        pose (OrLRule_I A B C (Γ0 ++ Γ5 ++ Γ4) (Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
        1-2: epose (list_exch_LI Γ0 (_ :: Γ3) Γ4 Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
  + simpl in e0. inversion e0. subst. exists (Γ0 ++ A :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). exists (Γ0 ++ B :: x ++ Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat rewrite <- app_assoc. repeat split.
      1-2: epose (list_exch_LI (Γ0 ++ _ :: x) Γ3 Γ4 Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
- apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
  + simpl in e0. subst. simpl. destruct Γ4.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ3) ++ A :: Γ1, C). exists ((Γ2 ++ Γ3) ++ B :: Γ1, C).  repeat split ; try apply list_exch_L_id. rewrite app_assoc.
           apply OrLRule_I. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A :: Γ5 ++ Γ3 ++ Γ6, C). exists (Γ2 ++ B :: Γ5 ++ Γ3 ++ Γ6, C). repeat split.
          1-2: epose (list_exch_LI Γ2 Γ3 [] (_ :: Γ5) Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
      * simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5) ++ A :: Γ4 ++ Γ3 ++ Γ6, C). exists ((Γ2 ++ Γ5) ++ B :: Γ4 ++ Γ3 ++ Γ6, C). repeat split.
        pose (OrLRule_I A B C (Γ2 ++ Γ5) (Γ4 ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
        1-2 : epose (list_exch_LI Γ2 Γ3 (_ :: Γ4) Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
  + apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
      * simpl in e0. simpl. destruct Γ5.
        { simpl in e0. subst. simpl. exists ((Γ2 ++ Γ4 ++ Γ3) ++ A :: Γ1, C). exists ((Γ2 ++ Γ4 ++ Γ3) ++ B :: Γ1, C). repeat split.
           pose (OrLRule_I A B C (Γ2 ++ Γ4 ++ Γ3) Γ1). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
           1-2 : epose (list_exch_LI Γ2 Γ3 [] Γ4 (_ :: Γ1) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
        { simpl in e0. inversion e0. subst. simpl. exists (Γ2 ++ A :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). exists (Γ2 ++ B :: Γ5 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
           1-2 : epose (list_exch_LI Γ2 Γ3 Γ4 (_ :: Γ5) Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
      * apply app2_find_hole in e0. destruct e0. repeat destruct s ; destruct p ; subst.
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ A :: Γ1, C).  exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply OrLRule_I. }
        {  repeat rewrite <- app_assoc. exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ A :: Γ1, C). exists (Γ2 ++ Γ5 ++ Γ4 ++ Γ3 ++ x0 ++ B :: Γ1, C). repeat split. repeat rewrite app_assoc. apply OrLRule_I. }
        { destruct x0.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ A :: Γ1, C). exists (Γ2 ++ x ++ Γ4 ++ Γ3 ++ B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply OrLRule_I.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ x) ++ A :: x0 ++ Γ4 ++ Γ3 ++ Γ6, C). exists ((Γ2 ++ x) ++ B :: x0 ++ Γ4 ++ Γ3 ++ Γ6, C). repeat split.
              pose (OrLRule_I A B C (Γ2 ++  x) (x0 ++ Γ4 ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
              1-2 : epose (list_exch_LI Γ2 Γ3 Γ4 (x ++ _ :: x0) Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
      * destruct x.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x0 ++ Γ3 ++ A :: Γ1, C). exists (Γ2 ++ x0 ++ Γ3 ++ B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply OrLRule_I.
              1-2 : epose (list_exch_LI Γ2 Γ3 [] x0 (_ :: Γ1) C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A :: Γ5 ++ x0 ++ Γ3 ++ Γ6, C). exists (Γ2 ++ B :: Γ5 ++ x0 ++ Γ3 ++ Γ6, C). repeat split.
              1-2 : epose (list_exch_LI Γ2 Γ3 x0 (_ :: Γ5) Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
        { simpl in e0. inversion e0. subst. exists ((Γ2 ++ Γ5 ++ x0) ++ A :: x ++ Γ3 ++ Γ6, C). exists ((Γ2 ++ Γ5 ++ x0) ++ B :: x ++ Γ3 ++ Γ6, C). repeat split.
          pose (OrLRule_I A B C (Γ2 ++ Γ5 ++ x0) (x ++ Γ3 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          1-2 : epose (list_exch_LI Γ2 Γ3 (x0 ++ _ :: x) Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
  + destruct x0.
      * simpl in e0. simpl. destruct Γ4.
        { simpl in e0. destruct Γ5.
            - simpl in e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ x ++ A :: Γ1, C). exists (Γ2 ++ x ++ B :: Γ1, C). repeat split.
              repeat rewrite app_assoc. apply OrLRule_I. apply list_exch_L_id. apply list_exch_L_id.
            - simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists (Γ2 ++ A :: Γ5 ++ x ++ Γ6, C). exists (Γ2 ++ B :: Γ5 ++ x ++ Γ6, C). repeat split.
              1-2 : epose (list_exch_LI Γ2 x [] (_ :: Γ5) Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
        { simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5) ++ A :: Γ4 ++ x ++ Γ6, C). exists ((Γ2 ++ Γ5) ++ B :: Γ4 ++ x ++ Γ6, C). repeat split.
          pose (OrLRule_I A B C (Γ2 ++ Γ5) (Γ4 ++ x ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
          1-2 : epose (list_exch_LI Γ2 x (_ :: Γ4) Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l. }
      * simpl in e0. inversion e0. subst. repeat rewrite <- app_assoc. simpl. exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ A :: x0 ++ Γ6, C). exists ((Γ2 ++ Γ5 ++ Γ4 ++ x) ++ B :: x0 ++ Γ6, C). repeat split.
        pose (OrLRule_I A B C (Γ2 ++ Γ5 ++ Γ4 ++ x) (x0 ++ Γ6)). repeat rewrite <- app_assoc ; repeat rewrite <- app_assoc in o ; simpl in o ; auto.
        1-2 : epose (list_exch_LI Γ2 (x ++ _ :: x0) Γ4 Γ5 Γ6 C) ; repeat rewrite <- app_assoc ; simpl ; repeat rewrite <- app_assoc in l ; simpl in l ; apply l.
Qed.