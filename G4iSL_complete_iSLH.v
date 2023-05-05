Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Ensembles.

Require Import general_export.

Require Import DG4iSL_export.

Require Import iSL_GHC.

Theorem G4iSL_proves_iSLAxioms : forall A, iSLAxioms A -> G4iSL_prv ([], A).
Proof.
intros. inversion H.
(* IA1 *)
- destruct H0. destruct s ; subst. unfold IA1 ; simpl.
  apply derI with (ps:=[([x], x0 → x)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x0;x], x)]). apply ImpR. epose (ImpRRule_I _ _ [] [x]). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  pose (Id_all_form x [x0] []). simpl in d. auto.
(* IA2 *)
- destruct H0. repeat destruct s ; subst. unfold IA2 ; simpl.
  apply derI with (ps:=[([x → x0 → x1],(x → x0) → x → x1)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x → x0;x → x0 → x1], x → x1)]). apply ImpR. epose (ImpRRule_I _ _ [] [x → x0 → x1]). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x;x → x0;x → x0 → x1], x1)]). apply ImpR. epose (ImpRRule_I _ _ [] [x → x0;x → x0 → x1]). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  pose (Id_all_form x [] [x → x0]). simpl in d.
  epose (ImpL_adm (derrec_height d) _ d x (x0 → x1) [x; x → x0] [] x1). simpl in d0. apply d0 ; auto.
  pose (Id_all_form x [] [x0 → x1]). simpl in d1.
  epose (ImpL_adm (derrec_height d1) _ d1 x x0 [x] [x0 → x1] x1). simpl in d2. apply d2 ; auto.
  pose (Id_all_form x0 [x] []). simpl in d3.
  epose (ImpL_adm (derrec_height d3) _ d3 x0 x1 [x;x0] [] x1). simpl in d4. apply d4 ; auto.
  pose (Id_all_form x1 [x; x0] []). simpl in d5. auto.
(* IA3 *)
- destruct H0. repeat destruct s ; subst. unfold IA3 ; simpl.
  apply derI with (ps:=[([x],x ∨ x0)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x], x)]). apply OrR1. epose (OrR1Rule_I _ _ [x]). simpl in o ; apply o.
  apply dlCons. 2: apply dersrec_nil.
  pose (Id_all_form x [] []). simpl in d ; auto.
(* IA4 *)
- destruct H0. repeat destruct s ; subst. unfold IA4 ; simpl.
  apply derI with (ps:=[([x0],x ∨ x0)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x0], x0)]). apply OrR2. epose (OrR2Rule_I _ _ [x0]). simpl in o ; apply o.
  apply dlCons. 2: apply dersrec_nil.
  pose (Id_all_form x0 [] []). simpl in d ; auto.
(* IA5 *)
- destruct H0. repeat destruct s ; subst. unfold IA5 ; simpl.
  apply derI with (ps:=[([x → x1],(x0 → x1) → (x ∨ x0) → x1)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x0 → x1;x → x1], (x ∨ x0) → x1)]). apply ImpR. epose (ImpRRule_I _ _ [] [x → x1]). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x ∨ x0;x0 → x1; x → x1], x1)]). apply ImpR. epose (ImpRRule_I _ _ [] [x0 → x1; x → x1]). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x; x0 → x1; x → x1], x1);([x0; x0 → x1; x → x1], x1)]). epose (OrLRule_I _ _ _ [] _). apply OrL. simpl in o. apply o.
  apply dlCons. 2: apply dlCons. 3: apply dersrec_nil.
  pose (Id_all_form x [] [x0 → x1]). simpl in d.
  epose (ImpL_adm (derrec_height d) _ d x x1 [x; x0 → x1] [] x1). simpl in d0. apply d0 ; auto.
  pose (Id_all_form x1 [x; x0 → x1] []). simpl in d1 ; auto.
  pose (Id_all_form x0 [] [x → x1]). simpl in d.
  epose (ImpL_adm (derrec_height d) _ d x0 x1 [x0] [x → x1] x1). simpl in d0. apply d0 ; auto.
  pose (Id_all_form x1 [x0] [x → x1]). simpl in d1 ; auto.
(* IA6 *)
- destruct H0. repeat destruct s ; subst. unfold IA6 ; simpl.
  apply derI with (ps:=[([x ∧ x0],x)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x;x0], x)]). apply AndL. epose (AndLRule_I _ _ _ [] []). simpl in a ; apply a.
  apply dlCons. 2: apply dersrec_nil.
  pose (Id_all_form x [] [x0]). simpl in d ; auto.
(* IA7 *)
- destruct H0. repeat destruct s ; subst. unfold IA7 ; simpl.
  apply derI with (ps:=[([x ∧ x0],x0)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x;x0], x0)]). apply AndL. epose (AndLRule_I _ _ _ [] []). simpl in a ; apply a.
  apply dlCons. 2: apply dersrec_nil.
  pose (Id_all_form x0 [x] []). simpl in d ; auto.
(* IA8 *)
- destruct H0. repeat destruct s ; subst. unfold IA8 ; simpl.
  apply derI with (ps:=[([x → x0],(x → x1) → x → x0 ∧ x1)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x → x1;x → x0], x → x0 ∧ x1)]). apply ImpR. epose (ImpRRule_I _ _ [] [x → x0]). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x;x → x1; x → x0], x0 ∧ x1)]). apply ImpR. epose (ImpRRule_I _ _ [] [x → x1; x → x0]). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x; x → x1; x → x0], x0);([x; x → x1; x → x0], x1)]). apply AndR. apply AndRRule_I.
  apply dlCons. 2: apply dlCons. 3: apply dersrec_nil.
  pose (Id_all_form x [] [x → x1]). simpl in d.
  epose (ImpL_adm (derrec_height d) _ d x x0 [x; x → x1] [] x0). simpl in d0. apply d0 ; auto.
  pose (Id_all_form x0 [x; x → x1] []). simpl in d1 ; auto.
  pose (Id_all_form x [] [x → x0]). simpl in d.
  epose (ImpL_adm (derrec_height d) _ d x x1 [x] [x → x0] x1). simpl in d0. apply d0 ; auto.
  pose (Id_all_form x1 [x] [x → x0]). simpl in d1 ; auto.
(* IA9 *)
- destruct H0. repeat destruct s ; subst. unfold IA9 ; simpl.
  apply derI with (ps:=[([⊥],x)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[]). apply BotL. epose (BotLRule_I [] []). simpl in b ; apply b. apply dersrec_nil.
(* MA10 *)
- destruct H0. repeat destruct s ; subst. unfold MA10 ; simpl.
  apply derI with (ps:=[([Box (x → x0)], Box x → Box x0)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([Box x;Box (x → x0)], Box x0)]). apply ImpR. epose (ImpRRule_I _ _ [] [Box (x → x0)]). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x;x → x0] ++ [Box x0], x0)]). apply SLR. epose (SLRRule_I _ [Box x; Box (x → x0)]). simpl in s. apply s.
  apply dlCons. 2: apply dersrec_nil.
  pose (ModusPonens x x0 [] [] [Box x0]). simpl in d ; auto.
(* MA11 *)
- destruct H0. repeat destruct s ; subst. unfold MA11 ; simpl.
  apply derI with (ps:=[([(Box x → x)], x)]). apply ImpR. epose (ImpRRule_I _ _ [] []). simpl in i ; apply i.
  apply dlCons. 2: apply dersrec_nil.
  apply derI with (ps:=[([x;Box x], x);([x], x)]). apply BoxImpL. epose (BoxImpLRule_I _ _ _ [] []). simpl in b ; apply b.
  apply dlCons. 2: apply dlCons. 3: apply dersrec_nil.
  pose (Id_all_form x [] [Box x]). simpl in d ; auto.
  pose (Id_all_form x [] []). simpl in d ; auto.
Qed.

Theorem G4iSL_simulates_iSLH : forall (Γ : Ensemble _) A, iSLH_prv (Γ, A) ->
        existsT2 (Γ0 : list MPropF), (forall B, List.In B Γ0 -> Γ B) * (G4iSL_prv (Γ0,A)).
Proof.
intros. remember (Γ, A) as P. revert HeqP. revert Γ. revert A. induction X.
- inversion i ; subst. intros. inversion HeqP ; subst. exists [A0]. intros. split.
  intros. inversion H0 ; subst ; auto. inversion H1.
  pose (Id_all_form A0 [] []). simpl in d ; auto.
- intros. subst. exists []. split. intros. inversion H. inversion a ; subst. apply G4iSL_proves_iSLAxioms ; auto.
- intros. subst. inversion m ; subst.
  assert (In (Γ, A0 → A) [(Γ, A0 → A); (Γ, A0)]). apply in_eq.
  assert ((Γ, A0 → A) = (Γ, A0 → A)) ; auto.
  pose (X _ H _ _ H0). destruct s. destruct p.
  assert (In (Γ, A0) [(Γ, A0 → A); (Γ, A0)]). apply in_cons ; apply in_eq.
  assert ((Γ, A0) = (Γ, A0)) ; auto.
  pose (X _ H1 _ _ H2). destruct s. destruct p.
  exists (x ++ x0). split. intros. apply in_app_or in H3. destruct H3 ; auto.
  pose (G4iSL_cut_adm0 A0 x x0 A). apply g1.
  pose (@G4iSL_list_wkn_L (derrec_height g0) [] x0 A0). simpl in s.
  assert (derrec_height g0 = derrec_height g0) ; auto. pose (s g0 H3 x).
  destruct s0 ; auto.
  apply ImpR_inv with (concl:=(x ++ x0, A0 → A)). 2: apply ImpRRule_I.
  pose (@G4iSL_list_wkn_L (derrec_height g) x [] (A0 → A)). simpl in s ; repeat rewrite <- app_nil_end in s.
  assert (derrec_height g = derrec_height g) ; auto. pose (s g H3 x0). destruct s0.
  clear l. rewrite <- app_nil_end in x1 ; auto.
- intros ; subst. inversion n ; subst.
  assert (In (Empty_set MPropF, A0) [(Empty_set MPropF, A0)]). apply in_eq.
  assert ((Empty_set MPropF, A0) = (Empty_set MPropF, A0)) ; auto.
  pose (X _ H _ _ H0). destruct s. destruct p. exists []. split. intros ; inversion H1.
  destruct x.
  pose (@G4iSL_list_wkn_L (derrec_height g) [] [] A0). simpl in s.
  assert (derrec_height g = derrec_height g) ; auto. pose (s g H1 [Box A0]).
  destruct s0 ; auto. clear l. rewrite <- app_nil_end in x.
  apply derI with (ps:=[([Box A0], A0)]). apply SLR. pose (SLRRule_I A0 []). simpl in s0 ; auto.
  apply dlCons. 2: apply dersrec_nil. auto.
  exfalso. assert (In m (m :: x)). apply in_eq. apply e in H1. inversion H1.
Qed.




