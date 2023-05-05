Require Import List.
Export ListNotations.
Require Import Lia.

Require Import general_export.

Declare Scope My_scope.
Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* In this file we define a calculus G4iSL based on multisets for the propositonal intuitionistic modal logic
   iSL. *)

(* Definitions Language *)

(* First, let us define the propositional formulae we use here. *)

Inductive MPropF : Type :=
 | Var : nat -> MPropF
 | Bot : MPropF
 | And : MPropF -> MPropF -> MPropF
 | Or : MPropF -> MPropF -> MPropF
 | Imp : MPropF -> MPropF -> MPropF
 | Box : MPropF -> MPropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Imp A B) (at level 16, right associativity) : My_scope.
Notation "A ∨ B" := (Or A B) (at level 16, right associativity) : My_scope.
Notation "A ∧ B" := (And A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.

Lemma eq_dec_form : forall x y : MPropF, {x = y}+{x <> y}.
Proof.
repeat decide equality.
Qed.

Fixpoint weight_form (A : MPropF) : nat :=
match A with
 | # P => 1
 | Bot => 1
 | And B C => 2 + (weight_form B) + (weight_form C)
 | Or B C => 1 + (weight_form B) + (weight_form C)
 | Imp B C =>  1 + (weight_form B) + (weight_form C)
 | Box B => 1 + (weight_form B)
end.


(* Now, we can define properties of formulae. *)

Definition is_atomicT (A : MPropF) : Type :=
                  (existsT2 (P : nat), A = # P) + (A = Bot).

Definition is_boxedT (A : MPropF) : Type :=
                  exists (B : MPropF), A = Box B.

Definition is_boxedT2 (A : MPropF) : Type :=
                  existsT2 (B : MPropF), A = Box B.

Definition is_primeT (A : MPropF) : Type :=
                  is_atomicT A + is_boxedT A.

(* We can define some types of lists formulae. For example, we can define
   lists of formulae which contain only propositional variables, or
   boxed formulae, or a combination of both. These are useful to define
   the rules. *)

Definition is_Atomic (Γ : list MPropF) : Prop :=
    forall A, (In A Γ) -> ((exists P, A = # P) \/ (A = ⊥)).

Definition is_Boxed_list (Γ : list MPropF) : Prop :=
    forall (A : MPropF), (In A Γ) -> (exists (B : MPropF), A = Box B).

Definition is_Prime (Γ : list MPropF) : Prop :=
    forall (A : MPropF), (In A Γ) ->
    (exists (B : MPropF), A = Box B) \/ (exists P, A = # P) \/ (A = ⊥).

(* The following definition allows us to non-deterministically box formulas
    in a list. If we have that ND_Box_list l0 l1, then we know that l1 is identical
    to l0 apart from some formulas which have been boxed. *)

Definition ND_Box_list := univ_gen_mod (fun x y => y = Box x).

(* The next definitions help to define the combination of a list of boxed
   formulae and the unboxing of all the formulae in that list. *)

Definition unBox_formula (A : MPropF) : MPropF :=
  match A with
              | # P => # P
              | ⊥ => ⊥
              | And A B => And A B
              | Or A B => Or A B
              | Imp A B => Imp A B
              | Box A => A
              end
.

Fixpoint unBoxed_list (Γ : list MPropF) : list MPropF:=
  match Γ with
  | [ ] => [ ]
  | h :: t => (unBox_formula h :: unBoxed_list t)
  end
.

Fixpoint top_boxes (l : list MPropF) : list MPropF :=
match l with
  | nil => nil
  | h :: t => match h with
                | Box A => (Box A) :: top_boxes t
                | _ => top_boxes t
              end
end.


(* Now that we have defined these, we can prove some properties about them. *)

Lemma unBox_app_distrib :
  forall (l1 l2: list MPropF), unBoxed_list (l1 ++ l2) = (unBoxed_list l1) ++ (unBoxed_list l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l with (l:=l2). simpl. reflexivity.
- intro l2. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma subl_of_boxl_is_boxl :
  forall (l1 l2: list MPropF), (incl l1 l2) -> (is_Boxed_list l2) -> (is_Boxed_list l1).
Proof.
intros. unfold is_Boxed_list. intros. apply H in H1. apply H0 in H1.
destruct H1. exists x. assumption.
Qed.

Lemma tl_of_boxl_is_boxl :
  forall (h : MPropF) (t l : list MPropF) (H: l = h :: t),
         (is_Boxed_list l) -> (is_Boxed_list t).
Proof.
intros. unfold is_Boxed_list. intros. assert (Hyp: In A l).
rewrite H. simpl. right. apply H1. apply H0 in Hyp. destruct Hyp.
exists x. assumption.
Qed.

Lemma is_box_is_in_boxed_list : forall l (A : MPropF), In A l -> is_Boxed_list l -> (exists B, Box B = A).
Proof.
induction l.
- intros. inversion H.
- intros. inversion H.
  + subst. unfold is_Boxed_list in H0. pose (H0 A).
    apply e in H. destruct H. exists x. symmetry. assumption.
  + apply IHl. assumption. unfold is_Boxed_list. intros. unfold is_Boxed_list in H0.
    pose (H0 A0). apply e. apply in_cons. assumption.
Qed.

Lemma top_boxes_distr_app : forall (l1 l2 : list MPropF),
      top_boxes (l1 ++ l2) = (top_boxes l1) ++ (top_boxes l2).
Proof.
induction l1.
- intro l2. rewrite app_nil_l. simpl. reflexivity.
- intro l2. simpl. destruct a ; try apply IHl1.
  simpl. rewrite IHl1. reflexivity.
Qed.

Lemma top_boxes_incl_list : forall l, incl (top_boxes l) l.
Proof.
induction l.
- simpl. unfold incl. intros. inversion H.
- unfold incl. intros. destruct a.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. apply in_cons. apply IHl. assumption.
  * simpl in H. destruct H.
    + subst. apply in_eq.
    + apply in_cons. apply IHl. assumption.
Qed.

Lemma in_top_boxes : forall l A, (In A (top_boxes l)) -> (existsT2 B l1 l2, (A = Box B) * (l = l1 ++ A :: l2)).
Proof.
induction l.
- intros. simpl in H. inversion H.
- intros. destruct a.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([# n] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([⊥] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([And a1 a2] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([Or a1 a2] ++ x0). exists x1. auto.
  * simpl in H. apply IHl in H. destruct H. destruct s. destruct s. destruct p. subst.
    exists x. exists ([Imp a1 a2] ++ x0). exists x1. auto.
  * simpl (top_boxes (Box a :: l)) in H. destruct (eq_dec_form (Box a) A).
    + subst. exists a. exists []. exists l. auto.
    + subst. assert (H0 : In A (top_boxes l)). inversion H. exfalso. apply n. assumption.
      assumption. apply IHl in H0. destruct H0. destruct s. destruct s. destruct p.
      subst. exists x. exists ([Box a] ++ x0). exists x1. auto.
Qed.

Lemma box_in_top_boxes : forall l1 l2 A, existsT2 l3 l4, top_boxes (l1 ++ Box A :: l2) = l3 ++ Box A :: l4.
Proof.
intros. exists (top_boxes l1). exists (top_boxes l2). rewrite top_boxes_distr_app. auto.
Qed.

Lemma is_Boxed_list_top_boxes : forall l, is_Boxed_list (top_boxes l).
Proof.
intros. induction l.
- simpl. intro. intros. inversion H.
- intro. destruct a.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. apply IHl in H. assumption.
  + simpl. intros. destruct H.
    * exists a. auto.
    * apply IHl. assumption.
Qed.

Definition Seq := (prod (list MPropF) (MPropF)).



(* Finally, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later. *)

Inductive IdPRule : rlsT Seq :=
  | IdPRule_I : forall P (Γ0 Γ1 : list MPropF),
          IdPRule [] (pair (Γ0 ++ # P :: Γ1) (# P))
.

Inductive BotLRule : rlsT Seq :=
  | BotLRule_I : forall Γ0 Γ1 A,
          BotLRule [] (pair (Γ0 ++ (⊥) :: Γ1) A)
.

Inductive AndRRule : rlsT Seq :=
  | AndRRule_I : forall A B Γ,
          AndRRule [(pair Γ A) ; (pair Γ B)]
                    (pair Γ (And A B))
.

Inductive AndLRule : rlsT Seq :=
  | AndLRule_I : forall A B C Γ0 Γ1,
          AndLRule [(pair (Γ0 ++ A :: B :: Γ1) C)]
                    (pair (Γ0 ++ (And A B) :: Γ1) C)
.

Inductive OrR1Rule : rlsT Seq :=
  | OrR1Rule_I : forall A B Γ,
          OrR1Rule [(pair Γ A)]
                    (pair Γ (Or A B))
.

Inductive OrR2Rule : rlsT Seq :=
  | OrR2Rule_I : forall A B Γ,
          OrR2Rule [(pair Γ B)]
                    (pair Γ (Or A B))
.

Inductive OrLRule : rlsT Seq :=
  | OrLRule_I : forall A B C Γ0 Γ1,
          OrLRule [(pair (Γ0 ++ A :: Γ1) C) ; (pair (Γ0 ++ B :: Γ1) C)]
                    (pair (Γ0 ++ (Or A B) :: Γ1) C)
.

Inductive ImpRRule : rlsT Seq :=
  | ImpRRule_I : forall A B Γ0 Γ1,
          ImpRRule [(pair (Γ0 ++ A :: Γ1) B)]
                    (pair (Γ0 ++ Γ1) (Imp A B))
.

Inductive AtomImpL1Rule  : rlsT Seq :=
  | AtomImpL1Rule_I : forall P A C Γ0 Γ1 Γ2,
          AtomImpL1Rule [(pair (Γ0 ++ # P :: Γ1 ++ A :: Γ2) C)]
                    (pair (Γ0 ++ # P :: Γ1 ++ (Imp (# P) A) :: Γ2) C)
.

Inductive AtomImpL2Rule  : rlsT Seq :=
  | AtomImpL2Rule_I : forall P A C Γ0 Γ1 Γ2,
          AtomImpL2Rule [(pair (Γ0 ++ A :: Γ1 ++ # P :: Γ2) C)]
                    (pair (Γ0 ++ (Imp (# P) A) :: Γ1 ++ # P :: Γ2) C)
.

Inductive AndImpLRule  : rlsT Seq :=
  | AndImpLRule_I : forall A B C D Γ0 Γ1,
          AndImpLRule [(pair (Γ0 ++  (Imp A (Imp B C)) :: Γ1) D)]
                    (pair (Γ0 ++  (Imp (And A B) C) :: Γ1) D)
.

Inductive OrImpLRule  : rlsT Seq :=
  | OrImpLRule_I : forall A B C D Γ0 Γ1 Γ2,
          OrImpLRule [(pair (Γ0 ++ (Imp A C) :: Γ1 ++ (Imp B C) :: Γ2) D)]
                    (pair (Γ0 ++ (Imp (Or A B) C) :: Γ1 ++ Γ2) D)
.

Inductive ImpImpLRule  : rlsT Seq :=
  | ImpImpLRule_I : forall A B C D Γ0 Γ1,
          ImpImpLRule [(pair (Γ0 ++ (Imp B C) :: Γ1) (Imp A B)) ; (pair (Γ0 ++ C :: Γ1) D)]
                    (pair (Γ0 ++ (Imp (Imp A  B) C) :: Γ1) D)
.

Inductive BoxImpLRule  : rlsT Seq :=
  | BoxImpLRule_I : forall A B C Γ0 Γ1,
          BoxImpLRule [(pair ((unBoxed_list Γ0) ++ B :: (unBoxed_list Γ1) ++ [Box A]) A) ; (pair (Γ0 ++ B :: Γ1) C)]
                    (pair (Γ0 ++ (Imp (Box A) B) :: Γ1) C)
.

Inductive SLRRule : rlsT Seq :=
  | SLRRule_I : forall A  Γ,
         SLRRule [(pair ((unBoxed_list Γ) ++ [Box A]) A)] (pair Γ (Box A))
.

(* At last we can define our calculus G4iSL. *)

Inductive G4iSL_rules : rlsT  Seq :=
  | IdP : forall ps c, IdPRule ps c -> G4iSL_rules ps c
  | BotL : forall ps c, BotLRule ps c -> G4iSL_rules ps c
  | AndR : forall ps c, AndRRule ps c -> G4iSL_rules ps c
  | AndL : forall ps c, AndLRule ps c -> G4iSL_rules ps c
  | OrR1 : forall ps c, OrR1Rule ps c -> G4iSL_rules ps c
  | OrR2 : forall ps c, OrR2Rule ps c -> G4iSL_rules ps c
  | OrL : forall ps c, OrLRule ps c -> G4iSL_rules ps c
  | ImpR : forall ps c, ImpRRule ps c -> G4iSL_rules ps c
  | AtomImpL1 : forall ps c, AtomImpL1Rule ps c -> G4iSL_rules ps c
  | AtomImpL2 : forall ps c, AtomImpL2Rule ps c -> G4iSL_rules ps c
  | AndImpL : forall ps c, AndImpLRule ps c -> G4iSL_rules ps c
  | OrImpL : forall ps c, OrImpLRule ps c -> G4iSL_rules ps c
  | ImpImpL : forall ps c, ImpImpLRule ps c -> G4iSL_rules ps c
  | BoxImpL : forall ps c, BoxImpLRule ps c -> G4iSL_rules ps c
  | SLR : forall ps c, SLRRule ps c -> G4iSL_rules ps c
.

Definition G4iSL_prv s := derrec G4iSL_rules (fun _ => False) s.

