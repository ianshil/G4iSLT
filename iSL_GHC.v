Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Ensembles.

Require Import general_export.

Require Import DiSL_calc.

(* We define here the axioms. *)

Definition IA1 (A B : MPropF) : MPropF := A → (B → A).
Definition IA2 (A B C : MPropF) : MPropF := (A → (B → C)) → ((A → B) → (A → C)).
Definition IA3 (A B : MPropF) : MPropF := A → (Or A B).
Definition IA4 (A B : MPropF) : MPropF := B → (Or A B).
Definition IA5 (A B C : MPropF) : MPropF := (A → C) → ((B → C) → ((Or A B) → C)).
Definition IA6 (A B : MPropF) : MPropF := (And A B) → A.
Definition IA7 (A B : MPropF) : MPropF := (And A B) → B.
Definition IA8 (A B C : MPropF) : MPropF := (A → B) → ((A → C) → (A → (And B C))).
Definition IA9 (A : MPropF) : MPropF := Bot → A.
Definition MA10 (A B : MPropF) : MPropF := Box (A → B) → (Box A → Box B).
Definition MA11 (A B : MPropF) : MPropF := (Box A → A) → A.

Inductive iSLAxioms (A : MPropF) : Type :=
 | IA1_I : (existsT2 B C, A = (IA1 B C)) -> iSLAxioms A
 | IA2_I : (existsT2 B C D, A = (IA2 B C D)) -> iSLAxioms A
 | IA3_I :  (existsT2 B C, A = (IA3 B C)) -> iSLAxioms A
 | IA4_I :  (existsT2 B C, A = (IA4 B C)) -> iSLAxioms A
 | IA5_I : (existsT2 B C D, A = (IA5 B C D)) -> iSLAxioms A
 | IA6_I :  (existsT2 B C, A = (IA6 B C)) -> iSLAxioms A
 | IA7_I :  (existsT2 B C, A = (IA7 B C)) -> iSLAxioms A
 | IA8_I : (existsT2 B C D, A = (IA8 B C D)) -> iSLAxioms A
 | IA9_I : (existsT2 B, A = (IA9 B)) -> iSLAxioms A
 | MA10_I :  (existsT2 B C, A = (MA10 B C)) -> iSLAxioms A
 | MA11_I :  (existsT2 B C, A = (MA11 B C)) -> iSLAxioms A.

(* Then, we can define the rules which constitute our calculi. We gather
   them in cacluli in a definition appearing later.

   We start by giving the rules common to both calculi. *)

Inductive IdRule : rlsT ((Ensemble MPropF) * MPropF) :=
  | IdRule_I : forall A (Γ : Ensemble _),
                  (Γ A) -> IdRule [] (Γ , A).

Inductive AxRule : rlsT ((Ensemble MPropF) * MPropF) :=
  | AxRule_I : forall Γ (A : MPropF),
          (iSLAxioms A) -> AxRule [] (Γ , A).

Inductive MPRule : rlsT ((Ensemble MPropF) * MPropF) :=
  | MPRule_I : forall A B Γ,
          MPRule [(Γ , A → B); (Γ , A)]
                    (Γ , B).

(* Then we turn to the distinctive rules of each calculus. *)

Inductive NecRule : rlsT ((Ensemble MPropF) * MPropF) :=
  | NecRule_I : forall (A : MPropF) Γ,
          NecRule [(Empty_set MPropF , A)]
                                     (Γ , Box A).

(* At last we can define our calculi iSLH and sKH. *)

Inductive iSLH_rules (s : ((Ensemble _) * MPropF)) : Type :=
  | Id : IdRule [] s -> iSLH_rules s
  | Ax : AxRule [] s -> iSLH_rules s
  | MP : forall ps, (forall prem, List.In prem ps -> iSLH_rules prem) -> MPRule ps s -> iSLH_rules s
  | wNec : forall ps, (forall prem, List.In prem ps -> iSLH_rules prem) -> NecRule ps s -> iSLH_rules s
.

(* Then, we define macros for provability. *)

Definition iSLH_prv s := iSLH_rules s.
