(**

Add meg a sorszamozott feladatok megoldasat! Ha valami nem sikerul, kommentezd ki!
A beadott fajlodat fogadja el a Coq! A BEGIN FIX es END FIX kozotti reszeken ne modosits!

Maximalis pontszam: 15 pont (plusz feladatok nelkul)
A minimum elerendo pontszam 7.

*)

(* BEGIN FIX *)
From Coq Require Import Strings.String
                        Arith.PeanoNat
                        Arith.Plus
                        Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Definition Ident : Type := string.

Inductive AExp : Type :=
| ALit (n : nat)
| AVar (x : Ident)
| APlus (a1 a2 : AExp)
| AMinus (a1 a2 : AExp)
| AMult (a1 a2 : AExp).

Inductive BExp : Type :=
| BTrue
| BFalse
| BAnd (b1 b2 : BExp)
| BNot (b : BExp)
| BEq (a1 a2 : AExp)
| BLe (a1 a2 : AExp)
.

Inductive Stmt : Type :=
| SSkip
| SIf (b : BExp) (S1 S2 : Stmt)
| SWhile (b : BExp) (S0 : Stmt)
| SAssign (x : Ident) (a : AExp)
| SSeq (S1 S2 : Stmt)
(* END FIX *)
(**
   1. feladat (1 pont): egeszitsd ki a parancsok szintaxisat 
   hatultesztelo ciklussal ("repeat-until" ciklus)!
   A konstruktor neve legyen SRepeat!
   Tehat pl. az alabbi programot legyen jol formazott:

     SSeq
       (SAssign X (ALit 0))
       (SRepeat (SAssign X (APlus (AVar X) (ALit 1))) (BLe (AVar X) (ALit 10)))

 *)

| SRepeat (S0 : Stmt) (b : BExp)
(* BEGIN FIX *)
.

Definition X : Ident := "X"%string.
Definition Y : Ident := "Y"%string.
Definition Z : Ident := "Z"%string.

Definition State : Type := Ident -> nat.

Definition empty : State := fun x => 0.

Definition update (s : State) (x : Ident) (n : nat) : State :=
  fun x' =>
    if eqb x x'
    then n
    else s x'.

Fixpoint aeval (a : AExp) (s : State) : nat :=
match a with
| ALit n => n
| AVar x => s x
| APlus a1 a2 => (aeval a1 s) + (aeval a2 s)
| AMinus a1 a2 => (aeval a1 s) - (aeval a2 s)
| AMult a1 a2 => (aeval a1 s) * (aeval a2 s)
end.

Fixpoint beval (b : BExp)(s : State) : bool :=
match b with
 | BTrue => true
 | BFalse => false
 | BAnd b1 b2 => (beval b1 s) && (beval b2 s)
 | BNot b => negb (beval b s)
 | BEq a1 a2 => aeval a1 s =? aeval a2 s
 | BLe a1 a2 => aeval a1 s <=? aeval a2 s
end.

Fixpoint eval (S0 : Stmt) (st : State) (fuel : nat) : State :=
match fuel with
| 0 => st
| S fuel' =>
  match S0 with
  | SSkip => st
  | SAssign x a => update st x (aeval a st)
  | SSeq S1 S2 => eval S2 (eval S1 st fuel') fuel'
  | SIf b S1 S2 => if beval b st
                   then eval S1 st fuel'
                   else eval S2 st fuel'
  | SWhile b S0 => if beval b st
                   then eval (SWhile b S0) (eval S0 st fuel') fuel'
                   else st
(* END FIX *)

(** 
   2. feladat (3 pont): 
   Add meg a hatultesztelo ciklus denotacios szemantikajat ugy, hogy az
   eval_test_0--eval_test_8 mind bizonyithato legyen! A hatultesztelo ciklus
   a megszokott modon mukodik: vegrehajtja a ciklusmagot, EZUTAN ellenorzi a feltetelt
   (a modositott allapotban), mely ha IGAZ, akkor a ciklus vegrehajtas MEGALL.
   FIGYELEM!! A ciklusfeltetel kilepesi feltetel, azaz akkor hajtodik vegre a
   ciklusmag ujra, ha a feltetel hamis! Nezd vegig a teszteseteket, es ertsd meg, 
   hogy mikor miert az a helyes vegeredmeny!
*)

| SRepeat S0 b => if  beval b (eval S0 st fuel')
                   then (eval S0 st fuel')
                   else eval( SRepeat S0 b) (eval S0 st fuel') fuel'
(* BEGIN FIX *)
    end
  end.
(* END FIX *)
(* Itt kiserletezgethetsz a denotacios szemantikaval: *)


(* BEGIN FIX *)
Definition test1 (k n : nat) : Stmt :=
   SSeq
     (SAssign X (ALit 0))
     (SRepeat (SAssign X (APlus (AVar X) (ALit k))) 
              (BNot (BLe (AVar X) (ALit n)))).

Definition test2 (n : nat) : Stmt :=
  SRepeat (SSeq
               (SIf (BLe (AVar Y) (AVar X))
               (SAssign X (AMinus (AVar X) (AVar Y)))
               SSkip)
               (SAssign Y (AMinus (AVar Y) (ALit n)))
          )
          (BEq (AVar Y) (ALit 0)).

Definition myState : State := update (update empty X 5) Y 3.

Compute eval (test1 2 2) empty 30 X = 4.
Example eval_test_0 : eval (test1 2 2) empty 30 X = 4. Proof. reflexivity. Qed.
Example eval_test_1 : eval (test1 10 2) empty 30 X = 10. Proof. reflexivity. Qed.
Example eval_test_2 : eval (test1 2 5) empty 30 X = 6. Proof. reflexivity. Qed.
Example eval_test_3 : eval (test2 5) empty 30 Y = 0. Proof. reflexivity. Qed.
Example eval_test_4 : eval (test2 5) empty 30 X = 0. Proof. reflexivity. Qed.
Example eval_test_5 : eval (test2 2) myState 30 Y = 0. Proof. reflexivity. Qed.
Example eval_test_6 : eval (test2 2) myState 30 X = 1. Proof. reflexivity. Qed.
Example eval_test_7 : eval (test2 3) myState 30 Y = 0. Proof. reflexivity. Qed.
Example eval_test_8 : eval (test2 3) myState 30 X = 2. Proof. reflexivity. Qed.

Reserved Notation "| s , st | -=> st'" (at level 50).
Inductive eval_bigstep : Stmt -> State -> State -> Prop :=

  | eval_skip (s : State) :

       (*----------------*)
       | SSkip , s | -=> s

  | eval_assign (x : string) (a : AExp) (s : State) :

       (*------------------------------------*)
       | SAssign x a , s | -=> update s x (aeval a s)

  | eval_seq (S1 S2 : Stmt) (s s' s'' : State) : 

       | S1 , s | -=> s'  ->  | S2 , s' | -=> s''  ->
       (*------------------------------------*)
              | SSeq S1 S2 , s | -=> s''

  | eval_if_true (S1 S2 : Stmt) (b : BExp) (s s' : State) :

       beval b s = true -> | S1 , s | -=> s' ->
       (*------------------------------------*)
       | SIf b S1 S2 , s | -=> s'

  | eval_if_false (S1 S2 : Stmt) (b : BExp) (s s' : State) :

       beval b s = false -> | S2 , s | -=> s' ->
       (*------------------------------------*)
       | SIf b S1 S2 , s | -=> s'

  | eval_while_false (S0 : Stmt) (b : BExp) (s : State) :

           beval b s = false ->
       (*------------------------*)
       | SWhile b S0 , s | -=> s

  | eval_while_true (S0 : Stmt) (b : BExp)(s s' s'' : State) :

       beval b s = true ->
       | S0 , s | -=> s' ->
       | SWhile b S0 , s' | -=> s'' ->
       (*---------------------------*)
       | SWhile b S0 , s | -=> s''

  | eval_repeat_true (S0 : Stmt) (s : State)  (b : BExp) :

           beval b s = true ->
       (*------------------------*)
       | SRepeat S0 b , s | -=> s

  | eval_repeat_false (S0 : Stmt) (b : BExp)(s s' s'' : State) :

       beval b s = false ->
       | S0 , s | -=> s' ->
       | SRepeat S0 b , s' | -=> s'' ->
       (*---------------------------*)
       | SRepeat S0 b , s | -=> s''
(* END FIX *)
(**
  3. feladat (4 pont): add meg a hatultesztelo ciklus operacios szemantikajat! A lenti
  opsem_test_0--opsem_test_2 lemmakat be kell tudnod majd bizonyitani ennek a 
  hasznalataval. Termeszetesen itt is figyelj arra, hogy a ciklusfeltetel KILEPESI
  feltetel, illetve, hogy a feltetel-ellenorzes elott lefut a ciklusmag!
*)

(* BEGIN FIX *)
where "| s , st | -=> st'" := (eval_bigstep s st st').
(* END FIX *)

(** 4. feladat (1 pont): *)
(* BEGIN FIX *)
Example opsem_test_0 :
  | test2 3, update empty Y 3 | -=> update (update empty Y 3) Y 0.
(* END FIX *)
Proof.
  unfold test2. unfold update.
Qed.

(** 5. feladat (2 pont): *)
(* BEGIN FIX *)
Example opsem_test_1 :
  | test1 2 2 , empty | -=> update (update (update empty X 0) X 2) X 4.
(* END FIX *)
Proof.

Qed.

(** 6. feladat (2 pont): *)

(* BEGIN FIX *)
Example opsem_test_2 :
  | test2 2, myState | -=> update (update (update (update myState X 2) Y 1) X 1) Y 0.
(* END FIX *)
Proof.

Qed.

(* BEGIN FIX *)
(**
   7. feladat (2 pont): Add meg a hatultesztelo ciklust szintaktikus cukorkakent!
   Azaz definiald a repeat-until ciklust az SRepeat konstruktor hasznalata nelkul!
*)

Definition repeat_sugar (S0 : Stmt) (b : BExp) : Stmt :=
(* END FIX *)
  (** Ennek a kommentnek a helyere ird a definiciot *)
.


(* BEGIN FIX *)
Definition test1_sugar (k n : nat) : Stmt :=
   SSeq
     (SAssign X (ALit 0))
     (repeat_sugar (SAssign X (APlus (AVar X) (ALit k))) 
              (BNot (BLe (AVar X) (ALit n)))).

Definition test2_sugar (n : nat) : Stmt :=
  repeat_sugar (SSeq
               (SIf (BLe (AVar Y) (AVar X))
               (SAssign X (AMinus (AVar X) (AVar Y)))
               SSkip)
               (SAssign Y (AMinus (AVar Y) (ALit n)))
          )
          (BEq (AVar Y) (ALit 0)).

Example eval_test_sugar_0 : eval (test1_sugar 2 2) empty 30 X = 4. Proof. reflexivity. Qed.
Example eval_test_sugar_1 : eval (test1_sugar 10 2) empty 30 X = 10. Proof. reflexivity. Qed.
Example eval_test_sugar_2 : eval (test1_sugar 2 5) empty 30 X = 6. Proof. reflexivity. Qed.
Example eval_test_sugar_3 : eval (test2_sugar 5) empty 30 Y = 0. Proof. reflexivity. Qed.
Example eval_test_sugar_4 : eval (test2_sugar 5) empty 30 X = 0. Proof. reflexivity. Qed.
Example eval_test_sugar_5 : eval (test2_sugar 2) myState 30 Y = 0. Proof. reflexivity. Qed.
Example eval_test_sugar_6 : eval (test2_sugar 2) myState 30 X = 1. Proof. reflexivity. Qed.
Example eval_test_sugar_7 : eval (test2_sugar 3) myState 30 Y = 0. Proof. reflexivity. Qed.
Example eval_test_sugar_8 : eval (test2_sugar 3) myState 30 X = 2. Proof. reflexivity. Qed.

Definition Equiv (S1 S2 : Stmt) : Prop := forall st st',
  | S1, st | -=> st' <-> | S2, st | -=> st'.

(**
  Bonusz feladat (3 plusz pont a gyakorlati reszhez): Bizonyitsd be, hogy a repeat-until ciklus ekvivalens a kigorgetettjevel!
  Tipp: hasznald a Search parancsot logikai erteken definialt negalasra vontakozo tetelek kereseseben.
*)
Theorem repeat_equiv :
  forall b S0, Equiv (SRepeat S0 b) (SSeq S0 (SIf (BNot b) (SRepeat S0 b) SSkip)).
Proof.
(* END FIX *)
  
Qed.