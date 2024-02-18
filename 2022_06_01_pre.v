(**

Add meg a sorszámozott feladatok megoldását! Ha valami nem sikerül, kommentezd ki!
A beadott fájlodat fogadja el a Coq! A BEGIN FIX és END FIX közötti részeken ne
módosíts!

A feladatok megoldása során a(z) (e)constructor takika használata nem
megengedett!

Maximális pontszám: 15 pont
A minimum elérendő pontszám: 7 pont.


*)

(* BEGIN FIX *)
From Coq Require Import Strings.String
                        Arith.PeanoNat
                        Arith.Plus
                        Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive AExp : Type :=
| ALit (n : nat)
| AVar (x : string)
| APlus (a1 a2 : AExp)
| AMinus (a1 a2 : AExp)
| AMult (a1 a2 : AExp).

Inductive BExp : Type :=
| BTrue
| BFalse
| BAnd (b1 b2 : BExp)
| BNot (b : BExp)
| BEq (a1 a2 : AExp)
| BLeq (a1 a2 : AExp)
.

Inductive Stmt : Type :=
| SSkip
| SIf (b : BExp) (S1 S2 : Stmt)
| SWhile (b : BExp) (S0 : Stmt)
| SAssign (x : string) (a : AExp)
| SSeq (S1 S2 : Stmt)
(* END FIX *)
(**
   1. feladat (1 pont): egészitsd ki a parancsok szintaxisát 
   hátultesztelő ciklussal ("repeat-until" ciklus)!
   A konstruktor neve legyen SRepeat!
   Tehát pl. az alábbi program legyen helyes:

     SSeq
       (SAssign X (ALit 0))
       (SRepeat (SAssign X (APlus (AVar X) (ALit 1))) (BLe (AVar X) (ALit 10)))

 *)

| SRepeat (S0 : Stmt) (b : BExp)
(* BEGIN FIX *)
.

Definition X : string := "X"%string.
Definition Y : string := "Y"%string.
Definition Z : string := "Z"%string.

Definition state : Type := string -> nat.

Definition empty : state := fun x => 0.

Definition update (s : state) (x : string) (n : nat) : state :=
  fun x' =>
    if eqb x x'
    then n
    else s x'.

Fixpoint aeval (a : AExp) (s : state) : nat :=
match a with
| ALit n => n
| AVar x => s x
| APlus a1 a2 => (aeval a1 s) + (aeval a2 s)
| AMinus a1 a2 => (aeval a1 s) - (aeval a2 s)
| AMult a1 a2 => (aeval a1 s) * (aeval a2 s)
end.

Fixpoint beval (b : BExp)(s : state) : bool :=
match b with
 | BTrue => true
 | BFalse => false
 | BAnd b1 b2 => (beval b1 s) && (beval b2 s)
 | BNot b => negb (beval b s)
 | BEq a1 a2 => aeval a1 s =? aeval a2 s
 | BLeq a1 a2 => aeval a1 s <=? aeval a2 s
end.

Fixpoint eval (fuel : nat) (S0 : Stmt) (st : state) : state :=
match fuel with
| 0 => st
| S fuel' =>
  match S0 with
  | SSkip => st
  | SAssign x a => update st x (aeval a st)
  | SSeq S1 S2 => eval fuel' S2 (eval fuel' S1 st)
  | SIf b S1 S2 => if beval b st
                   then eval fuel' S1 st
                   else eval fuel' S2 st
  | SWhile b S0 => if beval b st
                   then eval fuel' (SWhile b S0) (eval fuel' S0 st)
                   else st
(* END FIX *)

(**
   2. feladat (3 pont): 
   Add meg a hátultesztelő ciklus denotációs szemantikáját úgy, hogy az
   eval_test_0--eval_test_8 mind bizonyítható legyen! A hátultesztelő ciklus
   a megszokott módon működik: végrehajtja a ciklusmagot, EZUTÁN ellenőrzi a feltételt
   (a módositott állapotban), amely ha IGAZ, akkor a ciklus végrehajtása MEGÁLL.

   FIGYELEM!
   A ciklusfeltétel kilépési feltétel, azaz akkor hajtódik végre a
   ciklusmag újra, ha a feltétel hamis! Nézd végig a teszteseteket, és értsd meg, 
   hogy mikor miért az a helyes végeredmény!

   Itt a gyakorlaton megszokott módon, a kompozicionalitás elve annyiban sérülhet,
   hogy a definícióban a hátulteszteltelő ciklus szemanikáját felhasználhatod.
*)

| SRepeat S0 b => if beval b st
                   then st
                   else  eval fuel' (SRepeat S0 b) (eval fuel' S0 st ) 

(* BEGIN FIX *)
    end
  end.
(* END FIX *)
(* Itt kísérletezgethetsz a denotációs szemantikával: *)

Compute eval 10 (SRepeat SSkip BFalse) empty X.

(* BEGIN FIX *)
Definition test1 (k n : nat) : Stmt :=
   SSeq
     (SAssign X (ALit 0))
     (SRepeat (SAssign X (APlus (AVar X) (ALit k))) 
              (BNot (BLeq (AVar X) (ALit n)))).

Definition test2 (n : nat) : Stmt :=
  SRepeat (SSeq
               (SIf (BLeq (AVar Y) (AVar X))
               (SAssign X (AMinus (AVar X) (AVar Y)))
               SSkip)
               (SAssign Y (AMinus (AVar Y) (ALit n)))
          )
          (BEq (AVar Y) (ALit 0)).

Definition mystate : state := update (update empty X 5) Y 3.

Example eval_test_0 : eval 30 (test1 2 2) empty X = 4. Proof. reflexivity. Qed.
Example eval_test_1 : eval 30 (test1 10 2) empty X = 10. Proof. reflexivity. Qed.
Example eval_test_2 : eval 30 (test1 2 5) empty X = 6. Proof. reflexivity. Qed.
Example eval_test_3 : eval 30 (test2 5) empty Y = 0. Proof. reflexivity. Qed.
Example eval_test_4 : eval 30 (test2 5) empty X = 0. Proof. reflexivity. Qed.
Example eval_test_5 : eval 30 (test2 2) mystate Y = 0. Proof. reflexivity. Qed.
Example eval_test_6 : eval 30 (test2 2) mystate X = 1. Proof. reflexivity. Qed.
Example eval_test_7 : eval 30 (test2 3) mystate Y = 0. Proof. reflexivity. Qed.
Example eval_test_8 : eval 30 (test2 3) mystate X = 2. Proof. reflexivity. Qed.

Reserved Notation "| s , st | -=> st'" (at level 50).
Inductive eval_bigstep : Stmt -> state -> state -> Prop :=

  | eval_skip (s : state) :

       (*----------------*)
       | SSkip , s | -=> s

  | eval_assign (x : string) (a : AExp) (s : state) :

       (*------------------------------------*)
       | SAssign x a , s | -=> update s x (aeval a s)

  | eval_seq (S1 S2 : Stmt) (s s' s'' : state) : 

       | S1 , s | -=> s'  ->  | S2 , s' | -=> s''  ->
       (*------------------------------------*)
              | SSeq S1 S2 , s | -=> s''

  | eval_if_true (S1 S2 : Stmt) (b : BExp) (s s' : state) :

       beval b s = true -> | S1 , s | -=> s' ->
       (*------------------------------------*)
       | SIf b S1 S2 , s | -=> s'

  | eval_if_false (S1 S2 : Stmt) (b : BExp) (s s' : state) :

       beval b s = false -> | S2 , s | -=> s' ->
       (*------------------------------------*)
       | SIf b S1 S2 , s | -=> s'

  | eval_while_false (S0 : Stmt) (b : BExp) (s : state) :

           beval b s = false ->
       (*------------------------*)
       | SWhile b S0 , s | -=> s

  | eval_while_true (S0 : Stmt) (b : BExp)(s s' s'' : state) :

       beval b s = true ->
       | S0 , s | -=> s' ->
       | SWhile b S0 , s' | -=> s'' ->
       (*---------------------------*)
       | SWhile b S0 , s | -=> s''


  
(* END FIX *)
(**
   3. feladat (4 pont): add meg a hátultesztelő ciklus operációs szemantikáját! A lenti
   opsem_test_0--opsem_test_1 lemmákat be kell tudnod majd bizonyítani ennek a 
   használatával.

   Természetesen itt is figyelj arra, hogy a ciklusfeltétel KILÉPÉSI
   feltétel, illetve, hogy a feltétel-ellenőrzés előtt lefut a ciklusmag!
*)
  | eval_repeat_false (S0 : Stmt) (b : BExp)(s s' s'' : state) :

       beval b s = false ->
       | S0 , s | -=> s' ->
       | SRepeat S0 b , s' | -=> s'' ->
       (*---------------------------*)
       | SRepeat S0 b , s | -=> s''
  | eval_repeat_true (S0 : Stmt) (s : state)  (b : BExp) :

           beval b s = true ->
       (*------------------------*)
       | SRepeat S0 b , s | -=> s
  
(* BEGIN FIX *)
where "| s , st | -=> st'" := (eval_bigstep s st st').
(* END FIX *)

(** 4. feladat (1 pont): *)
(* BEGIN FIX *)
Example opsem_test_0 :
  | test2 3, update empty Y 3 | -=> update (update empty Y 3) Y 0.
(* END FIX *)
Proof.

Admitted.

(** 5. feladat (2 pont): *)
(* BEGIN FIX *)
Example opsem_test_1 :
  | test2 2, mystate | -=> update (update (update (update mystate X 2) Y 1) X 1) Y 0.
(* END FIX *)
Proof.

Admitted.

(* BEGIN FIX *)
(**
   6. feladat (1 pont): Add meg a hátultesztelő ciklust szintaktikus cukorkaként!
*)

Definition repeat_sugar (S0 : Stmt) (b : BExp) : Stmt :=
(* END FIX *)
  (** Ennek a kommentnek a helyére írd a definíciót *)



(* BEGIN FIX *)
Definition test1_sugar (k n : nat) : Stmt :=
   SSeq
     (SAssign X (ALit 0))
     (repeat_sugar (SAssign X (APlus (AVar X) (ALit k))) 
              (BNot (BLeq (AVar X) (ALit n)))).

Definition test2_sugar (n : nat) : Stmt :=
  repeat_sugar (SSeq
               (SIf (BLeq (AVar Y) (AVar X))
               (SAssign X (AMinus (AVar X) (AVar Y)))
               SSkip)
               (SAssign Y (AMinus (AVar Y) (ALit n)))
          )
          (BEq (AVar Y) (ALit 0)).

Example eval_test_sugar_0 : eval 30 (test1_sugar 2 2) empty X = 4. Proof. reflexivity. Qed.
Example eval_test_sugar_1 : eval 30 (test1_sugar 10 2) empty X = 10. Proof. reflexivity. Qed.
Example eval_test_sugar_2 : eval 30 (test1_sugar 2 5) empty X = 6. Proof. reflexivity. Qed.
Example eval_test_sugar_3 : eval 30 (test2_sugar 5) empty Y = 0. Proof. reflexivity. Qed.
Example eval_test_sugar_4 : eval 30 (test2_sugar 5) empty X = 0. Proof. reflexivity. Qed.
Example eval_test_sugar_5 : eval 30 (test2_sugar 2) mystate Y = 0. Proof. reflexivity. Qed.
Example eval_test_sugar_6 : eval 30 (test2_sugar 2) mystate X = 1. Proof. reflexivity. Qed.
Example eval_test_sugar_7 : eval 30 (test2_sugar 3) mystate Y = 0. Proof. reflexivity. Qed.
Example eval_test_sugar_8 : eval 30 (test2_sugar 3) mystate X = 2. Proof. reflexivity. Qed.

Definition Equiv (S1 S2 : Stmt) : Prop := forall st st',
 | S1 , st | -=> st' <-> | S2 , st | -=> st'.

(** 7. feladat (3 pont): Bizonyítsd az alábbi ekvivalenciát! Segítségképp
     megadtuk a kezdeti lépéseket mindkét bizonyítandó esetben. *)
Theorem equiv_sugar :
  forall b S0, Equiv (SRepeat S0 b) (repeat_sugar S0 b).
(* END FIX *)
Proof.
  split; intro.
  {
    dependent induction H.
    *
    *
  }
  {
    inversion H. subst. clear H. generalize dependent st. dependent induction H5.
    *
    *
  }
Qed.
