(**

Add meg a sorszámozott feladatok megoldását! Ha valami nem sikerül, kommentezd ki!
A beadott fájlodat fogadja el a Coq! A BEGIN FIX és END FIX közötti részeken ne
módosíts!

A feladatok megoldása során a(z) (e)constructor taktika használata nem
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
| BLe (a1 a2 : AExp)
.

Inductive Stmt : Type :=
| SSkip
| SIf (b : BExp) (S1 S2 : Stmt)
| SWhile (b : BExp) (S0 : Stmt)
| SAssign (x : string) (a : AExp)
| SSeq (S1 S2 : Stmt)
(* END FIX *)
(**
   1. feladat (1 pont): egészítsd ki a parancsok szintaxisát 
   feltételes nullázással (reset)! A konstruktor neve legyen SReset!
   Tehát pl. az alábbi program legyen helyes:

     SSeq
       (SReset (BEq (AVar X) (ALit 3)) X)
       (SReset (BLe (AVar Y) (ALit 14))) Z)

 *)
| SReset (b : BExp)  (x : string)

(* BEGIN FIX *) 
.

Definition X : string := "X"%string.
Definition Y : string := "Y"%string.
Definition Z : string := "Z"%string.

Definition state : Type := string -> nat.

Definition empty : state := fun x => 0.

Definition update (s : state) (x : string) (n : nat) : state :=
  fun x' =>
    match string_dec x x' with
    | left _ => n
    | right _ => s x'
    end.

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
 | BLe a1 a2 => aeval a1 s <=? aeval a2 s
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
   2. feladat (2 pont):
   Add meg a reset utasítás denotációs szemantikáját úgy, hogy az
   eval_test_0--eval_test_8 mind bizonyítható legyen! A definíció legyen
   kompozicionális!

   A reset utasítás a következőképpen működik:
   - ha a feltétel teljesül, a paraméter változó értékét lenullázza.
   - ha a feltétel nem teljesül, nem módosítja az állapotot.

   Nézd végig a teszteseteket, és értsd meg, hogy mikor miért az a helyes végeredmény!
*)

| SReset b x => if beval b st
                   then update st x (aeval (ALit 0) st)
                   else st

(* BEGIN FIX *)
    end
  end.
(* END FIX *)
(* Itt kísérletezgethetsz a denotációs szemantikával: *)

Compute eval 100 (SReset BFalse X) empty X.

(* BEGIN FIX *)
Definition test1 (n k : nat) : Stmt :=
  SSeq
    (SReset (BEq (AVar X) (ALit n)) X)
    (SReset (BLe (AVar Y) (ALit k)) Y).

Definition test2 (n : nat) : Stmt :=
  SWhile (BNot (BEq (AVar X) (ALit n)))
    (SSeq (SAssign X (APlus (AVar X) (ALit 2)))
          (SReset (BNot (BLe (AVar X) (ALit 4))) X)
    ).

Definition mystate1 : state := update (update empty X 5) Y 3.
Definition mystate2 : state := update empty X 1.

Example eval_test_0 : eval 30 (test1 5 4) mystate1 X = 0. Proof. reflexivity. Qed.
Example eval_test_1 : eval 30 (test1 5 4) mystate1 Y = 0. Proof. reflexivity. Qed.
Example eval_test_2 : eval 30 (test1 2 4) mystate1 X = 5. Proof. reflexivity. Qed.
Example eval_test_3 : eval 30 (test1 2 4) mystate1 Y = 0. Proof. reflexivity. Qed.
Example eval_test_4 : eval 30 (test1 2 2) mystate1 Y = 3. Proof. reflexivity. Qed.
Example eval_test_5 : eval 30 (test2 4) empty X = 4. Proof. reflexivity. Qed.
Example eval_test_6 : eval 30 (test2 4) mystate2 X = 4. Proof. reflexivity. Qed.
Example eval_test_7 : eval 30 (test2 3) mystate2 X = 3. Proof. reflexivity. Qed.


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
  3. feladat (3 pont): Add meg a reset operációs szemantikáját! A lenti
  opsem_test_0--opsem_test_2 lemmákat be kell tudnod majd bizonyítani ennek a 
  használatával. A reset működésének leírását az előző feladatban találod.
*)
 | eval_reset_true (b : BExp) (x : string) (s : state) :
       beval b s = true -> 
       (*------------------------------------*)
        | SReset b x , s | -=> update s x (aeval (ALit 0) s)

  | eval_reset_false (b : BExp) (x : string) (s : state) :

       beval b s = false ->
       (*------------------------------------*)
       | SReset b x , s |  -=> s

(* BEGIN FIX *)
where "| s , st | -=> st'" := (eval_bigstep s st st').
(* END FIX *)

(** 4. feladat (1 pont): *)
(* BEGIN FIX *)
Example opsem_test_0 :
  | test1 5 4, mystate1 | -=> update (update mystate1 X 0) Y 0.
(* END FIX *)
Proof.
unfold test1. eapply eval_seq .  apply eval_reset_true .  reflexivity. apply eval_reset_true . reflexivity. 
Qed.
(** 5. feladat (1 pont): *)
(* BEGIN FIX *)
Example opsem_test_1 :
  | test1 2 4, mystate1 | -=> update mystate1 Y 0.
(* END FIX *)
Proof.
unfold test1.  eapply eval_seq.  eapply eval_reset_false .  reflexivity. apply eval_reset_true . reflexivity. 
Qed.

(** 6. feladat (2 pont): *)
(* BEGIN FIX *)
Example opsem_test_2 :
  | test2 2, mystate2 | -=> update (update (update (update mystate2 X 3) X 5) X 0) X 2.
(* END FIX *)
Proof.
unfold test2. eapply eval_while_true. reflexivity. eapply eval_seq. eapply eval_assign. eapply eval_reset_false. 
reflexivity. eapply eval_while_true. reflexivity. eapply eval_seq. eapply eval_assign. eapply eval_reset_true. reflexivity. 
eapply eval_while_true. reflexivity.   eapply eval_seq. eapply eval_assign. eapply eval_reset_false.  reflexivity. 
eapply eval_while_false. reflexivity.
Qed.

(* BEGIN FIX *)
(**
   7. feladat (1 pont): Add meg a reset utasítást szintaktikus cukorkaként!
   (Ne használd az SReset konstruktort a feladat megoldásához)
*)

Definition reset_sugar (b : BExp) (x : string) : Stmt :=
(* END FIX *)
  (** Ennek a kommentnek a helyére írd a definíciót *)


(* BEGIN FIX *)
Definition test1_sugar (n k : nat) : Stmt :=
  SSeq
    (reset_sugar (BEq (AVar X) (ALit n)) X)
    (reset_sugar (BLe (AVar Y) (ALit k)) Y).

Definition test2_sugar (n : nat) : Stmt :=
  SWhile (BNot (BEq (AVar X) (ALit n)))
    (SSeq (SAssign X (APlus (AVar X) (ALit 2)))
          (reset_sugar (BNot (BLe (AVar X) (ALit 4))) X)
    ).

Example eval_test_0_sugar : eval 30 (test1_sugar 5 4) mystate1 X = 0. Proof. reflexivity. Qed.
Example eval_test_1_sugar : eval 30 (test1_sugar 5 4) mystate1 Y = 0. Proof. reflexivity. Qed.
Example eval_test_2_sugar : eval 30 (test1_sugar 2 4) mystate1 X = 5. Proof. reflexivity. Qed.
Example eval_test_3_sugar : eval 30 (test1_sugar 2 4) mystate1 Y = 0. Proof. reflexivity. Qed.
Example eval_test_4_sugar : eval 30 (test1_sugar 2 2) mystate1 Y = 3. Proof. reflexivity. Qed.
Example eval_test_5_sugar : eval 30 (test2_sugar 4) empty X = 4. Proof. reflexivity. Qed.
Example eval_test_6_sugar : eval 30 (test2_sugar 4) mystate2 X = 4. Proof. reflexivity. Qed.
Example eval_test_7_sugar : eval 30 (test2_sugar 3) mystate2 X = 3. Proof. reflexivity. Qed.

(* 8. feladat (2 pont): Bizonyítsd az alábbi tételt (Tipp: inversion, subst, disriminate, cbn in *, simpl in *, és clear taktikák használata sokat segíthet. Figyelj arra, hogy egy hipotézisre csak egyszer végezz inversion-t!) : *)
Goal forall st, | test2_sugar 2, mystate2 | -=> st -> 
   st X = 2.
Proof.
(* END FIX *)

Admitted.

(* BEGIN FIX *)
Definition Equiv (S1 S2 : Stmt) : Prop := forall st st',
  | S1, st | -=> st' <-> | S2, st | -=> st'.

(* 9. feladat (2 pont): Bizonyítsd az ekvivalenciát a reset utasítás és a 
   szintaktikus cukorként megadott reset utasítás között! *)
Theorem equiv_thm : forall b x, Equiv (SReset b x) (reset_sugar b x).
Proof.
(* END FIX *)

Admitted.
