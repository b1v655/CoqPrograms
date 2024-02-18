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
| BLe (a1 a2 : AExp).

Inductive Stmt : Type :=
| SSkip
| SIf (b : BExp) (S1 S2 : Stmt)
| SWhile (b : BExp) (S0 : Stmt)
| SAssign (x : Ident) (a : AExp)
| SSeq (S1 S2 : Stmt)
(* END FIX *)
(**
   1. feladat (1 pont): egeszitsd ki a parancsok szintaxisat 
   szimultan ertekadassal!
   A konstruktor neve legyen SAssigns!
   Tehat pl. az alabbi program legyen helyes:

     SSeq
       (SAssigns X Y (ALit 1) (APlus (ALit 2) (ALit 3)))
       (SAssign X (AVar Y)).

 *)
| SAssigns (x y : Ident) (a1 a2 : AExp)
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

Fixpoint eval (S0 : Stmt) (s : State) (niter : nat) : State :=
match niter with
| O => s
| S n' => match S0 with
  | SSkip       => s
  | SIf b c1 c2 => if beval b s then eval c1 s n' else eval c2 s n'
  | SWhile b c  => if beval b s then eval (SWhile b c) (eval c s n') n' else s
  | SAssign x a => update s x (aeval a s)
  | SSeq c1 c2  => eval c2 (eval c1 s n') n'
(* END FIX *)
  | SAssigns x y a1 a2 => update (update s y (aeval a2 s)) x (aeval a1 s)
(** 
   2. feladat (3 pont): 
   add meg a SAssigns denotacios szemantikajat ugy, hogy a eval_test_0--eval_test_7 
   mind bizonyithato legyen! Fontos, hogy ez szimultan ertekadas, nem ket ertekadas
   egymas utan. Ha ketszer ismetlodik ugyanaz a valtozo (pl. SAssigns X X 1 2),
   akkor a vegeredmeny mindegy, hogy mi. Nezd vegig a
   teszteseteket, es ertsd meg, hogy mikor miert az a helyes vegeredmeny.
*)


(* BEGIN FIX *)
    end
  end.
(* END FIX *)
(* Itt kiserletezgethetsz a denotacios szemantikaval: *)

Compute eval (SAssigns X Y (ALit 3) (ALit 2)) empty 20 X.

(* BEGIN FIX *)
Example eval_test_0 : eval (SAssigns X Y (ALit 3) (ALit 2)) empty 30 X = 3.
Proof. reflexivity. Qed.
Example eval_test_1 : eval (SAssigns X Y (ALit 3) (ALit 2)) empty 30 Y = 2.
Proof. reflexivity. Qed.
Example eval_test_2 : eval (SAssigns X Y (ALit 3) (AVar X)) empty 30 X = 3.
Proof. reflexivity. Qed.
Example eval_test_3 : eval (SAssigns X Y (ALit 3) (AVar X)) empty 30 Y = 0.
Proof. reflexivity. Qed.
Example eval_test_4 : eval (SAssigns Y X (ALit 3) (AVar Y)) empty 30 X = 0.
Proof. reflexivity. Qed.
Example eval_test_5 : eval (SAssigns Y X (ALit 3) (AVar Y)) empty 30 Y = 3.
Proof. reflexivity. Qed.
Example eval_test_6 : eval (SSeq (SAssigns X Y (ALit 1) (ALit 2)) (SAssigns X Y (AVar Y) (AVar X))) empty 30 X = 2. Proof. reflexivity. Qed.
Example eval_test_7 : eval (SSeq (SAssigns X Y (ALit 1) (ALit 2)) (SAssigns X Y (AVar Y) (AVar X))) empty 30 Y = 1. Proof. reflexivity. Qed.

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

(* END FIX *)
(**
  3. feladat (3 pont): add meg a szimultan ertekadas operacios szemantikajat! A lenti
  opsem_test_0--opsem_test_2 lemmakat be kell tudnod majd bizonyitani ennek a 
  hasznalataval.
*)
  | eval_assigns (x y : string) (a1 a2 : AExp) (s : State) :

       (*------------------------------------*)
       | SAssigns x y a1 a2 , s | -=> update (update s y (aeval a2 s) ) x (aeval a1 s)

(* BEGIN FIX *)
where "| s , st | -=> st'" := (eval_bigstep s st st').
(* END FIX *)

(** 4. feladat (1 pont): *)

(* BEGIN FIX *)
Example opsem_test_0 :
  exists s, | SAssigns X Y (ALit 6) (ALit 4) , empty | -=> s /\ s X = 6 /\ s Y = 4.
(* END FIX *)
Proof.

Qed.

(** 5. feladat (1 pont): *)

(* BEGIN FIX *)
Example opsem_test_1 :
  exists s, | SAssigns X Y (ALit 5) (AVar X) , empty | -=> s /\ s X = 5 /\ s Y = 0.
(* END FIX *)
Proof.

Qed.
(** 6. feladat (2 pont): *)

(* BEGIN FIX *)
Example opsem_test_2 :
  exists s, | SWhile (BLe (AVar X) (ALit 4)) 
                     (SAssigns Y X (APlus (AVar X) (ALit 5)) (AVar Y)), 
              empty | -=> s /\ s X = 5 /\ s Y = 5.
(* END FIX *)
Proof.

Qed.

(**
   7. feladat (2 pont): mutasd meg, hogy kulonbozik a szimultan es a
   szekvencialis ertekadas!
*)

(* BEGIN FIX *)
Lemma not_sugar : exists (a1 a2 : AExp) (s1 s2 : State),
  | SAssigns X Y a1 a2 , empty | -=> s1 /\
  | SSeq (SAssign X a1) (SAssign Y a2) , empty | -=> s2 /\
  s1 Y <> s2 Y.
(* END FIX *)
Proof.

Qed.

(* BEGIN FIX *)
Definition Equiv (S1 S2 : Stmt) : Prop := forall st st',
  | S1, st | -=> st' <-> | S2, st | -=> st'.

(**
   8. feladat (2 pont): Bizonyitsd be, hogy a szimultan ertekadas ekvivalens
   ertekadasok szekvenciajaval, ha az ertekadasokat literal kifejezesekkel hajtjuk
   vegre!

   Tipp: ha szukseges, hasznalj fuggvenyextenzionalitast!
*)

Theorem par_equiv_seq : forall (x y : Ident) (n1 n2 : nat), x <> y ->
  Equiv (SAssigns x y (ALit n1) (ALit n2))
        (SSeq (SAssign x (ALit n1)) ((SAssign y (ALit n2)))).
(* END FIX *)
Proof.

Qed.


(**
   Bónusz feladat (1 pont): mutasd meg, hogy a parhuzamos ertekadas felcserelheto
   (denotacios szemantika)!
*)

(* BEGIN FIX *)
Lemma par_swap_denot : forall (x1 x2 : Ident)(a1 a2 : AExp)(s : State), x1 <> x2 ->
  eval (SAssigns x1 x2 a1 a2) s 2 x1 = eval (SAssigns x2 x1 a2 a1) s 2 x1 /\
  eval (SAssigns x1 x2 a1 a2) s 2 x2 = eval (SAssigns x2 x1 a2 a1) s 2 x2.
(* END FIX *)
Proof.

Qed.