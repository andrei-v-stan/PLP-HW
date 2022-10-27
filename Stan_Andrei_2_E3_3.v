(* Set Printing All imi fuctiona doar cu optiunea "Display all basic low-level contents" (Shift + Alt + A) *)

(* EX 1 : *)

(* Vom considera cunoscute următoarele definiții: *)
Inductive Var := a | b | c | x | y | z | n | s | i .

Inductive AExp :=
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| avar : Var -> AExp. (*Modificare*)

Coercion anum : nat >-> AExp.
Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Coercion avar : Var >-> AExp. (*Modificare*)

(*Modificați definiția expresiilor aritmetice (AExp de mai sus) astfel încât aceasta să permită utilizarea de variabile (Var). 
Testați modificările făcute pe următoarele cazuri: *)

Check 2 +' (avar n).
Check n +' 1.
Check s +' i.



(* EX 2 : *)

(*Definiți un tip de date pentru expresii booleene care să includă valorile de adevăr, negații, conjuncții și comparații între expresii aritmetice. 
Testați modificările făcute pe următoarele cazuri: *)

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bmorethan : AExp -> AExp -> BExp.

Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bmorethan A B) (at level 70).
Infix "and'" := band (at level 80). 
(* Se poate folosi si : Notation "A 'and'' B" := (band A B) (at level 80). *)
Notation "!" := bnot (at level 80).
(* Se poate folosi si : Notation "! A" := (bnot A) (at level 80) *)

Check btrue.
Check bfalse.
Check ! (x <' 10).
Check btrue and' (n >' 0).



(* EX 3 : *)

(*Definiți un tip de date pentru instrucțiunile unui limbaj de programare simplu. 
Instrucțiunile sunt: atribuiri, bucle (de tip while) și secvențe de instrucțiuni. 
Pentru teste, utilizați cazurile de mai jos. 
Atenție la notații: acestea vă pot ajuta să determinați forma instrucțiunilor utilizate. *)

Require Import String.
Inductive Stmt :=
| assignment : Var-> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| iforelse : BExp -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 80).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 98, left associativity).
Notation "'while' ( A ) (  B )":= (iforelse A B)(at level 99).
(* Daca nu sunt puse parantezele de la ( A ) ( B ), va da eroare constructor operator level 200*)


Check n ::= 10.
Check s ::= 0.
Check n ::= 10 ;; s ::= 0 ;; i ::= 0.
Check n ::= 10 ;;
      s ::= 0 ;;
      i ::= 0 ;;
      while (i <' n +' 1) (
            s ::= s +' i ;;
            i ::= i +' 1
      ).