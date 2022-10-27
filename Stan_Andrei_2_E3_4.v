(* Set Printing All imi fuctiona doar cu optiunea "Display all basic low-level contents" (Shift + Alt + A) *)

(* EX 1 : *)

(* Descrieți un tip de date în Coq pentru expresiile aritmetice simple (e.g., +, -, *, /, %) cu variabile.: *)
Inductive Var := a | b | c | x | y | z | n | s | i .

Inductive AExp :=
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp (*Modificare*)
| amul : AExp -> AExp -> AExp
| aimp : AExp -> AExp -> AExp (*Modificare*)
| amod : AExp -> AExp -> AExp (*Modificare*)
| avar : Var -> AExp. 

Coercion anum : nat >-> AExp.
Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A -' B" := (amin A B) (at level 60, right associativity).   (*Modificare*)
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "A /' B" := (aimp A B) (at level 58, left associativity).    (*Modificare*)
Notation "A %' B" := (amod A B) (at level 56, left associativity).    (*Modificare*)
Coercion avar : Var >-> AExp.



(* EX 2 : *)

(*Scrieți o funcție recursivă eval care va primi la intrare o expresie aritmetică și un environment și va returna rezultatul evaluării acelei expresii în environmentul dat. *)

Scheme Equality for Var.
Check Var_beq.
Definition Env := Var->nat.


Fixpoint eval (a : AExp) (env : Env) : nat :=
  match a with
  | avar var => env var
  | anum n' => n'
  | aplus a1 a2 => (eval a1 env) + (eval a2 env)
  | amin a1 a2 => (eval a1 env) - (eval a2 env)
  | amul a1 a2 => (eval a1 env) * (eval a2 env)
  | aimp a1 a2 => Nat.div (eval a1 env)  (eval a2 env)
  | amod a1 a2 => Nat.modulo (eval a1 env)  (eval a2 env)
end.

Definition envl : Env :=
  fun var =>
    if (Var_beq var x)
    then 10
    else 0.

Check envl.
Check eval.
Compute (envl x).
Compute (Nat.div 20 5).
Compute (Nat.modulo 20 6).
Compute eval (1 +' 1) envl.
Compute eval (x *' 20) envl.
Compute eval (x *' 20 +' 5 *' 6 +' x +' 5 +' 8) envl.


(* EX 3 : *)

(* Demonstrați prin inducție că pentru orice expresie e și orice environment env, eval e env >= 0. *)

Lemma demonstratie :
  forall (e : AExp) (env : Env), Nat.leb 0 (eval e env) = true.
Proof.
  induction e.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.



(* EX 4 : *)

(* Definiți un limbaj de programare care să conțină expresii aritmetice cu variabile, expresii booleene, instrucțiuni de atribuire, secvențe de instrucțiuni și instrucțiuni condiționale (e.g., if then else). 
Definiți o funcție execute care evaluează programe scrise în acest limbaj. *)

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bmorethan : AExp -> AExp -> BExp
| bnot : BExp -> BExp.

Fixpoint Natmore n m : bool :=
  match n, m with
    | 0, _ => false
    | _, 0 => true
    | S n', S m' => Natmore n' m'
  end.

Fixpoint beval (b : BExp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | blessthan a1 a2 => Nat.leb (eval a1 env) (eval a2 env)
  | bmorethan a1 a2 => Natmore (eval a1 env) (eval a2 env)
  | bnot b' => negb (beval b' env)
  end.

Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bmorethan A B) (at level 70).
Notation "!" := bnot (at level 80).

Require Import String.
Inductive Stmt :=
| assignment : Var-> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| iforelse : BExp -> Stmt -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 80).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 98, left associativity).
Notation "'If' condition 'Then' string1 'Else' string2 'End'":= (iforelse condition string1 string2)(at level 99).

Definition update (env : Env) (var : Var) (value : nat) : Env :=
  fun var' =>
    if (Var_beq var' var)
    then value
    else (env var').


Fixpoint execute  (string : Stmt) (env : Env)  : Env :=
match string with
 | assignment Var AExp => update env Var (eval AExp env)
 | sequence string1 string2 => execute string1 (execute string1 env)
 | iforelse cond string1 string2  => if (beval cond env)
                                      then execute string1 env
                                      else execute string1 env
end.

Check execute.

