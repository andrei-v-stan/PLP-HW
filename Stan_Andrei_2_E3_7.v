(* Stan Andrei - Vladut (2E3) *)
Inductive Var := .





Require Import Strings.String.
Inductive VT :=
  | Bool : bool -> VT
  | Int : nat-> VT
  | String : string -> VT
  | Default : VT.

Coercion Bool : bool >-> VT.
Coercion Int : nat >-> VT.
Coercion String : string >-> VT.

Definition Env := string -> VT.

Definition env : Env :=
  fun x => Default.





Local Open Scope string_scope.
Scheme Equality for string.

(*
Definition updateIV (env : Env)
           (v : Var) (w : nat) : Env :=
  fun a =>
    if (Var_eq_dec a v)
    then w
    else (env a).
*)

Definition updateS (env : Env )(S : string)(vt : VT): Env:=
fun b => 
      if(string_eq_dec b S)
      then vt
      else(env b).





Inductive AExp :=
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| aimp : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.
(*| avar : Var -> AExp.*)

Coercion anum : nat >-> AExp.
Notation "A +' B" := (aplus A B) (at level 60, right associativity).
Notation "A -' B" := (amin A B) (at level 60, right associativity).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "A /' B" := (aimp A B) (at level 58, left associativity).
Notation "A %' B" := (amod A B) (at level 56, left associativity).
(*Coercion avar : Var >-> AExp.*)


Definition Boolval (bl : VT) : bool :=
match bl with
| Bool bl => bl
|  _ => false
end.

Definition Intval (n : VT) : nat :=
match n with
| Int n => n
|  _ => 0
end.

Definition Stringval (str : VT) : string :=
match str with
| String str => str
|  _ => " "
end.

Fixpoint eval (a : AExp) (sig : Env) : nat :=
  match a with
(*| avar u => Intval (sig u) *)
  | anum v => v
  | aplus a1 a2 => (eval a1 sig) + (eval a2 sig)
  | amin a1 a2 => (eval a1 sig) - (eval a2 sig)
  | amul a1 a2 => (eval a1 sig) * (eval a2 sig)
  | aimp a1 a2 => Nat.div (eval a1 sig)  (eval a2 sig)
  | amod a1 a2 => Nat.modulo (eval a1 sig)  (eval a2 sig)
end.

(*
Reserved Notation "A =[ S ]=> N" (at level 70).
Inductive Aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sig, anum n =[ sig ]=> n
(*| var : forall v sig, avar v =[ sig ]=> Intval(sig v)*)
| addition : forall a1 a2 b1 b2 sig n,
  a1 =[ sig ]=> b1 ->
  a2 =[ sig ]=> b2 ->
  n = b1 + b2 ->
  a1 +' a2 =[ sig ]=> n
| subtraction : forall a1 a2 b1 b2 sig n,
  a1 =[ sig ]=> b1 ->
  a2 =[ sig ]=> b2 ->
  n = b1 - b2 ->
  a1 -' a2 =[ sig ]=> n
| multiplication : forall a1 a2 b1 b2 sig n,
  a1 =[ sig ]=> b1 ->
  a2 =[ sig ]=> b2 ->
  n = b1 * b2 ->
  a1 *' a2 =[ sig ]=> n
(* etc... *)
where "a =[ sig ]=> n" := (eval a sig n).
*)


Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| blessthan : AExp -> AExp -> BExp
| bmorethan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Fixpoint Natmore n m : bool :=
  match n, m with
    | 0, _ => false
    | _, 0 => true
    | S n', S m' => Natmore n' m'
  end.

(*
Fixpoint beval (b : BExp) (env : Env) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | blessthan a1 a2 => Nat.leb (eval a1 env) (eval a2 env)
  | bmorethan a1 a2 => Natmore (eval a1 env) (eval a2 env)
  | bnot b' => negb (beval b' env)
  end.
*)

Notation "A <' B" := (blessthan A B) (at level 70).
Notation "A >' B" := (bmorethan A B) (at level 70).
Notation "!" := bnot (at level 80).
(* etc... *)

(*
Reserved Notation "ba =[ S ]=> bb" (at level 70).
Inductive Beval : BExp -> Env -> bool -> Prop :=
| Btrue : forall sig, btrue =[ sig ]=> true
| Bfalse : forall sig, bfalse =[ sig ]=> false
| Bvar : forall bx sig, bvar bx =[ sig ] => beval(sigma bx)
| Blessthan : forall a1 a2 b1 b2 sig bx,
  a1 =[ sig ]=> b1 ->
  a2 =[ sig ]=> b2 ->
  b = Nat.leb ->
  a1 <' a2 =[ sig ]=> bx
| Bmorethan : forall a1 a2 b1 b2 sig bx,
  a1 =[ sig ]=> b1 ->
  a2 =[ sig ]=> b2 ->
  b = Nat.leb ->
  a1 >' a2 =[ sig ]=> bx

(* Bnottrue, Bnotfalse, etc ... *)
where "ba =[ sig ]=> bb" := (eval ba sig bb).
*)





Require Import String.
Inductive Stmt :=
| assignment : Var-> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 80).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 98, left associativity).
Notation "'If' condition 'Then' string1 'Else' string2 'End'":= (ifthenelse condition string1 string2)(at level 99).

(*
Reserved Notation "S -[ sigma ]=> sigma" (at level 70).
Inductive Ceval : Stmt -> Env -> Env -> Prop :=
| Cassignment : forall ...,
...
| Csequence : forall ... ,
...
etc ...
where "S -[ sigma ]=> sigma" := (eval s sig sig').
*)





(* Or (from the course - it requires specific rules from above) :

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).
Reserved Notation "B ={ S }=> B'" (at level 60).
Inductive beval_small_step : BExp -> Env -> BExp -> Prop :=
| lessthan_1 : forall a1 a1' a2 sigma,
    a1 =[ sigma ]=> a1' ->
    a1 <=' a2 ={ sigma }=> a1' <=' a2
| lessthan_2 : forall i1 a2' a2 sigma,
    a2 =[ sigma ]=> a2' ->
    (anum i1) <=' a2 ={ sigma }=> (anum i1) <=' a2'
| lessthan : forall i1 i2 b sigma,
    b = (if Nat.leb i1 i2 then btrue else bfalse) ->
    (anum i1) <=' (anum i2) ={ sigma }=> b
| not : forall b b' sigma,
    b ={ sigma }=> b' ->
    (bnot b) ={ sigma }=> (bnot b')
| not_true : forall sigma, (bnot btrue) ={ sigma }=> bfalse
| not_false : forall sigma, (bnot bfalse) ={ sigma }=> btrue
| and_1 : forall b1 b1' sigma b2,
    b1 ={ sigma }=> b1' ->
    (band b1 b2) ={ sigma }=> (band b1' b2)
| and_false : forall b2 sigma,
    (band bfalse b2) ={ sigma }=> bfalse
| and_true : forall b2 sigma,
    (band btrue b2) ={ sigma }=> b2
where "B ={ S }=> B'" := (beval_small_step B S B').


Inductive Stmt :=
| skip : Stmt
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt 
| while : BExp -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).

Reserved Notation "St1 -{ State }->[ St2 ; State' ]" (at level 60).
Inductive eval_small_step : Stmt -> Env -> Stmt -> Env -> Prop :=
| assign_2 : forall a a' x sigma,
    a =[ sigma ]=> a' -> 
    (x ::= a) -{ sigma }->[ x ::= a' ; sigma ]
| assign : forall x i sigma,
    (x ::= (anum i)) -{ sigma }->[ skip ; sigma [ i /' x ] ]
| seq_1 : forall s1 s1' s2 sigma,
    s1 -{ sigma }->[ s1' ; sigma ] ->
    (s1 ;; s2) -{ sigma }->[ s1' ;; s2 ; sigma ]
| seq : forall s2 sigma,
    (skip ;; s2) -{ sigma }->[ s2 ; sigma ]
| if_1 : forall b b' s1 s2 sigma,
    b ={ sigma }=> b' -> 
    (ifthenelse b s1 s2) -{ sigma }->[ ifthenelse b' s1 s2 ; sigma ]
| if_true : forall s1 s2 sigma,
    (ifthenelse btrue s1 s2) -{ sigma }->[ s1 ; sigma ]
| if_false : forall s1 s2 sigma,
    (ifthenelse bfalse s1 s2) -{ sigma }->[ s2 ; sigma ]
| while_ : forall b s sigma,
    while b s -{ sigma }->[ ifthenelse b (s ;; while b s) skip ; sigma ]
where "St1 -{ State }->[ St2 ; State' ]" := (eval_small_step St1 State St2 State').


Reserved Notation "St1 -{ State }>*[ St2 ; State' ]" (at level 60).
Inductive eval_closure : Stmt -> Env -> Stmt -> Env -> Prop :=
| refl : forall s sigma, s -{ sigma }>*[ s ; sigma ]
| tran : forall s1 s2 s3 sigma1 sigma2 sigma3,
    s1 -{ sigma1 }->[ s2 ; sigma2 ] ->
    s2 -{ sigma2 }>*[ s3 ; sigma3 ] -> 
    s1 -{ sigma1 }>*[ s3 ; sigma3 ]
where "St1 -{ State }>*[ St2 ; State' ]" := (eval_closure St1 State St2 State').
*)











