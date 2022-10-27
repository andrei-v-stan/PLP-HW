
Inductive Var := a | b | c | x | y | z | n | s | i .
Scheme Equality for Var.

(* Tip suplimentar de date care pe langa contructorul de tip numere naturale (nat), mai contine si o valoare de tip eroare *)
Inductive ErrorNat :=
 | errnat : ErrorNat
 | num : nat -> ErrorNat.

Definition EnvNat := Var -> ErrorNat.
Coercion num: nat >-> ErrorNat.


Inductive ErrorBool :=
| errbool : ErrorBool
| boolean : bool -> ErrorBool.

Coercion boolean: bool >-> ErrorBool.


(* De la mapare de tip string catre Value *)
Require Import Strings.String.
Local Open Scope string_scope. 
Scheme Equality for string.

Inductive ErrorString :=
| errstring : ErrorString
| str : string -> ErrorString.

Coercion str: string >-> ErrorString.






(*  La declarare de variabile ar trebui sa avem un tip general de date, o colectie de valori pe care le adaug eu *)
Inductive Value :=
(* Valoare nu este declarata / assignata *)
| default : Value 
| errunass : Value
| errundec : Value
| nums : nat -> Value
| booleans : bool -> Value
| strs : string -> Value.


Scheme Equality for Value.
(* Tipurile de variabile de la errori / default *)
Inductive NatE :=
| erronat : NatE 
| valnat : nat -> NatE.

Inductive BoolE :=
| errobool : BoolE
| truebool : BoolE
| falsebool : BoolE.

Inductive StringE :=
| errostring : StringE
| valstring : string -> StringE.

Inductive Memap :=
| defmem : Memap
| mem: nat -> Memap.

(* Simulare zona de memorie 
- Un environment care trimite nume de variabila spre o zona de memorie 
- Layer intermediar *)
Definition Env := string -> Memap.
Definition Memory := Memap -> Value.

(* Daca nu e declarata trebuie sa aibe defmem, daca e declarata are valoare numerica *)
Definition env : Env :=
fun x => defmem.





(* Definirea unui tip de date pentru expresi aritmetrice *)
Inductive AExp :=
| anum : nat -> AExp
| avar : Env -> AExp
| aadd : AExp -> AExp -> AExp
| asub : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.
Coercion avar : Env >-> AExp.

Notation "A +' B" := (aadd A B) (at level 60, right associativity).
Notation "A -' B" := (asub A B) (at level 60, right associativity).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "a /' b" := (adiv a b) (at level 58, left associativity).
Notation "a %' b" := (amod a b) (at level 58, left associativity).




(* Definirea unui tip de date pentru expresi booleene *)
Inductive BExp :=
| bvar : Env -> BExp
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| bor : BExp -> BExp -> BExp
| band : BExp -> BExp -> BExp
| bless : AExp -> AExp -> BExp
| blessequal : AExp -> AExp -> BExp
| bequal : AExp -> AExp -> BExp
| bnotequal : AExp -> AExp -> BExp
| bmore : AExp -> AExp -> BExp
| bmoreequal : AExp -> AExp -> BExp.

Notation "A <' B" := (bless A B) (at level 70).
Notation "A <=' B" := (blessequal A B) (at level 70).
Notation "A =' B" := (bequal A B) (at level 70).
Notation "A !=' B" := (bnotequal A B) (at level 70).
Notation "A >' B" := (bmore A B) (at level 70).
Notation "A >=' B" := (bmoreequal A B) (at level 70).

Notation "!" := bnot (at level 75).  (* Se poate folosi si : Notation "! A" := (bnot A) (at level 75) *)
Infix "or'" := bor (at level 80).    (* Se poate folosi si : Notation "A 'or'' B" := (bor A B) (at level 80). sau Se poate folosi si : Infix "||" := bor (at level 80). dar este luat deja de Coq la nivelul 50 *)
Infix "and'" := band (at level 80).  (* Se poate folosi si : Notation "A 'and'' B" := (band A B) (at level 80). sau Se poate folosi si : Infix "&&" := band (at level 80). dar este luat deja de Coq la nivelul 40*)




(* Definirea unui tip de date pentru cateva instructiuni *)
Require Import String.
Inductive Stmt :=
| assignment : Env-> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| iforelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 80).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 98, left associativity).
Notation "'if' ( A ) 'else' (  B )":= (iforelse A B)(at level 85).
Notation "'while' ( A ) (  B )":= (while A B)(at level 85).
(* Daca nu sunt puse parantezele de la ( A ) ( B ), va da eroare constructor operator level 200*)




(* Manipulare de stringuri *)
Inductive SExp :=
| svar : Env -> SExp
| scat : SExp -> SExp -> SExp
| scpy : SExp -> SExp -> SExp.

Notation "S <concat> T" := (scat S T) (at level 55).
Notation "S <cpy> T" := (scpy S T) (at level 55).

(*
| slen : SExp -> AExp
| scmp : SExp -> SExp -> Axp
| schr : SExp -> SExp -> SExp (* Pointer *)
| sstr : SExp -> SExp -> SExp (* Pointer *).


Notation "S <len>" := (slen S ) (at level 55).
Notation "S <cmp> T" := (scmp S T) (at level 55).
Notation "S <chr> T" := (schr S T (at level 55).
Notation "S <str> T" := (scat S T) (at level 55).
*)


Inductive Exp :=
| EAExp : AExp -> Exp
| EBExp : BExp -> Exp
| ESExp : SExp -> Exp.

Inductive Addr :=
| addrvar : Env -> Addr.





Inductive Dec :=
| Decint : Env -> Dec
| Decintexp : Env -> AExp -> Dec
| Decintvec : Env -> nat -> Dec
| Decintmat : Env -> nat -> nat -> Dec
| Decintpoint : Env -> Dec
| Decbool : Env -> Dec
| Decboolexp : Env -> BExp -> Dec
| Decboolvec : Env -> nat -> Dec
| Decboolmat : Env -> nat -> nat -> Dec
| Decboolpoint : Env -> Dec
| Decstring : Env -> Dec
| Decstringexp : Env -> SExp -> Dec
| Decstringvec : Env -> nat -> Dec
| Decstringmat : Env -> nat -> nat -> Dec
| Decstringpoint : Env -> Dec.


Notation "'int' X " := (Decint AExp)(at level 50).
Notation "'int' X ~> V" := (Decintexp AExp)(at level 50).
Notation "'int' X ~> V [ nr ]" := (Decintvec V nr)(at level 50).
Notation "'int' X ~> V [ nr1 ] [ nr2 ]" := (Decintmat V nr1 nr2)(at level 50).
Notation "'int*' X ~> P" := (Decintpoint AExp)(at level 50).
Notation "'bool' X " := (Decbool BExp)(at level 50).
Notation "'bool' X ~> V" := (Decboolexp BExp)(at level 50).
Notation "'bool*' X ~> P" := (Decboolpoint BExp)(at level 50).
Notation "'bool' X ~> V [ nr ]" := (Decboolvec V nr)(at level 50).
Notation "'bool' X ~> V [ nr1 ] [ nr2 ]" := (Decboolmat V nr1 nr2)(at level 50).
Notation "'string' X " := (Decstring SExp)(at level 50).
Notation "'string' X ~> V" := (Decstringexp SExp)(at level 50).
Notation "'string*' X ~> P" := (Decstringpoint SExp)(at level 50).
Notation "'string' X ~> V [ nr ]" := (Decstringvec V nr)(at level 50).
Notation "'string' X ~> V [ nr1 ] [ nr2 ]" := (Decstringmat V nr1 nr2)(at level 50).







(*
| DecvectintI : Env ~ nat ~ L NatE ~ Dec
| DecmatintI : Env ~ nat ~ nat ~ L NatE ~ L NatE ~ Dec
| DecpointintI : Env ~ Addr ~ Dec
| DecvectboolI : Env ~ nat ~ L BoolE ~ Dec
| DecmatboolI : Env ~ nat ~ nat ~ L BoolE ~ L BoolE ~ Dec
| DecpointboolI : Env ~ Addr ~ Dec
| DecvectstringI : Env ~ nat ~ L StringE ~ Dec
| DecmatstringI : Env ~ nat ~ nat ~ L StringE ~ L StringE ~ Dec
| DecpointstringI : Env ~ Addr ~ Dec
| Decstruct: Env ~ L Dec ~ Dec.


Notation "'int*' A ~ AD" := (DecpointintI A AD) (at level 50).
Notation "'int' V [ nr ] ~ '{'' E1 , E2 , .. , En '}''" := (DecvectintI V nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'bool*' B ~ AD" := (DecpointboolI B AD) (at level 50).
Notation "'bool' V [ nr ] ~ '{'' E1 , E2 , .. , En '}''" := (DecvectboolI V nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'string*' S ~ AD" := (DecpointstringI S AD) (at level 50).
Notation "'struct'' S '{'' D1 ; D2 ; .. ; Dn '}''" := (Decstruct S (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) )(at level 50).
Notation "'string' V [ nr ]" := ( Decvectstring V nr) (at level 50). 
Notation "'string' V [ nr ] ~ '{'' E1 , E2 , .. , En '}''" := (DecvectstringI V nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'string' V [ nr ][ nr2 ]" := ( Decvectstring V nr nr2) (at level 50). 

*)