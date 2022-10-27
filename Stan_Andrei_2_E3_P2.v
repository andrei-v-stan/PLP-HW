Require Import Strings.String.
Require Import List.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.


(* Errors & Conversion -------------------------------------------------- *)

Inductive Var := a | b | c.
Scheme Equality for Var.

(* Tip suplimentar de date care pe langa contructorul de tip numere naturale (nat), mai contine si o valoare de tip eroare *)
Inductive ErrorNat :=
 | errnat : ErrorNat
 | num : nat -> ErrorNat.
Definition EnvNat := Var -> ErrorNat.
Coercion num: nat >-> ErrorNat.

Inductive ErrorBool :=
| errbool : ErrorBool
| btrueE : ErrorBool
| bfalseE : ErrorBool
| boolean : bool -> ErrorBool.
Coercion boolean: bool >-> ErrorBool.


Definition bTObool(b : bool) : ErrorBool :=
match b with
| true => btrueE
| false => bfalseE
end.


Inductive ErrorString :=
| errstringing : ErrorString
| str : string -> ErrorString.
Coercion str: string >-> ErrorString.

Inductive ErrorAddr :=
| erraddr : ErrorAddr
| addr : string -> ErrorAddr.
Coercion addr : string >-> ErrorAddr.

Inductive ErrorVec :=
| errvec : ErrorVec
| natvec : list ErrorNat -> ErrorVec
| boolvec : list ErrorBool -> ErrorVec
| strvec : list ErrorString -> ErrorVec
| vect : string -> ErrorVec.

(* -------------------------------------------------- Errors & Conversion *)









(* Data types & Expresions -------------------------------------------------- *)

(* Definirea unui tip de date pentru expresi aritmetrice *)
Inductive AExp :=
| anum : nat -> AExp
| avar : ErrorNat -> AExp
| anat : ErrorNat -> AExp
| aadd : AExp -> AExp -> AExp
| asub : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| natTOvec : string -> nat -> AExp
| boolTOnat : ErrorBool -> AExp.

Coercion anum : nat >-> AExp.
Coercion avar : ErrorNat >-> AExp.

Notation "A +' B" := (aadd A B) (at level 60, right associativity).
Notation "A -' B" := (asub A B) (at level 60, right associativity).
Notation "A *' B" := (amul A B) (at level 58, left associativity).
Notation "A /' B" := (adiv A B) (at level 58, left associativity).
Notation "A %' B" := (amod A B) (at level 58, left associativity).



(* Definirea unui tip de date pentru expresi booleene *)
Inductive BExp :=
| bvar : ErrorBool -> BExp
| bbool : ErrorBool -> BExp
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
| bmoreequal : AExp -> AExp -> BExp
| boolTOvec : string -> nat -> BExp
| natTObool : ErrorNat -> BExp.

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
| assigmanment : string -> AExp -> Stmt
| errstmt : Stmt
| sequence : Stmt -> Stmt -> Stmt
| iforelse : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| valTOvec : string -> nat -> Stmt.

Notation "X ::= A" := (assigmanment X A) (at level 80).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 98, left associativity).
Notation "'if' ( A ) 'else' (  B )":= (iforelse A B)(at level 85).
Notation "'while' ( A ) (  B )":= (while A B)(at level 85).
(* Daca nu sunt puse parantezele de la ( A ) ( B ), va da eroare constructor operator level 200*)



(* Manipulare de stringuri *)
Inductive SExp :=
| svar : string -> SExp
| scat : SExp -> SExp -> SExp
| scpy : SExp -> SExp -> SExp
| stringTOvec : string -> nat -> SExp.

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



Inductive ValueV :=
| defaultv : ValueV
| decnat : string -> ValueV
| decbool : string -> ValueV 
| decstring : string -> ValueV
| decstmt : Stmt -> ValueV.


Inductive Addr :=
| addrvar : string -> Addr.


Inductive Exp :=
| EAExp : AExp -> Exp
| EBExp : BExp -> Exp
| ESExp : SExp -> Exp.


Inductive Edec :=
| Enat : ErrorNat -> Edec
| Ebool : ErrorBool -> Edec
| Estring : ErrorString -> Edec.

(* -------------------------------------------------- Data types & Expresions *)







(* Other convertions & Error cases -------------------------------------------------- *)

Definition natCONVbool (x : ErrorNat) : ErrorBool :=
match x with
| num 0 => bfalseE
| errnat => errbool
| _ => btrueE
end. 

Definition boolCONVnat (x : ErrorBool) : ErrorNat :=
match x with
| btrueE => 1
| _ => 0
end. 

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

Inductive AddrE :=
| erroaddr : AddrE
| valaddr : string -> AddrE.

Inductive VecE :=
| errovec : VecE
| erronats : list NatE -> VecE
| errobools : list BoolE -> VecE
| errostrings : list StringE -> VecE.

(* -------------------------------------------------- Other convertions & Cases *)







(* Declarations & Notations -------------------------------------------------- *)

Inductive Dec :=
| Decint : string -> Dec
| Decintexp : string -> AExp -> Dec
| Decintvec : string -> nat -> Dec
| DecintvecI : string -> nat -> list NatE -> Dec
| Decintmat : string -> nat -> nat -> Dec
| Decintpoint : string -> Dec
| DecintpointI : string -> AddrE -> Dec
| Decbool : string -> Dec
| Decboolexp : string -> BExp -> Dec
| Decboolvec : string -> nat -> Dec
| DecboolvecI : string -> nat -> list BoolE -> Dec
| Decboolmat : string -> nat -> nat -> Dec
| Decboolpoint : string -> Dec
| DecboolpointI : string -> AddrE -> Dec
| Decstring : string -> Dec
| Decstringexp : string -> SExp -> Dec
| Decstringvec : string -> nat -> Dec
| DecstringvecI : string -> nat -> list StringE -> Dec
| Decstringmat : string -> nat -> nat -> Dec
| Decstringpoint : string -> Dec
| DecstringpointI : string -> AddrE -> Dec
| Decstruct: string -> list Dec -> Dec.

Notation "'int' X " := (Decint AExp)(at level 50).
Notation "'int' X ~> V" := (Decintexp AExp)(at level 50).
Notation "'int' X ~> V [ nr ]" := (Decintvec V nr)(at level 50).
Notation "'int' X ~> V [ nu ] [ nt ]" := (Decintmat V nu nt)(at level 50).
Notation "'int*' X ~> P" := (Decintpoint AExp)(at level 50).
Notation "'bool' X " := (Decbool BExp)(at level 50).
Notation "'bool' X ~> V" := (Decboolexp BExp)(at level 50).
Notation "'bool*' X ~> P" := (Decboolpoint BExp)(at level 50).
Notation "'bool' X ~> V [ nr ]" := (Decboolvec V nr)(at level 50).
Notation "'bool' X ~> V [ nu ] [ nt ]" := (Decboolmat V nu nt)(at level 50).
Notation "'char' X " := (Decstring SExp)(at level 50).
Notation "'char' X ~> V" := (Decstringexp SExp)(at level 50).
Notation "'char*' X ~> P" := (Decstringpoint SExp)(at level 50).
Notation "'char' X ~> V [ nr ]" := (Decstringvec V nr)(at level 50).
Notation "'char' X ~> V [ nu ] [ nt ]" := (Decstringmat V nu nt)(at level 50).
Notation "'struct'' S '{'' D1 ; D2 ; .. ; Dn '}''" := (Decstruct S (cons D1 ( cons D2 .. (cons Dn nil) .. ) ) )(at level 50).
Notation "(int) X" := (boolTOnat X) (at level 50).
Notation "(bool) Y" := (natTObool Y) (at level 50).

(*
| DecmatintI : string ~ nat ~ nat ~ list NatE ~ list NatE ~ Dec
| DecmatboolI : string ~ nat ~ nat ~ list BoolE ~ list BoolE ~ Dec
| DecmatstringI : string ~ nat ~ nat ~ list StringE ~ list StringE ~ Dec

Notation "'int*' A ~ AD" := (DecpointintI A AD) (at level 50).
Notation "'int' V [ nr ] ~ '{'' E1 , E2 , .. , En '}''" := (DecvectintI V nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'bool*' B ~ AD" := (DecpointboolI B AD) (at level 50).
Notation "'bool' V [ nr ] ~ '{'' E1 , E2 , .. , En '}''" := (DecvectboolI V nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'string*' S ~ AD" := (DecpointstringI S AD) (at level 50).
Notation "'string' V [ nr ]" := ( Decvectstring V nr) (at level 50). 
Notation "'string' V [ nr ] ~ '{'' E1 , E2 , .. , En '}''" := (DecvectstringI V nr (cons E1 ( cons E2 .. (cons En nil) .. ) ) ) (at level 50).
Notation "'string' V [ nr ][ nt ]" := ( Decvectstring V nr nt) (at level 50). 
*)

(* -------------------------------------------------- Declarations & Notations *)







(* Memory mapping & Cases -------------------------------------------------- *)

(*  La declarare de variabile ar trebui sa avem un tip general de date, o colectie de valori pe care le adaug eu *)
Inductive Value :=
(* Valoare nu este declarata / assigmanata *)
| default : Value
| errunass : Value
| errundec : Value
| errunini : Value
| nums : ErrorNat -> Value
| bools : ErrorBool -> Value
| strs : ErrorString -> Value
| addrs : ErrorAddr -> Value
| param : list Dec -> Stmt -> Value
| paramS : string -> Stmt -> Value
| vecs : ErrorVec -> Value
| NatP : ErrorNat -> Value
| BoolP : ErrorBool -> Value
| StringP : ErrorString -> Value. 



Definition NatV (x : Value) : ErrorNat :=
match x with
| nums n => n
| _ => errnat
end.
Coercion nums : ErrorNat >-> Value.

Definition BoolV (x : Value) : ErrorBool :=
match x with
| bools n => n
| _ => errbool
end.
Coercion bools : ErrorBool >-> Value.

Definition StringV (x : Value) : ErrorString :=
match x with
| strs n => n
| _ => errstringing
end.
Coercion strs : ErrorString >-> Value.

Definition AddrV (x : Value) : ErrorAddr :=
match x with
| addrs n => n
| _ => erraddr
end.
Coercion addrs : ErrorAddr >-> Value.



Inductive Memap :=
| defmem : Memap
| mem: nat -> Memap.


Definition Env := string -> Memap.
Definition Memory := Memap -> Value.

Definition env : Env :=
fun x => defmem.




(* -------------------------------------------------- Memory mapping & Cases *)







(* Environments & Operations -------------------------------------------------- *)

Definition EnvS := string -> Value.

Definition envS : EnvS := fun x => default.


Definition UpdateV (envS : EnvS) (s : string) (x : Value) : EnvS :=
  fun t =>
    if (string_dec t s)
    then x
    else (envS t).

Definition Update (envS : EnvS) (s : string) : EnvS := (UpdateV envS s errunini).
Definition envS0 := fun( var : string ) => errundec. Check envS0.
Definition envS1 := (UpdateV envS0 "n" "XXXXX").
Definition envS2 := (Update envS1 "s").


 Compute envS1 "n". 







Definition natG (x : Value) : ErrorNat :=
match x with
| num n => n
| _ => errnat
end.

Definition boolG (x : Value) : ErrorBool :=
match x with
| boolean n => n
| _ => errbool
end.

Definition strG (x : Value) : ErrorString :=
match x with
|  str n => n
| _ => errstringing
end.

Definition addrG (x : Value) : ErrorAddr :=
match x with
| addr n => n
| _ => erraddr
end.








Fixpoint NatvecG (l : list ErrorNat) (n : nat) : ErrorNat :=
match n, l with
| O, x::l1 => x
| S m, nil => errnat
| S m, x :: l2 => (NatvecG l2 m)
| _, _ => errnat
end.

Fixpoint BoolvecG (l : list ErrorBool) (n : nat) : ErrorBool :=
match n, l with
| O, x::l1 => x
| S m, nil => errbool
| S m, x::l2 => (BoolvecG l2 m)
| _, _ => errbool
end.

Fixpoint StrvecG (l : list ErrorString) (n : nat) : ErrorString :=
match n, l with
| O, x::l1 => x
| S m, nil => errstringing
| S m, x::l2 => (StrvecG l2 m)
| _, _ => errstringing
end.







(* Operatii aritmetrice *)
Definition Natadd (a b : ErrorNat) : ErrorNat :=
match a, b with
| errnat, _ => errnat
| _ ,errnat => errnat
| num n, num m => num (n + m)
end.

Definition Natsub (a b : ErrorNat) : ErrorNat :=
match a, b with
| errnat, _ => errnat
| _ ,errnat => errnat
| num n, num m => n - m
end.

Definition Natmul (a b : ErrorNat) : ErrorNat :=
match a, b with
| errnat, _ => errnat
| _ ,errnat => errnat
| num n, num m => n * m
end.

Definition Natdiv (a b : ErrorNat) : ErrorNat :=
match a, b with
| errnat, _ => errnat
| _ ,errnat => errnat
| num n, num m => Nat.div n m
end.

Definition Natmod (a b : ErrorNat) : ErrorNat :=
match a, b with
| errnat, _ => errnat
| _ ,errnat => errnat
| num n, num m => Nat.modulo n m
end.







Definition Boolless(a b : ErrorNat) : ErrorBool :=
match a, b with
| _, errnat => errbool
| errnat, _ => errbool
| num n, num m => bTObool (Nat.ltb n m)
end.

Definition Boollessequal(a b : ErrorNat) : ErrorBool :=
match a, b with
| _, errnat => errbool
| errnat, _ => errbool
| num n, num m => bTObool (Nat.leb n m)
end.

Definition Boolequal(a b : ErrorNat) : ErrorBool :=
match a, b with
| _, errnat => errbool
| errnat, _ => errbool
| num n, num m => bTObool (Nat.eqb n m)
end.

Definition Boolnotequal(a b : ErrorNat) : ErrorBool :=
match a, b with
| _, errnat => errbool
| errnat, _ => errbool
| num n, num m => bTObool (negb (Nat.eqb n m))
end.

Definition Boolmore(a b : ErrorNat) : ErrorBool :=
match a, b with
| _, errnat => errbool
| errnat, _ => errbool
| num n, num m => bTObool (Nat.ltb m n) (* sau : (negb (Nat.leb n m)) *)
end.

Definition Boolmoreequal(a b : ErrorNat) : ErrorBool :=
match a, b with
| _, errnat => errbool
| errnat, _ => errbool
| num n, num m => bTObool (Nat.leb m n) (* sau : (negb (Nat.ltb n m)) *)
end.








Fixpoint UpdateVs ( sigma : EnvS ) (p : list Dec) ( l : list Value ) : EnvS :=
match l with
| nil => sigma
| x::l' => match x, p with
           | NatP n, y::l'' => match y with
                                    | Decint nt => UpdateVs (UpdateV sigma nt n) l'' l'
                                    | Decbool bt => UpdateVs (UpdateV sigma bt n) l'' l'
                                    | Decstring st => UpdateVs (UpdateV sigma st n) l'' l'
                                    | _ => sigma
                                    end
           | _, _ => sigma
           end
end.


Definition call (sigma : EnvS ) ( v : string) ( x : Value ) (l' : Value) : EnvS :=
match x with
| paramS l st => UpdateV sigma l l'
| _ => sigma
end.


Definition get_st (x : Value) : Stmt :=
match x with
| paramS l st => st
| _ => errstmt
end.


(* -------------------------------------------------- Environments & Operations *)











(*

Reserved Notation "A =[ S ]=> N" (at level 60).
Inductive aeval : AExp -> EnvS -> ErrorNat -> Prop :=
| constE : forall n sigma, anat n =[ sigma ]=> n 

| avarE : forall n sigma, avar n =[ sigma ]=> (natG (sigma n))


| addE : forall a b i j sigma n,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    n =  Natadd i j ->
    a +' b =[sigma]=> n

| subE : forall a b i j sigma n,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    n =  Natsub i j ->
    a -' b =[sigma]=> n

| mulE : forall a b i j sigma n,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    n = Natmul i j ->
    a *' b =[sigma]=> n

| divE : forall a b i j sigma n,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    n =  Natdiv i j ->
    a /' b =[sigma]=> n

| modE : forall a b i j sigma n,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    n =  Natmod i j ->
    a %' b =[sigma]=> n
| boolTOnatE : forall c sigma, a_bool_to_nat c =[ sigma ]=> conv_bool_nat c

| e_aget_vect_valE : forall v1 v2 n sigma,
  v2 = (sigma v1) ->
  a_get_vect_val v1 n =[ sigma ]=> natG (get_element v2 n)
where "a =[ sigma ]=> n" := (aeval a sigma n).







Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : Bexp -> EnvS -> ErrorBool -> Prop :=
| trueE : forall sigma, btrueE ={ sigma }=> btrueE
| falseE : forall sigma, bfalseE ={ sigma }=> bfalseE

| bvarE : forall v sigma, bvar v ={ sigma }=> boolG (sigma v)

| lessE : forall a b i j sigma r,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    r = less_than (natG i) (natG j) ->
    a <' b ={ sigma }=> r

| lessequalE : forall a b i j sigma r,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    r = less_equal_than (natG i) (natG j) ->
    a <=' b ={ sigma }=> r

| equal : forall a b i j sigma r,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    r = equality i j ->
    a ==' b ={ sigma }=> r

| notequal : forall a b i j sigma r,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    r = different i j ->
    a ==' b ={ sigma }=> r

| greaterE : forall a b i j sigma r,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    r = greater_than (natG i) (natG j) ->
    a <' b ={ sigma }=> r

| graterequalE : forall a b i j sigma r,
    a =[ sigma ]=> i ->
    b =[ sigma ]=> j ->
    r = less_equal_than i j->
    a <=' b ={ sigma }=> r

| nottrue : forall r sigma,
    r ={ sigma }=> trueE ->
    !'r ={ sigma }=> falseE

| notfalse : forall r sigma,
    r ={ sigma }=> falseE ->
    !'r ={ sigma }=> trueE

| andtrue : forall u t sigma t,
    u ={ sigma }=> trueE ->
    t ={ sigma }=> t ->
    u &&' t ={ sigma }=> t
| andfalse : forall u t sigma,
    u ={ sigma }=> falseE ->
    u &&' t ={ sigma }=> falseE

| ortrue : forall u t sigma,
    u ={ sigma }=> trueE ->
    u ||' t ={ sigma }=> trueE

| orfalse : forall u t sigma t,
    u ={ sigma }=> falseE ->
    t ={ sigma }=> t ->
    u ||' t ={ sigma }=> t



| natTOboolE : forall a sigma,  natTOboolB a ={ sigma }=> natCONVbool a

| boolTOvecE : forall v1 v2 n sigma,
  v2 = (sigma v1) ->
 boolTOvec v1 n ={ sigma }=> boolE (get_element v2 n)

where "B ={ S }=> B'" := (beval B S B').







Reserved Notation "B  =< S >=> B'" (at level 80).
Inductive streval : STRexp -> Env -> String -> Prop :=
| svar : forall v sigma, s_var v =< sigma >=> strG (sigma v)
| str_const : forall v sigma, s_str v =< sigma >=> v
| concat : forall s1 s2 i j sigma s,
    s1 =< sigma >=> i->
    s2 =< sigma >=> j ->
    s = concatenate i j ->
    s1 <--> s2 =< sigma >=> s

| e_sget_vect_val : forall v1 v2 n sigma,
  v2 = (sigma v1) ->
  s_get_vect_val v1 n =< sigma >=> strG (get_element v2 n)

where "B =< S >=> B'" := (streval B S B').



Definition conca(s t : ErrorString) : ErrorString :=
match s, t with
  |_, errstring => errstring
  |errstring, _ => errstring
  |str s, str t => str (s ++ t)
end.


*)
















































