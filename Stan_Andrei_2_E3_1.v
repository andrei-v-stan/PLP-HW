(* Ex 1 : Definiți un tip de date algebric pentru zilele săptămânii *)
Inductive week_day : Type :=
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday.

(* Verificarea daca tipul de date este bine definit : *)
Check week_day.

(* Verificarea daca datele apartin lui "week_day" : *)
Check Monday.
Check Tuesday.
Check Wednesday.
Check Thursday.
Check Friday.
Check Saturday.
Check Sunday.





(* Ex 2 : Definiți o funcție de egalitate peste acest tip de date *)
Definition equal_day (D1 D2 : week_day) : bool:=
  match D1, D2 with
    | Monday, Monday => true
    | Tuesday, Tuesday => true
    | Wednesday, Wednesday => true
    | Thursday, Thursday => true
    | Friday, Friday => true
    | Saturday, Saturday => true
    | Sunday, Sunday => true
    | _, _ => false
  end.

(* Verificarea match-urilor din "equal_day" : *)
Compute (equal_day Monday Monday).
Compute (equal_day Tuesday Tuesday).
Compute (equal_day Wednesday Wednesday).
Compute (equal_day Thursday Thursday).
Compute (equal_day Friday Friday).
Compute (equal_day Saturday Saturday).
Compute (equal_day Sunday Sunday).

Compute (equal_day Monday Tuesday).
Compute (equal_day Tuesday Wednesday).
Compute (equal_day Wednesday Thursday).
Compute (equal_day Thursday Friday).
Compute (equal_day Friday Saturday).
Compute (equal_day Saturday Sunday).
Compute (equal_day Sunday Monday).






(* Ex 3 : Definiți o funcție care returnează ziua următoare *)
Definition next_day (D : week_day) :=
  match D with
    | Monday => Tuesday
    | Tuesday => Wednesday
    | Wednesday => Thursday
    | Thursday => Friday
    | Friday => Saturday
    | Saturday => Sunday
    | Sunday => Monday
  end.

(* Verificarea daca datele returneaza ziua urmatoare : *)
Compute (next_day Monday).
Compute (next_day Tuesday).
Compute (next_day Wednesday).
Compute (next_day Thursday).
Compute (next_day Friday).
Compute (next_day Saturday).
Compute (next_day Sunday).






(* Ex 4 : Definiți tipul de date boolean *)
Inductive bool : Type :=
 | true
 | false.

(* Verificarea daca tipul de date este bine definit : *)
Check bool.

(* Verificarea daca datele apartin lui "bool" : *)
Check true.
Check false.





(* Ex 5 : Definiți funcțiile: negație, conjuncție, disjuncție *)
Definition conjucntie (B1 B2 : bool) : bool :=
 match B1, B2 with
   |true, true => true
   |true, false => false
   |false, true => false
   |false, false => false
end.

(* Verificarea cazurilor conjunctiei : *)
Compute (conjucntie true true).
Compute (conjucntie true false).
Compute (conjucntie false true).
Compute (conjucntie false false).



Definition disjunctie (B1 B2 : bool) : bool :=
   match B1, B2 with
   |true, true => true
   |true, false => true
   |false, true => true
   |false, false => false
end.

(* Verificarea cazurilor disjunctiei : *)
Compute (disjunctie true true).
Compute (disjunctie true false).
Compute (disjunctie false true).
Compute (disjunctie false false).



Definition negatie (B : bool) : bool :=
 match B with
   | true => false
   | false => true
 end.

(* Verificarea cazurilor negatiei : *)
Compute (negatie true ).
Compute (negatie false).


Definition disjunctie_exclusiva (B1 B2 : bool) : bool :=
   match B1, B2 with
   |true, true => false
   |true, false => true
   |false, true => true
   |false, false => false
end.

(* Verificarea cazurilor disjunctiei exclusive : *)
Compute (disjunctie_exclusiva true true).
Compute (disjunctie_exclusiva true false).
Compute (disjunctie_exclusiva false true).
Compute (disjunctie_exclusiva false false).

