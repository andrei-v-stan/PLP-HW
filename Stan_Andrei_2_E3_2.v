(* Ex 1 : Definiți în Coq o structură de date de tip arbore binar *)
Inductive btree : Type :=
 | nil : btree
 | node : btree -> nat -> btree -> btree.

Check btree.

(* Construim primul nod (radacina) *)
Check (node nil 7 nil).
(* Construim 2 noduri fii, unul stang (9), si unul drept (6), tatal lor fiind scris la mijloc (7) *)
Check (node (node nil 9 nil) 7 (node nil 6 nil)).
(* Construim inca 4 fii, 2 pentru nodul (9) si 2 pentru nodul (6) *)
Check (node (node (node nil 18 nil) 9 (node nil 27 nil)) 7 (node (node nil 12 nil) 6 (node nil 18 nil))).

(* Ex 2 : Scrieți o funcție de căutare într-un arbore binar *)
Fixpoint search (n : nat) (t : btree) : bool :=
 match t with 
  | nil => false
  | node l value r => if (Nat.eqb n value)
                              then true
                              else (orb (search n l) (search n r))
end.

(* Ex 3 : Scrieți o funcție care oglindește un arbore binar *)
Inductive Btree : Type :=
 | Nil : Btree
 | Node : Btree -> nat -> Btree -> Btree.


Definition Tree :=
  (Node (Node Nil 3 Nil) 10 (Node Nil 7 Nil)).

Fixpoint Search (N : nat) (T : Btree) : bool :=
 match T with
 | Nil => false
 | Node L Value R => if (Nat.eqb N Value)
                       then true
                       else orb (Search N L) (Search N R)
end.

Fixpoint mirror (T : Btree) : Btree :=
 match T with
 | Nil => Nil
 | Node Ltree N Rtree => Node (mirror Rtree) N (mirror Ltree) 
end.

Compute mirror Tree