(* Set Printing All imi fuctiona doar cu optiunea "Display all basic low-level contents" (Shift + Alt + A) *)

(* EX 1 : *)

Inductive State :=
| state : nat -> nat -> State.

Notation "{ nr1 , nr2 }" := (state nr1 nr2) (at level 0).

Definition fst (nr : State) : nat :=
  match nr with
  | state nr1 nr2 => nr1
end.

Definition snd (nr : State) : nat :=
  match nr with
  | state nr1 nr2 => nr2
end.

Check {12, 15}.         (* {12, 15}  : State *)
Check fst.              (* fst  : State -> nat *)
Compute fst ({12,15}).  (* = 12   : nat *)
Check snd.              (* snd   : State -> nat *)
Compute snd ({12,15}).  (* = 15  : nat *)





(* EX 2 : *)

(* 
A transitiv sistem is defined by : a set of states, a set of initial states, a set of final states and a transition relation

The transitiv sistem is composed off of 2 states s and s', it returns a Prop (a multitude of properties - type, predefined in Coq);
  - comp from s to s' is a relation
  - s and s' are 2 states, we modify the state of s', based off of the state of s
  - "s ~~> s'" is the transitiv relation

The transitiv sistem must have 3 transitiv relations :

  - When the first component is larger than the second     if (comp1 s > comp2 s) it returns (through : ~~>) s'=(comp2 - comp1, comp2)
  - When the second component is larger than the first     if (comp1 s > comp2 s) it returns (through : ~~>) s'=(comp1-comp2, comp2)
  - And when they are equal                                if (comp1 s > comp2 s) it returns (through : ~~>) s'=(=nil)

In the case of a repetitiv change, we just have to processes the outputs;
 - if comp1 > comp2 or comp2 > comp1, we take s'-output and put it into s-input
 - If comp1 = comp2, we exit the comp() with return nil
*)






(* EX 3 : *)

 Reserved Notation "S1 ~~> S2" (at level 31).

 Inductive step (s s' : State) : Prop :=
 | left_gt : (fst s) > (snd s) ->
         s' = {fst s - snd s, snd s} ->              (* <---- Modification *)
         s ~~> s'
 | right_gt : (fst s) < (snd s) ->
         s' = {fst s, snd s - fst s} ->              (* <---- Modification *)
         s ~~> s'
 where "s ~~> s'" := (step s s').





(* EX 4 : *)

Require Import Omega.

Example ex0_step : {6, 3} ~~> {3, 3}.
Proof.
     apply left_gt. 
      - simpl. omega. 
      - simpl. reflexivity.
Qed.



Example ex1_step : {12, 15} ~~> {12, 3}.
Proof.
    apply right_gt. 
     - simpl. omega. 
     - simpl. reflexivity.
Qed.





(* EX 5 : *)

 Reserved Notation "A ==> B" (at level 32).
 Inductive steps(s s' : State) : Prop :=
 | refl : s = s' -> s ==> s'
 | tran : forall t,s ~~> t -> t ==> s' -> s ==> s'
 where "s ==> s'" := (steps s s').

 Example ex0_steps : {3, 3} ==> {3, 3}.
 Proof.
     apply refl. 
      - reflexivity.
 Qed.





(* EX 6 : *)

 Example ex1_steps: {12, 15} ==> {3, 3}.
 Proof.
     apply tran with (t := {12, 3}).
      - apply ex1_step.
      - apply tran with (t := {9, 3}).
        -- apply left_gt.
          --- simpl. simpl. omega. 
          --- simpl. reflexivity.
        -- apply tran with (t := {6,3}).
          --- apply left_gt.
            ---- simpl. simpl. omega. 
            ---- simpl. reflexivity.
          --- apply tran with (t := {3, 3}).
            ---- apply left_gt.
                  ----- simpl. simpl. omega. 
                  ----- simpl. reflexivity.
            ---- apply refl. 
            ----- reflexivity.

Qed.






































































