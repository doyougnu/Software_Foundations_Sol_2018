Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

 Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(******************************* Booleans **************************************)

(**These are defined in Coq.Init.Datatypes **)
Inductive bool : Type :=
  | true : bool
  | false : bool.

(* Negate a boolean by pattern matching on the data constructor *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* Given two bools, and a, and a b, compute their conjunction  *)
Definition andb (a:bool) (b:bool) : bool :=
  match a with
  | true => b
  | false => false
  end.

(* Given two bools, compute thier disjunction *)
(* in haskell this type is Bool -> Bool -> Bool *)
Definition orb (a:bool) (b:bool) : bool :=
  match a with
  | true => true
  | false => b
  end.

(* Some tests *)
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* Is notation a macro or a function? *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(* test the new notation *)
(* NOT LEGAL: Example test_&&: *)
Example test_and: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Some exercises *)

(* Why doesn't this work? *)
(* Notation "¬x" := (negb x). *)

(* Definition nandb (a:bool) (b:bool) : bool = ¬(a && b) *)
Definition nandb (a:bool) (b:bool) : bool := (negb (andb a b)).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.


(* Exercise 2 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := (b1 && (b2 && b3)).

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.


(******************************* Function Types ********************************)
(* Check is :t in ghci *)
Check negb.
(* negb *)
(*      : bool -> bool *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Definition monochrome (c:color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false (*Notice that c is being unboxed to a primary p*)
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(*Why not this? *)
(* Definition isred (c:color) : bool := *)
(*   match c with *)
(*   | primary red => true *)
(*   | _ => false *)
(*   end. *)

(******************************* Numbers ***************************************)