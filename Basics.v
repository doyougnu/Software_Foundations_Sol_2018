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
(* Notation "¬ x" := (negb x). *)

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

Abort All.
Module NatPlayground.

(* Peano Axioms *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(* Remember these are just representations, the meaning is in the semantics *)
(* deep embedding ayy-o *)
Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

Definition pred (n:nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.

End NatPlayground.

Check (S (S (S (S O)))).
(* 4 *)
(*      : nat *)

Definition minustwo (n:nat) : nat :=
  match n with
  | O => O             (* zero minus two is zero in set nat *)
  | S O => O           (* one minus two is zero in set nat*)
  | S (S b) => b       (* any other number minus two is that number minus two *)
end.

Compute (minustwo 1729).

(* Check out these types *)
Check S.             (* nat -> nat*)
Check pred.          (* nat -> nat*)
Check minustwo.      (* nat -> nat*)

(* The data constructor S has the same type as these functions that operate on
nat. But these are fundamentally different, the functions have computation rules
attached to them. The constructor S is just a way to write down numbers, it is
data! *)

(* We use fixpoint for recursive functions. We pattern match on numbers. If zero
then true, if one then false, if greater than one, then minus two and recur. If
it is even you'll get to 0, if not you'll get to one. *)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S b) => evenb b
  end.

(* oddb is just negation composed with evenb. Wouldn't this look nice with
function composition and eta reduction *)
Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

(* addition, we check the first argument for zero, if it is zero we return the
second arg. If not zero, then we take an S from the first argument and build a
recursive bunch of S's. so (plus 2 1) turns into (S (S (plus 0 1))) = 3 *)
Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
  | O => m
  | S newN => S (plus newN m)
  end.

(* check the plus function *)
Compute (plus 3 2).

(* This is the simplification that happens for plus *)
(*  plus (S (S (S O))) (S (S O))
==> S (plus (S (S O)) (S (S O)))
      by the second clause of the match
==> S (S (plus (S O) (S (S O))))
      by the second clause of the match
==> S (S (S (plus O (S (S O)))))
      by the second clause of the match
==> S (S (S (S (S O))))
      by the first clause of the match
*)

(* multiplication we just add the second parameter, the number of times of the
first *)
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S newN => plus m (mult newN m)
  end.

(* The lack of a comma between (a b : nat) and the require comma in the match
pattern bothers me *)
Fixpoint minus (a b : nat) : nat :=
  match a,b with
  | O,_ => O
  | S _, O => a
  | S newA, S newB => minus newA newB
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(********************************* Exercises ***********************************)
(* factorial function. I wonder if it has the same memory issues as haskell? It
shouldn't*)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S newN => mult n (factorial newN)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
        | O => true
        | S m' => false
        end
  | S n' => match m with
            | O  => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (a b : nat) : bool :=
  match a with
  | O => true
  | S newA => match b with
             | O => false
             | S newB => leb newA newB
             end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise 2 less than *)
Definition blt_nat (a b : nat) : bool := negb (beq_nat a b) && leb a b.
Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(****************************** Simplification *********************************)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(* reflexivity can perform simple reduction, so simpl. is not actuall required*)
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = O.
Proof.
  intros n. reflexivity. Qed.

(****************************** Rewriting **************************************)
Theorem plus_id_example : forall n m :nat,
    n = m -> n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.

(****************************** Exercises **************************************)
Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  (* introduce all the varibles *)
  intros n m o.
  (* introduce all both hypotheses *)
  intros H I.
  (* rewrite the left side with hypothesis H *)
  rewrite -> H.
  (* rewrite the right side with hypothesis I *)
  rewrite <- I.
  (* Oh look both sides equate yay! *)
  reflexivity. Qed.

(* We can rewrite using these proven theorems *)
Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.  (* Like this! *)
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n -> m * (1 + n) = m * m.
Proof.
  (* introduce our variables *)
  intros n m.
  (* introduce the hypothesis given by implication *)
  intros H.
  (* looks like we can rewrite the left side for equivalence *)
  rewrite -> H.
  (* and we can  *)
  reflexivity. Qed.

(****************************** Case **************************************)
Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

 Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(****************************** Exercises **************************************)
(* There must be a cleaner way to write this than the direct case enum *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + intros H.
      rewrite <- H.
      simpl.
      reflexivity.
 - destruct c.
   + reflexivity.
   + intros H.
     rewrite <- H.
     simpl. reflexivity.
     Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [].
  - simpl. reflexivity.
  - simpl. reflexivity.

(* Fixpoint plus' (n : nat) (m : nat) : nat := *)
(*   match n, m with *)
(*   | O, O => O *)
(*   | S n' , O => S (plus' n' O) *)
(*   | O, S m' => S (plus' O m') *)
(*   | S n', S m' => S (plus' n' m') *)
(*   end. *)


(****************************** More Exercises *********************************)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool), (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f H [].
  - rewrite -> H.
    rewrite -> H.
    simpl. reflexivity.
  - rewrite ->  H.
    rewrite -> H.
    simpl. reflexivity.
Qed.

Lemma  eq_commutative : forall (a b : bool), (a = b -> b = a).
  Proof.
    intros [] [].
    - reflexivity.
    - intros H. rewrite -> H. reflexivity.
    - intros H. rewrite -> H. reflexivity.
    - reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

(* a *)
Inductive bin : Type :=
| OO : bin
| S' : bin -> bin
| SS : bin -> bin.

(* b *)

(* Fixpoint mult (n m : nat) : nat := *)
(*   match n with *)
(*   | O => O *)
(*   | S newN => plus m (mult newN m) *)
(*   end. *)
Fixpoint incr (a : bin) : bin := S' a.

Fixpoint bin_to_nat (a : bin) : nat :=
  match a with
  | OO => O
  | S' a' => S (bin_to_nat a')
  | SS a' => 2 * (bin_to_nat a')
  end.

(* unary counting can still work *)
Example test1: bin_to_nat (S' (S' (S' (S' OO)))) = 4.
Proof. simpl. reflexivity. Qed.

(* or we can do 2^2 * 1 *)
Example test2: bin_to_nat (SS (SS (S' OO))) = 4.
Proof. simpl. reflexivity. Qed.

(* just checking that 2^10 = 1024 *)
Example test3: bin_to_nat (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (S' OO))))))))))) = 1024.
Proof. simpl. reflexivity. Qed.