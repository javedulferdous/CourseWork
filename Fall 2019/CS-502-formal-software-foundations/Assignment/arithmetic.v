Require Export Arith.

(* Prove the following theorem.

   Hint 1: It is convenient to use the SearchPattern utility. From the main menu 
   select View, then Query Pane. Select SearchPattern in the top left drop box. 
   In the top right box type your pattern followed by enter. For example, the 
   pattern 
      ((_ + _) * _ = _ *_ + _ * _) 
   will result in 
      Nat.mul_add_distr_r.

   Hint 2: Sometimes the 
      rewrite 
   tactic needs to be supplemented with variable assignments that tell Coq how 
   the variables in the used theorem correspond to the expressions in your goal.
   For example, 
      rewrite Nat.mul_comm with (m := 2) (n := m).

   Hint 3: Variables can be assigned complex expressions, too. For example,
      (n := m * m)

   Hint 4: The tactic
      reflexivity.
   can finish up remaining constant expressions, such as
      2 * 2
   and therefore they can be left until the very end.
*)
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. reflexivity.  Qed.

Theorem Homework : forall n m p : nat, 
n = S m -> p = m + 2 -> n * p = m * m + 3 * m + 2.

(*
n = S m 
p = m + 2 
n * p = m * m + 3 * m + 2.
*)
Proof.
intros a b c d e.
rewrite e.
rewrite d.
rewrite <- plus_1_l.
rewrite ->Nat.mul_add_distr_r.
rewrite ->Nat.mul_add_distr_l.
rewrite Nat.mul_1_l.
rewrite Nat.mul_1_l.
rewrite Nat.mul_comm.
rewrite Nat.mul_add_distr_r.
repeat rewrite Nat.add_assoc.
rewrite <-Nat.add_shuffle0.
simpl.
repeat rewrite Nat.add_assoc.
rewrite <-Nat.add_comm.
repeat rewrite Nat.add_assoc.
rewrite Nat.add_0_r.
rewrite -> Nat.add_0_r.          (*b * b + b + 2 + b + b = b * b + b + b + b + 2*)
rewrite <-Nat.add_assoc.
rewrite <-Nat.add_shuffle0.
repeat rewrite Nat.add_assoc.
reflexivity.
Qed.
