(* A post office in a galaxy far far away uses three denominations of stamps:
   1-cent stamps, 2-cent stamps, and 3-cent stamps. An element of the Postage 
   type defined below contains the number of stamps of each denomination in the
   respective position. Accordingly, Stamps x y z is x 1-cent stamps + y 2-cent 
   stamps + z 3-cent stamps. *)
Inductive Postage : Type :=
  | Stamps : nat -> nat -> nat -> Postage.

Inductive stamp : Type :=
  | _Stamps (x y z : Postage).

Print stamp.
 
Definition all_zero (nb : stamp) : Postage :=
  match nb with
    | (_Stamps x y z) => 0
    | (_Stamps _ _ _) => 1
  end.
(* Complete the definition of function Dispense below, such that it returns
   the correct number of stamps of each denomination required to pay a total
   of amount cents. Prioritize stamps of higher denominations to minimize
   the number of stamps used. You can introduce other functions if needed.
   Make sure that your definition passes the tests below. *)


Definition Dispense (amount : nat) : Postage := 
  match amount with
  | O => O
  | S n' => n'
  end.  

  match amount with
  | O => O
  | S n => O
  | S (S n') => n'
  end.

  match amount with
  | O => O
  | S O => O
  | S (S O) => O
  | S (S (S n')) => n'
  end.
end.


Example test_0: Dispense 0 = Stamps 0 0 0.
Proof. reflexivity. Qed.

Example test_1: Dispense 1 = Stamps 1 0 0.
Proof. reflexivity. Qed.

Example test_2: Dispense 2 = Stamps 0 1 0.
Proof. reflexivity. Qed.

Example test_3: Dispense 3 = Stamps 0 0 1.
Proof. reflexivity. Qed.

Example test_4: Dispense 4 = Stamps 1 0 1.
Proof. reflexivity. Qed.

Example test_5: Dispense 5 = Stamps 0 1 1.
Proof. reflexivity. Qed.

Example test_6: Dispense 6 = Stamps 0 0 2.
Proof. reflexivity. Qed.

