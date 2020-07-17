(** Exercise: 1 star, standard (nandb)*)

Definition nandb (b1:bool) (b2:bool) : bool:=
  match (b1, b2) with
  | (true,  true)  => false
  | _              => true
  end.
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(**Exercise: 1 star, standard (andb3)*)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool:=
  match (b1,b2,b3) with
  | (true,true,true) => true
  | _                => false
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(**Exercise: 1 star, standard (factorial)*)

Fixpoint factorial (n:nat) : nat:=
match n with
  | O    => 1
  | S n' => mult (S n') (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

(**Exercise: 1 star, standard (ltb)*)

Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' => match m with
              | O => false
              | S m' => leb n' m'
              end
    end.

Definition ltb (n m : nat) : bool :=
    (andb (leb n m) (negb (leb m n))).
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(*Exercise: 1 star, standard (plus_id_exercise)*)

Theorem plus_id_exercise: forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros. rewrite -> H. rewrite <- H0. reflexivity. Qed.

(**Exercise: 2 stars, standard (mult_S_1)*)


Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.


Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity. Qed.

(**Exercise: 2 stars, standard (andb_true_elim2)*)


Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  Proof.
intros b c H.
destruct c.
reflexivity.
rewrite <- H.
destruct b.
reflexivity.
reflexivity.
Qed.

(**Exercise: 1 star, standard (zero_nbeq_plus_1)*)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [|n'].
    reflexivity.
    reflexivity. Qed.

