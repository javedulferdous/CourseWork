Require Export NArith.

(* Consider the example function Fib below. It computes the Fibonacci number
   with index n. Fibonacci numbers are defined by the formulas:
   Fib 0 = 0,
   Fib 1 = 1,
   Fib n = (Fib (n-1)) + (Fib (n-2)). *)

Fixpoint Fib_aux (n : nat) : (N * N) :=
  match n with
  | O => (0%N, 1%N)
  | S n' => 
      let (a, b) := Fib_aux n' in
      (b, (a + b)%N)
  end.

Definition Fib (n : nat) : N := fst (Fib_aux n).

(* Complete the definition of function Factorial below. You may write
   auxiliary functions if necessary. The Factorial function is defined by
   the formulas:
   Factorial 0 = 1,
   Factorial n = (Factorial (n-1)) * n. *)

Fixpoint factorial_aux (n : nat) : N :=
match n with
  | O => (1%N)
  | S n' => (factorial_aux (n') * N.of_nat n)%N
end.


Definition Factorial (n : nat) : N := factorial_aux n. 



(* Make sure that your function passes the tests below. 
   They should compute in less than a second each. *)

Example Test_Factorial_50 :
Factorial 50 =
30414093201713378043612608166064768844377641568960512000000000000%N.
Proof. time reflexivity. Qed.

Example Test_Factorial_100 :
Factorial 100 =
93326215443944152681699238856266700490715968264381621468592963895217599993229915608941463976156518286253697920827223758251185210916864000000000000000000000000%N.
Proof. time reflexivity. Qed.

