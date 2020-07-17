Require Import Arith.
Require Import ZArith.

(*If a<=c and b<=d then a*b<=c*d*)

Theorem multiByMulti :
  forall a b c d : nat, a <= c -> b <= d -> a*b <= c*d.
Proof.
  intros a b c d H H0. 
  apply le_trans with (m := c*b).
  apply mult_le_compat_r. 
  apply H. 
  apply mult_le_compat_l. auto.
Qed.

(*If n < m then n < succ (m)*)
Theorem LessThanSuccesor : forall n m : nat, n < m -> n < S m.
Proof.
  intros n m H. auto.
Qed.

Open Scope Z_scope.
Parameters (A:Type)  (P Q: A->Prop).

  Theorem ExistentialImplyToExistential :
    (ex P) -> (forall x : A, P x -> Q x) -> (ex Q).
Proof.
    intros H H0. 
    elim H. 
    intros x Hx. 
    exists x. auto.
  Qed.

  Theorem ExistentialOr :
    (exists (x : A), P x \/ Q x) -> (ex P) \/ (ex Q).
  Proof.
    intros H. 
    elim H.
    intros x H_PQ. 
    elim H_PQ. 
    intros H_Px.
    left.
    exists x.
    apply H_Px.
    intros H_Qx. 
    right. 
    exists x. auto.
  Qed.



  Theorem ExistentialOrReverse :
    (ex P) \/ (ex Q) -> (exists x: A, P x \/ Q x).
  Proof.
    intro H_or.
    elim H_or.
    intro H_Px.
    elim H_Px.
    intros x H_Px'. 
    exists x.
    left.
    apply H_Px'.
    intro H_ex_Qx.
    elim H_ex_Qx.
    intros x H_Qx.
    exists x. auto.
  Qed.

  Theorem RealNumber :
    (exists x : A, forall R:A -> Prop, R x) -> 3 = 3.
  Proof.
    intros H.
    elim H.
    intros x Hx. simpl.
    elim (Hx (fun y:A => True)). auto.
  Qed.

  Theorem approximatelyequal	 :
    (forall x : A, P x) -> ~(exists y : A, ~ P y).
  Proof.
    intros.
    unfold not. 
    intros.
    elim H0. auto.
  Qed.


Theorem symmetric : forall (A:Type) (x y :A), x=y -> y=x.
Proof.
  intros. auto.
Qed.

Theorem mult_distribution : forall n x : Z, n*x+x = (n+1)*x.
Proof.
  intros  x z.
  rewrite -> Zmult_plus_distr_l.
  rewrite -> Zmult_1_l. auto.
Qed.

Theorem mult_sym : forall n x : Z, n*x = x*n.
Proof.
  intros  x z.
  rewrite -> Z.mul_comm. auto.
Qed.

Theorem mult_sym' : forall n m x : Z, (n*m)*x = n*(m*x).
Proof.
  intros  x m z.
  rewrite -> Z.mul_assoc. auto.
Qed.

 Theorem mult_sym'' : forall n m x : Z, x*(n+m) = x*n+x*m.
Proof.
  intros  x m z.
  auto with zarith.
Qed. 

 Theorem additive_inverses : forall a : Z, a+ (-a) = (-a)+a.
Proof.
  intros. 
  rewrite Z.add_opp_r. rewrite <- Z.add_opp_l. auto.
Qed. 

Theorem mult_property : forall a : Z, -1 * a = -a.
Proof.
  intros.  simpl. auto.
Qed.

Theorem axiom1 : forall a b : Z, - (a + b) = -a - b.
Proof.
  intros.  rewrite <-  Z.add_opp_r. rewrite  Z.add_opp_l. rewrite Z.opp_add_distr. rewrite <-  Z.add_opp_l. auto.
Qed.

Theorem axiom2 : forall a b : Z, - (a + b) = -(1*a) + (- (1*b)).
Proof.
   intros.   rewrite Z.opp_add_distr. rewrite ->Z.add_opp_r. 
   rewrite <-Z.opp_add_distr. rewrite Z.mul_1_l. 
   rewrite Z.mul_1_l. rewrite axiom1. auto.
Qed.




Theorem SummationOf : forall a:Z, a+a+a+a+a+a+a+a+a+a = 10 * a.
Proof.
  intros a. 
  rewrite <- Zmult_1_l.
  auto with zarith.
Qed.

 Theorem trans : forall a b c : nat, a=b -> b=c -> a=c.
Proof.
  intros.
  transitivity a; rewrite H.
  - auto.
  - rewrite H0. auto.
Qed. 
Close Scope Z_scope.


Theorem permute :  forall n m p:nat, n+m+p = n+p+m.
Proof.
  intros n m p.
  rewrite <- plus_assoc.
  pattern (m+p) at 1.
  rewrite plus_comm.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem plus_comm  : forall n m:nat, n + m = m + n.
Proof.
  intros n m. 
  rewrite plus_comm.
  auto.
Qed.

Theorem plus_assoc_reverse : forall n m p:nat, n + m + p = n + (m + p).
Proof.
  intros n m p. 
  repeat rewrite plus_assoc_reverse.
  auto. 
Qed.

Lemma all_perm : forall (A:Type) (P:A -> A -> Prop),
   (forall x y:A, P x y) -> 
   forall x y:A, P y x.

Proof.
   intros A P H x y; apply H. 
Qed.

Lemma resolution : forall (A:Type) (P Q R S:A -> Prop),
   (forall a:A, Q a -> R a -> S a) ->
   (forall b:A, P b -> Q b) -> forall c:A, P c -> R c -> S c.
Proof.
 intros A P Q R S H H0 c H1 H2. auto.
Qed.

Theorem deMorgan1 (P Q: Prop):  ~(P \/ Q) -> ~P /\ ~Q.

Proof.
intros. unfold not. auto.
Qed.

Theorem deMorgan2 (P Q: Prop): ~P/\~Q -> ~(P\/Q).

Proof.
   intros A B.
  destruct A as [_A _B].
  destruct B as [A_1 | B_1].
  - apply _A. exact A_1.
  - apply _B. exact B_1.
Qed.  

Theorem bool_equal_0 : forall b : bool, b = true \/ b = false.
Proof.
intros a .
induction a.
-auto.
-auto.
Qed. 
 
Theorem All_true : True \/ True.
Proof.
auto.
Qed.

Theorem not_true_false : ~true = false.
Proof.
  unfold not.
  intros H_eq.  
  change ((fun (v:bool) => match v with true => True | false => False end)
          false). 
  rewrite <- H_eq.  auto.
Qed.

Inductive TypeOfPolygon : Set :=
  | Triangle  | Quadrilateral | Pentagon  | Hexagon | Heptagon | Octagon
  | Nonagon     | Decagon    | Hendecagon | Dodecagon | Tridecagon | Tetradecagon
  | Pendedecagon | Hexdecagon | Heptdecagon | Octdecagon | Enneadecagon | Icosagon.
Print TypeOfPolygon_rec.

(*  *)

Inductive NumberOfAngle : Set :=
  | three | four | five | six | seven | eight | nine  | ten | eleven | twelve | thirteen | fourteen 
  | fifteen | sixteen | seventeen | eighteen | ninteen | twenty.


Definition angle_for_polygon (m : TypeOfPolygon) : NumberOfAngle :=
  match m with
      | Triangle => three
      | Quadrilateral => four
      | Pentagon => five
      | Hexagon => six
      | Heptagon => seven
      | Octagon => eight
      | Nonagon => nine
      | Decagon => ten
      | Hendecagon => eleven
      | Dodecagon => twelve
      | Tridecagon => thirteen
      | Tetradecagon =>  fourteen
      | Pendedecagon =>  fifteen
      | Hexdecagon => sixteen
      | Heptdecagon => seventeen
      | Octdecagon => eighteen
      | Enneadecagon => ninteen
      | Icosagon => twenty
  end.

Theorem All_polygon :
  forall m : TypeOfPolygon, 
  m = Triangle \/ m = Quadrilateral \/ m = Pentagon \/m = Hexagon \/m = Heptagon \/m = Octagon
  \/m = Nonagon     \/m = Decagon   \/m = Hendecagon \/m = Dodecagon \/m = Tridecagon \/m = Tetradecagon
  \/m = Pendedecagon \/m = Hexdecagon \/m = Heptdecagon \/m = Octdecagon \/m = Enneadecagon \/m = Icosagon.  
Proof.
  intro m.
  pattern m.
  Check TypeOfPolygon_ind.
  apply TypeOfPolygon_ind.
  left. reflexivity.
  right. left. reflexivity.
  right. right. left. reflexivity.
  right. right. right. left. reflexivity.
  right. right. right. right. left. reflexivity.
  right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. right. right. right. left. reflexivity. 
  right. right. right. right. right. right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. right. right. right. right. right.  left. reflexivity.
  right. right. right. right. right. right. right. right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. left.  reflexivity.
  right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. reflexivity.
Qed.

(* Undirected graph: (n*(n-1))/2 *)


Inductive NumberOfEdge : Set :=
  | three' | six' | ten' | fifteen' | TwentyOne | twentyEight| ThirtySix | fortyFive 
  | fiftyFive | sistySix | seventyEight | nintyOne | oneHundredFive | onehundredTwenty
  | oneHundredThirtySix | oneHundredFiftyThree | oneHundredSeventyOne | oneHundredNinty.

Definition Edge_Polygon (m : TypeOfPolygon) : NumberOfEdge :=
  match m with
      | Triangle => three'
      | Quadrilateral => six'
      | Pentagon => ten'
      | Hexagon => fifteen'
      | Heptagon => TwentyOne
      | Octagon => twentyEight
      | Nonagon => ThirtySix
      | Decagon => fortyFive
      | Hendecagon => fiftyFive
      | Dodecagon => sistySix
      | Tridecagon => seventyEight
      | Tetradecagon =>  nintyOne
      | Pendedecagon =>  oneHundredFive
      | Hexdecagon => onehundredTwenty
      | Heptdecagon => oneHundredThirtySix
      | Octdecagon => oneHundredFiftyThree
      | Enneadecagon => oneHundredSeventyOne
      | Icosagon => oneHundredNinty
  end.

Theorem Hexagon_has_fifteen'_edge:
  forall m : TypeOfPolygon, m = Hexagon -> Edge_Polygon m = fifteen'.
Proof.
  intros m.
  intros H.
  rewrite -> H.
  simpl.
  reflexivity.
Qed.  

Theorem IcosagonIsNotEqualToQuadrilateral : ~Icosagon = Quadrilateral.
Proof.
  unfold not.
  intros H.
  change ((fun m:TypeOfPolygon => 
            match m with Icosagon => True | _ => False end) Quadrilateral).
  rewrite <- H. auto.
Qed.