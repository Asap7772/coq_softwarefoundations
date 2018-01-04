Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
intros n.
induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros n m.
induction m as [| m' IHm'].
- simpl. induction n as [| n' IHn'].
+ reflexivity.
+ simpl. rewrite -> IHn'. reflexivity.
- simpl. rewrite <- IHm'. rewrite -> plus_n_Sm. reflexivity.
Qed. 

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.





