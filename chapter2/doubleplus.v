Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
induction n as [| n' IHn'].
- reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.
 
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
intros n.
induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.