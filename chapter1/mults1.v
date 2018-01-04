Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
intros n m.
intros H.
rewrite -> H.
simpl.
reflexivity.
Qed.