Theorem andb_eq_orb :
  forall(b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
intros [] [].
- intros H. reflexivity.
- simpl. intros H. rewrite H. reflexivity.
- simpl. intros H. rewrite H. reflexivity.
- intros H. reflexivity.
Qed.