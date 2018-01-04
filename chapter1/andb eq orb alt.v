Theorem andb_eq_orb :
  forall(b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
intros b c.
destruct b.
- simpl. destruct c. 
+ intros H. reflexivity.
+ intros H. rewrite H. reflexivity.
- simpl. destruct c. 
+ intros H. rewrite H. reflexivity.
+ intros H. reflexivity.
Qed.

