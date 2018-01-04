Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
 
intros [] [].
+ reflexivity.
+ intros N. rewrite <- N. reflexivity.
+ reflexivity.
+ intros N. rewrite <- N. reflexivity.
Qed.