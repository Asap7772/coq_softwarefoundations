Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m.
  intros o.
  
  intros H.
  intros I.
  
  rewrite -> H.
  rewrite -> I.
  reflexivity.
Qed.