 Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
intros n.
induction n as [ | n' IHn'].
- simpl. reflexivity.
- rewrite -> IHn'. simpl. rewrite -> negb_involutive. reflexivity.
Qed.
  