Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Check (S (S (S (S O)))).
  (* ===> 4 : nat *)
Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.
Compute (minustwo 4).
  (* ===> 2 : nat *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Compute oddb(S O).
Compute oddb(S (S O)).

Compute evenb(S O).
Compute evenb(S (S O)).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 5 2).
