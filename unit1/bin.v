Inductive bin: Type := | O : bin | B: bin -> bin | S: bin -> bin.

Fixpoint incr (b : bin) : bin :=
match b with
|O => S O
|B n' => S n'
|S n' => B (incr n')
end.

Example test_incr_1:
incr(O) = S O. 

Proof. simpl. reflexivity. Qed.

Example test_incr_2:
incr(S O) = B (S O).

Proof. simpl. reflexivity. Qed.