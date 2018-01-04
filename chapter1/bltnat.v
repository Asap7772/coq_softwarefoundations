Fixpoint blt_nat (n m : nat) : bool :=
    match n with
    | 0 => 
      match m with
      |0 => false
      |_ => true
      end
    | S n' =>
      match m with
      |0 => false
      |S m' =>  blt_nat n' m'
      end
end.

Example test_blt_nat4: (blt_nat 0 0) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.

