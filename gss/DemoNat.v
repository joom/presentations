Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Theorem plus_0_n : forall (n : nat), n = plus O n.
Proof. Admitted.

Print plus_0_n.


Theorem plus_n_0 : forall n, n = plus n O.
Proof. Admitted.


Theorem plus_assoc : forall n m p : nat,
  plus n (plus m p) = plus (plus n m) p.
Proof. Admitted.
