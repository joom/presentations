Require Import Omega.

Theorem plus_0_n : forall (n : nat), n = plus O n.
Proof. intros. omega. Qed.

Print plus_0_n.

Theorem plus_n_0 : forall n, n = plus n O.
Proof. intros. omega. Qed.

Theorem plus_assoc : forall n m p : nat,
  plus n (plus m p) = plus (plus n m) p.
Proof. intros. omega. Qed.

Theorem nat_total_order : forall (n m : nat), (n < m) \/ (n = m) \/ (n > m).
Proof. intros. omega. Qed.
