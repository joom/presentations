(* part 1 *)
Inductive day : Set :=
  | monday    : day
  | tuesday   : day
  | wednesday : day
  | thursday  : day
  | friday    : day
  | saturday  : day
  | sunday    : day.

Definition next_day (d : day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end.

Compute (next_day friday).

Fixpoint app_times {a : Set} (f : a -> a) (x : a) (n : nat) : a :=
  match n with
  | O => x
  | S n' => app_times f (f x) n'
  end.

Compute (app_times next_day monday 7).

Theorem seven_is_the_charm : forall (d : day), d = app_times next_day d 7.
Proof.
