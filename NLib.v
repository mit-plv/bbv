Require Import Coq.NArith.NArith.

Local Open Scope N_scope.

Definition Nlt_dec: forall (l r : N), {l < r} + {l >= r}.
  refine (fun l r =>
    match Ncompare l r as k return Ncompare l r = k -> _ with
      | Lt => fun pf => left _ _
      | _ => fun pf => right _ _
    end (refl_equal _));
  abstract congruence.
Defined.
