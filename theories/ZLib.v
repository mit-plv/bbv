Require Import Coq.ZArith.BinInt.
Require Import Coq.omega.Omega.

Local Open Scope Z_scope.


Lemma mod2_cases: forall (n: Z), n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros. pose proof (Z.mod_pos_bound n 2). omega.
Qed.

Lemma div_mul_undo: forall a b,
    b <> 0 ->
    a mod b = 0 ->
    a / b * b = a.
Proof.
  intros.
  pose proof Z.div_mul_cancel_l as A. specialize (A a 1 b).
  replace (b * 1) with b in A by omega.
  rewrite Z.div_1_r in A.
  rewrite Z.mul_comm.
  rewrite <- Z.divide_div_mul_exact; try assumption.
  - apply A; congruence.
  - apply Z.mod_divide; assumption.
Qed.

Lemma mod_add_r: forall a b,
    b <> 0 ->
    (a + b) mod b = a mod b.
Proof.
  intros. rewrite <- Z.add_mod_idemp_r by omega.
  rewrite Z.mod_same by omega.
  rewrite Z.add_0_r.
  reflexivity.
Qed.
