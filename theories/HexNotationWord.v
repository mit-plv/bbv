Require Export bbv.HexNotation.
Require Import bbv.WordScope.

Notation "'Ox' a" := (NToWord _ (hex a)) (at level 50).

Goal Ox"41" = WO~1~0~0~0~0~0~1.
Proof. reflexivity. Qed.
