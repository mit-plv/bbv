Set Loose Hint Behavior "Strict".
Require Export bbv.HexNotation.
Require Export bbv.ReservedNotations.
From Coq Require Import BinInt.

Notation "'Ox' a" := (Z.of_N (hex a)).

Goal Ox"41" = 65%Z.
Proof. reflexivity. Qed.
