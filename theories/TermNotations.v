From Stdlib Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped.
From GhostTT Require Export SubstNotations.

Open Scope subst_scope.

Set Default Goal Selector "!".

Notation "A ⇒[ i | j / mx | m ] B" :=
  (Pi i j m mx A (shift ⋅ B))
  (at level 20, i, j, mx, m at next level, right associativity).

Notation top := (bot ⇒[ 0 | 0 / mProp | mProp ] bot).
