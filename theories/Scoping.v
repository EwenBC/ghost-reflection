(** Scoping

  Stating that all variables are in a given scope, and in a given mode.

**)

From Coq Require Import Utf8 List.
From GhostTT.autosubst Require Import AST unscoped.
From GhostTT Require Import BasicAST SubstNotations ContextDecl CastRemoval.

Import ListNotations.

Set Default Goal Selector "!".

Inductive scoping (Γ : scope) : term → mode → Prop :=

| scope_var :
    ∀ x m,
      nth_error Γ x = Some m →
      scoping Γ (var x) m

| scpoe_sort :
    ∀ m i,
      scoping Γ (Sort m i) mKind

| scope_pi :
    ∀ mx m A B,
      scoping Γ A mKind →
      scoping (mx :: Γ) B mKind →
      scoping Γ (Pi m mx A B) mKind

| scope_lam :
    ∀ mx m A t,
      scoping Γ A mKind →
      scoping (mx :: Γ) t m →
      scoping Γ (lam mx A t) m

| scope_app :
    ∀ mx m t u,
      scoping Γ t m →
      scoping Γ u mx →
      scoping Γ (app t u) m

| scope_erased :
    ∀ A,
      scoping Γ A mKind →
      scoping Γ (Erased A) mKind

| scope_erase :
    ∀ t,
      scoping Γ t mType →
      scoping Γ (erase t) mGhost

| scope_reveal :
    ∀ m t P p,
      In m [ mProp ; mGhost ] →
      scoping Γ t mGhost →
      scoping Γ P mKind →
      scoping Γ p m →
      scoping Γ (reveal t P p) m

| scope_revealP :
    ∀ t p,
      scoping Γ t mGhost →
      scoping Γ p mKind →
      scoping Γ (revealP t p) mKind

| scope_gheq :
    ∀ A u v,
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ v mGhost →
      scoping Γ (gheq A u v) mKind

| scope_ghrefl :
    ∀ A u,
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ (ghrefl A u) mProp

| scope_ghcast :
    ∀ m A u v e P t,
      m ≠ mKind →
      scoping Γ A mKind →
      scoping Γ u mGhost →
      scoping Γ v mGhost →
      scoping Γ e mProp →
      scoping Γ P mKind →
      scoping Γ t m →
      scoping Γ (ghcast e P t) m

| scope_bot :
    scoping Γ bot mKind

| scope_bot_elim :
    ∀ m A p,
      scoping Γ A mKind →
      scoping Γ p mProp →
      scoping Γ (bot_elim m A p) m
.

Definition cscoping (Γ : context) := scoping (sc Γ).
