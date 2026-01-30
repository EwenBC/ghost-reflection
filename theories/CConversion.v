From Stdlib Require Import Utf8 List.
From GhostTT.autosubst Require Import CCAST unscoped.
From GhostTT Require Import Util SubstNotations ContextDecl CScoping.

Import CombineNotations.


Reserved Notation "Γ ⊢ᶜ u ≡ v"
  (at level 80, u, v at next level, format "Γ  ⊢ᶜ  u  ≡  v").

Inductive conversion (Γ : ccontext) : cterm → cterm → Prop :=

(** Computation rules **)

| cconv_beta :
    ∀ mx A t u,
      Γ ⊢ᶜ capp (clam mx A t) u ≡ t <[ u .. ]

| cconv_El_val :
    ∀ mk A a,
      Γ ⊢ᶜ cEl (ctyval mk A a) ≡ A

| cconv_Err_val :
    ∀ mk A a,
      Γ ⊢ᶜ cErr (ctyval mk A a) ≡ a

| cconv_El_err :
    Γ ⊢ᶜ cEl ctyerr ≡ cunit

| cconv_Err_err :
    Γ ⊢ᶜ cErr ctyerr ≡ ctt

| cconv_J_refl :
    ∀ A u P t,
      Γ ⊢ᶜ tJ (trefl A u) P t ≡ t

| cconv_if_true :
    ∀ m P t f e,
      Γ ⊢ᶜ eif m etrue P t f e ≡ t

| cconv_if_false :
    ∀ m P t f e,
      Γ ⊢ᶜ eif m efalse P t f e ≡ f

| cconv_if_err :
    ∀ m P t f e,
      Γ ⊢ᶜ eif m bool_err P t f e ≡ e

| cconv_pif_true :
    ∀ P t f,
      Γ ⊢ᶜ pif ptrue P t f ≡ t

| cconv_pif_false :
    ∀ P t f,
      Γ ⊢ᶜ pif pfalse P t f ≡ f

| cconv_enat_elim_zero :
    ∀ P z s,
      Γ ⊢ᶜ enat_elim ezero P z s ≡ z

| cconv_enat_elim_succ :
    ∀ P z s n,
      Γ ⊢ᶜ enat_elim (esucc n) P z s ≡ capp (capp s n) (enat_elim n P z s)

| cconv_evec_elim_nil :
    ∀ A P z s,
      Γ ⊢ᶜ evec_elim (evnil A) P z s ≡ z

| cconv_evec_elim_cons :
    ∀ a v P z s,
      Γ ⊢ᶜ evec_elim (evcons a v) P z s ≡
      capp (capp (capp s a) v) (evec_elim v P z s)

(** Congruence rules **)

(** A rule to quotient away all levels of Prop, making it impredicative **)
| ccong_Prop :
    ∀ i j,
      Γ ⊢ᶜ cSort cProp i ≡ cSort cProp j

| ccong_Pi :
    ∀ mx A A' B B',
      Γ ⊢ᶜ A ≡ A' →
      Some (mx, A) :: Γ ⊢ᶜ B ≡ B' →
      Γ ⊢ᶜ cPi mx A B ≡ cPi mx A' B'

| ccong_clam :
    ∀ mx A A' t t',
      Γ ⊢ᶜ A ≡ A' →
      Some (mx, A) :: Γ ⊢ᶜ t ≡ t' →
      Γ ⊢ᶜ clam mx A t ≡ clam mx A' t'

| ccong_app :
    ∀ u u' v v',
      Γ ⊢ᶜ u ≡ u' →
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ capp u v ≡ capp u' v'

(* Maybe not needed? *)
| ccong_bot_elim :
    ∀ m A A' p p',
      Γ ⊢ᶜ A ≡ A' →
      (* Needed because syntactically we don't know p and p' are irrelevant *)
      Γ ⊢ᶜ p ≡ p' →
      Γ ⊢ᶜ cbot_elim m A p ≡ cbot_elim m A' p'

| ccong_tyval :
    ∀ mk A A' a a',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ a ≡ a' →
      Γ ⊢ᶜ ctyval mk A a ≡ ctyval mk A' a'

| ccong_El :
    ∀ T T',
      Γ ⊢ᶜ T ≡ T' →
      Γ ⊢ᶜ cEl T ≡ cEl T'

| ccong_Err :
    ∀ T T',
      Γ ⊢ᶜ T ≡ T' →
      Γ ⊢ᶜ cErr T ≡ cErr T'

| ccong_squash :
    ∀ A A',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ squash A ≡ squash A'

| ccong_teq :
    ∀ A A' u u' v v',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ u ≡ u' →
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ teq A u v ≡ teq A' u' v'

| ccong_trefl :
    ∀ A A' u u',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ u ≡ u' →
      Γ ⊢ᶜ trefl A u ≡ trefl A' u'

| ccong_tJ :
    ∀ e e' P P' t t',
      Γ ⊢ᶜ e ≡ e' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ t ≡ t' →
      Γ ⊢ᶜ tJ e P t ≡ tJ e' P' t'

| ccong_eif :
    ∀ m b P t f e b' P' t' f' e',
      Γ ⊢ᶜ b ≡ b' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ t ≡ t' →
      Γ ⊢ᶜ f ≡ f' →
      Γ ⊢ᶜ e ≡ e' →
      Γ ⊢ᶜ eif m b P t f e ≡ eif m b' P' t' f' e'

| ccong_pif :
    ∀ bP P t f bP' P' t' f',
      Γ ⊢ᶜ bP ≡ bP' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ t ≡ t' →
      Γ ⊢ᶜ f ≡ f' →
      Γ ⊢ᶜ pif bP P t f ≡ pif bP' P' t' f'

| ccong_esucc :
    ∀ n n',
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ esucc n ≡ esucc n'

| ccong_enat_elim :
    ∀ n P z s n' P' z' s',
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ z ≡ z' →
      Γ ⊢ᶜ s ≡ s' →
      Γ ⊢ᶜ enat_elim n P z s ≡ enat_elim n' P' z' s'

(* Morally unnecessary because of proof irrelevance, but we would need scoping *)
| ccong_psucc :
    ∀ n n',
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ psucc n ≡ psucc n'

(* Same *)
| ccong_pnat_elim :
    ∀ ne nP Pe PP ze zP se sP ne' nP' Pe' PP' ze' zP' se' sP',
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ ze ≡ ze' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ se ≡ se' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pnat_elim ne nP Pe PP ze zP se sP ≡ pnat_elim ne' nP' Pe' PP' ze' zP' se' sP'

(* Same *)
| ccong_pnat_elimP :
    ∀ ne nP Pe PP zP sP ne' nP' Pe' PP' zP' sP',
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pnat_elimP ne nP Pe PP zP sP ≡ pnat_elimP ne' nP' Pe' PP' zP' sP'

| ccong_evec :
    ∀ A A',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ evec A ≡ evec A'

| ccong_evnil :
    ∀ A A',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ evnil A ≡ evnil A'

| ccong_evcons :
    ∀ a v a' v',
      Γ ⊢ᶜ a ≡ a' →
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ evcons a v ≡ evcons a' v'

| ccong_evec_elim :
    ∀ v P z s v' P' z' s',
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ P ≡ P' →
      Γ ⊢ᶜ z ≡ z' →
      Γ ⊢ᶜ s ≡ s' →
      Γ ⊢ᶜ evec_elim v P z s ≡ evec_elim v' P' z' s'

(* Also unnecessary *)
| ccong_pvec :
    ∀ A AP n nP A' AP' n' nP',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ AP ≡ AP' →
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ pvec A AP n nP ≡ pvec A' AP' n' nP'

(* Same *)
| ccong_pvnil :
    ∀ A A',
      Γ ⊢ᶜ A ≡ A' →
      Γ ⊢ᶜ pvnil A ≡ pvnil A'

(* Same *)
| ccong_pvcons :
    ∀ a n v a' n' v',
      Γ ⊢ᶜ a ≡ a' →
      Γ ⊢ᶜ n ≡ n' →
      Γ ⊢ᶜ v ≡ v' →
      Γ ⊢ᶜ pvcons a n v ≡ pvcons a' n' v'

(* Same *)
| ccong_pvec_elim :
    ∀ Ae AP ne nP ve vP Pe PP ze zP se sP Ae' AP' ne' ve' vP' nP' Pe' PP' ze' zP' se' sP',
      Γ ⊢ᶜ Ae ≡ Ae' →
      Γ ⊢ᶜ AP ≡ AP' →
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ ve ≡ ve' →
      Γ ⊢ᶜ vP ≡ vP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ ze ≡ ze' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ se ≡ se' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pvec_elim Ae AP ne nP ve vP Pe PP ze zP se sP ≡ pvec_elim Ae' AP' ne' nP' ve' vP' Pe' PP' ze' zP' se' sP'

(* Same *)
| ccong_pvec_elimG :
    ∀ Ae AP ne nP ve vP Pe PP ze zP se sP Ae' AP' ne' ve' vP' nP' Pe' PP' ze' zP' se' sP',
      Γ ⊢ᶜ Ae ≡ Ae' →
      Γ ⊢ᶜ AP ≡ AP' →
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ ve ≡ ve' →
      Γ ⊢ᶜ vP ≡ vP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ ze ≡ ze' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ se ≡ se' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pvec_elimG Ae AP ne nP ve vP Pe PP ze zP se sP ≡ pvec_elimG Ae' AP' ne' nP' ve' vP' Pe' PP' ze' zP' se' sP'

(* Same *)
| ccong_pvec_elimP :
    ∀ Ae AP ne nP ve vP Pe PP zP sP Ae' AP' ne' nP' ve' vP' Pe' PP' zP' sP',
      Γ ⊢ᶜ Ae ≡ Ae' →
      Γ ⊢ᶜ AP ≡ AP' →
      Γ ⊢ᶜ ne ≡ ne' →
      Γ ⊢ᶜ nP ≡ nP' →
      Γ ⊢ᶜ ve ≡ ve' →
      Γ ⊢ᶜ vP ≡ vP' →
      Γ ⊢ᶜ Pe ≡ Pe' →
      Γ ⊢ᶜ zP ≡ zP' →
      Γ ⊢ᶜ sP ≡ sP' →
      Γ ⊢ᶜ pvec_elimP Ae AP ne nP ve vP Pe PP zP sP ≡ pvec_elimP Ae' AP' ne' nP' ve' vP' Pe' PP' zP' sP'

(** Structural rules **)

| cconv_refl :
    ∀ u,
      Γ ⊢ᶜ u ≡ u

| cconv_sym :
    ∀ u v,
      Γ ⊢ᶜ u ≡ v →
      Γ ⊢ᶜ v ≡ u

| cconv_trans :
    ∀ u v w,
      Γ ⊢ᶜ u ≡ v →
      Γ ⊢ᶜ v ≡ w →
      Γ ⊢ᶜ u ≡ w

(** Proof irrelevance **)

| cconv_irr :
    ∀ p q,
      ccxscoping Γ p cProp →
      ccxscoping Γ q cProp →
      Γ ⊢ᶜ p ≡ q

where "Γ ⊢ᶜ u ≡ v" := (conversion Γ u v).



Create HintDb cc_conv discriminated.

Hint Resolve cconv_beta cconv_El_val cconv_Err_val cconv_El_err cconv_Err_err
  cconv_J_refl ccong_Prop ccong_Pi ccong_clam ccong_app ccong_bot_elim
  ccong_tyval ccong_El ccong_Err ccong_squash ccong_teq ccong_trefl ccong_tJ
  cconv_if_true cconv_if_false cconv_if_err ccong_eif cconv_pif_true
  cconv_pif_false ccong_pif cconv_enat_elim_zero cconv_enat_elim_succ
  ccong_esucc ccong_enat_elim ccong_psucc ccong_pnat_elim ccong_pnat_elimP
  cconv_evec_elim_nil cconv_evec_elim_cons ccong_evec ccong_evnil ccong_evcons
  ccong_evec_elim ccong_pvec ccong_pvnil ccong_pvcons ccong_pvec_elim
  ccong_pvec_elimG ccong_pvec_elimP
  cconv_refl
: cc_conv.


Ltac econv :=
  unshelve typeclasses eauto with cc_conv shelvedb ; shelve_unifiable.
