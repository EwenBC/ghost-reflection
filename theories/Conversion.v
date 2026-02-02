From Stdlib Require Import Utf8 List.
From GhostTT.autosubst Require Import GAST unscoped GAST_rasimpl.
From GhostTT Require Import Util ContextDecl CastRemoval TermMode Scoping.
From GhostTT Require Import Univ TermNotations.

Reserved Notation "Γ ⊢ u ≡ v"
  (at level 80, u, v at next level, format "Γ  ⊢  u  ≡  v").

Import ListNotations.

(** Before we define typing for vectors we need to define the gS function **)
Definition gS n :=
  reveal n (lam mGhost (Erased tnat) (Erased tnat))
    (lam mType tnat (hide (tsucc (var 0)))).

(** We also need something which is essentially the length function
  but whose main idea is to recompute the index of a vector.
**)
Definition glength A n v :=
  tvec_elim mGhost A n v
    (* return *) (lam mGhost (Erased tnat) (
      lam mType (tvec (S ⋅ A) (var 0)) (Erased tnat)
    )
    )
    (* vnil => *) (hide tzero)
    (* vcons => *) (lam mType A (
      lam mGhost (Erased tnat) (
        lam mType (tvec (S ⋅ S ⋅ A) (var 0)) (
          lam mGhost (Erased tnat) (gS (var 0))
        )
      )
    )).
Inductive conversion (Γ : context) : term → term → Prop :=

  (** Computation rules **)

  | conv_beta :
      ∀ m mx A t u,
      cscoping Γ A mKind →
      scoping (mx :: sc Γ) t m →
      cscoping Γ u mx →
      Γ ⊢ app (lam mx A t) u ≡ t <[ u .. ]

  | reveal_hide :
      ∀ mp t P p,
      cscoping Γ t mType →
      cscoping Γ P mKind →
      cscoping Γ p mp →
      In mp [ mProp ; mGhost ] →
      Γ ⊢ reveal (hide t) P p ≡ app p t

  | conv_if_true :
      ∀ m P t f,
      cscoping Γ t m →
      Γ ⊢ tif m ttrue P t f ≡ t

  | conv_if_false :
      ∀ m P t f,
      cscoping Γ f m →
      Γ ⊢ tif m tfalse P t f ≡ f

  | conv_nat_elim_zero :
      ∀ m P z s,
      m ≠ mKind →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ tnat_elim m tzero P z s ≡ z

  | conv_nat_elim_succ :
      ∀ m P z s n,
      m ≠ mKind →
      cscoping Γ n mType →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ tnat_elim m (tsucc n) P z s ≡ app (app s n) (tnat_elim m n P z s)

  | conv_vec_elim_nil :
      ∀ m A P z s,
      m ≠ mKind →
      cscoping Γ A mKind →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ tvec_elim m A (hide tzero) (tvnil A) P z s ≡ z

  | conv_vec_elim_cons :
      ∀ m A a n n' v P z s,
      m ≠ mKind →
      cscoping Γ A mKind →
      cscoping Γ a mType →
      cscoping Γ n mGhost →
      cscoping Γ n' mGhost →
      cscoping Γ v mType →
      cscoping Γ P mKind →
      cscoping Γ z m →
      cscoping Γ s m →
      Γ ⊢ tvec_elim m A n' (tvcons a n v) P z s ≡
      app (app (app (app s a) (glength A n v)) v) (tvec_elim m A n v P z s)

      (** Congruence rules **)

      (** A rule to quotient away all levels of Prop, making it impredicative **)
  | cong_Prop :
      ∀ i j,
      Γ ⊢ Sort mProp i ≡ Sort mProp j

  | cong_Pi :
      ∀ i i' j j' m mx A A' B B',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ B ≡ B' →
      ueq mx i i' →
      ueq m j j' →
      Γ ⊢ Pi i j m mx A B ≡ Pi i' j' m mx A' B'

  | cong_lam :
      ∀ mx A A' t t',
      Γ ⊢ A ≡ A' →
      Γ ,, (mx, A) ⊢ t ≡ t' →
      Γ ⊢ lam mx A t ≡ lam mx A' t'

  | cong_app :
      ∀ u u' v v',
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ app u v ≡ app u' v'

  | cong_Erased :
      ∀ A A',
      Γ ⊢ A ≡ A' →
      Γ ⊢ Erased A ≡ Erased A'

  | cong_hide :
      ∀ u u',
      Γ ⊢ u ≡ u' →
      Γ ⊢ hide u ≡ hide u'

  | cong_reveal :
      ∀ t t' P P' p p',
      Γ ⊢ t ≡ t' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ p ≡ p' →
      Γ ⊢ reveal t P p ≡ reveal t' P' p'

  | cong_Reveal :
      ∀ t t' p p',
      Γ ⊢ t ≡ t' →
      Γ ⊢ p ≡ p' →
      Γ ⊢ Reveal t p ≡ Reveal t' p'

  | cong_gheq :
      ∀ A A' u u' v v',
      Γ ⊢ A ≡ A' →
      Γ ⊢ u ≡ u' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ gheq A u v ≡ gheq A' u' v'

      (* No need for it thanks to proof irrelevance *)
      (* | cong_ghrefl :
         ∀ A A' u u',
         Γ ⊢ A ≡ A' →
         Γ ⊢ u ≡ u' →
         Γ ⊢ ghrefl A u ≡ ghrefl A' u' *)

  | cong_if :
      ∀ m b P t f b' P' t' f',
      Γ ⊢ b ≡ b' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ t ≡ t' →
      Γ ⊢ f ≡ f' →
      Γ ⊢ tif m b P t f ≡ tif m b' P' t' f'

  | cong_succ :
      ∀ n n',
      Γ ⊢ n ≡ n' →
      Γ ⊢ tsucc n ≡ tsucc n'

  | cong_nat_elim :
      ∀ m n P z s n' P' z' s',
      Γ ⊢ n ≡ n' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ z ≡ z' →
      Γ ⊢ s ≡ s' →
      Γ ⊢ tnat_elim m n P z s ≡ tnat_elim m n' P' z' s'

  | cong_vec :
      ∀ A A' n n',
      Γ ⊢ A ≡ A' →
      Γ ⊢ n ≡ n' →
      Γ ⊢ tvec A n ≡ tvec A' n'

  | cong_vnil :
      ∀ A A',
      Γ ⊢ A ≡ A' →
      Γ ⊢ tvnil A ≡ tvnil A'

  | cong_vcons :
      ∀ a n v a' n' v',
      Γ ⊢ a ≡ a' →
      Γ ⊢ n ≡ n' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ tvcons a n v ≡ tvcons a' n' v'

  | cong_vec_elim :
      ∀ m A n v P z s A' n' v' P' z' s',
      Γ ⊢ A ≡ A' →
      Γ ⊢ n ≡ n' →
      Γ ⊢ v ≡ v' →
      Γ ⊢ P ≡ P' →
      Γ ⊢ z ≡ z' →
      Γ ⊢ s ≡ s' →
      Γ ⊢ tvec_elim m A n v P z s ≡ tvec_elim m A' n' v' P' z' s'

      (* Maybe not needed? *)
  | cong_bot_elim :
      ∀ m A A' p p',
      Γ ⊢ A ≡ A' →
      (* Needed because syntactically we don't know p and p' are irrelevant *)
      Γ ⊢ p ≡ p' →
      Γ ⊢ bot_elim m A p ≡ bot_elim m A' p'

      (** Structural rules **)

  | conv_refl :
      ∀ u,
      Γ ⊢ u ≡ u

  | conv_sym :
      ∀ u v,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ u

  | conv_trans :
      ∀ u v w,
      Γ ⊢ u ≡ v →
      Γ ⊢ v ≡ w →
      Γ ⊢ u ≡ w

      (** Proof irrelevance **)

  | conv_irr :
      ∀ p q,
      cscoping Γ p mProp →
      cscoping Γ q mProp →
      Γ ⊢ p ≡ q

      where "Γ ⊢ u ≡ v" := (conversion Γ u v).

Create HintDb gtt_conv discriminated.

Hint Resolve conv_beta reveal_hide conv_if_true conv_if_false conv_nat_elim_zero
  conv_nat_elim_succ conv_vec_elim_nil conv_vec_elim_cons cong_Prop cong_Pi
  cong_lam cong_app cong_Erased cong_hide cong_reveal cong_Reveal cong_gheq
  cong_if cong_succ cong_nat_elim cong_vec cong_vnil cong_vcons cong_vec_elim
  cong_bot_elim conv_refl
: gtt_conv.

Ltac gconv :=
  unshelve typeclasses eauto with gtt_scope gtt_conv shelvedb ; shelve_unifiable.
