(*** Parametricity ***)

From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST CastRemoval SubstNotations ContextDecl
  CScoping Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory Erasure
  Revival.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

(** Variables and parametricity

  x : A in the context is translated to x : A, xP : AP when A is not a Prop.
  When x : P : Prop then x is translated to only one variable. To keep the
  context regular we will still make use of our flexible contexts.
  Variables are then either odd and regular or even and correspond to
  parametricity.

**)

Definition vreg x := S (x * 2).
Definition vpar x := x * 2.

(** Lifting erasure and revival

  Because erasure and revival produce terms in ⟦ Γ ⟧ε and ⟦ Γ ⟧v respectively
  when we expect ⟦ Γ ⟧p, we need to do some lifting. Thankfully this lifting
  can be done simply by using vreg as a renaming.
  We define handy notations to make it all work.

**)

Definition epm_lift (t : cterm) :=
  vreg ⋅ t.

Definition rpm_lift (t : cterm) :=
  vreg ⋅ t.

Notation "⟦ G | u '⟧pε'":=
  (epm_lift ⟦ G | u ⟧ε) (at level 9, G, u at next level).

Notation "⟦ G | u '⟧pτ'":=
  (epm_lift ⟦ G | u ⟧τ) (at level 9, G, u at next level).

Notation "⟦ G | u '⟧p∅'":=
  (epm_lift ⟦ G | u ⟧∅) (at level 9, G, u at next level).

Notation "⟦ G | u '⟧pv'":=
  (rpm_lift ⟦ G | u ⟧v) (at level 9, G, u at next level).

(** Parametricity translation

  We start by defining useful shorthands.

**)

Definition pKind i :=
  clam cType (cty i) (cEl (cvar 0) ⇒[ cType ] cSort cType i).

Definition pType i :=
  clam cType (cty i) (cEl (cvar 0) ⇒[ cType ] cSort cProp 0).

Definition pProp i :=
  clam cType (cty i) (cSort cProp 0).

(* ∀ (x : A) (x@mp : B x). C *)
Definition pPi mp A B C :=
  cPi cType A (cPi mp (capp (S ⋅ B) (cvar 0)) C).

Definition plam mp A B t :=
  clam cType A (clam mp (capp (S ⋅ B) (cvar 0)) t).

Definition pcastTG Ae AP uv vv vP eP PP te tP :=
  sq_elim
    eP
    (clam cProp (squash (teq Ae uv vv)) (S ⋅ (capp (capp (capp PP vv) vP) te)))
    (clam cType (teq Ae uv vv) (
      capp
        (tJ
          (cvar 0)
          (S ⋅ (clam cType Ae (
            clam cType (teq (S ⋅ Ae) (S ⋅ uv) (cvar 0)) (
              cPi cProp (capp (plus 2 ⋅ AP) (cvar 1)) (
                capp (capp (capp (plus 3 ⋅ PP) (cvar 2)) (cvar 0)) (plus 3 ⋅ te)
              )
            )
          )))
          (S ⋅ (clam cProp (capp AP uv) (S ⋅ tP))))
        (S ⋅ vP)
    )).

Definition pcastP Ae AP uv vv vP eP PP tP :=
  sq_elim
    eP
    (clam cProp (squash (teq Ae uv vv)) (S ⋅ (capp (capp PP vv) vP)))
    (clam cType (teq Ae uv vv) (
      capp
        (tJ
          (cvar 0)
          (S ⋅ (clam cType Ae (
            clam cType (teq (S ⋅ Ae) (S ⋅ uv) (cvar 0)) (
              cPi cProp (capp (plus 2 ⋅ AP) (cvar 1)) (
                capp (capp (plus 3 ⋅ PP) (cvar 2)) (cvar 0)
              )
            )
          )))
          (S ⋅ (clam cProp (capp AP uv) (S ⋅ tP))))
        (S ⋅ vP)
    )).

Reserved Notation "⟦ G | u '⟧p'" (at level 9, G, u at next level).

Equations param_term (Γ : scope) (t : term) : cterm := {
  ⟦ Γ | var x ⟧p :=
    match nth_error Γ x with
    | Some m => cvar (if isProp m then vreg x else vpar x)
    | None => cDummy
    end ;
  ⟦ Γ | Sort m i ⟧p :=
    if isKind m then pKind i
    else if isProp m then pProp i
    else pType i ;
  ⟦ Γ | Pi i j m mx A B ⟧p :=
    let Te := ⟦ Γ | Pi i j m mx A B ⟧pε in
    let Ae := ⟦ Γ | A ⟧pε in
    let Ap := ⟦ Γ | A ⟧p in
    let Bp := ⟦ mx :: Γ | B ⟧p in
    let k := umax m i j in
    match m with
    | mKind =>
      clam cType (capp (pKind k) Te) (
        match mx with
        | mKind => pPi cType (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mType => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mGhost => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (cvar 2))
        | mProp => cPi cProp (S ⋅ Ap) (capp ((up_ren S) ⋅ (close Bp)) (cvar 1))
        end
      )
    | mType =>
      clam cProp (capp (pKind k) Te) (
        match mx with
        | mKind => pPi cType (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mType => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        | mGhost => pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (cvar 2))
        | mProp => cPi cProp (S ⋅ Ap) (capp ((up_ren S) ⋅ (close Bp)) (cvar 1))
        end
      )
    | mGhost =>
      clam cProp (capp (pKind k) Te) (
        if isKind mx then pPi cType (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
        else if isProp mx then cPi cProp (S ⋅ Ap) (capp ((up_ren S) ⋅ (close Bp)) (cvar 1))
        else pPi cProp (S ⋅ Ae) (S ⋅ Ap) (capp ((up_ren (up_ren S)) ⋅ Bp) (capp (cvar 2) (cvar 1)))
      )
    | mProp =>
      if isProp mx then cPi cProp Ap (close Bp)
      else if isKind mx then pPi cType Ae Ap Bp
      else pPi cProp Ae Ap Bp
    end ;
  ⟦ Γ | lam mx A B t ⟧p :=
    if isProp mx then clam cProp ⟦ Γ | A ⟧p (close ⟦ mx :: Γ | t ⟧p)
    else if isKind mx then plam cType ⟦ Γ | A ⟧pε ⟦ Γ | A ⟧p ⟦ mx :: Γ | t ⟧p
    else plam cProp ⟦ Γ | A ⟧pε ⟦ Γ | A ⟧p ⟦ mx :: Γ | t ⟧p ;
  ⟦ Γ | app u v ⟧p :=
    if relm (md Γ v) then capp (capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧pε) ⟦ Γ | v ⟧p
    else if isGhost (md Γ v) then capp (capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧pv) ⟦ Γ | v ⟧p
    else capp ⟦ Γ | u ⟧p ⟦ Γ | v ⟧p
  ;
  ⟦ Γ | Erased A ⟧p :=
    if isKind (md Γ A) then ⟦ Γ | A ⟧p else cDummy ;
  ⟦ Γ | hide t ⟧p :=
    if isType (md Γ t) then ⟦ Γ | t ⟧p else cDummy ;
  ⟦ Γ | reveal t P p ⟧p :=
    if relm (md Γ p) then cDummy
    else capp (capp ⟦ Γ | p ⟧p ⟦ Γ | t ⟧pv) ⟦ Γ | t ⟧p ;
  ⟦ Γ | revealP t p ⟧p :=
    if isKind (md Γ p) then cDummy
    else capp (capp ⟦ Γ | p ⟧p ⟦ Γ | t ⟧pv) ⟦ Γ | t ⟧p ;
  ⟦ Γ | gheq A u v ⟧p := squash (teq ⟦ Γ | A ⟧pε ⟦ Γ | u ⟧pv ⟦ Γ | v ⟧pv) ;
  ⟦ Γ | ghrefl A u ⟧p := sq (trefl ⟦ Γ | A ⟧pε ⟦ Γ | u ⟧pv) ;
  ⟦ Γ | ghcast A u v e P t ⟧p :=
    let eP := ⟦ Γ | e ⟧p in
    let PP := ⟦ Γ | P ⟧p in
    let uv := ⟦ Γ | u ⟧pv in
    let vv := ⟦ Γ | v ⟧pv in
    let vP := ⟦ Γ | v ⟧p in
    let Ae := ⟦ Γ | A ⟧pε in
    let AP := ⟦ Γ | A ⟧p in
    let te := ⟦ Γ | t ⟧pε in
    let tv := ⟦ Γ | t ⟧pv in
    let tP := ⟦ Γ | t ⟧p in
    match md Γ t with
    | mKind => tP (* Not cDummy for technical reasons *)
    | mType => pcastTG Ae AP uv vv vP eP PP te tP
    | mGhost => pcastTG Ae AP uv vv vP eP PP tv tP
    | mProp => pcastP Ae AP uv vv vP eP PP tP
    end ;
  ⟦ Γ | bot ⟧p := cbot ;
  ⟦ Γ | bot_elim m A p ⟧p :=
    if isProp m then cbot_elim cProp ⟦ Γ | A ⟧p ⟦ Γ | p ⟧p
    else if isKind m then cbot_elim cType (capp ⟦ Γ | A ⟧p ⟦ Γ | A ⟧p∅) ⟦ Γ | p ⟧p
    else cbot_elim cProp (capp ⟦ Γ | A ⟧p ⟦ Γ | A ⟧p∅) ⟦ Γ | p ⟧p
}
where "⟦ G | u '⟧p'" := (param_term G u).

Reserved Notation "⟦ G '⟧p'" (at level 9, G at next level).

Equations param_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧p := [] ;
  ⟦ Γ ,, (mx, A) ⟧p :=
    if isProp mx then None :: Some (cProp, ⟦ sc Γ | A ⟧p) :: ⟦ Γ ⟧p
    else if isKind mx then
      Some (cType, capp (S ⋅ ⟦ sc Γ | A ⟧p) (cvar 0)) ::
      Some (cType, ⟦ sc Γ | A ⟧pτ) :: ⟦ Γ ⟧p
    else
      Some (cProp, capp (S ⋅ ⟦ sc Γ | A ⟧p) (cvar 0)) ::
      Some (cType, ⟦ sc Γ | A ⟧pτ) :: ⟦ Γ ⟧p
}
where "⟦ G '⟧p'" := (param_ctx G).

Fixpoint param_sc (Γ : scope) : cscope :=
  match Γ with
  | [] => []
  | m :: Γ =>
    if isProp m then None :: Some cProp :: param_sc Γ
    else if isKind m then Some cType :: Some cType :: param_sc Γ
    else Some cProp :: Some cType :: param_sc Γ
  end.

(** Scope lookups **)

Lemma nth_error_param_vreg :
  ∀ Γ x,
    nth_error (param_sc Γ) (vreg x) =
    option_map (λ m, if isProp m then Some cProp else Some cType) (nth_error Γ x).
Proof.
  intros Γ x.
  induction Γ as [| m Γ ih] in x |- *.
  - destruct x. all: reflexivity.
  - destruct x.
    + cbn. destruct_ifs. all: reflexivity.
    + unfold vreg. simpl "*". remember (S (x * 2)) as y eqn:e.
      cbn. subst. destruct_ifs. all: eapply ih.
Qed.

Lemma nth_error_param_vpar :
  ∀ Γ x,
    nth_error (param_sc Γ) (vpar x) =
    option_map (λ m,
      if isProp m then None
      else if isKind m then Some cType
      else Some cProp
    ) (nth_error Γ x).
Proof.
  intros Γ x.
  induction Γ as [| m Γ ih] in x |- *.
  - destruct x. all: reflexivity.
  - destruct x.
    + cbn. destruct_ifs. all: reflexivity.
    + cbn. destruct_ifs. all: eapply ih.
Qed.

(** ⟦ Γ ⟧v is a sub-context of ⟦ Γ ⟧p **)

Lemma scoping_rev_sub_param :
  ∀ Γ,
    crscoping (param_sc Γ) vreg (revive_sc Γ).
Proof.
  intros Γ. intros x m e.
  unfold revive_sc in e. rewrite nth_error_map in e.
  rewrite nth_error_param_vreg.
  destruct (nth_error Γ x) as [mx|] eqn:ex. 2: discriminate.
  cbn - [mode_inb] in e. cbn - [mode_inb].
  destruct_ifs. 1: discriminate.
  assumption.
Qed.

Hint Resolve scoping_rev_sub_param : cc_scope.

Lemma typing_rev_sub_param :
  ∀ Γ,
    crtyping ⟦ Γ ⟧p vreg ⟦ Γ ⟧v.
Proof.
  intros Γ. intros x m A e.
  assert (h : nth_error ⟦ Γ ⟧p (vreg x) = Some (Some (m, vreg ⋅ A))).
  { induction Γ as [| [my B] Γ ih] in x, m, A, e |- *.
    1:{ destruct x. all: discriminate. }
    destruct x.
    - cbn - [mode_inb] in e.
      destruct (isProp my) eqn:ey. 1: discriminate.
      noconf e. cbn. rewrite ey.
      destruct_if e1. all: reflexivity.
    - cbn - [mode_inb] in e.
      unfold vreg. simpl "*". remember (S (x * 2)) as z eqn:ez.
      cbn - [mode_inb]. subst.
      destruct_if ey.
      + eapply ih. assumption.
      + destruct_if e1.
        * eapply ih. assumption.
        * eapply ih. assumption.
  }
  eexists. split.
  - eassumption.
  - ssimpl. unfold vreg. cbn. ssimpl. eapply extRen_cterm.
    intro. ssimpl. lia.
Qed.

(** ⟦ Γ ⟧ε is a sub-context of ⟦ Γ ⟧p **)

Lemma crscoping_comp :
  ∀ Γ Δ Ξ ρ δ,
    crscoping Γ ρ Δ →
    crscoping Δ δ Ξ →
    crscoping Γ (δ >> ρ) Ξ.
Proof.
  intros Γ Δ Ξ ρ δ hρ hδ.
  intros x m e.
  unfold_funcomp. eapply hρ. eapply hδ. assumption.
Qed.

Lemma scoping_er_sub_param :
  ∀ Γ,
    crscoping (param_sc Γ) vreg (erase_sc Γ).
Proof.
  intros Γ.
  pose proof (scoping_sub_rev Γ) as lem.
  eapply crscoping_comp in lem. 2: eapply scoping_rev_sub_param.
  eapply crscoping_morphism. all: eauto.
  intros x. reflexivity.
Qed.

Hint Resolve scoping_er_sub_param : cc_scope.

Lemma crtyping_comp :
  ∀ Γ Δ Ξ ρ δ,
    crtyping Γ ρ Δ →
    crtyping Δ δ Ξ →
    crtyping Γ (δ >> ρ) Ξ.
Proof.
  intros Γ Δ Ξ ρ δ hρ hδ.
  intros x m A e.
  eapply hδ in e as [B [e eB]].
  eapply hρ in e as [C [e eC]].
  eexists. split.
  - eassumption.
  - eapply (f_equal (λ A, ρ ⋅ A)) in eB.
    revert eB eC. ssimpl. intros eB eC.
    rewrite eB. assumption.
Qed.

Lemma typing_er_sub_param :
  ∀ Γ,
    crtyping ⟦ Γ ⟧p vreg ⟦ Γ ⟧ε.
Proof.
  intros Γ.
  pose proof (typing_sub_rev Γ) as lem.
  eapply crtyping_comp in lem. 2: eapply typing_rev_sub_param.
  eapply crtyping_morphism. all: eauto.
  intros x. reflexivity.
Qed.

(** Parametricity preserves scoping **)

Lemma scoping_epm_lift :
  ∀ Γ Γ' t,
    ccscoping (erase_sc Γ) t cType →
    Γ' = param_sc Γ →
    ccscoping Γ' (epm_lift t) cType.
Proof.
  intros Γ Γ' t h ->.
  eapply cscoping_ren.
  - eapply scoping_er_sub_param.
  - assumption.
Qed.

(* Hint Resolve scoping_epm_lift | 1000 : cc_scope. *)

Lemma pscoping_erase_term :
  ∀ Γ Γ' t,
    Γ' = param_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧pε cType.
Proof.
  intros Γ Γ' t ->.
  eapply scoping_epm_lift.
  - eapply erase_scoping_strong.
  - reflexivity.
Qed.

Hint Resolve pscoping_erase_term : cc_scope.

Lemma pscoping_erase_type :
  ∀ Γ Γ' t,
    Γ' = param_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧pτ cType.
Proof.
  intros Γ Γ' t ->.
  eapply scoping_epm_lift.
  - constructor. eapply erase_scoping_strong.
  - reflexivity.
Qed.

Hint Resolve pscoping_erase_type : cc_scope.

Lemma pscoping_erase_err :
  ∀ Γ Γ' t,
    Γ' = param_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧p∅ cType.
Proof.
  intros Γ Γ' t ->.
  eapply scoping_epm_lift.
  - constructor. eapply erase_scoping_strong.
  - reflexivity.
Qed.

Hint Resolve pscoping_erase_err : cc_scope.

Lemma scoping_rpm_lift :
  ∀ Γ Γ' t,
    ccscoping (revive_sc Γ) t cType →
    Γ' = param_sc Γ →
    ccscoping Γ' (rpm_lift t) cType.
Proof.
  intros Γ Γ' t h ->.
  eapply cscoping_ren.
  - eapply scoping_rev_sub_param.
  - assumption.
Qed.

(* Hint Resolve scoping_rpm_lift | 1000 : cc_scope. *)

Lemma pscoping_revive :
  ∀ Γ Γ' t,
    scoping Γ t mGhost →
    Γ' = param_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧pv cType.
Proof.
  intros Γ Γ' t h ->.
  eapply scoping_rpm_lift.
  - eapply revive_scoping. 2: eassumption. reflexivity.
  - reflexivity.
Qed.

Hint Resolve pscoping_revive : cc_scope.

Lemma erase_scoping_strong_eq :
  ∀ Γ Γ' t,
    Γ' = erase_sc Γ →
    ccscoping Γ' ⟦ Γ | t ⟧ε cType.
Proof.
  intros Γ ? t ->.
  eapply erase_scoping_strong.
Qed.

Hint Resolve erase_scoping_strong_eq : cc_scope.
Hint Resolve revive_scoping : cc_scope.
Hint Resolve cscoping_ren : cc_scope.
Hint Resolve crscoping_S : cc_scope.
Hint Resolve crscoping_plus : cc_scope.

Lemma pPi_scoping :
  ∀ Γ mx A B C,
    ccscoping Γ A cType →
    ccscoping Γ B cType →
    ccscoping (Some mx :: Some cType :: Γ) C cType →
    ccscoping Γ (pPi mx A B C) cType.
Proof.
  intros Γ mx A B C hA hB hC.
  unshelve eauto with cc_scope shelvedb ; shelve_unifiable.
  constructor. reflexivity.
Qed.

Hint Resolve pPi_scoping : cc_scope.

(* So that they're not unfolded too eagerly *)
Opaque epm_lift rpm_lift.

Lemma param_scoping :
  ∀ Γ t m,
    scoping Γ t m →
    ccscoping (param_sc Γ) ⟦ Γ | t ⟧p (if isKind m then cType else cProp).
Proof.
  intros Γ t m h.
  induction h.
  all: try solve [ cbn ; eauto with cc_scope ].
  all: try solve [ cbn ; destruct_ifs ; eauto with cc_scope ].
  - cbn. rewrite H. destruct_if e.
    + mode_eqs. cbn. constructor.
      rewrite nth_error_param_vreg. rewrite H. reflexivity.
    + constructor. rewrite nth_error_param_vpar. rewrite H.
      cbn. rewrite e. destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    (* For debug *)
    (* remember m as m' eqn:em. remember mx as mx' eqn:emx.
    destruct m', mx'. all: cbn in *. *)
    (* End debug *)
    destruct m, mx. all: cbn in *.
    all: try solve [ typeclasses eauto 50 with cc_scope ].
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      1:{
        eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      }
      eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        all: reflexivity.
      * eapply crscoping_shift. eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      * eapply scoping_epm_lift. 2: reflexivity.
        unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
        reflexivity.
      * eapply crscoping_shift. eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
  - cbn - [mode_inb] in *. destruct_ifs. all: mode_eqs. all: cbn in *.
    all: try solve [ typeclasses eauto 50 with cc_scope ].
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: reflexivity.
  - cbn - [mode_inb] in *.
    erewrite scoping_md. 2: eassumption.
    destruct_ifs. all: mode_eqs.
    all: try solve [ typeclasses eauto 50 with cc_scope ].
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      reflexivity.
  - cbn - [mode_inb] in *.
    erewrite scoping_md. 2: eassumption.
    cbn. assumption.
  - cbn - [mode_inb] in *.
    erewrite scoping_md. 2: eassumption.
    destruct_ifs. all: mode_eqs. all: try intuition discriminate.
    1:{ destruct m. all: intuition discriminate. }
    unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
    reflexivity.
  - cbn - [mode_inb] in *.
    unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
    all: reflexivity.
  - cbn - [mode_inb] in *.
    erewrite scoping_md. 2: eassumption.
    destruct m. 1: contradiction.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      all: repeat try eapply crscoping_shift.
      all: eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      all: repeat try eapply crscoping_shift.
      all: eauto with cc_scope.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      all: try reflexivity.
      all: repeat try eapply crscoping_shift.
      all: eauto with cc_scope.
  - cbn - [mode_inb] in *.
    destruct_ifs. all: mode_eqs. all: try discriminate.
    all: try solve [ typeclasses eauto 50 with cc_scope ].
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      reflexivity.
    + unshelve typeclasses eauto 50 with cc_scope shelvedb ; shelve_unifiable.
      reflexivity.
Qed.

(** Parametricity commutes with renaming

  For this we define pren ρ which is basically the following function:
  pren ρ (2 * n) = 2 * (ρ n)
  pren ρ (2 * n + 1) = 2 * (ρ n) + 1

**)

Definition pren (ρ : nat → nat) :=
  λ n, PeanoNat.Nat.b2n (Nat.odd n) + 2 * ρ (Nat.div2 n).

Lemma pren_even :
  ∀ ρ n,
    pren ρ (n * 2) = (ρ n) * 2.
Proof.
  intros ρ n.
  unfold pren.
  replace (n * 2) with (2 * n) by lia.
  rewrite PeanoNat.Nat.div2_double.
  rewrite PeanoNat.Nat.odd_mul. cbn. lia.
Qed.

Lemma pren_odd :
  ∀ ρ n,
    pren ρ (S (n * 2)) = S ((ρ n) * 2).
Proof.
  intros ρ n.
  unfold pren.
  replace (n * 2) with (2 * n) by lia.
  rewrite PeanoNat.Nat.div2_succ_double.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_mul. cbn. lia.
Qed.

Lemma div2_SS :
  ∀ n, Nat.div2 (S (S n)) = S (Nat.div2 n).
Proof.
  intro n.
  destruct (PeanoNat.Nat.Even_Odd_dec n) as [h | h].
  - rewrite <- PeanoNat.Nat.Odd_div2.
    2:{ apply PeanoNat.Nat.Odd_succ. assumption. }
    rewrite <- PeanoNat.Nat.Even_div2. 2: assumption.
    reflexivity.
  - rewrite <- PeanoNat.Nat.Even_div2.
    2:{ apply PeanoNat.Nat.Even_succ. assumption. }
    rewrite <- PeanoNat.Nat.Odd_div2. 2: assumption.
    reflexivity.
Qed.

Lemma pren_SS :
  ∀ ρ n, pren ρ (S (S n)) = pren (S >> ρ) n.
Proof.
  intros ρ n.
  unfold pren.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_succ.
  rewrite div2_SS. reflexivity.
Qed.

Lemma pren_comp_S :
  ∀ ρ n, pren (ρ >> S) n = S (S (pren ρ n)).
Proof.
  intros ρ n.
  unfold pren. ssimpl. lia.
Qed.

Transparent epm_lift rpm_lift.

Lemma pren_epm_lift :
  ∀ ρ t,
    pren ρ ⋅ epm_lift t = epm_lift (ρ ⋅ t).
Proof.
  intros ρ t.
  unfold epm_lift. ssimpl.
  eapply extRen_cterm. intro x.
  unfold vreg, pren. ssimpl.
  replace (x * 2) with (2 * x) by lia.
  rewrite PeanoNat.Nat.div2_succ_double.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_mul. cbn. lia.
Qed.

Lemma pren_rpm_lift :
  ∀ ρ t,
    pren ρ ⋅ rpm_lift t = rpm_lift (ρ ⋅ t).
Proof.
  intros ρ t.
  apply pren_epm_lift.
Qed.

Opaque epm_lift rpm_lift.

Lemma param_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    ⟦ Γ | ρ ⋅ t ⟧p = (pren ρ) ⋅ ⟦ Δ | t ⟧p.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  - cbn - [mode_inb].
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e as e'. rewrite e'.
      destruct_if e1.
      * unfold vreg, pren. ssimpl. f_equal.
        replace (n * 2) with (2 * n) by lia.
        rewrite PeanoNat.Nat.div2_succ_double.
        rewrite PeanoNat.Nat.odd_succ.
        rewrite PeanoNat.Nat.even_mul. cbn. lia.
      * unfold pren, vpar. ssimpl. f_equal.
        replace (n * 2) with (2 * n) by lia.
        rewrite PeanoNat.Nat.div2_double.
        rewrite PeanoNat.Nat.odd_mul. cbn. lia.
    + eapply hcρ in e as e'. rewrite e'. reflexivity.
  - cbn - [mode_inb]. destruct_ifs. all: reflexivity.
  - cbn - [mode_inb]. unfold pPi.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. eassumption. }
    erewrite ?erase_ren, ?revive_ren.
    2-5: eauto using rscoping_upren, rscoping_comp_upren.
    rewrite ?pren_epm_lift, ?pren_rpm_lift.
    destruct m, m0. all: cbn in *. (* all: try reflexivity. *)
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ ssimpl. reflexivity. }
      f_equal.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ ssimpl. reflexivity. }
      f_equal.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. all: f_equal.
      * ssimpl. reflexivity.
      * ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
        ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{
        rewrite pren_epm_lift. cbn. f_equal.
        unfold close. ssimpl. reflexivity.
      }
      1:{ ssimpl. reflexivity. }
      f_equal.
      ssimpl. eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. cbn. reflexivity. }
      1:{ ssimpl. reflexivity. }
      ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. reflexivity. }
      1:{ ssimpl. reflexivity. }
      ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + f_equal. all: f_equal.
      1:{ rewrite pren_epm_lift. reflexivity. }
      1:{ ssimpl. reflexivity. }
      ssimpl. eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + f_equal. unfold close. ssimpl.
      eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. eassumption. }
    unfold plam.
    erewrite erase_ren. 2,3: eassumption.
    destruct_ifs. all: mode_eqs.
    + cbn. unfold close. ssimpl. f_equal.
      eapply ext_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. cbn. reflexivity.
    + cbn. rewrite pren_epm_lift. ssimpl. f_equal. f_equal.
      eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
    + cbn. rewrite pren_epm_lift. ssimpl. f_equal. f_equal.
      eapply extRen_cterm. intros [| []]. all: cbn. 1,2: reflexivity.
      ssimpl. rewrite pren_SS. ssimpl. rewrite pren_comp_S. reflexivity.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite erase_ren. 2,3: eassumption.
    erewrite revive_ren. 2,3: eassumption.
    rewrite <- pren_epm_lift. rewrite <- pren_rpm_lift.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. 1: reflexivity.
    cbn. erewrite IHt3. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2,3: eassumption.
    rewrite !pren_rpm_lift. reflexivity.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. 1: reflexivity.
    cbn. erewrite IHt2. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2,3: eassumption.
    rewrite !pren_rpm_lift. reflexivity.
  - cbn - [mode_inb].
    erewrite ?erase_ren, ?revive_ren. 2-7: eassumption.
    rewrite ?pren_epm_lift. reflexivity.
  - cbn - [mode_inb].
    erewrite ?erase_ren, ?revive_ren. 2-5: eassumption.
    rewrite ?pren_epm_lift. reflexivity.
  - cbn - [mode_inb].
    erewrite md_ren. 2,3: eassumption.
    erewrite ?erase_ren, ?revive_ren. 2-11: eassumption.
    destruct (md _ _).
    + eauto.
    + unfold pcastTG. cbn.
      erewrite IHt1. 2,3: eassumption.
      erewrite IHt3. 2,3: eassumption.
      erewrite IHt4. 2,3: eassumption.
      erewrite IHt5. 2,3: eassumption.
      erewrite IHt6. 2,3: eassumption.
      rewrite ?pren_epm_lift, ?pren_rpm_lift.
      f_equal. all: f_equal. all: f_equal.
      2:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      2:{ ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      3:{ ssimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      2:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. f_equal.
      ssimpl. reflexivity.
    + unfold pcastTG. cbn.
      erewrite IHt1. 2,3: eassumption.
      erewrite IHt3. 2,3: eassumption.
      erewrite IHt4. 2,3: eassumption.
      erewrite IHt5. 2,3: eassumption.
      erewrite IHt6. 2,3: eassumption.
      rewrite ?pren_epm_lift, ?pren_rpm_lift.
      f_equal. all: f_equal. all: f_equal.
      2:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      2:{ ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      3:{ ssimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      2:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      f_equal. f_equal.
      ssimpl. reflexivity.
    + unfold pcastP. cbn.
      erewrite IHt1. 2,3: eassumption.
      erewrite IHt3. 2,3: eassumption.
      erewrite IHt4. 2,3: eassumption.
      erewrite IHt5. 2,3: eassumption.
      erewrite IHt6. 2,3: eassumption.
      rewrite ?pren_epm_lift, ?pren_rpm_lift.
      f_equal. all: f_equal. all: f_equal.
      2:{ ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      3:{ ssimpl. reflexivity. }
      all: f_equal.
      3:{ ssimpl. reflexivity. }
      3:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ rewrite <- pren_epm_lift. ssimpl. reflexivity. }
      1:{ rewrite <- pren_rpm_lift. ssimpl. reflexivity. }
      all: f_equal.
      1:{ ssimpl. reflexivity. }
      f_equal.
      ssimpl. reflexivity.
  - cbn - [mode_inb]. reflexivity.
  - cbn - [mode_inb]. destruct_ifs. all: mode_eqs.
    + cbn. f_equal. all: eauto.
    + cbn. f_equal. 1: f_equal. all: eauto.
      erewrite erase_ren. 2,3: eassumption.
      rewrite pren_epm_lift. reflexivity.
    + cbn. f_equal. 1: f_equal. all: eauto.
      erewrite erase_ren. 2,3: eassumption.
      rewrite pren_epm_lift. reflexivity.
Qed.

(** Parametricity commutes with substitution

  As for revival we need to craft a new substitution that gets the scopes as
  input in order to determine the mode of the various variables.

**)

Definition psubst Δ Γ σ n :=
  let p := Nat.div2 n in
  match nth_error Δ p with
  | Some m =>
    if relm m then (
      if Nat.odd n then ⟦ Γ | σ p ⟧pε
      else ⟦ Γ | σ p ⟧p
    )
    else if isGhost m then (
      if Nat.odd n then ⟦ Γ | σ p ⟧pv
      else ⟦ Γ | σ p ⟧p
    )
    else (
      if Nat.odd n then ⟦ Γ | σ p ⟧p
      else cDummy
    )
  | None => cDummy
  end.

Lemma div2_vreg :
  ∀ n, Nat.div2 (vreg n) = n.
Proof.
  intros n.
  unfold vreg. replace (n * 2) with (2 * n) by lia.
  apply PeanoNat.Nat.div2_succ_double.
Qed.

Lemma div2_vpar :
  ∀ n, Nat.div2 (vpar n) = n.
Proof.
  intros n.
  unfold vpar. replace (n * 2) with (2 * n) by lia.
  apply PeanoNat.Nat.div2_double.
Qed.

Lemma odd_vreg :
  ∀ n, Nat.odd (vreg n) = true.
Proof.
  intros n.
  unfold vreg. replace (n * 2) with (2 * n) by lia.
  rewrite PeanoNat.Nat.odd_succ.
  rewrite PeanoNat.Nat.even_mul. reflexivity.
Qed.

Lemma odd_vpar :
  ∀ n, Nat.odd (vpar n) = false.
Proof.
  intros n.
  unfold vpar. replace (n * 2) with (2 * n) by lia.
  rewrite PeanoNat.Nat.odd_mul. reflexivity.
Qed.

Transparent epm_lift rpm_lift.

Lemma psubst_rpm_lift :
  ∀ Γ Δ σ t,
    (* sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ → *)
    (rpm_lift t) <[ psubst Δ Γ σ ] = rpm_lift (t <[ rev_subst Δ Γ σ ]).
Proof.
  intros Γ Δ σ t (* hσ hcσ *).
  unfold rpm_lift. ssimpl.
  eapply ext_cterm_scoped with (Γ := revive_sc Δ) (m := cType).
  1: admit.
  intros x hx.
  ssimpl. unfold psubst. rewrite div2_vreg.
  unfold rev_subst. unfold ghv.
  unfold inscope in hx. unfold revive_sc in hx.
  rewrite nth_error_map in hx.
  destruct (nth_error Δ x) eqn:e. 2: discriminate.
  cbn in hx. destruct (isProp m) eqn:e1. 1: discriminate.
  rewrite odd_vreg.
  destruct_ifs. all: mode_eqs. all: try discriminate.
  all: try reflexivity.
  destruct m. all: discriminate.
Abort.

Opaque epm_lift rpm_lift.

Lemma param_subst :
  ∀ Γ Δ σ t,
    sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ →
    ⟦ Γ | t <[ σ ] ⟧p = ⟦ Δ | t ⟧p <[ psubst Δ Γ σ ].
Proof.
  intros Γ Δ σ t hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  - cbn. destruct (nth_error Δ n) eqn:e.
    + destruct_if e1.
      * mode_eqs. cbn. unfold psubst. rewrite div2_vreg.
        rewrite e. cbn. rewrite odd_vreg. reflexivity.
      * cbn. unfold psubst. rewrite div2_vpar. rewrite e.
        rewrite odd_vpar.
        destruct_ifs. all: try reflexivity.
        destruct m. all: discriminate.
    + eapply hcσ in e as e'. destruct e' as [k [e1 e2]].
      rewrite e1. cbn. rewrite e2. reflexivity.
  - cbn - [mode_inb]. destruct_ifs. all: reflexivity.
  - admit.
  - admit.
  - admit.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt. 2,3: eassumption.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt. 2,3: eassumption.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    destruct_ifs. 1: reflexivity.
    cbn. f_equal. f_equal.
    (* Need similar rpm_lift vs rev_subst commutation *)
    admit.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    destruct_ifs. 1: reflexivity.
    cbn. admit.
  - cbn - [mode_inb].
    erewrite !revive_subst. 2-5: eassumption.
    erewrite !erase_subst. 2,3: eassumption.
    admit.
  - cbn - [mode_inb].
    erewrite erase_subst. 2,3: eassumption.
    erewrite revive_subst. 2,3: eassumption.
    admit.
  - admit.
  - cbn. reflexivity.
  - cbn.
    erewrite erase_subst. 2,3: eassumption.
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    destruct_ifs. all: try reflexivity.
    + admit.
    + admit.
Abort.

(** Parametricity preserves typing **)

Definition ptype Γ t A :=
  if relm (mdc Γ t) then capp ⟦ sc Γ | A ⟧p ⟦ sc Γ | t ⟧ε
  else if isGhost (mdc Γ t) then capp ⟦ sc Γ | A ⟧p ⟦ sc Γ | t ⟧v
  else ⟦ sc Γ | A ⟧p.

Theorem param_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    ⟦ Γ ⟧v ⊢ᶜ ⟦ sc Γ | t ⟧p : ptype Γ t A.
Proof.
  intros Γ t A h.
  induction h.
Abort.
