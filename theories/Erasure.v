From Coq Require Import Utf8 List Bool Lia.
From Equations Require Import Equations.
From GhostTT.autosubst Require Import CCAST GAST core unscoped.
From GhostTT Require Import Util BasicAST SubstNotations ContextDecl CScoping
  Scoping CTyping TermMode Typing BasicMetaTheory CCMetaTheory.
From Coq Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.
Import CombineNotations.

Set Default Goal Selector "!".
Set Equations Transparent.

Definition cDummy := ctt.

(* TODO MOVE to utils *)
Section Inb.

  Context {A} (eqb : A → A → bool).

  Definition inb (a : A) (l : list A) :=
    existsb (eqb a) l.

  Definition inclb (l l' : list A) : bool :=
    forallb (λ x, inb x l') l.

End Inb.

(* TODO MOVE *)
Definition mode_eqb (m m' : mode) : bool :=
  match m, m' with
  | mProp, mProp
  | mGhost, mGhost
  | mType, mType
  | mKind, mKind => true
  | _,_ => false
  end.

Definition isProp m := mode_eqb m mProp.
Definition isGhost m := mode_eqb m mGhost.

Definition mode_inb := inb mode_eqb.
(* Definition mode_inclb := inclb mode_eqb. *)

Notation relm m :=
  (mode_inb m [ mType ; mKind ]).

(* TODO MOVE *)

Ltac autosubst_unfold :=
  unfold Ren_cterm, upRen_cterm_cterm, Subst_cterm, VarInstance_cterm,
    upRen_cterm_cterm.

Ltac resubst :=
  rewrite ?renRen_cterm, ?renSubst_cterm, ?substRen_cterm, ?substSubst_cterm.

Ltac ssimpl :=
  asimpl ;
  autosubst_unfold ;
  asimpl ;
  repeat unfold_funcomp ;
  resubst ;
  asimpl ;
  repeat unfold_funcomp.

(** Test whether a variable is defined and relevant **)

Definition relv (Γ : scope) x :=
  match nth_error Γ x with
  | Some m => relm m
  | None => false
  end.

Reserved Notation "⟦ G | u '⟧ε'" (at level 9, G, u at next level).
Reserved Notation "⟦ G | u '⟧τ'" (at level 9, G, u at next level).
Reserved Notation "⟦ G | u '⟧∅'" (at level 9, G, u at next level).

Equations erase_term (Γ : scope) (t : term) : cterm := {
  ⟦ Γ | var x ⟧ε := if relv Γ x then cvar x else cDummy ;
  ⟦ Γ | Sort m i ⟧ε :=
    if isProp m
    then ctyval cunit ctt (* In the paper, ⊤/* *)
    else ctyval (cty i) ctyerr ;
  ⟦ Γ | Pi i j m mx A B ⟧ε :=
    if relm mx && negb (isProp m)
    then ctyval (cPi cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | B ⟧τ) (clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | B ⟧∅)
    else if isGhost m && isGhost mx
    then ctyval (⟦ Γ | A ⟧τ ⇒[ cType ] (close ⟦ mx :: Γ | B ⟧τ)) (clam cType ⟦ Γ | A ⟧τ (ignore ⟦ mx :: Γ | B ⟧∅))
    else if isProp m
    then ctt
    else close ⟦ mx :: Γ | B ⟧ε ;
  ⟦ Γ | lam mx A B t ⟧ε :=
    if relm (md (mx :: Γ) t)
    then
      if relm mx
      then clam cType ⟦ Γ | A ⟧τ ⟦ mx :: Γ | t ⟧ε
      else close ⟦ mx :: Γ | t ⟧ε
    else cDummy ;
  ⟦ Γ | app u v ⟧ε :=
    if relm (md Γ u)
    then
      if relm (md Γ v)
      then capp ⟦ Γ | u ⟧ε ⟦ Γ | v ⟧ε
      else ⟦ Γ | u ⟧ε
    else cDummy ;
  ⟦ Γ | Erased A ⟧ε := ⟦ Γ | A ⟧ε ;
  ⟦ Γ | revealP t P ⟧ε := ctt ;
  ⟦ Γ | gheq A u v ⟧ε := ctt ;
  ⟦ Γ | ghcast e P t ⟧ε := ⟦ Γ | t ⟧ε ;
  ⟦ Γ | bot ⟧ε := ctt ;
  ⟦ Γ | bot_elim m A p ⟧ε := if relm m then ⟦ Γ | A ⟧∅ else cDummy ;
  ⟦ _ | _ ⟧ε := cDummy
}
where "⟦ G | u '⟧ε'" := (erase_term G u)
where "⟦ G | u '⟧τ'" := (cEl ⟦ G | u ⟧ε)
where "⟦ G | u '⟧∅'" := (cErr ⟦ G | u ⟧ε).

Reserved Notation "⟦ G '⟧ε'" (at level 9, G at next level).

Equations erase_ctx (Γ : context) : ccontext := {
  ⟦ [] ⟧ε := [] ;
  ⟦ Γ ,, (mx, A) ⟧ε :=
    if relm mx
    then Some (cType, ⟦ sc Γ | A ⟧τ) :: ⟦ Γ ⟧ε
    else None :: ⟦ Γ ⟧ε
}
where "⟦ G '⟧ε'" := (erase_ctx G).

Definition erase_sc (Γ : scope) : cscope :=
  map (λ m, if relm m then Some cType else None) Γ.

(* TODO MOVE *)

Ltac destruct_if e :=
  lazymatch goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct b eqn: e
  end.

Ltac destruct_if' :=
  let e := fresh "e" in
  destruct_if e.

Ltac destruct_ifs :=
  repeat destruct_if'.

Ltac destruct_bool b :=
  lazymatch b with
  | negb ?b => destruct_bool b
  | ?b && ?c => destruct_bool b
  | _ => let e := fresh "e" in destruct b eqn: e
  end.

Ltac d_if :=
  lazymatch goal with
  | |- context [ if ?b then _ else _ ] =>
    destruct_bool b
  end.

(** Erasure of irrelevant terms is cDummy **)

Lemma erase_irr :
  ∀ Γ t,
    relm (md Γ t) = false →
    ⟦ Γ | t ⟧ε = cDummy.
Proof.
  intros Γ t hm.
  induction t in Γ, hm |- *.
  all: try reflexivity.
  all: try discriminate hm.
  - cbn - [mode_inb] in *. unfold relv.
    destruct (nth_error _ _) eqn:e. 2: reflexivity.
    erewrite nth_error_nth in hm. 2: eassumption.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *.
    rewrite hm. cbn. reflexivity.
  - cbn - [mode_inb] in *.
    rewrite hm. reflexivity.
  - cbn - [mode_inb] in *. eauto.
  - cbn - [mode_inb] in *. rewrite hm. reflexivity.
Qed.

(** Erasure of context and of variables **)

Lemma erase_sc_var :
  ∀ Γ x m,
    nth_error Γ x = Some m →
    relm m = true →
    nth_error (erase_sc Γ) x = Some (Some cType).
Proof.
  intros Γ x m e hr.
  unfold erase_sc. rewrite nth_error_map.
  rewrite e. cbn - [mode_inb]. rewrite hr. reflexivity.
Qed.

Lemma erase_ctx_var :
  ∀ Γ x m A,
    nth_error Γ x = Some (m, A) →
    relm m = true →
    nth_error ⟦ Γ ⟧ε x = Some (Some (cType, ⟦ skipn (S x) (sc Γ) | A ⟧τ)).
Proof.
  intros Γ x m A e hr.
  induction Γ as [| [my B] Γ ih ] in x, m, A, e, hr |- *.
  1: destruct x ; discriminate.
  destruct x.
  - cbn in e. noconf e.
    cbn - [mode_inb]. rewrite hr. reflexivity.
  - cbn in e. cbn - [mode_inb skipn]. destruct (mode_inb my _) eqn:ey.
    + erewrite ih. 2,3: eauto. reflexivity.
    + cbn - [mode_inb skipn]. erewrite ih. 2,3: eauto. reflexivity.
Qed.

Definition rscoping_comp (Γ : scope) ρ (Δ : scope) :=
  ∀ x,
    nth_error Δ x = None →
    nth_error Γ (ρ x) = None.

(* TODO MOVE *)
Notation "#| l |" := (length l).

Lemma nth_error_app_r :
  ∀ A (l l' : list A) n,
    nth_error (l ++ l') (#|l| + n) = nth_error l' n.
Proof.
  intros A l l' n.
  induction l as [| a l ih] in l', n |- *.
  - reflexivity.
  - cbn. apply ih.
Qed.

Lemma rscoping_weak :
  ∀ Γ Δ,
    rscoping (Δ ++ Γ) (plus #|Δ|) Γ.
Proof.
  intros Γ Δ. intros n m e.
  rewrite nth_error_app_r. assumption.
Qed.

Lemma rscoping_upren :
  ∀ Γ Δ m ρ,
    rscoping Γ ρ Δ →
    rscoping (m :: Γ) (up_ren ρ) (m :: Δ).
Proof.
  intros Γ Δ m ρ h. intros x mx e.
  destruct x.
  - cbn in *. assumption.
  - cbn in *. apply h. assumption.
Qed.

Lemma rscoping_comp_weak :
  ∀ Γ Δ,
    rscoping_comp (Δ ++ Γ) (plus #|Δ|) Γ.
Proof.
  intros Γ Δ. intros n e.
  rewrite nth_error_app_r. assumption.
Qed.

Lemma rscoping_comp_upren :
  ∀ Γ Δ m ρ,
    rscoping_comp Γ ρ Δ →
    rscoping_comp (m :: Γ) (up_ren ρ) (m :: Δ).
Proof.
  intros Γ Δ m ρ h. intros x e.
  destruct x.
  - cbn in *. assumption.
  - cbn in *. apply h. assumption.
Qed.

(** Erasure preserves scoping **)

Lemma erase_scoping :
  ∀ Γ t m,
    relm m = true →
    scoping Γ t m →
    ccscoping (erase_sc Γ) ⟦ Γ | t ⟧ε cType.
Proof.
  intros Γ t m hrm h.
  induction h in hrm |- *.
  all: try solve [ cbn ; eauto with cc_scope ].
  all: try solve [ cbn ; destruct_ifs ; eauto with cc_scope ].
  - cbn. destruct_if e. 2: constructor.
    constructor. eapply erase_sc_var. all: eassumption.
  - cbn - [mode_inb].
    cbn - [mode_inb] in IHh2. fold (erase_sc Γ) in IHh2.
    destruct_ifs.
    all: try solve [ eauto with cc_scope cc_type ].
    + destruct (relm mx) eqn:e'. 2: discriminate.
      auto with cc_scope.
    + destruct m. all: try discriminate.
      destruct mx. all: try discriminate.
      cbn in *.
      unshelve auto with cc_scope shelvedb. 2: eauto.
      ssimpl. eapply cscope_ignore. eauto.
    + destruct (relm mx) eqn:e'. 1: discriminate.
      auto with cc_scope shelvedb.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    rewrite hrm. cbn - [mode_inb] in IHh3.
    destruct_if e. all: eauto with cc_scope.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    rewrite hrm.
    destruct_if e. 2: eauto with cc_scope.
    erewrite scoping_md in e. 2: eassumption.
    eauto with cc_scope.
Qed.

(** Erasure commutes with renaming **)

Lemma nth_nth_error :
  ∀ A (l : list A) (d : A) n,
    nth n l d = match nth_error l n with Some x => x | None => d end.
Proof.
  intros A l d n.
  induction l in n |- *.
  - cbn. destruct n. all: reflexivity.
  - cbn. destruct n.
    + cbn. reflexivity.
    + cbn. apply IHl.
Qed.

Lemma md_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    md Γ (ρ ⋅ t) = md Δ t.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  - cbn. rewrite 2!nth_nth_error.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e. rewrite e. reflexivity.
    + eapply hcρ in e. rewrite e. reflexivity.
  - cbn. eapply IHt3.
    + eapply rscoping_shift. assumption.
    + eapply rscoping_comp_upren. assumption.
  - cbn. erewrite IHt3. 2,3: eauto.
    reflexivity.
Qed.

Lemma erase_ren :
  ∀ Γ Δ ρ t,
    rscoping Γ ρ Δ →
    rscoping_comp Γ ρ Δ →
    ⟦ Γ | ρ ⋅ t ⟧ε = ρ ⋅ ⟦ Δ | t ⟧ε.
Proof.
  intros Γ Δ ρ t hρ hcρ.
  induction t in Γ, Δ, ρ, hρ, hcρ |- *.
  all: try solve [ asimpl ; cbn ; eauto ].
  - cbn - [mode_inb].
    unfold relv.
    destruct (nth_error Δ n) eqn:e.
    + eapply hρ in e. rewrite e.
      destruct (relm m). all: reflexivity.
    + eapply hcρ in e. rewrite e. reflexivity.
  - cbn - [mode_inb].
    destruct_if e. all: eauto.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    destruct_ifs. all: try solve [ eauto ].
    2:{ unfold close. ssimpl. cbn. reflexivity. }
    ssimpl. cbn. ssimpl. unfold nones. ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt3.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    erewrite md_ren.
    2:{ eapply rscoping_upren. eassumption. }
    2:{ eapply rscoping_comp_upren. assumption. }
    destruct_ifs. all: eauto.
    unfold close. ssimpl. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    erewrite IHt2. 2,3: eassumption.
    erewrite md_ren. 2,3: eassumption.
    erewrite md_ren. 2,3: eassumption.
    destruct_ifs. all: eauto.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    destruct_ifs. all: eauto.
Qed.

Lemma nth_skipn :
  ∀ A (l : list A) x y d,
    nth (x + y) l d = nth y (skipn x l) d.
Proof.
  intros A l x y d.
  induction l as [| a l ih] in x, y |- *.
  1:{ destruct x, y. all: reflexivity. }
  destruct x, y. all: cbn. 1,2: reflexivity.
  - apply ih.
  - apply ih.
Qed.

Lemma nth_error_skipn :
  ∀ A (l : list A) x y,
    nth_error l (x + y) = nth_error (skipn x l) y.
Proof.
  intros A l x y.
  induction l as [| a l ih] in x, y |- *.
  1:{ destruct x, y. all: reflexivity. }
  destruct x, y. all: cbn. 1,2: reflexivity.
  - apply ih.
  - apply ih.
Qed.

Lemma nth_app_r :
  ∀ A (l l' : list A) d n,
    nth (#|l| + n) (l ++ l') d = nth n l' d.
Proof.
  intros A l l' d n.
  induction l as [| a l ih] in l', n |- *.
  - reflexivity.
  - cbn. apply ih.
Qed.

(** Erasure commutes with substitution **)

Definition sscoping_comp (Γ : scope) σ (Δ : scope) :=
  ∀ n,
    nth_error Δ n = None →
    ∃ m,
      σ n = var m ∧
      nth_error Γ m = None.

Lemma sscoping_comp_shift :
  ∀ Γ Δ σ mx,
    sscoping_comp Γ σ Δ →
    sscoping_comp (mx :: Γ) (up_term σ) (mx :: Δ).
Proof.
  intros Γ Δ σ mx h. intros n e.
  destruct n.
  - cbn in e. discriminate.
  - cbn in e. cbn.
    eapply h in e as e'. destruct e' as [m [e1 e2]].
    ssimpl. exists (S m). intuition eauto.
    rewrite e1. ssimpl. reflexivity.
Qed.

Lemma rscoping_comp_S :
  ∀ Γ m,
    rscoping_comp (m :: Γ) S Γ.
Proof.
  intros Γ m. intros n e. cbn. assumption.
Qed.

Lemma md_subst :
  ∀ Γ Δ σ t,
    sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ →
    md Γ (t <[ σ ]) = md Δ t.
Proof.
  intros Γ Δ σ t hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  all: try reflexivity.
  all: try solve [ cbn ; eauto ].
  - cbn. rewrite nth_nth_error.
    destruct (nth_error Δ n) eqn:e.
    + clear hcσ. induction hσ as [| σ Δ mx hσ ih hm] in n, m, e |- *.
      1: destruct n ; discriminate.
      destruct n.
      * cbn in *. noconf e.
        erewrite scoping_md. 2: eassumption. reflexivity.
      * cbn in e. eapply ih. assumption.
    + eapply hcσ in e. destruct e as [m [e1 e2]].
      rewrite e1. cbn. rewrite nth_nth_error. rewrite e2. reflexivity.
  - cbn. eapply IHt3.
    + eapply sscoping_shift. assumption.
    + eapply sscoping_comp_shift. assumption.
  - cbn. erewrite IHt3. 2,3: eauto.
    reflexivity.
Qed.

Lemma erase_subst :
  ∀ Γ Δ σ t,
    sscoping Γ σ Δ →
    sscoping_comp Γ σ Δ →
    ⟦ Γ | t <[ σ ] ⟧ε = ⟦ Δ | t ⟧ε <[ σ >> erase_term Γ ].
Proof.
  intros Γ Δ σ t hσ hcσ.
  induction t in Γ, Δ, σ, hσ, hcσ |- *.
  all: try solve [ asimpl ; cbn ; eauto ].
  (* all: try solve [ cbn - [mode_inb] ; destruct_ifs ; ssimpl ; eauto ]. *)
  (* Solves only 1 *)
  - ssimpl. cbn. unfold relv. destruct (nth_error Δ n) eqn:e.
    + destruct (relm m) eqn:em.
      * cbn. ssimpl. reflexivity.
      * cbn. eapply erase_irr. clear hcσ.
        induction hσ as [| σ Δ mx hσ ih hm] in n, m, e, em |- *.
        1: destruct n ; discriminate.
        destruct n.
        -- cbn - [mode_inb] in *.
          erewrite scoping_md. 2: eassumption.
          noconf e. assumption.
        -- cbn in e. eapply ih. all: eassumption.
    + cbn. eapply hcσ in e as e'. destruct e' as [m [e1 e2]].
      rewrite e1. cbn.
      unfold relv. rewrite e2. reflexivity.
  - cbn. destruct_if em.
    + cbn. reflexivity.
    + cbn. reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eauto.
    erewrite IHt2.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ ssimpl. eapply sscoping_comp_shift. assumption. }
    destruct_ifs.
    + cbn. ssimpl. f_equal. all: f_equal. all: f_equal.
      * cbn - [mode_inb]. destruct_if e'. 2: discriminate.
        eapply ext_cterm. intros [].
        -- ssimpl. cbn. reflexivity.
        -- ssimpl. cbn. ssimpl.
          erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. reflexivity.
      * cbn - [mode_inb]. destruct_if e'. 2: discriminate.
        eapply ext_cterm. intros [].
        -- ssimpl. cbn. reflexivity.
        -- ssimpl. cbn. ssimpl.
          erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. reflexivity.
    + destruct m. all: try discriminate.
      destruct m0. all: try discriminate.
      cbn. ssimpl. f_equal. all: f_equal. all: f_equal.
      * cbn.
        eapply ext_cterm. intros [].
        -- ssimpl. reflexivity.
        -- ssimpl. cbn. ssimpl.
          erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. rewrite rinstInst'_cterm.
          eapply ext_cterm. intro x.
          cbn. ssimpl. reflexivity.
      * cbn.
        eapply ext_cterm. intros [].
        -- ssimpl. reflexivity.
        -- ssimpl. cbn. ssimpl.
          erewrite erase_ren.
          2:{ eapply rscoping_S. }
          2:{ eapply rscoping_comp_S. }
          ssimpl. rewrite rinstInst'_cterm.
          eapply ext_cterm. intro x.
          cbn. ssimpl. reflexivity.
    + reflexivity.
    + unfold close. ssimpl. cbn - [mode_inb].
      destruct_if e'. 1: discriminate.
      cbn. eapply ext_cterm. intros [].
      * cbn. reflexivity.
      * cbn. ssimpl. erewrite erase_ren.
        2:{ eapply rscoping_S. }
        2:{ eapply rscoping_comp_S. }
        ssimpl. rewrite instId'_cterm. reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst.
    2:{ eapply sscoping_shift. eassumption. }
    2:{ eapply sscoping_comp_shift. assumption. }
    destruct_ifs.
    + erewrite IHt1. 2,3: eauto.
      erewrite IHt3.
      2:{ eapply sscoping_shift. eassumption. }
      2:{ eapply sscoping_comp_shift. assumption. }
      ssimpl. cbn - [mode_inb].
      rewrite e0. f_equal.
      eapply ext_cterm. intros [].
      * cbn. reflexivity.
      * cbn. ssimpl.
        erewrite erase_ren.
        2:{ eapply rscoping_S. }
        2:{ eapply rscoping_comp_S. }
        ssimpl. reflexivity.
    + unfold close. ssimpl.
      erewrite IHt3.
      2:{ eapply sscoping_shift. eassumption. }
      2:{ eapply sscoping_comp_shift. assumption. }
      ssimpl. cbn - [mode_inb]. rewrite e0. cbn.
      eapply ext_cterm. intros [].
      * reflexivity.
      * cbn. ssimpl.
        erewrite erase_ren.
        2:{ eapply rscoping_S. }
        2:{ eapply rscoping_comp_S. }
        ssimpl. rewrite instId'_cterm. reflexivity.
    + reflexivity.
  - cbn - [mode_inb].
    erewrite md_subst. 2,3: eauto.
    erewrite md_subst. 2,3: eauto.
    erewrite IHt1. 2,3: eauto.
    erewrite IHt2. 2,3: eauto.
    destruct_ifs. all: reflexivity.
  - cbn - [mode_inb].
    erewrite IHt1. 2,3: eassumption.
    destruct_ifs. all: reflexivity.
Qed.

Lemma sscoping_comp_one :
  ∀ Γ u mx,
    sscoping_comp Γ u.. (mx :: Γ).
Proof.
  intros Γ u mx. intros n e.
  destruct n.
  - cbn in e. discriminate.
  - cbn in e. cbn. eexists. intuition eauto.
Qed.

(** Erasure preserves conversion **)

Lemma erase_conv :
  ∀ Γ u v,
    Γ ⊢ u ≡ v →
    ⟦ Γ ⟧ε ⊢ᶜ ⟦ sc Γ | u ⟧ε ≡ ⟦ sc Γ | v ⟧ε.
Proof.
  intros Γ u v h.
  induction h.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    destruct_ifs.
    + eapply cmeta_conv_trans_r. 1: constructor.
      erewrite erase_subst.
      2: eapply sscoping_one. 2: eassumption.
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped.
      1: eapply erase_scoping. 2: eassumption. 1: assumption.
      intros [| x] ex.
      * cbn. reflexivity.
      * cbn. unfold relv. unfold inscope in ex.
        cbn - [mode_inb] in ex.
        rewrite nth_error_map in ex.
        destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
        cbn - [mode_inb] in ex.
        destruct (relm m0). 2: discriminate.
        reflexivity.
    + unfold close. eapply cmeta_conv_trans_r. 1: constructor.
      erewrite erase_subst.
      2: eapply sscoping_one. 2: eassumption.
      2: eapply sscoping_comp_one.
      ssimpl. eapply ext_cterm_scoped.
      1: eapply erase_scoping. 2: eassumption. 1: assumption.
      intros [| x] ex.
      * unfold inscope in ex. cbn - [mode_inb] in ex.
        rewrite e0 in ex. discriminate.
      * cbn. unfold relv. unfold inscope in ex.
        cbn - [mode_inb] in ex.
        rewrite nth_error_map in ex.
        destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
        cbn - [mode_inb] in ex.
        destruct (relm m0). 2: discriminate.
        reflexivity.
    + erewrite erase_irr.
      2:{ erewrite md_subst.
        2:{ eapply sscoping_one. eassumption. }
        2:{ eapply sscoping_comp_one. }
        erewrite scoping_md. 2: eassumption.
        assumption.
      }
      constructor.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    cbn in H2.
    destruct_if e.
    1:{ destruct mp. all: intuition discriminate. }
    constructor.
  - cbn - [mode_inb].
    erewrite scoping_md. 2: eassumption.
    erewrite scoping_md. 2: eassumption.
    cbn.
    (* Ok, here is the problem when using unit and not Prop!
      It needs to be fixed somehow…
    *)
Abort.

(** Erasure preserves typing **)

Lemma erase_typing_El :
  ∀ Γ Γ' A m i,
    Γ' ⊢ᶜ ⟦ Γ | A ⟧ε : ⟦ Γ | Sort m i ⟧τ →
    isProp m = false →
    Γ' ⊢ᶜ ⟦ Γ | A ⟧τ : cSort cType i.
Proof.
  intros Γ Γ' A m i h hm.
  econstructor. cbn in h. rewrite hm in h.
  econstructor.
  - eassumption.
  - constructor.
  - econstructor.
Qed.

Lemma erase_typing_Err :
  ∀ Γ Γ' A m i,
    Γ' ⊢ᶜ ⟦ Γ | A ⟧ε : ⟦ Γ | Sort m i ⟧τ →
    isProp m = false →
    Γ' ⊢ᶜ ⟦ Γ | A ⟧∅ : ⟦ Γ | A ⟧τ.
Proof.
  intros Γ Γ' A m i h hm.
  econstructor. cbn in h. rewrite hm in h.
  econstructor.
  - eassumption.
  - constructor.
  - econstructor.
Qed.

Theorem erase_typing :
  ∀ Γ t A,
    Γ ⊢ t : A →
    relm (mdc Γ t) = true →
    ⟦ Γ ⟧ε ⊢ᶜ ⟦ sc Γ | t ⟧ε : ⟦ sc Γ | A ⟧τ.
Proof.
  intros Γ t A h hm.
  induction h.
  all: try solve [ cbn in hm ; discriminate ].
  (* all: try solve [ cbn ; eauto using erase_typing_El, erase_typing_Err with cc_scope cc_type ]. *)
  - cbn. unfold relv. unfold sc. rewrite nth_error_map.
    rewrite H. cbn - [mode_inb].
    cbn - [mode_inb] in hm.
    erewrite nth_error_nth in hm.
    2:{ unfold sc. erewrite nth_error_map. erewrite H. reflexivity. }
    cbn - [mode_inb] in hm. rewrite hm.
    cbn. eapply ccmeta_conv.
    + econstructor. eapply erase_ctx_var. all: eassumption.
    + cbn - [skipn]. f_equal.
      erewrite erase_ren.
      * reflexivity.
      * intros y my ey. rewrite <- nth_error_skipn in ey. assumption.
      * intros y ey. rewrite <- nth_error_skipn in ey. assumption.
  - cbn. destruct_if e.
    + econstructor.
      * constructor. all: constructor.
      * apply cconv_sym. eapply cconv_trans. 1: econstructor.
        (* Uh oh, unit is not lifted to the upper level, maybe we can do it
          in CC though!
        *)
        admit.
      * repeat econstructor.
    + econstructor.
      * repeat constructor.
      * apply cconv_sym. econstructor.
      * repeat econstructor.
  - cbn - [mode_inb]. cbn - [mode_inb] in IHh1, IHh2.
    destruct_ifs.
    (* repeat (d_if ; cbn - [mode_inb]).
    all: try solve [ destruct m ; discriminate ]. *)
    + (* Redundant case *)
      destruct mx. all: discriminate.
    + destruct (relm mx) eqn:e'. 2: discriminate.
      econstructor.
      * econstructor. all: econstructor.
      (* TODO IH tactic *)
        -- eapply erase_typing_El.
          ++ eapply IHh1. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ destruct mx. all: try discriminate. all: reflexivity.
        -- eapply erase_typing_El. 2: eassumption.
          cbn. rewrite e0. eapply IHh2. erewrite scoping_md. 2: eauto.
          reflexivity.
        -- eapply erase_typing_El.
          ++ eapply IHh1. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ destruct mx. all: try discriminate. all: reflexivity.
        -- eapply erase_typing_Err. 2: eassumption.
          cbn. rewrite e0. eapply IHh2. erewrite scoping_md. 2: eauto.
          reflexivity.
        -- eapply erase_typing_El. 2: eassumption.
          cbn. rewrite e0. eapply IHh2. erewrite scoping_md. 2: eauto.
          reflexivity.
      * apply cconv_sym. constructor.
      * repeat econstructor.
    + destruct m. all: try discriminate.
    + destruct m. all: try discriminate.
      destruct mx. all: try discriminate.
      ssimpl.
      econstructor.
      * econstructor. all: econstructor.
        -- eapply erase_typing_El. 1: eapply IHh1. 2: reflexivity.
          erewrite scoping_md. 2: eassumption. reflexivity.
        -- econstructor. econstructor.
          ++ eapply ctype_ignore.
            eapply IHh2. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ cbn. econstructor.
          ++ eauto with cc_scope cc_type.
        -- eapply erase_typing_El.
          ++ eapply IHh1. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ reflexivity.
        -- econstructor. econstructor.
          ++ eapply ctype_ignore.
            eapply IHh2. erewrite scoping_md. 2: eassumption. reflexivity.
          ++ cbn. constructor.
          ++ eauto with cc_scope cc_type.
        -- unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
          econstructor.
          ++ eapply ctype_ignore. eapply IHh2.
            erewrite scoping_md. 2: eassumption. reflexivity.
          ++ cbn. constructor.
          ++ eauto with cc_scope cc_type.
      * eapply cconv_sym. constructor.
      * eauto with cc_scope cc_type.
    + econstructor.
      * eauto with cc_scope cc_type.
      * eapply cconv_sym. constructor.
      * eauto with cc_scope cc_type.
    + destruct (relm mx) eqn:e'. 1: discriminate.
      econstructor.
      * eapply ctype_close. eapply IHh2.
        erewrite scoping_md. 2: eassumption. reflexivity.
      * cbn. eapply cconv_trans. 1: constructor.
        apply cconv_sym. constructor.
        (* Uh oh: Not the right universe level here either! *)
        admit.
      * eauto with cc_scope cc_type.
  - cbn - [mode_inb]. cbn - [mode_inb] in IHh1, IHh2, IHh3.
    repeat (erewrite scoping_md ; [| eassumption]).
    cbn - [mode_inb] in hm.
    erewrite scoping_md in hm. 2: eassumption.
    rewrite hm.
    erewrite scoping_md in IHh1. 2: eassumption.
    erewrite scoping_md in IHh2. 2: eassumption.
    erewrite scoping_md in IHh3. 2: eassumption.
    rewrite hm in IHh3.
    destruct_ifs. all: try discriminate.
    + destruct (isProp m) eqn:e'. 1: discriminate.
      destruct (isProp mx) eqn:ex.
      1:{ destruct mx ; discriminate. }
      econstructor.
      * econstructor.
        -- eapply erase_typing_El. 2: eassumption.
          econstructor.
          ++ eauto.
          ++ cbn. rewrite e'. constructor.
          ++ eapply erase_typing_El with (m := mKind). 2: reflexivity.
            cbn. rewrite e'.
            econstructor.
            ** eauto with cc_type.
            ** apply cconv_sym. constructor.
            ** eauto with cc_type.
        -- eauto.
        -- eapply erase_typing_El.
          ++ econstructor.
            ** eauto.
            ** cbn. rewrite ex. constructor.
            ** cbn. rewrite ex. eauto with cc_type.
          ++ assumption.
      * apply cconv_sym. constructor.
      * unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
        -- econstructor.
          ++ eauto.
          ++ constructor.
          ++ eauto with cc_type.
        -- eapply erase_typing_El.
          ++ cbn. rewrite ex. eauto.
          ++ assumption.
        -- econstructor.
          ++ eapply erase_typing_El.
            ** cbn. rewrite ex. eauto.
            ** assumption.
          ++ eapply erase_typing_Err.
            ** cbn. rewrite ex. eauto.
            ** assumption.
          ++ eapply erase_typing_El.
            ** cbn. rewrite ex. eauto.
            ** assumption.
    + destruct m. all: discriminate.
    + destruct m. all: discriminate.
    + destruct m. all: discriminate.
    + destruct m. all: discriminate.
    + eapply ccmeta_conv.
      * eapply ctype_close. eauto.
      * cbn. reflexivity.
  - cbn - [mode_inb] in *.
    erewrite scoping_md in hm. 2: eassumption.
    erewrite scoping_md in IHh1. 2: eassumption.
    erewrite scoping_md in IHh2. 2: eassumption.
    repeat (erewrite scoping_md ; [| eassumption]).
    rewrite hm.
    destruct_ifs.
    + destruct (isProp m) eqn:e1. 1:{ destruct m ; discriminate. }
      simpl "&&" in IHh1. cbn match in IHh1.
      eapply ccmeta_conv.
      * unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
        econstructor.
        -- eauto.
        -- constructor.
        -- unshelve eauto with cc_scope cc_type shelvedb ; shelve_unifiable.
          ++ (* Missing info here. *) admit.
          ++ (* Same *) admit.
      * cbn. f_equal. erewrite erase_subst.
        2: eapply sscoping_one. 2: eassumption.
        2: eapply sscoping_comp_one.
        ssimpl.
        eapply ext_cterm_scoped.
        1: eapply erase_scoping. 2: eassumption. 1: reflexivity.
        intros [| x] ex.
        -- cbn. reflexivity.
        -- cbn. unfold relv. unfold inscope in ex.
          cbn - [mode_inb] in ex.
          rewrite nth_error_map in ex.
          destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
          cbn - [mode_inb] in ex.
          destruct (relm m0). 2: discriminate.
          reflexivity.
    + destruct (isProp m) eqn:e1. 1:{ destruct m ; discriminate. }
      simpl "&&" in IHh1. cbn match in IHh1.
      destruct (isGhost m) eqn:e2. 1:{ destruct m ; discriminate. }
      simpl "&&" in IHh1. cbn match in IHh1.
      eapply ccmeta_conv.
      * eauto.
      * f_equal. unfold close.
        erewrite erase_subst.
        2: eapply sscoping_one. 2: eassumption.
        2: eapply sscoping_comp_one.
        ssimpl.
        eapply ext_cterm_scoped.
        1: eapply erase_scoping. 2: eassumption. 1: reflexivity.
        intros [| x] ex.
        -- unfold inscope in ex. cbn - [mode_inb] in ex.
          rewrite e in ex. discriminate.
        -- cbn. unfold relv. unfold inscope in ex.
          cbn - [mode_inb] in ex.
          rewrite nth_error_map in ex.
          destruct (nth_error (sc Γ) x) eqn:e'. 2: discriminate.
          cbn - [mode_inb] in ex.
          destruct (relm m0). 2: discriminate.
          reflexivity.
  - erewrite scoping_md in IHh. 2: eassumption.
    cbn. econstructor.
    + eauto.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb] in hm. erewrite scoping_md in hm. 2: eassumption.
    destruct m. all: discriminate.
  - cbn - [mode_inb]. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb]. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb].
    cbn - [mode_inb] in hm. erewrite scoping_md in hm. 2: eassumption.
    repeat (erewrite scoping_md ; [| eassumption]). cbn.
    cbn - [mode_inb] in IHh6.
    repeat (erewrite scoping_md in IHh6 ; [| eassumption]).
    rewrite hm in IHh6.
    cbn in IHh6. eauto.
  - cbn - [mode_inb]. econstructor.
    + eauto with cc_type.
    + apply cconv_sym. constructor.
    + eauto with cc_type.
  - cbn - [mode_inb]. cbn - [mode_inb] in hm.
    rewrite hm. eapply erase_typing_Err.
    + eapply IHh1. erewrite scoping_md. 2: eassumption.
      reflexivity.
    + destruct m. all: try reflexivity. discriminate.
  - econstructor.
    + eauto.
    + (* TODO conv lemma *) admit.
    + eapply erase_typing_El.
      * eapply IHh2. erewrite scoping_md. 2: eassumption. reflexivity.
      * erewrite scoping_md in hm. 2: eassumption.
        destruct m. all: try reflexivity. discriminate.
Abort.
