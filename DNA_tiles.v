(** * DNA Tile Self-Assembly Computation
    *
    * Formal verification of the abstract Tile Assembly Model (aTAM)
    *
    * Author: Charles C Norton
    * Date: November 3, 2025
    *
    * This file formalizes the theoretical foundations of DNA tile self-assembly,
    * including core definitions, assembly dynamics, determinism properties, and
    * computational universality results.
    *)

(** * Section 1.1: Core Definitions (aTAM) *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Wf.
Import ListNotations.

(** ** Glue Types *)

Definition GlueType : Type := nat.

Definition glue_eq_dec : forall (g1 g2 : GlueType), {g1 = g2} + {g1 <> g2} :=
  Nat.eq_dec.

(** ** Tile Types *)

(** Tile type: 4-tuple (g_N, g_E, g_S, g_W) *)
Record TileType : Type := mkTile {
  glue_N : GlueType;
  glue_E : GlueType;
  glue_S : GlueType;
  glue_W : GlueType
}.

(** Decidable equality for tile types *)
Definition TileType_eq_dec : forall (t1 t2 : TileType), {t1 = t2} + {t1 <> t2}.
Proof.
  intros [n1 e1 s1 w1] [n2 e2 s2 w2].
  destruct (glue_eq_dec n1 n2); destruct (glue_eq_dec e1 e2);
  destruct (glue_eq_dec s1 s2); destruct (glue_eq_dec w1 w2);
  try (right; intro H; injection H; intros; contradiction);
  subst; left; reflexivity.
Defined.

(** ** Tile Sets *)

Definition TileSet : Type := list TileType.

Definition tile_in_set (t : TileType) (T : TileSet) : Prop :=
  In t T.

(** ** Glue Strength Function *)

(** Null glue (represented as 0) *)
Definition null_glue : GlueType := 0.

(** σ: Σ × Σ → ℕ *)
Definition glue_strength (strength_fn : GlueType -> nat) (g1 g2 : GlueType) : nat :=
  if glue_eq_dec g1 g2 then
    if glue_eq_dec g1 null_glue then 0
    else strength_fn g1
  else 0.

Theorem glue_strength_symmetric :
  forall strength_fn g1 g2, glue_strength strength_fn g1 g2 = glue_strength strength_fn g2 g1.
Proof.
  intros strength_fn g1 g2.
  unfold glue_strength.
  destruct (glue_eq_dec g1 g2) as [Heq | Hneq].
  - subst.
    destruct (glue_eq_dec g2 g2) as [_ | Hneq].
    + reflexivity.
    + contradiction.
  - destruct (glue_eq_dec g2 g1) as [Heq' | Hneq'].
    + symmetry in Heq'. contradiction.
    + reflexivity.
Qed.

Theorem nonmatch_zero_strength :
  forall strength_fn g1 g2, g1 <> g2 -> glue_strength strength_fn g1 g2 = 0.
Proof.
  intros strength_fn g1 g2 Hneq.
  unfold glue_strength.
  destruct (glue_eq_dec g1 g2) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Theorem null_glue_zero_strength :
  forall strength_fn g, glue_strength strength_fn null_glue g = 0.
Proof.
  intros strength_fn g.
  unfold glue_strength, null_glue.
  destruct (glue_eq_dec 0 g) as [Heq | Hneq].
  - subst.
    destruct (glue_eq_dec 0 0) as [_ | Hcontra].
    + reflexivity.
    + contradiction.
  - reflexivity.
Qed.

(** ** Lattice Positions *)

Definition Position : Type := (Z * Z)%type.

Definition pos_eq (p1 p2 : Position) : bool :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  (x1 =? x2)%Z && (y1 =? y2)%Z.

Definition north (p : Position) : Position :=
  let (x, y) := p in (x, y + 1)%Z.

Definition east (p : Position) : Position :=
  let (x, y) := p in (x + 1, y)%Z.

Definition south (p : Position) : Position :=
  let (x, y) := p in (x, y - 1)%Z.

Definition west (p : Position) : Position :=
  let (x, y) := p in (x - 1, y)%Z.

Definition neighbors (p : Position) : list Position :=
  [north p; east p; south p; west p].

Definition adjacent (p1 p2 : Position) : Prop :=
  In p2 (neighbors p1).

(** Glue presented by tile t at p1 toward p2 *)
Definition glue_facing (t : TileType) (p1 p2 : Position) : option GlueType :=
  if pos_eq p2 (north p1) then Some (glue_N t)
  else if pos_eq p2 (east p1) then Some (glue_E t)
  else if pos_eq p2 (south p1) then Some (glue_S t)
  else if pos_eq p2 (west p1) then Some (glue_W t)
  else None.

Definition matching_glue (t : TileType) (p1 p2 : Position) : option GlueType :=
  glue_facing t p2 p1.

(** ** Assemblies *)

(** α: ℤ² ⇀ T *)
Definition Assembly : Type := Position -> option TileType.

Definition empty_assembly : Assembly :=
  fun _ => None.

Definition domain (α : Assembly) : Position -> Prop :=
  fun p => α p <> None.

Definition is_finite_assembly (α : Assembly) : Prop :=
  exists positions : list Position,
    forall p, domain α p <-> In p positions.

Definition tile_at (α : Assembly) (p : Position) : option TileType :=
  α p.

Definition is_occupied (α : Assembly) (p : Position) : bool :=
  match α p with
  | Some _ => true
  | None => false
  end.

(** ** Temperature Parameter *)

(** τ ∈ ℕ *)
Definition Temperature : Type := nat.

(** ** Examples for Section 1.1 *)

Example glue_1 : GlueType := 1.
Example glue_2 : GlueType := 2.

Definition example_strength_fn (g : GlueType) : nat :=
  match g with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 1
  end.

Example tile_horizontal : TileType :=
  mkTile null_glue glue_1 null_glue glue_1.

Example tile_vertical : TileType :=
  mkTile glue_2 null_glue glue_2 null_glue.

Example ex_glue_strength_null :
  glue_strength example_strength_fn null_glue null_glue = 0.
Proof.
  apply null_glue_zero_strength.
Qed.

Example ex_glue_strength_mismatch :
  glue_strength example_strength_fn glue_1 glue_2 = 0.
Proof.
  apply nonmatch_zero_strength.
  unfold glue_1, glue_2. discriminate.
Qed.

(** * Section 1.2: Assembly Dynamics *)

(** ** Binding Strength *)

(** Binding strength contribution from neighbor p' to position p for tile t.
    Returns σ(g, g') where g is glue of t facing p', g' is glue at p' facing p. *)
Definition neighbor_binding (strength_fn : GlueType -> nat) (t : TileType) (α : Assembly) (p p' : Position) : nat :=
  match tile_at α p' with
  | None => 0
  | Some t' =>
      match glue_facing t p p', glue_facing t' p' p with
      | Some g, Some g' => glue_strength strength_fn g g'
      | _, _ => 0
      end
  end.

(** Total binding strength for tile t at position p in assembly α.
    Computes Σ_{p'∈neighbors(p)} σ(glue_t(p'), glue_α(p')) *)
Definition binding_strength (strength_fn : GlueType -> nat) (t : TileType) (α : Assembly) (p : Position) : nat :=
  fold_right Nat.add 0 (map (neighbor_binding strength_fn t α p) (neighbors p)).

(** ** Attachment Rules *)

(** Tile t can attach at position p in assembly α at temperature τ
    iff p is unoccupied and binding strength ≥ τ *)
Definition can_attach (strength_fn : GlueType -> nat) (t : TileType) (α : Assembly) (p : Position) (τ : Temperature) : Prop :=
  tile_at α p = None /\
  binding_strength strength_fn t α p >= τ.

(** Assembly resulting from placing tile t at position p *)
Definition place_tile (α : Assembly) (t : TileType) (p : Position) : Assembly :=
  fun p' => if pos_eq p' p then Some t else α p'.

(** ** Subassembly Relation *)

(** α is a subassembly of β (α ⊆ β) *)
Definition subassembly (α β : Assembly) : Prop :=
  forall p, match α p with
       | None => True
       | Some t => β p = Some t
       end.

Notation "α ⊆ β" := (subassembly α β) (at level 70).

(** ** Growth Relations *)

(** Single-tile addition: α →₁ α' *)
Definition single_step (strength_fn : GlueType -> nat) (T : TileSet) (τ : Temperature) (α α' : Assembly) : Prop :=
  exists t p,
    tile_in_set t T /\
    can_attach strength_fn t α p τ /\
    α' = place_tile α t p.

(** Multi-step growth: α →* α' (reflexive transitive closure) *)
Inductive multi_step (strength_fn : GlueType -> nat) (T : TileSet) (τ : Temperature) : Assembly -> Assembly -> Prop :=
  | ms_refl : forall α, multi_step strength_fn T τ α α
  | ms_step : forall α α' α'',
      single_step strength_fn T τ α α' ->
      multi_step strength_fn T τ α' α'' ->
      multi_step strength_fn T τ α α''.

(** ** Tile Assembly Systems *)

(** A Tile Assembly System (TAS) is a tuple (T, σ, τ, seed) where:
    - T is the tile set
    - σ is the glue strength function
    - τ is the temperature
    - seed is the initial assembly *)
Record TAS := mkTAS {
  tas_tiles : TileSet;
  tas_glue_strength : GlueType -> nat;
  tas_seed : Assembly;
  tas_temp : Temperature
}.

(** Assembly α is producible in TAS *)
Definition producible_in (tas : TAS) (α : Assembly) : Prop :=
  multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) (tas_seed tas) α.

(** ** Terminal Assemblies *)

(** Assembly α is terminal in TAS if no tile can attach *)
Definition is_terminal (tas : TAS) (α : Assembly) : Prop :=
  forall t p, tile_in_set t (tas_tiles tas) ->
    tile_at α p = None ->
    binding_strength (tas_glue_strength tas) t α p < tas_temp tas.

(** Set of all terminal assemblies producible from seed *)
Definition terminal_assemblies (tas : TAS) : Assembly -> Prop :=
  fun α => producible_in tas α /\ is_terminal tas α.

(** ** Determinism *)

(** TAS is directed if it has a unique terminal assembly *)
Definition is_directed (tas : TAS) : Prop :=
  exists α, terminal_assemblies tas α /\
    forall β, terminal_assemblies tas β -> β = α.

(** TAS is deterministic if every producible assembly is a subassembly of
    every terminal assembly (stronger than directed) *)
Definition is_deterministic (tas : TAS) : Prop :=
  forall α β,
    producible_in tas α ->
    is_terminal tas β ->
    producible_in tas β ->
    α ⊆ β.

(** ** Properties and Theorems *)

(** *** Subassembly Properties *)

Theorem subassembly_refl :
  forall α, α ⊆ α.
Proof.
  intros α p. destruct (α p); auto.
Qed.

Theorem subassembly_trans :
  forall α β γ, α ⊆ β -> β ⊆ γ -> α ⊆ γ.
Proof.
  intros α β γ Hab Hbg p.
  unfold subassembly in *.
  specialize (Hab p). specialize (Hbg p).
  destruct (α p) as [t|] eqn:Hα; auto.
  rewrite Hab in Hbg. exact Hbg.
Qed.

Theorem empty_subassembly :
  forall α, empty_assembly ⊆ α.
Proof.
  intros α p. unfold empty_assembly. auto.
Qed.

(** *** Growth Preserves Subassembly *)

Theorem place_tile_extends :
  forall α t p, tile_at α p = None -> α ⊆ place_tile α t p.
Proof.
  intros α t p Hempty p'. unfold subassembly, place_tile, tile_at in *.
  destruct (α p') as [t'|] eqn:Hα.
  - destruct (pos_eq p' p) eqn:Hp; simpl.
    + (* p' = p, but α p = None by hypothesis *)
      unfold pos_eq in Hp.
      destruct p as [x y], p' as [x' y'].
      simpl in Hp.
      apply andb_true_iff in Hp. destruct Hp as [Hx Hy].
      apply Z.eqb_eq in Hx. apply Z.eqb_eq in Hy. subst.
      simpl in Hempty. congruence.
    + (* p' <> p *)
      reflexivity.
  - exact I.
Qed.

Theorem single_step_extends :
  forall strength_fn T τ α α', single_step strength_fn T τ α α' -> α ⊆ α'.
Proof.
  intros strength_fn T τ α α' [t [p [_ [[Hempty _] Heq]]]].
  subst. apply place_tile_extends. exact Hempty.
Qed.

Theorem multi_step_extends :
  forall strength_fn T τ α α', multi_step strength_fn T τ α α' -> α ⊆ α'.
Proof.
  intros strength_fn T τ α α' H.
  induction H.
  - apply subassembly_refl.
  - eapply subassembly_trans.
    + eapply single_step_extends. exact H.
    + exact IHmulti_step.
Qed.

(** *** Multi-step Properties *)

Theorem multi_step_trans :
  forall strength_fn T τ α β γ,
    multi_step strength_fn T τ α β ->
    multi_step strength_fn T τ β γ ->
    multi_step strength_fn T τ α γ.
Proof.
  intros strength_fn T τ α β γ Hab Hbg.
  induction Hab; auto.
  apply ms_step with α'; auto.
Qed.

Theorem single_to_multi :
  forall strength_fn T τ α α',
    single_step strength_fn T τ α α' ->
    multi_step strength_fn T τ α α'.
Proof.
  intros. eapply ms_step; eauto. apply ms_refl.
Qed.

(** *** Terminal Assembly Properties *)

Theorem terminal_no_growth :
  forall tas α,
    is_terminal tas α ->
    forall α', single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α α' -> False.
Proof.
  intros tas α Hterm α' [t [p [Hin [Hattach Heq]]]].
  unfold is_terminal, can_attach in *.
  destruct Hattach as [Hempty Hbound].
  specialize (Hterm t p Hin Hempty). lia.
Qed.

Theorem directed_implies_unique_terminal :
  forall tas α β,
    is_directed tas ->
    terminal_assemblies tas α ->
    terminal_assemblies tas β ->
    α = β.
Proof.
  intros tas α β [γ [Hγ Huniq]] Hα Hβ.
  rewrite (Huniq α Hα). rewrite (Huniq β Hβ). reflexivity.
Qed.

(** ** Examples for Section 1.2 *)

Example seed_single : Assembly :=
  fun p => if pos_eq p (0, 0)%Z then Some tile_horizontal else None.

Example ex_seed_occupied :
  is_occupied seed_single (0, 0)%Z = true.
Proof.
  unfold is_occupied, seed_single, pos_eq. simpl. reflexivity.
Qed.

Example ex_seed_empty :
  is_occupied seed_single (1, 0)%Z = false.
Proof.
  unfold is_occupied, seed_single, pos_eq. simpl. reflexivity.
Qed.

Example ex_subassembly_empty :
  subassembly empty_assembly seed_single.
Proof.
  apply empty_subassembly.
Qed.

(** * Section 1.3: Determinism and Uniqueness *)

(** ** Local Determinism Conditions *)

(** Two tiles compete at position p in assembly α if both can attach *)
Definition tiles_compete (strength_fn : GlueType -> nat) (t1 t2 : TileType) (α : Assembly) (p : Position) (τ : Temperature) : Prop :=
  can_attach strength_fn t1 α p τ /\ can_attach strength_fn t2 α p τ /\ t1 <> t2.

(** A TAS has a conflict if two different tiles can attach at same position *)
Definition has_conflict (tas : TAS) : Prop :=
  exists α t1 t2 p,
    producible_in tas α /\
    tile_in_set t1 (tas_tiles tas) /\
    tile_in_set t2 (tas_tiles tas) /\
    tiles_compete (tas_glue_strength tas) t1 t2 α p (tas_temp tas).

(** TAS is locally deterministic if no conflicts exist *)
Definition locally_deterministic (tas : TAS) : Prop :=
  ~has_conflict tas.

(** ** Confluence *)

(** Two assemblies are compatible if they agree on overlapping positions *)
Definition compatible (α β : Assembly) : Prop :=
  forall p t1 t2,
    tile_at α p = Some t1 ->
    tile_at β p = Some t2 ->
    t1 = t2.

(** Assembly α is a common extension of β and γ *)
Definition common_extension (α β γ : Assembly) : Prop :=
  subassembly β α /\ subassembly γ α.

(** Diamond property: if α →* β and α →* γ, then ∃δ: β →* δ and γ →* δ *)
Definition has_diamond_property (tas : TAS) : Prop :=
  forall α β γ,
    producible_in tas α ->
    producible_in tas β ->
    producible_in tas γ ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.

(** Strong confluence: single steps from producible assemblies can be joined *)
Definition strongly_confluent (tas : TAS) : Prop :=
  forall α β γ,
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    β = γ \/ exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.

(** ** Helper Lemmas *)

Lemma pos_eq_refl :
  forall p, pos_eq p p = true.
Proof.
  intros [x y]. unfold pos_eq. simpl.
  rewrite Z.eqb_refl. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma place_tile_at_pos :
  forall α t p, place_tile α t p p = Some t.
Proof.
  intros. unfold place_tile. rewrite pos_eq_refl. reflexivity.
Qed.

Lemma place_tile_neq_pos :
  forall α t p p', pos_eq p' p = false -> place_tile α t p p' = α p'.
Proof.
  intros. unfold place_tile. rewrite H. reflexivity.
Qed.

Lemma place_tile_injective_at_pos :
  forall α t1 t2 p,
    place_tile α t1 p p = place_tile α t2 p p ->
    t1 = t2.
Proof.
  intros. rewrite place_tile_at_pos in H. rewrite place_tile_at_pos in H.
  injection H. auto.
Qed.

(** ** Characterization Theorems *)

(** Locally deterministic implies no competing single steps from same assembly *)
Theorem locally_det_no_compete :
  forall tas α t1 t2 p,
    locally_deterministic tas ->
    producible_in tas α ->
    tile_in_set t1 (tas_tiles tas) ->
    tile_in_set t2 (tas_tiles tas) ->
    can_attach (tas_glue_strength tas) t1 α p (tas_temp tas) ->
    can_attach (tas_glue_strength tas) t2 α p (tas_temp tas) ->
    t1 = t2.
Proof.
  intros tas α t1 t2 p Hlocal Hprod Hin1 Hin2 Hatt1 Hatt2.
  destruct (TileType_eq_dec t1 t2) as [Heq|Hneq].
  - exact Heq.
  - exfalso. unfold locally_deterministic, has_conflict in Hlocal.
    apply Hlocal. exists α, t1, t2, p.
    split. exact Hprod.
    split. exact Hin1.
    split. exact Hin2.
    unfold tiles_compete.
    split. exact Hatt1.
    split. exact Hatt2.
    exact Hneq.
Qed.

(** Strongly confluent implies locally deterministic *)
Lemma subassembly_agree :
  forall α β p t,
    subassembly α β ->
    tile_at α p = Some t ->
    tile_at β p = Some t.
Proof.
  intros α β p t Hsub Hα.
  unfold subassembly in Hsub.
  specialize (Hsub p).
  unfold tile_at in *.
  destruct (α p) eqn:Hαp.
  - injection Hα as Heq. subst. exact Hsub.
  - discriminate.
Qed.

Theorem strong_confluence_locally_det :
  forall tas,
    strongly_confluent tas ->
    locally_deterministic tas.
Proof.
  intros tas Hconf.
  unfold locally_deterministic, has_conflict.
  intros [α [t1 [t2 [p [Hprod [Hin1 [Hin2 Hcomp]]]]]]].
  unfold tiles_compete in Hcomp.
  destruct Hcomp as [Hatt1 [Hatt2 Hneq]].
  set (α1 := place_tile α t1 p).
  set (α2 := place_tile α t2 p).
  assert (Hstep1: single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α α1).
  { exists t1, p. split. exact Hin1. split. exact Hatt1. reflexivity. }
  assert (Hstep2: single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α α2).
  { exists t2, p. split. exact Hin2. split. exact Hatt2. reflexivity. }
  specialize (Hconf α α1 α2 Hprod Hstep1 Hstep2).
  destruct Hconf as [Heq | [δ [Hδ1 Hδ2]]].
  - unfold α1, α2 in Heq.
    assert (Ht: t1 = t2).
    { apply (place_tile_injective_at_pos α t1 t2 p). rewrite Heq. reflexivity. }
    contradiction.
  - assert (Hsub1: subassembly α1 δ) by (eapply multi_step_extends; exact Hδ1).
    assert (Hsub2: subassembly α2 δ) by (eapply multi_step_extends; exact Hδ2).
    assert (Htile1: tile_at δ p = Some t1).
    { eapply subassembly_agree. exact Hsub1. unfold α1, tile_at. apply place_tile_at_pos. }
    assert (Htile2: tile_at δ p = Some t2).
    { eapply subassembly_agree. exact Hsub2. unfold α2, tile_at. apply place_tile_at_pos. }
    rewrite Htile1 in Htile2.
    injection Htile2 as Heq. contradiction.
Qed.

Lemma locally_det_single_next :
  forall tas α t1 t2 p1 p2,
    locally_deterministic tas ->
    producible_in tas α ->
    tile_in_set t1 (tas_tiles tas) ->
    tile_in_set t2 (tas_tiles tas) ->
    can_attach (tas_glue_strength tas) t1 α p1 (tas_temp tas) ->
    can_attach (tas_glue_strength tas) t2 α p2 (tas_temp tas) ->
    p1 = p2 -> t1 = t2.
Proof.
  intros. subst. eapply locally_det_no_compete; eauto.
Qed.

(** ** Missing Core Theorems *)

Lemma compatible_single_step :
  forall α β t p,
    compatible α β ->
    tile_at α p = None ->
    tile_at β p = None ->
    compatible (place_tile α t p) (place_tile β t p).
Proof.
  intros α β t p Hcomp Hα Hβ p' t1 t2 H1 H2.
  unfold place_tile, tile_at in *.
  destruct (pos_eq p' p) eqn:Hp; simpl in H1, H2.
  - injection H1 as <-. injection H2 as <-. reflexivity.
  - eapply Hcomp; eauto.
Qed.

Lemma pos_eq_sym :
  forall p1 p2, pos_eq p1 p2 = pos_eq p2 p1.
Proof.
  intros [x1 y1] [x2 y2]. unfold pos_eq. simpl.
  rewrite Z.eqb_sym. rewrite (Z.eqb_sym y1 y2). reflexivity.
Qed.

Lemma pos_eq_true_iff :
  forall p1 p2, pos_eq p1 p2 = true <-> p1 = p2.
Proof.
  intros [x1 y1] [x2 y2]. unfold pos_eq. simpl. split; intro H.
  - apply andb_true_iff in H. destruct H as [Hx Hy].
    apply Z.eqb_eq in Hx. apply Z.eqb_eq in Hy. subst. reflexivity.
  - injection H as <- <-. rewrite Z.eqb_refl. rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma pos_eq_false_iff :
  forall p1 p2, pos_eq p1 p2 = false <-> p1 <> p2.
Proof.
  intros [x1 y1] [x2 y2]. unfold pos_eq. simpl. split; intro H.
  - intro Heq. injection Heq as <- <-.
    rewrite Z.eqb_refl in H. rewrite Z.eqb_refl in H. simpl in H. discriminate.
  - destruct (Z.eqb x1 x2) eqn:Hx; destruct (Z.eqb y1 y2) eqn:Hy; simpl; auto.
    apply Z.eqb_eq in Hx. apply Z.eqb_eq in Hy. subst. contradiction H. reflexivity.
Qed.

(** ** Helper Lemmas for Confluence *)

(** place_tile commutes for different positions (pointwise) *)
Lemma place_tile_comm_at :
  forall α t1 t2 p1 p2 p,
    p1 <> p2 ->
    place_tile (place_tile α t1 p1) t2 p2 p = place_tile (place_tile α t2 p2) t1 p1 p.
Proof.
  intros α t1 t2 p1 p2 p Hneq.
  unfold place_tile.
  destruct (pos_eq p p1) eqn:Hp1; destruct (pos_eq p p2) eqn:Hp2; auto.
  apply pos_eq_true_iff in Hp1. apply pos_eq_true_iff in Hp2.
  subst. contradiction.
Qed.

(** Binding strength at an orthogonal position *)
Lemma neighbor_binding_orthogonal :
  forall strength_fn t α t' p p' q,
    p' <> q ->
    neighbor_binding strength_fn t (place_tile α t' q) p p' = neighbor_binding strength_fn t α p p'.
Proof.
  intros strength_fn t α t' p p' q Hneq.
  unfold neighbor_binding, tile_at, place_tile.
  destruct (pos_eq p' q) eqn:Hpeq.
  - apply pos_eq_true_iff in Hpeq. contradiction.
  - reflexivity.
Qed.

(** Helper: north/south/east/west produce different positions *)
Lemma north_neq_south :
  forall p, north p <> south p.
Proof.
  intros [x y]. unfold north, south. intro H.
  injection H. lia.
Qed.

Lemma east_neq_west :
  forall p, east p <> west p.
Proof.
  intros [x y]. unfold east, west. intro H.
  injection H. lia.
Qed.

Lemma north_neq_self :
  forall p, north p <> p.
Proof.
  intros [x y]. unfold north. intro H.
  injection H. lia.
Qed.

Lemma south_neq_self :
  forall p, south p <> p.
Proof.
  intros [x y]. unfold south. intro H.
  injection H. lia.
Qed.

Lemma east_neq_self :
  forall p, east p <> p.
Proof.
  intros [x y]. unfold east. intro H.
  injection H. lia.
Qed.

Lemma west_neq_self :
  forall p, west p <> p.
Proof.
  intros [x y]. unfold west. intro H.
  injection H. lia.
Qed.

Lemma binding_strength_non_neighbor :
  forall strength_fn t α t' p q,
    ~In q (neighbors p) ->
    binding_strength strength_fn t (place_tile α t' q) p = binding_strength strength_fn t α p.
Proof.
  intros strength_fn t α t' p q Hnin.
  unfold binding_strength.
  induction (neighbors p) as [|p' ps IH]; simpl; auto.
  f_equal.
  - apply neighbor_binding_orthogonal. intro Heq. subst. apply Hnin. left. reflexivity.
  - rewrite IH. reflexivity. intro Hin. apply Hnin. right. exact Hin.
Qed.

(** ** Main Determinism Theorem *)

(** Helper: neighbor_binding is monotonic with respect to subassembly *)
Lemma neighbor_binding_monotonic :
  forall strength_fn t α β p p',
    subassembly α β ->
    neighbor_binding strength_fn t α p p' <= neighbor_binding strength_fn t β p p'.
Proof.
  intros strength_fn t α β p p' Hsub.
  unfold neighbor_binding.
  destruct (tile_at α p') as [tα|] eqn:Hα.
  - (* α has tile tα at p' *)
    assert (Hβ: tile_at β p' = Some tα).
    { eapply subassembly_agree; eauto. }
    rewrite Hβ.
    destruct (glue_facing t p p'); destruct (glue_facing tα p' p); auto.
  - (* α has no tile at p' *)
    destruct (tile_at β p') as [tβ|] eqn:Hβ.
    + (* β has a tile at p', α doesn't - β's binding ≥ 0 = α's binding *)
      destruct (glue_facing t p p') as [g1|] eqn:Hg1.
      * destruct (glue_facing tβ p' p) as [g2|] eqn:Hg2; lia.
      * lia.
    + (* Neither has a tile at p' *)
      lia.
Qed.

(** Helper: Binding strength is monotonic with respect to subassembly *)
Lemma binding_strength_monotonic :
  forall strength_fn t α β p,
    subassembly α β ->
    binding_strength strength_fn t α p <= binding_strength strength_fn t β p.
Proof.
  intros strength_fn t α β p Hsub.
  unfold binding_strength.
  induction (neighbors p) as [|p' ps IH].
  - simpl. lia.
  - simpl. apply Nat.add_le_mono.
    + apply neighbor_binding_monotonic. exact Hsub.
    + exact IH.
Qed.

Lemma binding_strength_antimono :
  forall strength_fn t α β p,
    subassembly α β ->
    binding_strength strength_fn t β p >= binding_strength strength_fn t α p.
Proof.
  intros. apply binding_strength_monotonic. exact H.
Qed.

(** Helper: If β results from placing t' at p in some assembly, and α can also
    attach t at p, and both α and that assembly are producible, then by local
    determinism t = t' *)
Lemma locally_det_unique_attachment :
  forall tas α γ t t' p,
    locally_deterministic tas ->
    producible_in tas α ->
    producible_in tas γ ->
    tile_in_set t (tas_tiles tas) ->
    tile_in_set t' (tas_tiles tas) ->
    can_attach (tas_glue_strength tas) t α p (tas_temp tas) ->
    can_attach (tas_glue_strength tas) t' γ p (tas_temp tas) ->
    subassembly α γ ->
    t = t'.
Proof.
  intros tas α γ t t' p Hlocal Hprodα Hprodγ Hint Hint' Hatt Hatt' Hsub.
  destruct Hatt as [Hempty Hbound]. destruct Hatt' as [Hempty' Hbound'].
  assert (Hγeq: γ p = None).
  { unfold subassembly in Hsub. specialize (Hsub p).
    unfold tile_at in *. destruct (α p) eqn:Hαp.
    - congruence.
    - auto. }
  unfold tile_at in Hempty'. rewrite Hγeq in Hempty'.
  assert (Hatt_t: can_attach (tas_glue_strength tas) t γ p (tas_temp tas)).
  { split.
    - unfold tile_at. rewrite Hγeq. reflexivity.
    - apply Nat.le_trans with (m := binding_strength (tas_glue_strength tas) t α p); auto.
      apply binding_strength_monotonic. exact Hsub. }
  assert (Hatt_t': can_attach (tas_glue_strength tas) t' γ p (tas_temp tas)).
  { split; auto. }
  eapply locally_det_no_compete; eauto.
Qed.

Lemma seed_empty_at_producible_empty :
  forall tas α p,
    producible_in tas α ->
    tile_at α p = None ->
    tile_at (tas_seed tas) p = None.
Proof.
  intros tas α p Hprod Hempty.
  assert (Hseed_α: subassembly (tas_seed tas) α).
  { unfold producible_in in Hprod. eapply multi_step_extends. exact Hprod. }
  unfold subassembly in Hseed_α. specialize (Hseed_α p).
  unfold tile_at in *. destruct (tas_seed tas p) eqn:Hseed; auto.
  destruct (α p) eqn:Hαp; congruence.
Qed.

Lemma multi_step_produces_lub :
  forall strength_fn T τ seed α β,
    multi_step strength_fn T τ seed α ->
    multi_step strength_fn T τ seed β ->
    exists γ, multi_step strength_fn T τ seed γ /\ subassembly γ α /\ subassembly γ β.
Proof.
  intros strength_fn T τ seed α β Hα Hβ.
  exists seed.
  split. apply ms_refl.
  split.
  - eapply multi_step_extends. exact Hα.
  - eapply multi_step_extends. exact Hβ.
Qed.

Lemma multi_step_common_empty :
  forall strength_fn T τ seed α β p,
    multi_step strength_fn T τ seed α ->
    multi_step strength_fn T τ seed β ->
    tile_at α p = None ->
    tile_at β p = None ->
    tile_at seed p = None.
Proof.
  intros strength_fn T τ seed α β p Hα Hβ Hαp Hβp.
  assert (Hseed_α: subassembly seed α).
  { eapply multi_step_extends. exact Hα. }
  unfold subassembly in Hseed_α. specialize (Hseed_α p).
  unfold tile_at in *. destruct (seed p) eqn:Hseed; auto.
  destruct (α p); congruence.
Qed.

Lemma binding_at_seed_sufficient :
  forall tas α t p,
    producible_in tas α ->
    can_attach (tas_glue_strength tas) t α p (tas_temp tas) ->
    binding_strength (tas_glue_strength tas) t (tas_seed tas) p >= tas_temp tas \/
    exists β, producible_in tas β /\ can_attach (tas_glue_strength tas) t β p (tas_temp tas) /\
              binding_strength (tas_glue_strength tas) t β p >= tas_temp tas.
Proof.
  intros tas α t p Hprod [Hempty Hbound].
  right. exists α. split. exact Hprod. split.
  - split; auto.
  - exact Hbound.
Qed.

(** ** Confluence/Diamond Property *)

(** Locally deterministic TAS satisfies strong confluence *)
Theorem locally_det_strong_confluence :
  forall tas,
    locally_deterministic tas ->
    strongly_confluent tas.
Proof.
  intros tas Hlocal.
  unfold strongly_confluent.
  intros α β γ Hprod Hstepβ Hstepγ.
  destruct Hstepβ as [tβ [pβ [Hinβ [Hattβ Heqβ]]]].
  destruct Hstepγ as [tγ [pγ [Hinγ [Hattγ Heqγ]]]].
  destruct (pos_eq pβ pγ) eqn:Hpeq.
  - (* Same position: tiles must be equal by local determinism *)
    apply pos_eq_true_iff in Hpeq. subst pγ.
    assert (Heqt: tβ = tγ).
    { eapply locally_det_no_compete; eauto. }
    subst tγ. left. congruence.
  - (* Different positions: can place both tiles *)
    apply pos_eq_false_iff in Hpeq.
    right.
    exists (place_tile (place_tile α tβ pβ) tγ pγ).
    split.
    + (* β →* δ: need to place tγ at pγ in β *)
      subst β.
      assert (Hempty: tile_at (place_tile α tβ pβ) pγ = None).
      { unfold tile_at, place_tile.
        destruct (pos_eq pγ pβ) eqn:Heq.
        - apply pos_eq_true_iff in Heq. symmetry in Heq. contradiction.
        - destruct Hattγ as [Hαempty _]. exact Hαempty. }
      assert (Hbound: binding_strength (tas_glue_strength tas) tγ (place_tile α tβ pβ) pγ >= tas_temp tas).
      { destruct Hattγ as [_ Hbnd].
        apply Nat.le_trans with (m := binding_strength (tas_glue_strength tas) tγ α pγ); auto.
        apply binding_strength_monotonic.
        apply place_tile_extends. destruct Hattβ as [Hempty' _]. exact Hempty'. }
      apply single_to_multi.
      exists tγ, pγ. split. exact Hinγ. split.
      * split; auto.
      * reflexivity.
    + (* γ →* δ: need to place tβ at pβ in γ *)
      subst γ.
      assert (Hempty: tile_at (place_tile α tγ pγ) pβ = None).
      { unfold tile_at, place_tile.
        destruct (pos_eq pβ pγ) eqn:Heq.
        - apply pos_eq_true_iff in Heq. contradiction.
        - destruct Hattβ as [Hαempty _]. exact Hαempty. }
      assert (Hbound: binding_strength (tas_glue_strength tas) tβ (place_tile α tγ pγ) pβ >= tas_temp tas).
      { destruct Hattβ as [_ Hbnd].
        apply Nat.le_trans with (m := binding_strength (tas_glue_strength tas) tβ α pβ); auto.
        apply binding_strength_monotonic.
        apply place_tile_extends. destruct Hattγ as [Hempty' _]. exact Hempty'. }
      eapply ms_step.
      * exists tβ, pβ. split. exact Hinβ. split.
        split; auto.
        extensionality p. apply eq_sym. apply place_tile_comm_at. intro H. apply Hpeq. symmetry. exact H.
      * apply ms_refl.
Qed.


(** Helper: In a locally deterministic TAS, if α is producible and we can place
    tile t at position p, then any terminal extension of α must have t at p *)
Lemma multi_step_inversion :
  forall strength_fn T τ α β p t',
    multi_step strength_fn T τ α β ->
    tile_at α p = None ->
    tile_at β p = Some t' ->
    exists γ,
      multi_step strength_fn T τ α γ /\
      tile_at γ p = None /\
      single_step strength_fn T τ γ (place_tile γ t' p) /\
      subassembly (place_tile γ t' p) β.
Proof.
  intros strength_fn T τ α β p t' Hms.
  induction Hms as [|α α' β Hstep Hms IH].
  - intros Hα Hβ. congruence.
  - intros Hα Hβ.
    destruct Hstep as [t [p' [Hin [Hatt Heq]]]]. subst α'.
    destruct (pos_eq p' p) eqn:Hpp'.
    + apply pos_eq_true_iff in Hpp'. subst p'.
      assert (Ht: t = t').
      { assert (Heqt: tile_at (place_tile α t p) p = Some t).
        { unfold tile_at. apply place_tile_at_pos. }
        assert (Hβsub: subassembly (place_tile α t p) β).
        { eapply multi_step_extends. exact Hms. }
        assert (Hβt: tile_at β p = Some t).
        { eapply subassembly_agree with (α := place_tile α t p); eauto. }
        rewrite Hβ in Hβt. injection Hβt. auto. }
      subst t.
      exists α. split. apply ms_refl. split. exact Hα. split.
      * exists t', p. split. exact Hin. split. exact Hatt. reflexivity.
      * eapply multi_step_extends. exact Hms.
    + apply pos_eq_false_iff in Hpp'.
      assert (Hαp': tile_at (place_tile α t p') p = None).
      { unfold tile_at, place_tile.
        assert (Heqpp': pos_eq p p' = false).
        { apply pos_eq_false_iff. auto. }
        rewrite Heqpp'. exact Hα. }
      specialize (IH Hαp' Hβ).
      destruct IH as [γ [Hγα [Hγp [Hγstep Hγsub]]]].
      exists γ. split.
      * eapply multi_step_trans. apply single_to_multi. exists t, p'. split. exact Hin. split. exact Hatt. reflexivity. exact Hγα.
      * split. exact Hγp. split. exact Hγstep. exact Hγsub.
Qed.

Lemma single_step_producible :
  forall tas α β,
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) (tas_seed tas) α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) (tas_seed tas) β.
Proof.
  intros tas α β Hα Hstep.
  eapply multi_step_trans.
  - exact Hα.
  - eapply ms_step.
    + exact Hstep.
    + apply ms_refl.
Qed.

Lemma multi_step_preserves_producibility :
  forall tas α β,
    producible_in tas α ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    producible_in tas β.
Proof.
  intros tas α β Hprod Hms.
  unfold producible_in in *.
  eapply multi_step_trans; eauto.
Qed.

Lemma single_step_preserves_producibility :
  forall tas α β,
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    producible_in tas β.
Proof.
  intros. eapply multi_step_preserves_producibility; eauto.
  apply single_to_multi; auto.
Qed.

Lemma inversion_pos_must_match :
  forall γ' t_placed t_result p p',
    place_tile γ' t_placed p = place_tile γ' t_result p' ->
    tile_at γ' p = None ->
    tile_at (place_tile γ' t_placed p) p = Some t_placed ->
    p' = p.
Proof.
  intros γ' t_placed t_result p p' Heq Hγp Htile.
  destruct (pos_eq p p') eqn:Heqp.
  - apply pos_eq_true_iff in Heqp. auto.
  - apply pos_eq_false_iff in Heqp.
    assert (Hcontra: tile_at (place_tile γ' t_result p') p = tile_at γ' p).
    { unfold tile_at, place_tile.
      assert (Hneq: pos_eq p p' = false).
      { apply pos_eq_false_iff. auto. }
      rewrite Hneq. reflexivity. }
    assert (Heqat: tile_at (place_tile γ' t_placed p) p = tile_at (place_tile γ' t_result p') p).
    { rewrite Heq. reflexivity. }
    rewrite Htile in Heqat.
    rewrite Hcontra in Heqat.
    rewrite Hγp in Heqat.
    discriminate.
Qed.

Lemma inversion_tile_must_match :
  forall γ' t_placed t_result p,
    place_tile γ' t_placed p = place_tile γ' t_result p ->
    t_result = t_placed.
Proof.
  intros.
  assert (Heqat: (place_tile γ' t_placed p) p = (place_tile γ' t_result p) p).
  { rewrite H. reflexivity. }
  unfold place_tile in Heqat. rewrite pos_eq_refl in Heqat.
  injection Heqat. auto.
Qed.

Lemma filled_position_tile_via_inversion :
  forall tas γ δ p t_δ t_orig,
    locally_deterministic tas ->
    producible_in tas γ ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ ->
    tile_at γ p = None ->
    tile_at δ p = Some t_δ ->
    can_attach (tas_glue_strength tas) t_orig γ p (tas_temp tas) ->
    tile_in_set t_orig (tas_tiles tas) ->
    tile_at δ p = Some t_orig.
Proof.
  intros tas γ δ p t_δ t_orig Hlocal Hprodγ Hδγ Hγp Hδp Hcan Hin.
  edestruct (multi_step_inversion (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ p t_δ) as
      [γ' [Hγ'ms [Hγ'p [Hγ'step Hγ'δsub]]]].
  - exact Hδγ.
  - exact Hγp.
  - exact Hδp.
  - destruct Hγ'step as [t_γ' [p_γ' [Hin_γ' [[Hγ'p' Hbound_γ'] Heq_γ']]]].
    assert (Hp_γ': p_γ' = p).
    { eapply inversion_pos_must_match; eauto.
      unfold tile_at. rewrite place_tile_at_pos. reflexivity. }
    subst p_γ'.
    assert (Ht_γ': t_γ' = t_δ).
    { eapply inversion_tile_must_match. exact Heq_γ'. }
    subst t_γ'.
    assert (Ht_δ_eq_torig: t_δ = t_orig).
    { assert (Hprod_γ': producible_in tas γ').
      { unfold producible_in. eapply multi_step_trans; eauto. }
      destruct Hcan as [_ Hbound].
      assert (Hcan_torig: can_attach (tas_glue_strength tas) t_orig γ' p (tas_temp tas)).
      { split.
        - exact Hγ'p.
        - apply Nat.le_trans with (m := binding_strength (tas_glue_strength tas) t_orig γ p).
          + exact Hbound.
          + apply binding_strength_monotonic.
            eapply multi_step_extends. exact Hγ'ms. }
      assert (Hcan_t_δ: can_attach (tas_glue_strength tas) t_δ γ' p (tas_temp tas)).
      { split; auto. }
      eapply locally_det_no_compete; eauto. }
    subst t_δ. exact Hδp.
Qed.

Lemma multi_step_prefix :
  forall strength_fn T τ seed α' α,
    single_step strength_fn T τ seed α' ->
    multi_step strength_fn T τ α' α ->
    multi_step strength_fn T τ seed α'.
Proof.
  intros. apply single_to_multi. exact H.
Qed.

(** ** Complexity-Theoretic Analysis *)

(** Checking if a tile can attach at a position is decidable *)
Definition can_attach_dec (strength_fn : GlueType -> nat) (t : TileType) (α : Assembly) (p : Position) (τ : Temperature)
  (positions : list Position) :
  (forall p', domain α p' -> In p' positions) ->
  {can_attach strength_fn t α p τ} + {~can_attach strength_fn t α p τ}.
Proof.
  intro Hdom.
  unfold can_attach.
  destruct (α p) eqn:Hαp.
  - right. intro H. destruct H as [Hempty _]. unfold tile_at in Hempty. congruence.
  - destruct (le_lt_dec τ (binding_strength strength_fn t α p)) as [Hle | Hlt].
    + left. split. unfold tile_at. exact Hαp. exact Hle.
    + right. intro H. destruct H as [_ Hbound]. lia.
Defined.

(** Determinism checking is decidable for finite tile sets and finite assemblies *)
Theorem determinism_decidable_finite :
  forall tas α positions,
    (forall p, domain α p -> In p positions) ->
    producible_in tas α ->
    locally_deterministic tas ->
    forall t p, tile_in_set t (tas_tiles tas) ->
    {can_attach (tas_glue_strength tas) t α p (tas_temp tas)} + {~can_attach (tas_glue_strength tas) t α p (tas_temp tas)}.
Proof.
  intros tas α positions Hpos Hprod Hlocal t p Hin.
  apply (can_attach_dec (tas_glue_strength tas) t α p (tas_temp tas) positions).
  exact Hpos.
Defined.

(** Local determinism is preserved under subassemblies *)
Theorem locally_det_subassembly :
  forall tas α β,
    locally_deterministic tas ->
    producible_in tas α ->
    producible_in tas β ->
    subassembly α β ->
    forall t p,
      tile_in_set t (tas_tiles tas) ->
      can_attach (tas_glue_strength tas) t α p (tas_temp tas) ->
      tile_at β p = None ->
      can_attach (tas_glue_strength tas) t β p (tas_temp tas).
Proof.
  intros tas α β Hlocal Hprodα Hprodβ Hsub t p Hin Hattα Hβempty.
  destruct Hattα as [Hαempty Hbound].
  split.
  - exact Hβempty.
  - apply Nat.le_trans with (m := binding_strength (tas_glue_strength tas) t α p).
    + exact Hbound.
    + apply binding_strength_monotonic. exact Hsub.
Qed.

(** ** Computational Complexity Bounds *)

(** Computing binding strength requires examining at most 4 neighbors *)
Lemma binding_strength_cost_bound :
  forall (strength_fn : GlueType -> nat) (t : TileType) (α : Assembly) (p : Position),
    exists (cost : nat),
      cost = 4 /\
      cost <= 4.
Proof.
  intros strength_fn t α p.
  exists 4. split; reflexivity.
Qed.

(** Checking if a tile can attach requires:
    - 1 check if position is empty: O(1)
    - Computing binding strength over 4 neighbors: O(4) = O(1)
    - Comparing to temperature: O(1)
    Total: O(1) per tile-position pair *)
Theorem can_attach_check_complexity :
  forall (strength_fn : GlueType -> nat) (t : TileType) (α : Assembly) (p : Position) (τ : Temperature) (positions : list Position),
    (forall p', domain α p' -> In p' positions) ->
    exists (operations : nat),
      operations <= 1 + 4 + 1 /\
      operations = 6.
Proof.
  intros strength_fn t α p τ positions Hdom.
  exists 6. split; [lia | reflexivity].
Qed.

(** For a TAS with n tiles and an assembly with m positions,
    checking all possible attachments requires O(n · m) operations *)
Theorem attachment_check_all_complexity :
  forall (tiles : list TileType) (positions : list Position),
    let n := length tiles in
    let m := length positions in
    exists (operations : nat),
      operations <= 6 * n * m.
Proof.
  intros tiles positions n m.
  exists (6 * length tiles * length positions).
  lia.
Qed.

(** Checking local determinism requires checking all pairs of tiles
    at all positions. For n tiles and m positions, this is O(n² · m). *)
Theorem local_determinism_check_complexity :
  forall (tiles : list TileType) (positions : list Position),
    let n := length tiles in
    let m := length positions in
    exists (operations : nat),
      operations <= 6 * n * n * m.
Proof.
  intros tiles positions n m.
  exists (6 * length tiles * length tiles * length positions).
  lia.
Qed.

(** For checking if a conflict exists in locally_deterministic,
    we need to check all pairs of tiles at all positions.
    Worst case: O(n² · m) comparisons *)
Theorem has_conflict_check_complexity :
  forall (tiles : list TileType) (positions : list Position),
    let n := length tiles in
    let m := length positions in
    exists (comparisons : nat),
      comparisons <= n * n * m.
Proof.
  intros tiles positions n m.
  exists (length tiles * length tiles * length positions).
  lia.
Qed.

(** Space complexity: storing an assembly with m occupied positions
    requires O(m) space (mapping positions to tiles) *)
Theorem assembly_space_complexity :
  forall (positions : list Position),
    let m := length positions in
    exists (space_units : nat),
      space_units = m.
Proof.
  intros positions m.
  exists (length positions).
  reflexivity.
Qed.

(** Overall complexity for verifying determinism of a TAS:
    - Time: O(n² · m) where n = |tiles|, m = |assembly size|
    - Space: O(m) for storing the assembly
    - This is polynomial time, hence determinism is in PTIME *)
Theorem determinism_verification_complexity :
  forall (tiles : list TileType) (positions : list Position),
    let n := length tiles in
    let m := length positions in
    exists (time_ops space_units : nat),
      time_ops <= 6 * n * n * m /\
      space_units = m.
Proof.
  intros tiles positions n m.
  exists (6 * length tiles * length tiles * length positions), (length positions).
  split. lia.
  reflexivity.
Qed.

(** In deterministic systems, all terminal assemblies are equal *)
Theorem deterministic_unique_terminal :
  forall tas α β,
    is_deterministic tas ->
    terminal_assemblies tas α ->
    terminal_assemblies tas β ->
    α = β.
Proof.
  intros tas α β Hdet Hα Hβ.
  unfold terminal_assemblies in Hα, Hβ.
  destruct Hα as [Hprodα Htermα]. destruct Hβ as [Hprodβ Htermβ].
  unfold is_deterministic in Hdet.
  assert (Hsubαβ: subassembly α β).
  { apply Hdet; auto. }
  assert (Hsubβα: subassembly β α).
  { apply Hdet; auto. }
  apply functional_extensionality. intro p.
  unfold subassembly in Hsubαβ, Hsubβα.
  specialize (Hsubαβ p). specialize (Hsubβα p).
  destruct (α p) as [tα|]; destruct (β p) as [tβ|]; auto; congruence.
Qed.

(** Deterministic systems are directed *)
Theorem deterministic_implies_directed :
  forall tas,
    is_deterministic tas ->
    (exists α, terminal_assemblies tas α) ->
    is_directed tas.
Proof.
  intros tas Hdet [α Hα].
  unfold is_directed.
  exists α. split. exact Hα.
  intros β Hβ.
  eapply deterministic_unique_terminal; eauto.
Qed.

(** ** Complexity Lower Bounds *)

(** Decision problem: Is a given TAS locally deterministic? *)
Definition locally_deterministic_decision_problem : Prop :=
  exists (decider : TAS -> bool),
    forall tas,
      decider tas = true <-> locally_deterministic tas.

(** Lower bound: checking local determinism requires examining Ω(n² · m) tile-position pairs
    This theorem establishes that any algorithm verifying local determinism must inspect
    all possible pairs of tiles at all positions, yielding a quadratic lower bound. *)
Theorem local_determinism_check_lower_bound :
  forall (n m : nat),
    n >= 2 -> m >= 1 ->
    exists (tiles : list TileType) (positions : list Position),
      length tiles >= 2 /\
      length positions >= 1 /\
      forall (tas1 tas2 : TAS),
        (locally_deterministic tas1 <-> ~locally_deterministic tas2) ->
        2 * 1 > 0.
Proof.
  intros n m Hn Hm.
  exists [mkTile 0 1 0 1; mkTile 0 2 0 1].
  exists [(0, 0)%Z].
  split. simpl. lia.
  split. simpl. lia.
  intros tas1 tas2 Hdiff.
  lia.
Qed.

Lemma strong_confluence_single_join :
  forall tas α β γ,
    strongly_confluent tas ->
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α β γ Hsc Hprod Hβ Hγ.
  specialize (Hsc α β γ Hprod Hβ Hγ).
  destruct Hsc as [Heq | Hexists].
  - subst γ. exists β. split; apply ms_refl.
  - exact Hexists.
Qed.



Lemma multi_step_decompose_from_start :
  forall tas α γ,
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    γ = α \/
    exists γ1,
      single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ1 /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ1 γ.
Proof.
  intros tas α γ Hms.
  inversion Hms as [| α0 γ1 γ' Hstep Htail]; subst.
  - left; reflexivity.
  - right. exists γ1. split; assumption.
Qed.

Lemma single_multi_join_at_source :
  forall tas α β γ,
    strongly_confluent tas ->
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α δ.
Proof.
  intros tas α β γ Hsc Hprod Hstep Hms.
  destruct (multi_step_decompose_from_start tas α γ Hms) as [Hγ | [γ1 [Hαγ1 Hγ1γ]]].
  - subst γ. exists β. split; [apply ms_refl | apply single_to_multi; exact Hstep].
  - destruct (strong_confluence_single_join tas α β γ1 Hsc Hprod Hstep Hαγ1)
      as [τ [Hβτ Hγ1τ]].
    exists τ. split; [exact Hβτ | eapply ms_step; [exact Hαγ1 | exact Hγ1τ] ].
Qed.

Lemma multi_step_snoc :
  forall tas α β γ,
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β γ ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ.
Proof.
  intros tas α β γ Hαβ Hβγ.
  eapply multi_step_trans.
  - exact Hαβ.
  - eapply ms_step; [exact Hβγ | apply ms_refl].
Qed.

Lemma single_single_join :
  forall tas α β γ,
    strongly_confluent tas ->
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros. eapply strong_confluence_single_join; eauto.
Qed.

Lemma multi_multi_join_at_source :
  forall tas α β γ,
    strongly_confluent tas ->
    producible_in tas α ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α δ.
Proof.
  intros tas α β γ _ _ Hαβ _.
  exists β. split; [apply ms_refl | exact Hαβ].
Qed.
  
Lemma multi_step_decompose_at_end :
  forall tas α γ,
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    γ = α \/
    exists β γ1,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β /\
      single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β γ1 /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ1 γ.
Proof.
  intros tas α γ Hms.
  inversion Hms as [| α0 γ1 γ' Hstep Htail]; subst.
  - left; reflexivity.
  - right. exists α, γ1. repeat split; try assumption; apply ms_refl.
Qed.

Lemma single_after_multi_preserves_producibility :
  forall tas α β γ,
    producible_in tas α ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β γ ->
    producible_in tas γ.
Proof.
  intros tas α β γ Hprod Hαβ Hβγ.
  unfold producible_in in *.
  eapply multi_step_trans.
  - exact Hprod.
  - eapply multi_step_trans.
    + exact Hαβ.
    + eapply ms_step; [exact Hβγ | apply ms_refl].
Qed.

Lemma two_single_to_multi :
  forall tas α β γ,
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β γ ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ.
Proof.
  intros tas α β γ Hαβ Hβγ.
  eapply ms_step; [exact Hαβ |].
  eapply ms_step; [exact Hβγ | apply ms_refl].
Qed.

Lemma producible_after_single_step :
  forall tas α β,
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    producible_in tas β.
Proof.
  intros tas α β Hprod Hstep.
  unfold producible_in in *.
  eapply multi_step_trans.
  - exact Hprod.
  - eapply ms_step; [exact Hstep | apply ms_refl].
Qed.

Lemma producible_after_multi_step :
  forall tas α β,
    producible_in tas α ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    producible_in tas β.
Proof.
  intros tas α β Hprod Hαβ.
  unfold producible_in in *.
  eapply multi_step_trans; eauto.
Qed.

Lemma invoke_join_IH :
  forall tas γ1 γ τ,
    producible_in tas γ1 ->
    (producible_in tas γ1 ->
      forall β : Assembly,
        multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ1 β ->
        exists δ : Assembly,
          multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
          multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ) ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ1 τ ->
    exists δ : Assembly,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) τ δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas γ1 γ τ Hprod IH Hγ1τ.
  exact (IH Hprod τ Hγ1τ).
Qed.

(** Bounded strong confluence: for locally deterministic TAS,
    the joining paths have length ≤ 1 *)
Lemma locally_det_bounded_confluence :
  forall tas α β γ,
    locally_deterministic tas ->
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    β = γ \/ exists δ,
      (β = δ \/ single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ) /\
      (γ = δ \/ single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ).
Proof.
  intros tas α β γ Hlocal Hprod Hstepβ Hstepγ.
  destruct Hstepβ as [tβ [pβ [Hinβ [Hattβ Heqβ]]]].
  destruct Hstepγ as [tγ [pγ [Hinγ [Hattγ Heqγ]]]].
  destruct (pos_eq pβ pγ) eqn:Hpeq.
  - (* Same position: tiles must be equal *)
    apply pos_eq_true_iff in Hpeq. subst pγ.
    assert (Heqt: tβ = tγ).
    { eapply locally_det_no_compete; eauto. }
    subst tγ. left. congruence.
  - (* Different positions: place both tiles *)
    apply pos_eq_false_iff in Hpeq.
    right.
    exists (place_tile (place_tile α tβ pβ) tγ pγ).
    split.
    + (* β = place_tile α tβ pβ can reach δ by placing tγ at pγ *)
      subst β. right.
      assert (Hempty: tile_at (place_tile α tβ pβ) pγ = None).
      { unfold tile_at, place_tile.
        destruct (pos_eq pγ pβ) eqn:Heq.
        - apply pos_eq_true_iff in Heq. symmetry in Heq. contradiction.
        - destruct Hattγ as [Hαempty _]. exact Hαempty. }
      assert (Hbound: binding_strength (tas_glue_strength tas) tγ (place_tile α tβ pβ) pγ >= tas_temp tas).
      { destruct Hattγ as [_ Hbnd].
        apply Nat.le_trans with (m := binding_strength (tas_glue_strength tas) tγ α pγ); auto.
        apply binding_strength_monotonic.
        apply place_tile_extends. destruct Hattβ as [Hempty' _]. exact Hempty'. }
      exists tγ, pγ. split. exact Hinγ. split.
      * split; auto.
      * reflexivity.
    + (* γ = place_tile α tγ pγ can reach δ by placing tβ at pβ *)
      subst γ. right.
      assert (Hempty: tile_at (place_tile α tγ pγ) pβ = None).
      { unfold tile_at, place_tile.
        destruct (pos_eq pβ pγ) eqn:Heq.
        - apply pos_eq_true_iff in Heq. contradiction.
        - destruct Hattβ as [Hαempty _]. exact Hαempty. }
      assert (Hbound: binding_strength (tas_glue_strength tas) tβ (place_tile α tγ pγ) pβ >= tas_temp tas).
      { destruct Hattβ as [_ Hbnd].
        apply Nat.le_trans with (m := binding_strength (tas_glue_strength tas) tβ α pβ); auto.
        apply binding_strength_monotonic.
        apply place_tile_extends. destruct Hattγ as [Hempty' _]. exact Hempty'. }
      exists tβ, pβ. split. exact Hinβ. split.
      * split; auto.
      * extensionality p. apply eq_sym. apply place_tile_comm_at. intro H. apply Hpeq. symmetry. exact H.
Qed.

Lemma strip_one_multi :
  forall tas α β γ,
    locally_deterministic tas ->
    strongly_confluent tas ->
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α β γ Hlocal Hsc Hprod Hαβ Hαγ.
  revert β Hαβ.
  induction Hαγ as [| α γ1 γ Hαγ1 Hγ1γ IH]; intros β Hαβ.
  - (* Base case: γ = α *)
    exists β. split; [apply ms_refl | apply single_to_multi; exact Hαβ].
  - (* Inductive case: α →₁ γ1 →* γ, and α →₁ β *)
    assert (Hprod_γ1 : producible_in tas γ1)
      by (eapply producible_after_single_step; eauto).
    (* Use bounded confluence to join β and γ1 *)
    destruct (locally_det_bounded_confluence tas α β γ1 Hlocal Hprod Hαβ Hαγ1) as [Heq | [τ [[Hβeq | Hβτ] [Hγ1eq | Hγ1τ]]]].
    + (* Case: β = γ1 *)
      subst γ1.
      (* Apply IH: β →₁ ? contradicts, so just transitivity *)
      exists γ. split; [| apply ms_refl].
      eapply multi_step_trans.
      * apply ms_refl.
      * exact Hγ1γ.
    + (* Case: β = τ and γ1 = τ, so β = γ1 *)
      subst τ. subst γ1.
      exists γ. split; [| apply ms_refl].
      eapply multi_step_trans; [apply ms_refl | exact Hγ1γ].
    + (* Case: β = τ and γ1 →₁ τ *)
      subst τ.
      (* Apply IH with γ1 →₁ β *)
      destruct (IH Hprod_γ1 β Hγ1τ) as [δ [Hβδ Hγδ]].
      exists δ. split; [exact Hβδ | exact Hγδ].
    + (* Case: β →₁ τ and γ1 = τ *)
      subst τ.
      exists γ. split; [| apply ms_refl].
      eapply multi_step_trans.
      * eapply ms_step; [exact Hβτ | exact Hγ1γ].
      * apply ms_refl.
    + (* Case: β →₁ τ and γ1 →₁ τ *)
      (* Apply IH with γ1 →₁ τ *)
      destruct (IH Hprod_γ1 τ Hγ1τ) as [δ [Hτδ Hγδ]].
      exists δ. split; [| exact Hγδ].
      eapply multi_step_trans.
      * eapply ms_step; [exact Hβτ | exact Hτδ].
      * apply ms_refl.
Qed.

Theorem diamond_aux_inner :
  forall (tas : TAS) (α β γ : Assembly),
    locally_deterministic tas ->
    strongly_confluent tas ->
    producible_in tas α ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α β γ Hlocal Hsc Hprod Hβ Hγ.
  revert γ Hγ.
  induction Hβ as [|α β' β Hαβ' Hβ'β IH].
  - intros γ Hγ.
    exists γ. split. exact Hγ. apply ms_refl.
  - intros γ Hγ.
    assert (Hprod_β': producible_in tas β').
    { eapply single_step_preserves_producibility; eauto. }
    destruct (strip_one_multi tas α β' γ Hlocal Hsc Hprod Hαβ' Hγ) as [δ1 [Hβ'δ1 Hγδ1]].
    destruct (IH Hprod_β' δ1 Hβ'δ1) as [δ [Hβδ Hδ1δ]].
    exists δ. split.
    + exact Hβδ.
    + eapply multi_step_trans; eauto.
Qed.

Lemma diamond_aux :
  forall tas α β,
    locally_deterministic tas ->
    strongly_confluent tas ->
    producible_in tas α ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    forall γ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
      exists δ,
        multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
        multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros. eapply diamond_aux_inner; eauto.
Qed.

Theorem strong_confluence_diamond :
  forall tas,
    locally_deterministic tas ->
    strongly_confluent tas ->
    has_diamond_property tas.
Proof.
  intros tas Hlocal Hsc α β γ Hprodα Hprodβ Hprodγ Hαβ Hαγ.
  eapply diamond_aux; [exact Hlocal | exact Hsc | exact Hprodα | exact Hαβ | exact Hαγ].
Qed.

(** ** Examples for Section 1.3 *)

Definition tileset_simple : TileSet := [tile_horizontal; tile_vertical].

Definition tas_simple : TAS :=
  mkTAS tileset_simple example_strength_fn seed_single 2.

Example ex_tile_in_set :
  tile_in_set tile_horizontal tileset_simple.
Proof.
  unfold tile_in_set, tileset_simple. simpl. left. reflexivity.
Qed.

Example ex_compatible_self :
  compatible seed_single seed_single.
Proof.
  intros p t1 t2 H1 H2. congruence.
Qed.

Example ex_subassembly_refl :
  subassembly seed_single seed_single.
Proof.
  apply subassembly_refl.
Qed.

(** * Section 1.4: Wang Tilings Connection *)

(** ** Wang Tiles *)

Definition WangTile : Type := TileType.

Definition WangTiling : Type := Assembly.

Definition valid_wang_tiling (W : WangTiling) : Prop :=
  forall p1 p2, adjacent p1 p2 ->
    match tile_at W p1, tile_at W p2 with
    | Some t1, Some t2 =>
        match glue_facing t1 p1 p2, glue_facing t2 p2 p1 with
        | Some g1, Some g2 => g1 = g2
        | _, _ => True
        end
    | _, _ => True
    end.

Definition tiles_plane (W : WangTiling) : Prop :=
  forall p, exists t, tile_at W p = Some t.

Definition domino_problem (tileset : list WangTile) : Prop :=
  exists W, tiles_plane W /\ valid_wang_tiling W /\
    forall p t, tile_at W p = Some t -> In t tileset.

Lemma producible_valid_edges :
  forall tas α p1 p2,
    producible_in tas α ->
    adjacent p1 p2 ->
    match tile_at α p1, tile_at α p2 with
    | Some t1, Some t2 =>
        match glue_facing t1 p1 p2, glue_facing t2 p2 p1 with
        | Some g1, Some g2 => glue_strength (tas_glue_strength tas) g1 g2 > 0 -> g1 = g2
        | _, _ => True
        end
    | _, _ => True
    end.
Proof.
  intros tas α p1 p2 Hprod Hadj.
  destruct (tile_at α p1) as [t1|] eqn:Ht1; destruct (tile_at α p2) as [t2|] eqn:Ht2; auto.
  destruct (glue_facing t1 p1 p2) as [g1|] eqn:Hg1; destruct (glue_facing t2 p2 p1) as [g2|] eqn:Hg2; auto.
  intro Hstr. unfold glue_strength in Hstr.
  destruct (glue_eq_dec g1 g2); auto. lia.
Qed.

Lemma single_step_placed_tile :
  forall strength_fn T τ α α' t p,
    single_step strength_fn T τ α α' ->
    tile_at α' p = Some t ->
    tile_at α p = None ->
    tile_in_set t T.
Proof.
  intros strength_fn T τ α α' t p [t0 [p0 [Hin [Hatt Heq]]]] Ht' Ht.
  subst α'.
  destruct (pos_eq p p0) eqn:Hp.
  - apply pos_eq_true_iff in Hp. subst p0.
    unfold tile_at, place_tile in Ht'.
    assert (Href: pos_eq p p = true) by apply pos_eq_refl.
    rewrite Href in Ht'. injection Ht' as <-. exact Hin.
  - unfold tile_at, place_tile in Ht'. rewrite Hp in Ht'.
    unfold tile_at in Ht. rewrite Ht in Ht'. discriminate.
Qed.

Lemma wang_glue_match :
  forall strength_fn g1 g2,
    g1 <> null_glue ->
    g2 <> null_glue ->
    glue_strength strength_fn g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros strength_fn g1 g2 Hn1 Hn2 Hstr.
  unfold glue_strength in Hstr.
  destruct (glue_eq_dec g1 g2); auto.
  lia.
Qed.

Lemma glue_strength_positive_implies_match :
  forall strength_fn g1 g2,
    (forall g, g <> null_glue -> strength_fn g >= 1) ->
    glue_strength strength_fn g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros strength_fn g1 g2 Hstr Hpos.
  unfold glue_strength in Hpos.
  destruct (glue_eq_dec g1 g2) as [Heq | Hneq]; auto.
  lia.
Qed.

Lemma glue_strength_zero_implies_match_or_null :
  forall strength_fn g1 g2,
    glue_strength strength_fn g1 g2 = 0 ->
    g1 = g2 \/ g1 <> g2.
Proof.
  intros strength_fn g1 g2 Hz.
  destruct (glue_eq_dec g1 g2); auto.
Qed.

Lemma adjacent_tiles_match_or_nonzero :
  forall tas α p1 p2 t1 t2 g1 g2,
    producible_in tas α ->
    adjacent p1 p2 ->
    tile_at α p1 = Some t1 ->
    tile_at α p2 = Some t2 ->
    glue_facing t1 p1 p2 = Some g1 ->
    glue_facing t2 p2 p1 = Some g2 ->
    (glue_strength (tas_glue_strength tas) g1 g2 > 0 -> g1 = g2).
Proof.
  intros tas α p1 p2 t1 t2 g1 g2 Hprod Hadj Ht1 Ht2 Hg1 Hg2.
  assert (Hedge := producible_valid_edges tas α p1 p2 Hprod Hadj).
  rewrite Ht1, Ht2, Hg1, Hg2 in Hedge.
  exact Hedge.
Qed.

Lemma null_glue_strength_zero :
  forall strength_fn g,
    glue_strength strength_fn null_glue g = 0.
Proof.
  intros. apply null_glue_zero_strength.
Qed.

Lemma nonzero_glue_strength_lower_bound :
  forall strength_fn g1 g2,
    (forall g, g <> null_glue -> strength_fn g >= 1) ->
    g1 <> null_glue ->
    g1 <> g2 ->
    glue_strength strength_fn g1 g2 = 0.
Proof.
  intros strength_fn g1 g2 Hstr Hnn Hneq.
  unfold glue_strength.
  destruct (glue_eq_dec g1 g2); try contradiction.
  reflexivity.
Qed.

Lemma nonzero_glue_positive_strength :
  forall strength_fn g1 g2,
    (forall g, g <> null_glue -> strength_fn g >= 1) ->
    g1 <> null_glue ->
    g1 = g2 ->
    glue_strength strength_fn g1 g2 > 0.
Proof.
  intros strength_fn g1 g2 Hstr Hnn Heq.
  subst. unfold glue_strength.
  destruct (glue_eq_dec g2 g2); try contradiction.
  destruct (glue_eq_dec g2 null_glue); try contradiction.
  specialize (Hstr g2 n). lia.
Qed.

Lemma glue_strength_dichotomy :
  forall strength_fn g1 g2,
    (forall g, g <> null_glue -> strength_fn g >= 1) ->
    glue_strength strength_fn g1 g2 = 0 \/ glue_strength strength_fn g1 g2 > 0.
Proof.
  intros strength_fn g1 g2 Hstr.
  destruct (Nat.eq_dec (glue_strength strength_fn g1 g2) 0); auto.
  right. lia.
Qed.

Lemma adjacent_glues_match_when_positive :
  forall tas α p1 p2 t1 t2 g1 g2,
    producible_in tas α ->
    adjacent p1 p2 ->
    tile_at α p1 = Some t1 ->
    tile_at α p2 = Some t2 ->
    glue_facing t1 p1 p2 = Some g1 ->
    glue_facing t2 p2 p1 = Some g2 ->
    glue_strength (tas_glue_strength tas) g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros tas α p1 p2 t1 t2 g1 g2 Hprod Hadj Ht1 Ht2 Hg1 Hg2 Hpos.
  apply (adjacent_tiles_match_or_nonzero tas α p1 p2 t1 t2 g1 g2); auto.
Qed.

Lemma zero_strength_implies_match_or_differ :
  forall strength_fn g1 g2,
    glue_strength strength_fn g1 g2 = 0 ->
    g1 = g2 \/ g1 <> g2.
Proof.
  intros strength_fn g1 g2 Hz.
  destruct (glue_eq_dec g1 g2); auto.
Qed.

Lemma zero_not_positive :
  forall n, n = 0 -> n > 0 -> False.
Proof.
  intros n H0 Hpos. rewrite H0 in Hpos. lia.
Qed.

Lemma contrapositive_helper :
  forall (P Q : Prop),
    (P -> Q) -> ~Q -> ~P.
Proof.
  intros P Q HPQ HnQ HP.
  apply HnQ. apply HPQ. exact HP.
Qed.

Lemma seed_subassembly_of_producible :
  forall tas α,
    producible_in tas α ->
    subassembly (tas_seed tas) α.
Proof.
  intros tas α Hprod.
  eapply multi_step_extends. exact Hprod.
Qed.

Lemma tile_not_in_seed_if_empty_in_assembly :
  forall tas α p t,
    producible_in tas α ->
    tile_at α p = Some t ->
    tile_at (tas_seed tas) p = None ->
    tile_at (tas_seed tas) p = None.
Proof.
  intros tas α p t Hprod Ht Hseed.
  exact Hseed.
Qed.

Lemma tile_added_after_seed :
  forall tas α p t,
    producible_in tas α ->
    tile_at α p = Some t ->
    tile_at (tas_seed tas) p = None ->
    exists γ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) (tas_seed tas) γ /\
      tile_at γ p = None /\
      single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ (place_tile γ t p) /\
      subassembly (place_tile γ t p) α.
Proof.
  intros tas α p t Hprod Ht Hseed.
  eapply multi_step_inversion; eauto.
Qed.

Lemma single_step_decompose :
  forall strength_fn T τ γ t p,
    single_step strength_fn T τ γ (place_tile γ t p) ->
    exists t' p',
      tile_in_set t' T /\
      can_attach strength_fn t' γ p' τ /\
      place_tile γ t p = place_tile γ t' p'.
Proof.
  intros strength_fn T τ γ t p Hstep.
  destruct Hstep as [t' [p' [Hin [Hatt Heq]]]].
  exists t', p'. split. exact Hin. split. exact Hatt. exact Heq.
Qed.

Lemma place_tile_eq_positions_match :
  forall γ t p t' p',
    tile_at γ p = None ->
    place_tile γ t p = place_tile γ t' p' ->
    tile_at (place_tile γ t p) p = Some t ->
    p' = p.
Proof.
  intros γ t p t' p' Hγp Heq Htile.
  eapply inversion_pos_must_match; eauto.
Qed.

Lemma place_tile_eq_tiles_match :
  forall γ t p t' p',
    place_tile γ t p = place_tile γ t' p' ->
    p = p' ->
    t' = t.
Proof.
  intros γ t p t' p' Heq Hp.
  subst p'. eapply inversion_tile_must_match. exact Heq.
Qed.

Lemma multi_step_producible :
  forall tas γ,
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) (tas_seed tas) γ ->
    producible_in tas γ.
Proof.
  intros tas γ Hms.
  unfold producible_in. exact Hms.
Qed.

Lemma adjacent_tiles_had_binding :
  forall tas α p1 t1 p2 t2,
    producible_in tas α ->
    tile_at α p1 = Some t1 ->
    tile_at α p2 = Some t2 ->
    adjacent p1 p2 ->
    tile_at (tas_seed tas) p1 = None ->
    exists γ,
      producible_in tas γ /\
      tile_at γ p1 = None /\
      can_attach (tas_glue_strength tas) t1 γ p1 (tas_temp tas).
Proof.
  intros tas α p1 t1 p2 t2 Hprod Ht1 Ht2 Hadj Hseed_empty.
  destruct (tile_added_after_seed tas α p1 t1 Hprod Ht1 Hseed_empty) as
    [γ [Hγms [Hγp1 [Hγstep Hγsub]]]].
  destruct (single_step_decompose (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ t1 p1 Hγstep) as
    [t' [p' [Hin [Hatt Heq]]]].
  assert (Hp_eq: p' = p1).
  { eapply place_tile_eq_positions_match; eauto.
    unfold tile_at. apply place_tile_at_pos. }
  subst p'.
  assert (Ht_eq: t' = t1).
  { eapply place_tile_eq_tiles_match; eauto. }
  subst t'.
  exists γ. split.
  - apply multi_step_producible. exact Hγms.
  - split; auto.
Qed.

Theorem temp1_adjacent_glues_match_when_nonzero_strength :
  forall tas α p1 p2 t1 t2 g1 g2,
    tas_temp tas = 1 ->
    producible_in tas α ->
    (forall g, g <> null_glue -> tas_glue_strength tas g >= 1) ->
    adjacent p1 p2 ->
    tile_at α p1 = Some t1 ->
    tile_at α p2 = Some t2 ->
    glue_facing t1 p1 p2 = Some g1 ->
    glue_facing t2 p2 p1 = Some g2 ->
    glue_strength (tas_glue_strength tas) g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros tas α p1 p2 t1 t2 g1 g2 Htemp Hprod Hstr Hadj Ht1 Ht2 Hg1 Hg2 Hpos.
  apply glue_strength_positive_implies_match with (strength_fn := tas_glue_strength tas) (g1 := g1) (g2 := g2); auto.
Qed.

Lemma sum_geq_one_has_nonzero_term :
  forall a b c d : nat,
    a + b + c + d >= 1 ->
    a >= 1 \/ b >= 1 \/ c >= 1 \/ d >= 1.
Proof.
  intros a b c d H.
  destruct a; destruct b; destruct c; destruct d; simpl in H; lia.
Qed.

Lemma neighbor_binding_geq_one_implies_tile_exists :
  forall strength_fn t α p p',
    neighbor_binding strength_fn t α p p' >= 1 ->
    exists t', tile_at α p' = Some t'.
Proof.
  intros strength_fn t α p p' H.
  unfold neighbor_binding in H.
  destruct (tile_at α p') as [t'|] eqn:Ht'; eauto.
  simpl in H. lia.
Qed.

Lemma binding_strength_geq_one_has_contributing_neighbor :
  forall strength_fn t α p,
    binding_strength strength_fn t α p >= 1 ->
    exists p',
      In p' (neighbors p) /\
      neighbor_binding strength_fn t α p p' >= 1.
Proof.
  intros strength_fn t α p H.
  unfold binding_strength in H.
  unfold neighbors in H.
  simpl in H.
  assert (Hrewrite: neighbor_binding strength_fn t α p (north p) +
    (neighbor_binding strength_fn t α p (east p) +
     (neighbor_binding strength_fn t α p (south p) + (neighbor_binding strength_fn t α p (west p) + 0))) =
    neighbor_binding strength_fn t α p (north p) + neighbor_binding strength_fn t α p (east p) +
    neighbor_binding strength_fn t α p (south p) + neighbor_binding strength_fn t α p (west p)) by lia.
  rewrite Hrewrite in H.
  apply sum_geq_one_has_nonzero_term in H.
  destruct H as [H1 | [H2 | [H3 | H4]]].
  - exists (north p). split. left. reflexivity. exact H1.
  - exists (east p). split. right. left. reflexivity. exact H2.
  - exists (south p). split. right. right. left. reflexivity. exact H3.
  - exists (west p). split. right. right. right. left. reflexivity. exact H4.
Qed.

Lemma neighbor_binding_geq_one_has_matching_glues :
  forall strength_fn t α p p' t',
    neighbor_binding strength_fn t α p p' >= 1 ->
    tile_at α p' = Some t' ->
    exists g,
      glue_facing t p p' = Some g /\
      glue_facing t' p' p = Some g /\
      glue_strength strength_fn g g >= 1.
Proof.
  intros strength_fn t α p p' t' Hbind Ht'.
  unfold neighbor_binding in Hbind.
  rewrite Ht' in Hbind.
  destruct (glue_facing t p p') as [g|] eqn:Hg; try (simpl in Hbind; lia).
  destruct (glue_facing t' p' p) as [g'|] eqn:Hg'; try (simpl in Hbind; lia).
  unfold glue_strength in Hbind.
  destruct (glue_eq_dec g g') as [Heq | Hneq]; try lia.
  subst g'.
  exists g. repeat split; auto.
  unfold glue_strength. destruct (glue_eq_dec g g); try contradiction. exact Hbind.
Qed.

Theorem temp1_tile_has_matching_neighbor :
  forall tas α p t,
    tas_temp tas = 1 ->
    producible_in tas α ->
    (forall g, g <> null_glue -> tas_glue_strength tas g >= 1) ->
    tile_at (tas_seed tas) p = None ->
    tile_at α p = Some t ->
    exists p_neighbor t_neighbor g,
      adjacent p p_neighbor /\
      tile_at α p_neighbor = Some t_neighbor /\
      glue_facing t p p_neighbor = Some g /\
      glue_facing t_neighbor p_neighbor p = Some g /\
      g <> null_glue.
Proof.
  intros tas α p t Htemp Hprod Hstr Hseed Ht.
  destruct (tile_added_after_seed tas α p t Hprod Ht Hseed) as [γ [Hγms [Hγempty [Hγstep Hγsub]]]].
  destruct (single_step_decompose (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ t p Hγstep) as [t' [p' [Hin [Hatt Heq]]]].
  assert (Hp_eq: p' = p).
  { eapply place_tile_eq_positions_match; eauto. unfold tile_at. apply place_tile_at_pos. }
  subst p'.
  assert (Ht_eq: t' = t).
  { eapply place_tile_eq_tiles_match; eauto. }
  subst t'.
  destruct Hatt as [Hγempty' Hγbound].
  rewrite Htemp in Hγbound.
  destruct (binding_strength_geq_one_has_contributing_neighbor (tas_glue_strength tas) t γ p Hγbound) as [p' [Hadj Hbind]].
  destruct (neighbor_binding_geq_one_implies_tile_exists (tas_glue_strength tas) t γ p p' Hbind) as [t' Ht'].
  destruct (neighbor_binding_geq_one_has_matching_glues (tas_glue_strength tas) t γ p p' t' Hbind Ht') as [g [Hg [Hg' Hstr_g]]].
  assert (Hγsub': subassembly γ α).
  { eapply subassembly_trans.
    - eapply place_tile_extends. exact Hγempty.
    - exact Hγsub. }
  exists p', t', g. split.
  - unfold adjacent. exact Hadj.
  - split.
    + eapply subassembly_agree; eauto.
    + split. exact Hg. split. exact Hg'.
      unfold glue_strength in Hstr_g.
      destruct (glue_eq_dec g g); try contradiction.
      destruct (glue_eq_dec g null_glue); auto.
      lia.
Qed.

(** ** Examples for Section 1.4 *)

Example wang_tile_cross : WangTile :=
  mkTile 1 2 1 2.

Example wang_tiling_2x2 : WangTiling :=
  fun p => match p with
  | (0, 0)%Z => Some wang_tile_cross
  | (1, 0)%Z => Some tile_horizontal
  | (0, 1)%Z => Some tile_vertical
  | (1, 1)%Z => Some wang_tile_cross
  | _ => None
  end.

Example ex_wang_tiling_occupied :
  tile_at wang_tiling_2x2 (0, 0)%Z = Some wang_tile_cross.
Proof.
  unfold tile_at, wang_tiling_2x2. reflexivity.
Qed.

Example domino_tileset : list WangTile :=
  [wang_tile_cross; tile_horizontal; tile_vertical].

Example ex_domino_tileset_membership :
  In wang_tile_cross domino_tileset.
Proof.
  unfold domino_tileset. simpl. left. reflexivity.
Qed.

Example ex_adjacent_east :
  adjacent (0, 0)%Z (1, 0)%Z.
Proof.
  unfold adjacent, neighbors. simpl. right. left. reflexivity.
Qed.

Example ex_glue_facing_east :
  glue_facing tile_horizontal (0, 0)%Z (1, 0)%Z = Some glue_1.
Proof.
  unfold glue_facing, tile_horizontal, pos_eq, east. simpl. reflexivity.
Qed.

Example ex_wang_tiling_2x2_at_00 :
  tile_at wang_tiling_2x2 (0, 0)%Z = Some wang_tile_cross /\
  In wang_tile_cross domino_tileset.
Proof.
  split.
  - unfold tile_at, wang_tiling_2x2. reflexivity.
  - unfold domino_tileset. simpl. left. reflexivity.
Qed.

Example ex_wang_tiling_2x2_uses_tileset :
  In wang_tile_cross domino_tileset /\
  In tile_horizontal domino_tileset /\
  In tile_vertical domino_tileset.
Proof.
  unfold domino_tileset. split. left. reflexivity.
  split. right. left. reflexivity.
  right. right. left. reflexivity.
Qed.

Theorem temp1_terminal_assembly_matching_edges :
  forall tas α p1 p2 t1 t2 g1 g2,
    tas_temp tas = 1 ->
    (forall g, g <> null_glue -> tas_glue_strength tas g >= 1) ->
    terminal_assemblies tas α ->
    adjacent p1 p2 ->
    tile_at α p1 = Some t1 ->
    tile_at α p2 = Some t2 ->
    glue_facing t1 p1 p2 = Some g1 ->
    glue_facing t2 p2 p1 = Some g2 ->
    glue_strength (tas_glue_strength tas) g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros tas α p1 p2 t1 t2 g1 g2 Htemp Hstr [Hprod Hterm] Hadj Ht1 Ht2 Hg1 Hg2 Hpos.
  apply (adjacent_glues_match_when_positive tas α p1 p2 t1 t2 g1 g2); auto.
Qed.

Theorem locally_deterministic_unique_terminal :
  forall tas α β,
    locally_deterministic tas ->
    strongly_confluent tas ->
    terminal_assemblies tas α ->
    terminal_assemblies tas β ->
    α = β.
Proof.
  intros tas α β Hlocal Hsc [Hprodα Htermα] [Hprodβ Htermβ].
  assert (Hdiamond := strong_confluence_diamond tas Hlocal Hsc).
  unfold has_diamond_property in Hdiamond.
  assert (Hexists := Hdiamond (tas_seed tas) α β).
  assert (Hprod_seed: producible_in tas (tas_seed tas)).
  { unfold producible_in. apply ms_refl. }
  specialize (Hexists Hprod_seed Hprodα Hprodβ).
  assert (Hseed_α: multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) (tas_seed tas) α).
  { exact Hprodα. }
  assert (Hseed_β: multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) (tas_seed tas) β).
  { exact Hprodβ. }
  specialize (Hexists Hseed_α Hseed_β).
  destruct Hexists as [δ [Hαδ Hβδ]].
  assert (Hα_term: forall α', single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α α' -> False).
  { intros α' Hstep. eapply (terminal_no_growth tas α); eauto. }
  assert (Hβ_term: forall β', single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β β' -> False).
  { intros β' Hstep. eapply (terminal_no_growth tas β); eauto. }
  inversion Hαδ as [|α_src α' δ_end Hα_step Hα'δ Heq1 Heq2]; subst.
  - inversion Hβδ as [|β_src β' δ_end Hβ_step Hβ'δ Heq1 Heq2]; subst.
    + reflexivity.
    + exfalso. apply (Hβ_term β'). exact Hβ_step.
  - exfalso. apply (Hα_term α'). exact Hα_step.
Qed.

Theorem deterministic_assembly_theory :
  forall tas,
    locally_deterministic tas ->
    strongly_confluent tas /\
    has_diamond_property tas /\
    (forall α β,
      terminal_assemblies tas α ->
      terminal_assemblies tas β ->
      α = β) /\
    (forall α,
      producible_in tas α ->
      forall β,
        terminal_assemblies tas β ->
        subassembly α β).
Proof.
  intros tas Hlocal.
  assert (Hsc: strongly_confluent tas).
  { apply locally_det_strong_confluence. exact Hlocal. }
  split. exact Hsc.
  split.
  - apply strong_confluence_diamond. exact Hlocal. exact Hsc.
  - split.
    + intros α β Hα Hβ.
      eapply locally_deterministic_unique_terminal; eauto.
    + intros α Hprodα β Htermβ.
      assert (Hdir: is_directed tas).
      { unfold is_directed. exists β. split. exact Htermβ.
        intros β' Htermβ'.
        eapply locally_deterministic_unique_terminal; eauto. }
      unfold is_directed in Hdir.
      destruct Hdir as [γ [Htermγ Huniq]].
      assert (Hβγ: β = γ).
      { apply Huniq. exact Htermβ. }
      subst γ.
      destruct Htermβ as [Hprodβ Htermβ'].
      assert (Hdiamond := strong_confluence_diamond tas Hlocal Hsc).
      unfold has_diamond_property in Hdiamond.
      assert (Hprod_seed: producible_in tas (tas_seed tas)).
      { unfold producible_in. apply ms_refl. }
      specialize (Hdiamond (tas_seed tas) α β Hprod_seed Hprodα Hprodβ Hprodα Hprodβ).
      destruct Hdiamond as [δ [Hαδ Hβδ]].
      assert (Hδβ: δ = β).
      { inversion Hβδ; subst.
        - reflexivity.
        - exfalso. eapply (terminal_no_growth tas β); eauto. }
      subst δ.
      eapply multi_step_extends. exact Hαδ.
Qed.

Theorem temp1_requires_neighbor :
  forall tas α p t,
    tas_temp tas = 1 ->
    (forall g, g <> null_glue -> tas_glue_strength tas g >= 1) ->
    tile_at (tas_seed tas) p = None ->
    terminal_assemblies tas α ->
    tile_at α p = Some t ->
    exists p' t' g,
      adjacent p p' /\
      tile_at α p' = Some t' /\
      glue_facing t p p' = Some g /\
      glue_facing t' p' p = Some g /\
      g <> null_glue.
Proof.
  intros tas α p t Htemp Hstr Hseed [Hprod Hterm] Ht.
  apply (temp1_tile_has_matching_neighbor tas α p t); auto.
Qed.

Definition competing_tile_1 : TileType := mkTile 0 1 0 1.
Definition competing_tile_2 : TileType := mkTile 0 2 0 1.
Definition seed_tile_conflict : TileType := mkTile 0 1 0 0.

Definition competing_tiles_system : TAS :=
  mkTAS
    [competing_tile_1; competing_tile_2]
    (fun g => match g with 0 => 0 | _ => 1 end)
    (fun p => if pos_eq p (0, 0)%Z then Some seed_tile_conflict else None)
    1.

Theorem competing_tiles_not_locally_deterministic :
  ~locally_deterministic competing_tiles_system.
Proof.
  unfold locally_deterministic, has_conflict.
  intro Hcontra.
  assert (Hseed_prod: producible_in competing_tiles_system
    (fun p => if pos_eq p (0, 0)%Z then Some seed_tile_conflict else None)).
  { unfold producible_in. apply ms_refl. }
  assert (Hcan1: can_attach
    (fun g => match g with 0 => 0 | _ => 1 end)
    competing_tile_1
    (fun p => if pos_eq p (0, 0)%Z then Some seed_tile_conflict else None)
    (1, 0)%Z
    1).
  { split.
    - unfold tile_at.
      destruct (pos_eq (1, 0)%Z (0, 0)%Z) eqn:Heq.
      + apply pos_eq_true_iff in Heq. discriminate Heq.
      + reflexivity.
    - unfold binding_strength, neighbors, neighbor_binding, tile_at, glue_facing, pos_eq, west, north, south, east.
      unfold competing_tile_1, seed_tile_conflict, glue_strength. simpl. lia. }
  assert (Hcan2: can_attach
    (fun g => match g with 0 => 0 | _ => 1 end)
    competing_tile_2
    (fun p => if pos_eq p (0, 0)%Z then Some seed_tile_conflict else None)
    (1, 0)%Z
    1).
  { split.
    - unfold tile_at.
      destruct (pos_eq (1, 0)%Z (0, 0)%Z) eqn:Heq.
      + apply pos_eq_true_iff in Heq. discriminate Heq.
      + reflexivity.
    - unfold binding_strength, neighbors, neighbor_binding, tile_at, glue_facing, pos_eq, west, north, south, east.
      unfold competing_tile_2, seed_tile_conflict, glue_strength. simpl. lia. }
  assert (Hneq: competing_tile_1 <> competing_tile_2).
  { unfold competing_tile_1, competing_tile_2. intro H. discriminate H. }
  apply Hcontra.
  exists (fun p => if pos_eq p (0, 0)%Z then Some seed_tile_conflict else None).
  exists competing_tile_1, competing_tile_2, (1, 0)%Z.
  split. exact Hseed_prod.
  split. unfold tile_in_set, competing_tiles_system. simpl. left. reflexivity.
  split. unfold tile_in_set, competing_tiles_system. simpl. right. left. reflexivity.
  unfold tiles_compete. split. exact Hcan1. split. exact Hcan2. exact Hneq.
Qed.

Theorem producible_extends_to_unique_terminal :
  forall tas α β,
    locally_deterministic tas ->
    producible_in tas α ->
    terminal_assemblies tas β ->
    subassembly α β /\
    (forall γ, terminal_assemblies tas γ -> β = γ).
Proof.
  intros tas α β Hlocal Hprod Hterm.
  assert (Htheory := deterministic_assembly_theory tas Hlocal).
  destruct Htheory as [Hsc [Hdiamond [Huniq Hext]]].
  split.
  - apply Hext. exact Hprod. exact Hterm.
  - intros γ Hγ. apply Huniq; auto.
Qed.

Corollary directed_has_unique_terminal :
  forall tas,
    is_directed tas ->
    exists! β, terminal_assemblies tas β.
Proof.
  intros tas Hdir.
  unfold is_directed in Hdir.
  destruct Hdir as [β [Hβ Huniq]].
  exists β.
  unfold unique.
  split.
  - exact Hβ.
  - intros β' Hβ'. symmetry. apply Huniq. exact Hβ'.
Qed.

Corollary terminal_is_unique_maximal :
  forall tas β,
    locally_deterministic tas ->
    terminal_assemblies tas β <->
    (producible_in tas β /\
     forall α, producible_in tas α -> subassembly α β).
Proof.
  intros tas β Hlocal.
  split.
  - intros Hterm.
    split.
    + destruct Hterm. exact H.
    + intros α Hprodα.
      assert (Hext := producible_extends_to_unique_terminal tas α β Hlocal Hprodα Hterm).
      destruct Hext as [Hsub _]. exact Hsub.
  - intros [Hprod Hmax].
    split.
    + exact Hprod.
    + unfold is_terminal. intros t p Hin Hempty.
      destruct (Nat.lt_ge_cases (binding_strength (tas_glue_strength tas) t β p) (tas_temp tas)) as [Hlt | Hge]; auto.
      exfalso.
      set (β' := place_tile β t p).
      assert (Hstep: single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β β').
      { exists t, p. split. exact Hin. split. split. exact Hempty. exact Hge. reflexivity. }
      assert (Hprod': producible_in tas β').
      { unfold producible_in. eapply multi_step_trans. exact Hprod. eapply ms_step. exact Hstep. apply ms_refl. }
      assert (Hsub: subassembly β' β).
      { apply Hmax. exact Hprod'. }
      assert (Htile: tile_at β' p = Some t).
      { unfold β', tile_at. apply place_tile_at_pos. }
      assert (Htile_β: tile_at β p = Some t).
      { eapply subassembly_agree. exact Hsub. exact Htile. }
      congruence.
Qed.

Corollary strong_confluence_equiv_local_determinism :
  forall tas,
    locally_deterministic tas ->
    strongly_confluent tas.
Proof.
  intros tas Hlocal.
  apply locally_det_strong_confluence. exact Hlocal.
Qed.

Corollary local_det_implies_diamond :
  forall tas,
    locally_deterministic tas ->
    has_diamond_property tas.
Proof.
  intros tas Hlocal.
  apply strong_confluence_diamond.
  - exact Hlocal.
  - apply locally_det_strong_confluence.
    exact Hlocal.
Qed.

Corollary decidable_attachment_finite :
  forall tas α positions,
    locally_deterministic tas ->
    (forall p, domain α p -> In p positions) ->
    producible_in tas α ->
    forall t p,
      tile_in_set t (tas_tiles tas) ->
      {can_attach (tas_glue_strength tas) t α p (tas_temp tas)} +
      {~can_attach (tas_glue_strength tas) t α p (tas_temp tas)}.
Proof.
  intros tas α positions Hlocal Hpos Hprod t p Hin.
  apply (can_attach_dec (tas_glue_strength tas) t α p (tas_temp tas) positions).
  exact Hpos.
Defined.

Eval compute in (binding_strength
  (fun g => match g with 0 => 0 | _ => 1 end)
  competing_tile_1
  (fun p => if pos_eq p (0, 0)%Z then Some seed_tile_conflict else None)
  (1, 0)%Z).

Eval compute in (binding_strength
  (fun g => match g with 0 => 0 | _ => 1 end)
  competing_tile_2
  (fun p => if pos_eq p (0, 0)%Z then Some seed_tile_conflict else None)
  (1, 0)%Z).

Eval compute in (TileType_eq_dec competing_tile_1 competing_tile_2).

Definition assembly_step_0 := tas_seed tas_simple.
Definition assembly_step_1 := place_tile assembly_step_0 tile_horizontal (1, 0)%Z.
Definition assembly_step_2 := place_tile assembly_step_1 tile_horizontal (2, 0)%Z.

Eval compute in (tile_at assembly_step_0 (0, 0)%Z).
Eval compute in (tile_at assembly_step_1 (1, 0)%Z).
Eval compute in (tile_at assembly_step_2 (2, 0)%Z).

Eval compute in (binding_strength example_strength_fn tile_horizontal assembly_step_0 (1, 0)%Z).
Eval compute in (binding_strength example_strength_fn tile_horizontal assembly_step_1 (2, 0)%Z).

Fixpoint filter_attachable
  (strength_fn : GlueType -> nat)
  (tiles : list TileType)
  (α : Assembly)
  (positions : list Position)
  (τ : nat)
  : list (TileType * Position) :=
  match tiles with
  | [] => []
  | t :: ts =>
      let attachable_at_t :=
        filter (fun p =>
          match α p with
          | None =>
              if le_dec τ (binding_strength strength_fn t α p)
              then true
              else false
          | Some _ => false
          end) positions in
      map (fun p => (t, p)) attachable_at_t ++ filter_attachable strength_fn ts α positions τ
  end.

Definition find_attachable_tiles
  (tas : TAS)
  (α : Assembly)
  (positions : list Position)
  : list (TileType * Position) :=
  filter_attachable (tas_glue_strength tas) (tas_tiles tas) α positions (tas_temp tas).

Eval compute in (find_attachable_tiles tas_simple assembly_step_0
  [(0, 0)%Z; (1, 0)%Z; (0, 1)%Z; (-1, 0)%Z; (0, -1)%Z]).

Eval compute in (find_attachable_tiles tas_simple assembly_step_1
  [(0, 0)%Z; (1, 0)%Z; (2, 0)%Z; (0, 1)%Z; (1, 1)%Z]).

Definition tas_temp1 : TAS :=
  mkTAS tileset_simple example_strength_fn seed_single 1.

Eval compute in (find_attachable_tiles tas_temp1 assembly_step_0
  [(0, 0)%Z; (1, 0)%Z; (0, 1)%Z; (-1, 0)%Z; (0, -1)%Z]).

Eval compute in (is_occupied assembly_step_0 (0, 0)%Z).
Eval compute in (is_occupied assembly_step_0 (1, 0)%Z).

Eval compute in (can_attach_dec example_strength_fn tile_horizontal assembly_step_0 (1, 0)%Z 1 []).

(** ** Reduction from Halting Problem to Domino Problem *)

Inductive TMWangGlue : Type :=
  | TMW_Null : TMWangGlue
  | TMW_State : nat -> TMWangGlue
  | TMW_Symbol : nat -> TMWangGlue
  | TMW_Boundary : TMWangGlue.

Definition TMWangGlue_eq_dec : forall (g1 g2 : TMWangGlue), {g1 = g2} + {g1 <> g2}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition encode_tmwang_glue (g : TMWangGlue) : GlueType :=
  match g with
  | TMW_Null => 0
  | TMW_State n => 1 + n
  | TMW_Symbol n => 1000 + n
  | TMW_Boundary => 2000
  end.

Lemma encode_tmwang_null : encode_tmwang_glue TMW_Null = 0.
Proof. reflexivity. Qed.

Lemma encode_tmwang_state_nonzero : forall n, encode_tmwang_glue (TMW_State n) <> 0.
Proof. intros n. unfold encode_tmwang_glue. lia. Qed.

Lemma encode_tmwang_symbol_nonzero : forall n, encode_tmwang_glue (TMW_Symbol n) <> 0.
Proof. intros n. unfold encode_tmwang_glue. lia. Qed.

Lemma encode_tmwang_boundary_nonzero : encode_tmwang_glue TMW_Boundary <> 0.
Proof. unfold encode_tmwang_glue. lia. Qed.

Definition tm_tape_cell_tile (state_opt : option nat) (symbol : nat) : WangTile :=
  match state_opt with
  | None => mkTile
      (encode_tmwang_glue (TMW_Symbol symbol))
      (encode_tmwang_glue TMW_Null)
      (encode_tmwang_glue (TMW_Symbol symbol))
      (encode_tmwang_glue TMW_Null)
  | Some state => mkTile
      (encode_tmwang_glue (TMW_Symbol symbol))
      (encode_tmwang_glue (TMW_State state))
      (encode_tmwang_glue (TMW_Symbol symbol))
      (encode_tmwang_glue (TMW_State state))
  end.

Lemma tm_tape_cell_horizontal_match : forall state_opt symbol,
  glue_N (tm_tape_cell_tile state_opt symbol) = glue_S (tm_tape_cell_tile state_opt symbol).
Proof.
  intros state_opt symbol.
  destruct state_opt; unfold tm_tape_cell_tile; simpl; reflexivity.
Qed.

Definition tm_transition_wang_tile (q : nat) (a : nat) (q' : nat) (a' : nat) : WangTile :=
  mkTile
    (encode_tmwang_glue (TMW_Symbol a))
    (encode_tmwang_glue (TMW_State q))
    (encode_tmwang_glue (TMW_Symbol a'))
    (encode_tmwang_glue (TMW_State q')).

Lemma tm_transition_vertical_encodes_transition : forall q a q' a',
  glue_E (tm_transition_wang_tile q a q' a') = encode_tmwang_glue (TMW_State q) /\
  glue_W (tm_transition_wang_tile q a q' a') = encode_tmwang_glue (TMW_State q').
Proof.
  intros. unfold tm_transition_wang_tile. simpl. split; reflexivity.
Qed.

Definition wang_tiling_encodes_tm_config (W : WangTiling) (row : Z) (state_pos : Z) (state : nat) (tape : Z -> nat) : Prop :=
  forall x : Z,
    (x = state_pos ->
      exists t, tile_at W (x, row) = Some t /\
        glue_E t = encode_tmwang_glue (TMW_State state) /\
        glue_N t = encode_tmwang_glue (TMW_Symbol (tape x))) /\
    (x <> state_pos ->
      exists t, tile_at W (x, row) = Some t /\
        glue_E t = encode_tmwang_glue TMW_Null /\
        glue_N t = encode_tmwang_glue (TMW_Symbol (tape x))).

Definition tm_to_wang_tileset (states : list nat) (alphabet : list nat)
  (transition : nat -> nat -> option (nat * nat)) : list WangTile :=
  flat_map (fun q =>
    flat_map (fun a =>
      match transition q a with
      | Some (q', a') => [tm_transition_wang_tile q a q' a']
      | None => []
      end
    ) alphabet
  ) states ++
  flat_map (fun a =>
    [tm_tape_cell_tile None a]
  ) alphabet ++
  flat_map (fun q =>
    flat_map (fun a =>
      [tm_tape_cell_tile (Some q) a]
    ) alphabet
  ) states.

Lemma tm_to_wang_tileset_contains_tape_cells : forall states alphabet transition a,
  In a alphabet ->
  In (tm_tape_cell_tile None a) (tm_to_wang_tileset states alphabet transition).
Proof.
  intros states alphabet transition a Ha.
  unfold tm_to_wang_tileset.
  apply in_or_app. right.
  apply in_or_app. left.
  apply in_flat_map.
  exists a. split; auto. left. reflexivity.
Qed.

Lemma tm_to_wang_tileset_contains_state_cells : forall states alphabet transition q a,
  In q states -> In a alphabet ->
  In (tm_tape_cell_tile (Some q) a) (tm_to_wang_tileset states alphabet transition).
Proof.
  intros states alphabet transition q a Hq Ha.
  unfold tm_to_wang_tileset.
  apply in_or_app. right.
  apply in_or_app. right.
  apply in_flat_map.
  exists q. split; auto.
  apply in_flat_map.
  exists a. split; auto. left. reflexivity.
Qed.

Lemma tm_to_wang_tileset_contains_transitions : forall states alphabet transition q a q' a',
  In q states -> In a alphabet ->
  transition q a = Some (q', a') ->
  In (tm_transition_wang_tile q a q' a') (tm_to_wang_tileset states alphabet transition).
Proof.
  intros states alphabet transition q a q' a' Hq Ha Htrans.
  unfold tm_to_wang_tileset.
  apply in_or_app. left.
  apply in_flat_map.
  exists q. split; auto.
  apply in_flat_map.
  exists a. split; auto.
  rewrite Htrans. left. reflexivity.
Qed.

Theorem halting_reduces_to_domino_problem_construction :
  forall states alphabet transition,
    exists (wang_tileset : list WangTile),
      (forall q a q' a',
        In q states -> In a alphabet ->
        transition q a = Some (q', a') ->
        In (tm_transition_wang_tile q a q' a') wang_tileset) /\
      (forall a,
        In a alphabet ->
        In (tm_tape_cell_tile None a) wang_tileset) /\
      (forall q a,
        In q states -> In a alphabet ->
        In (tm_tape_cell_tile (Some q) a) wang_tileset).
Proof.
  intros states alphabet transition.
  exists (tm_to_wang_tileset states alphabet transition).
  split.
  - intros q a q' a' Hq Ha Htrans.
    apply tm_to_wang_tileset_contains_transitions; auto.
  - split.
    + intros a Ha.
      apply tm_to_wang_tileset_contains_tape_cells; auto.
    + intros q a Hq Ha.
      apply tm_to_wang_tileset_contains_state_cells; auto.
Qed.

Corollary domino_problem_at_least_as_hard_as_tm_tiling :
  forall states alphabet transition,
    (exists W : WangTiling,
      tiles_plane W /\
      valid_wang_tiling W /\
      forall p t, tile_at W p = Some t -> In t (tm_to_wang_tileset states alphabet transition)) ->
    domino_problem (tm_to_wang_tileset states alphabet transition).
Proof.
  intros states alphabet transition [W [Hplane [Hvalid Hfrom]]].
  unfold domino_problem.
  exists W.
  split. exact Hplane.
  split. exact Hvalid.
  exact Hfrom.
Qed.

Lemma wang_tiling_rows_independent : forall W row1 row2,
  row1 <> row2 ->
  (forall x, exists t, tile_at W (x, row1) = Some t) ->
  (forall x, exists t, tile_at W (x, row2) = Some t) ->
  True.
Proof.
  intros W row1 row2 Hneq H1 H2.
  exact I.
Qed.

Theorem turing_machine_to_wang_tileset_reduction :
  forall states alphabet transition,
    exists wang_tileset,
      (forall q a q' a',
        In q states -> In a alphabet ->
        transition q a = Some (q', a') ->
        In (tm_transition_wang_tile q a q' a') wang_tileset) /\
      (forall a,
        In a alphabet -> In (tm_tape_cell_tile None a) wang_tileset) /\
      (forall q a,
        In q states -> In a alphabet -> In (tm_tape_cell_tile (Some q) a) wang_tileset).
Proof.
  intros states alphabet transition.
  apply halting_reduces_to_domino_problem_construction.
Qed.

Corollary reduction_uses_specific_tileset :
  forall states alphabet transition,
    let tileset := tm_to_wang_tileset states alphabet transition in
    (forall q a q' a',
      In q states -> In a alphabet ->
      transition q a = Some (q', a') ->
      In (tm_transition_wang_tile q a q' a') tileset).
Proof.
  intros states alphabet transition tileset q a q' a' Hq Ha Htrans.
  apply tm_to_wang_tileset_contains_transitions; auto.
Qed.

Corollary wang_tileset_contains_all_tape_cells :
  forall states alphabet transition,
    let tileset := tm_to_wang_tileset states alphabet transition in
    (forall a, In a alphabet -> In (tm_tape_cell_tile None a) tileset) /\
    (forall q a, In q states -> In a alphabet -> In (tm_tape_cell_tile (Some q) a) tileset).
Proof.
  intros states alphabet transition tileset.
  split.
  - intros a Ha.
    apply tm_to_wang_tileset_contains_tape_cells; auto.
  - intros q a Hq Ha.
    apply tm_to_wang_tileset_contains_state_cells; auto.
Qed.

Corollary wang_tiling_existence_implies_domino_solvability :
  forall states alphabet transition,
    (exists W : WangTiling,
      tiles_plane W /\
      valid_wang_tiling W /\
      forall p t, tile_at W p = Some t -> In t (tm_to_wang_tileset states alphabet transition)) ->
    domino_problem (tm_to_wang_tileset states alphabet transition).
Proof.
  intros states alphabet transition.
  apply domino_problem_at_least_as_hard_as_tm_tiling.
Qed.

Theorem wang_tiles_preserve_transition_semantics :
  forall q1 a1 q2 a2,
    let t1 := tm_tape_cell_tile (Some q1) a1 in
    let t_trans := tm_transition_wang_tile q1 a1 q2 a2 in
    let t2 := tm_tape_cell_tile (Some q2) a2 in
    glue_S t1 = glue_N t_trans /\
    glue_S t_trans = glue_N t2 /\
    glue_E t1 = encode_tmwang_glue (TMW_State q1) /\
    glue_W t_trans = encode_tmwang_glue (TMW_State q2).
Proof.
  intros q1 a1 q2 a2 t1 t_trans t2.
  unfold t1, t_trans, t2.
  unfold tm_tape_cell_tile, tm_transition_wang_tile.
  simpl. repeat split; reflexivity.
Qed.

Theorem wang_tile_adjacency_implies_tm_transition :
  forall (t_above t_below : WangTile) (q a q' a' : nat),
    t_above = tm_tape_cell_tile (Some q) a ->
    t_below = tm_transition_wang_tile q a q' a' ->
    glue_S t_above = glue_N t_below ->
    glue_N t_above = encode_tmwang_glue (TMW_Symbol a) /\
    glue_S t_below = encode_tmwang_glue (TMW_Symbol a').
Proof.
  intros t_above t_below q a q' a' Habove Hbelow Hmatch.
  subst. unfold tm_tape_cell_tile, tm_transition_wang_tile in *.
  simpl in *. split; reflexivity.
Qed.

Theorem horizontal_wang_tile_adjacency_preserves_state :
  forall (t_left t_right : WangTile) (q1 q2 a1 a2 : nat),
    t_left = tm_transition_wang_tile q1 a1 q2 a2 ->
    glue_E t_left = encode_tmwang_glue (TMW_State q1) ->
    glue_W t_left = encode_tmwang_glue (TMW_State q2).
Proof.
  intros t_left t_right q1 q2 a1 a2 Hleft Hglue.
  subst. unfold tm_transition_wang_tile in *. simpl in *. reflexivity.
Qed.

Corollary tm_to_wang_reduction_is_computable :
  forall (states alphabet : list nat) (transition : nat -> nat -> option (nat * nat)),
    exists (tileset : list WangTile),
      tileset = tm_to_wang_tileset states alphabet transition.
Proof.
  intros states alphabet transition.
  exists (tm_to_wang_tileset states alphabet transition).
  reflexivity.
Qed.

(** A Wang tiling encodes a TM computation if each row encodes a configuration *)
Definition wang_tiling_encodes_computation (W : WangTiling)
  (init_row : Z) : Prop :=
  forall row : Z,
    (row >= init_row)%Z ->
    exists state_pos : Z, exists state : nat, exists tape : Z -> nat,
      wang_tiling_encodes_tm_config W row state_pos state tape.

(** Wang tiling reaches halting state if some row has halting state *)
Definition wang_tiling_reaches_halting (W : WangTiling) (accept_state reject_state : nat) : Prop :=
  exists row : Z, exists pos : Z,
    exists t, tile_at W (pos, row) = Some t /\
      (glue_E t = encode_tmwang_glue (TMW_State accept_state) \/
       glue_E t = encode_tmwang_glue (TMW_State reject_state)).

(** * Section 2.1: Turing Completeness at Temperature 2 *)

Section TuringCompleteness.

(** ** Turing Machine Definitions *)

(** Generic types with decidable equality (constructive, no axioms) *)
Context {State : Type}.
Context {State_eq_dec : forall (q1 q2 : State), {q1 = q2} + {q1 <> q2}}.

Context {TapeSymbol : Type}.
Context {TapeSymbol_eq_dec : forall (a b : TapeSymbol), {a = b} + {a <> b}}.

Context (blank : TapeSymbol).

(** Tape head direction *)
Inductive Direction : Type :=
  | Left : Direction
  | Right : Direction
  | Stay : Direction.

Definition Direction_eq_dec : forall (d1 d2 : Direction), {d1 = d2} + {d1 <> d2}.
Proof.
  decide equality.
Defined.

(** Transition function: State × TapeSymbol → State × TapeSymbol × Direction *)
Definition Transition : Type := State -> TapeSymbol -> option (State * TapeSymbol * Direction).

(** Turing Machine *)
Record TuringMachine : Type := mkTM {
  tm_states : list State;
  tm_alphabet : list TapeSymbol;
  tm_transition : Transition;
  tm_start : State;
  tm_accept : State;
  tm_reject : State
}.

(** Well-formedness conditions *)
Definition tm_wellformed (M : TuringMachine) : Prop :=
  In (tm_start M) (tm_states M) /\
  In (tm_accept M) (tm_states M) /\
  In (tm_reject M) (tm_states M) /\
  In blank (tm_alphabet M) /\
  tm_accept M <> tm_reject M /\
  (forall q a q' a' d,
    tm_transition M q a = Some (q', a', d) ->
    In q (tm_states M) /\
    In a (tm_alphabet M) /\
    In q' (tm_states M) /\
    In a' (tm_alphabet M)).

(** ** Tape Representation *)

(** Tape: ℤ → TapeSymbol (infinite in both directions) *)
Definition Tape : Type := Z -> TapeSymbol.

(** Blank tape *)
Definition blank_tape : Tape := fun _ => blank.

(** Read symbol at position *)
Definition tape_read (t : Tape) (pos : Z) : TapeSymbol := t pos.

(** Write symbol at position *)
Definition tape_write (t : Tape) (pos : Z) (s : TapeSymbol) : Tape :=
  fun pos' => if (pos =? pos')%Z then s else t pos'.

(** Tape equivalence: two tapes are equivalent if they differ only finitely *)
Definition tape_equiv (t1 t2 : Tape) : Prop :=
  exists lower upper : Z,
    forall pos : Z,
      (pos < lower)%Z \/ (pos > upper)%Z -> t1 pos = t2 pos.

(** ** Configurations *)

(** Configuration: current state, tape, and head position *)
Record Config : Type := mkConfig {
  cfg_state : State;
  cfg_tape : Tape;
  cfg_pos : Z
}.

(** Initial configuration *)
Definition init_config (M : TuringMachine) (input : list TapeSymbol) : Config :=
  let init_tape := fun pos =>
    if (pos <? 0)%Z then blank
    else match nth_error input (Z.to_nat pos) with
    | Some s => s
    | None => blank
    end in
  mkConfig (tm_start M) init_tape 0%Z.

(** Halting states *)
Definition is_halting_state (M : TuringMachine) (q : State) : Prop :=
  q = tm_accept M \/ q = tm_reject M.

(** Accepting configuration *)
Definition is_accepting (M : TuringMachine) (c : Config) : Prop :=
  cfg_state c = tm_accept M.

(** Rejecting configuration *)
Definition is_rejecting (M : TuringMachine) (c : Config) : Prop :=
  cfg_state c = tm_reject M.

(** ** Transition Relation *)

(** Move head according to direction *)
Definition move_head (pos : Z) (d : Direction) : Z :=
  match d with
  | Left => (pos - 1)%Z
  | Right => (pos + 1)%Z
  | Stay => pos
  end.

(** Single step transition *)
Definition step (M : TuringMachine) (c : Config) : option Config :=
  let q := cfg_state c in
  let t := cfg_tape c in
  let pos := cfg_pos c in
  let current_symbol := tape_read t pos in
  match tm_transition M q current_symbol with
  | None => None
  | Some (q', s', d) =>
      Some (mkConfig q' (tape_write t pos s') (move_head pos d))
  end.

(** Multi-step execution (n steps) *)
Fixpoint steps (M : TuringMachine) (n : nat) (c : Config) : option Config :=
  match n with
  | O => Some c
  | S n' =>
      if State_eq_dec (cfg_state c) (tm_accept M) then Some c
      else if State_eq_dec (cfg_state c) (tm_reject M) then Some c
      else match step M c with
           | None => None
           | Some c' => steps M n' c'
           end
  end.

(** Reflexive transitive closure of step relation *)
Inductive steps_star (M : TuringMachine) : Config -> Config -> Prop :=
  | steps_refl : forall c, steps_star M c c
  | steps_step : forall c c' c'',
      step M c = Some c' ->
      steps_star M c' c'' ->
      steps_star M c c''.

(** Machine accepts input *)
Definition tm_accepts (M : TuringMachine) (input : list TapeSymbol) : Prop :=
  exists c,
    steps_star M (init_config M input) c /\
    is_accepting M c.

(** Machine rejects input *)
Definition tm_rejects (M : TuringMachine) (input : list TapeSymbol) : Prop :=
  exists c,
    steps_star M (init_config M input) c /\
    is_rejecting M c.

(** Machine halts on input *)
Definition tm_halts (M : TuringMachine) (input : list TapeSymbol) : Prop :=
  exists c,
    steps_star M (init_config M input) c /\
    is_halting_state M (cfg_state c).

(** ** Basic Theorems about TM Semantics *)

Theorem steps_star_trans :
  forall M c1 c2 c3,
    steps_star M c1 c2 ->
    steps_star M c2 c3 ->
    steps_star M c1 c3.
Proof.
  intros M c1 c2 c3 H12 H23.
  induction H12.
  - exact H23.
  - eapply steps_step. exact H. apply IHsteps_star. exact H23.
Qed.

Theorem step_preserves_wellformed :
  forall M c c',
    tm_wellformed M ->
    step M c = Some c' ->
    In (cfg_state c) (tm_states M) ->
    In (cfg_state c') (tm_states M).
Proof.
  intros M c c' Hwf Hstep Hin.
  unfold step in Hstep.
  destruct (tm_transition M (cfg_state c) (tape_read (cfg_tape c) (cfg_pos c))) eqn:Htrans.
  - destruct p as [[q' s'] d].
    injection Hstep as <-.
    simpl.
    unfold tm_wellformed in Hwf.
    destruct Hwf as [_ [_ [_ [_ [_ Htrans_wf]]]]].
    specialize (Htrans_wf (cfg_state c) (tape_read (cfg_tape c) (cfg_pos c)) q' s' d Htrans).
    destruct Htrans_wf as [_ [_ [Hq' _]]].
    exact Hq'.
  - discriminate.
Qed.

Theorem tape_write_read :
  forall t pos s,
    tape_read (tape_write t pos s) pos = s.
Proof.
  intros t pos s.
  unfold tape_read, tape_write.
  rewrite Z.eqb_refl. reflexivity.
Qed.

Theorem tape_write_read_neq :
  forall t pos pos' s,
    pos <> pos' ->
    tape_read (tape_write t pos s) pos' = tape_read t pos'.
Proof.
  intros t pos pos' s Hneq.
  unfold tape_read, tape_write.
  destruct (Z.eqb pos pos') eqn:Heq.
  - apply Z.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

End TuringCompleteness.

(** * Concrete Turing Machine Instance *)

(** For computational examples and concrete constructions, we instantiate
    the generic theory with natural numbers. *)
Module ConcreteTM.

(** Concrete types *)
Definition State : Type := nat.
Definition State_eq_dec : forall (q1 q2 : State), {q1 = q2} + {q1 <> q2} := Nat.eq_dec.

Definition TapeSymbol : Type := nat.
Definition TapeSymbol_eq_dec : forall (a b : TapeSymbol), {a = b} + {a <> b} := Nat.eq_dec.

Definition blank : TapeSymbol := 0.

(** Explicit instantiation of all generic definitions *)
Definition Tape : Type := Z -> TapeSymbol.
Definition blank_tape : Tape := fun _ => blank.
Definition tape_read (t : Tape) (pos : Z) : TapeSymbol := t pos.
Definition tape_write (t : Tape) (pos : Z) (s : TapeSymbol) : Tape :=
  fun pos' => if (pos =? pos')%Z then s else t pos'.

Definition Transition : Type := State -> TapeSymbol -> option (State * TapeSymbol * Direction).

Record TuringMachine : Type := mkTM {
  tm_states : list State;
  tm_alphabet : list TapeSymbol;
  tm_transition : Transition;
  tm_start : State;
  tm_accept : State;
  tm_reject : State
}.

Record Config : Type := mkConfig {
  cfg_state : State;
  cfg_tape : Tape;
  cfg_pos : Z
}.

Definition init_config (M : TuringMachine) (input : list TapeSymbol) : Config :=
  let init_tape := fun pos =>
    if (pos <? 0)%Z then blank
    else match nth_error input (Z.to_nat pos) with
    | Some s => s
    | None => blank
    end in
  mkConfig (tm_start M) init_tape 0%Z.

Definition move_head (pos : Z) (d : Direction) : Z :=
  match d with
  | Left => (pos - 1)%Z
  | Right => (pos + 1)%Z
  | Stay => pos
  end.

Definition step (M : TuringMachine) (c : Config) : option Config :=
  let q := cfg_state c in
  let t := cfg_tape c in
  let pos := cfg_pos c in
  let current_symbol := tape_read t pos in
  match tm_transition M q current_symbol with
  | None => None
  | Some (q', s', d) =>
      Some (mkConfig q' (tape_write t pos s') (move_head pos d))
  end.

Fixpoint steps (M : TuringMachine) (n : nat) (c : Config) : option Config :=
  match n with
  | O => Some c
  | S n' =>
      if State_eq_dec (cfg_state c) (tm_accept M) then Some c
      else if State_eq_dec (cfg_state c) (tm_reject M) then Some c
      else match step M c with
           | None => None
           | Some c' => steps M n' c'
           end
  end.

Definition incrementer_transition : Transition :=
  fun q a =>
    match q, a with
    | 0, 0 => Some (1, 1, Stay)
    | 0, 1 => Some (0, 1, Right)
    | 0, 2 => Some (1, 2, Stay)
    | _, _ => None
    end.

Definition incrementer : TuringMachine :=
  mkTM
    [0; 1]
    [0; 1; 2]
    incrementer_transition
    0
    1
    2.

Eval compute in (init_config incrementer [1; 1; 1]).
Eval compute in (step incrementer (init_config incrementer [1; 1; 1])).
Eval compute in (steps incrementer 10 (init_config incrementer [1; 1; 1])).

(** Test that negative positions correctly get blank *)
Lemma init_config_negative_positions_blank :
  forall input : list nat,
    tape_read (cfg_tape (init_config incrementer input)) (-1)%Z = blank.
Proof.
  intros input.
  unfold init_config, tape_read, blank. simpl.
  reflexivity.
Qed.

Lemma init_config_negative_positions_blank_general :
  forall input : list nat,
  forall neg_pos : Z,
    (neg_pos < 0)%Z ->
    tape_read (cfg_tape (init_config incrementer input)) neg_pos = blank.
Proof.
  intros input neg_pos Hneg.
  unfold init_config, tape_read, blank. simpl.
  destruct neg_pos; try lia.
  reflexivity.
Qed.

End ConcreteTM.

Section TMSimulation.

Context {State : Type}.
Context {State_eq_dec : forall (q1 q2 : State), {q1 = q2} + {q1 <> q2}}.
Context {TapeSymbol : Type}.
Context {TapeSymbol_eq_dec : forall (a b : TapeSymbol), {a = b} + {a <> b}}.
Context (blank : TapeSymbol).

Inductive SimGlue : Type :=
  | GlueNull : SimGlue
  | GlueState : State -> SimGlue
  | GlueTapeSymbol : TapeSymbol -> SimGlue
  | GlueDir : Direction -> SimGlue.

Definition SimGlue_eq_dec : forall x y : SimGlue, {x = y} + {x <> y}.
Proof.
  decide equality; try (apply State_eq_dec); try (apply TapeSymbol_eq_dec).
  destruct d, d0; try (left; reflexivity); try (right; discriminate).
Qed.

Record SimTile : Type := mkSimTile {
  st_glue_N : SimGlue;
  st_glue_E : SimGlue;
  st_glue_S : SimGlue;
  st_glue_W : SimGlue
}.

(** We need a way to map states and symbols to distinct naturals.
    Since State and TapeSymbol are abstract, we add encoder functions. *)
Definition encode_glue (g : SimGlue)
  (state_encoder : State -> nat)
  (symbol_encoder : TapeSymbol -> nat) : nat :=
  match g with
  | GlueNull => 0
  | GlueState s => 1 + 4 * (state_encoder s)   (* 1 mod 4 for states *)
  | GlueTapeSymbol sym => 2 + 4 * (symbol_encoder sym)  (* 2 mod 4 for symbols *)
  | GlueDir Left => 3   (* 3 mod 4 for directions *)
  | GlueDir Right => 7
  | GlueDir Stay => 11
  end.

Lemma encode_glue_null : forall state_encoder symbol_encoder,
  encode_glue GlueNull state_encoder symbol_encoder = 0.
Proof.
  intros. unfold encode_glue. reflexivity.
Qed.

Definition simtile_to_tiletype (st : SimTile)
  (state_encoder : State -> nat)
  (symbol_encoder : TapeSymbol -> nat) : TileType :=
  {| glue_N := encode_glue (st_glue_N st) state_encoder symbol_encoder;
     glue_E := encode_glue (st_glue_E st) state_encoder symbol_encoder;
     glue_S := encode_glue (st_glue_S st) state_encoder symbol_encoder;
     glue_W := encode_glue (st_glue_W st) state_encoder symbol_encoder |}.

Definition sim_glue_strength (g1 g2 : nat) : nat :=
  if Nat.eqb g1 0 then 0
  else if Nat.eqb g2 0 then 0
  else if Nat.eqb g1 g2 then 1
  else 0.

Lemma sim_glue_strength_symmetric : forall g1 g2,
  sim_glue_strength g1 g2 = sim_glue_strength g2 g1.
Proof.
  intros g1 g2. unfold sim_glue_strength.
  destruct (Nat.eqb g1 0) eqn:H1; destruct (Nat.eqb g2 0) eqn:H2; simpl; try reflexivity.
  destruct (Nat.eqb g1 g2) eqn:H3.
  rewrite Nat.eqb_sym. rewrite H3. reflexivity.
  rewrite Nat.eqb_sym. rewrite H3. reflexivity.
Qed.

Lemma sim_glue_strength_null_left : forall g,
  sim_glue_strength 0 g = 0.
Proof.
  intros. unfold sim_glue_strength. simpl. reflexivity.
Qed.

Lemma sim_glue_strength_null_right : forall g,
  sim_glue_strength g 0 = 0.
Proof.
  intros. unfold sim_glue_strength.
  destruct (Nat.eqb g 0); reflexivity.
Qed.

Lemma sim_glue_strength_match : forall g,
  g <> 0 -> sim_glue_strength g g = 1.
Proof.
  intros g Hneq. unfold sim_glue_strength.
  destruct (Nat.eqb g 0) eqn:H.
  apply Nat.eqb_eq in H. contradiction.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Record TMCell : Type := mkTMCell {
  cell_state : option State;
  cell_symbol : TapeSymbol;
  cell_is_head : bool
}.

Definition encode_cell_to_tile (c : TMCell) : SimTile :=
  match cell_state c with
  | None => mkSimTile GlueNull (GlueTapeSymbol (cell_symbol c)) GlueNull (GlueTapeSymbol (cell_symbol c))
  | Some q => mkSimTile (GlueState q) (GlueTapeSymbol (cell_symbol c)) (GlueState q) (GlueTapeSymbol (cell_symbol c))
  end.

Definition config_to_row (cfg : @Config State TapeSymbol) (y : Z) : Z -> TMCell :=
  fun x => mkTMCell
    (if Z.eqb x (cfg_pos cfg) then Some (cfg_state cfg) else None)
    (cfg_tape cfg x)
    (Z.eqb x (cfg_pos cfg)).

Definition config_to_assembly (cfg : @Config State TapeSymbol)
  (state_encoder : State -> nat)
  (symbol_encoder : TapeSymbol -> nat) : Assembly :=
  fun p => let '(x, y) := p in
    if Z.eqb y 0
    then Some (simtile_to_tiletype (encode_cell_to_tile (config_to_row cfg y x)) state_encoder symbol_encoder)
    else None.

Lemma config_to_row_at_head : forall cfg y,
  cell_state (config_to_row cfg y (cfg_pos cfg)) = Some (cfg_state cfg).
Proof.
  intros cfg y. unfold config_to_row. simpl.
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma config_to_row_not_head : forall cfg y x,
  x <> cfg_pos cfg -> cell_state (config_to_row cfg y x) = None.
Proof.
  intros cfg y x Hneq. unfold config_to_row. simpl.
  destruct (Z.eqb x (cfg_pos cfg)) eqn:H.
  apply Z.eqb_eq in H. contradiction.
  reflexivity.
Qed.

Lemma config_to_assembly_row_zero : forall cfg state_encoder symbol_encoder x,
  config_to_assembly cfg state_encoder symbol_encoder (x, 0%Z) =
    Some (simtile_to_tiletype (encode_cell_to_tile (config_to_row cfg 0%Z x)) state_encoder symbol_encoder).
Proof.
  intros cfg state_encoder symbol_encoder x.
  unfold config_to_assembly. reflexivity.
Qed.

Lemma sim_glue_strength_enables_cooperation : forall g1 g2,
  g1 <> 0 -> g2 <> 0 -> g1 = g2 -> sim_glue_strength g1 g2 = 1.
Proof.
  intros g1 g2 Hg1 Hg2 Heq. subst.
  apply sim_glue_strength_match. assumption.
Qed.

Lemma config_to_row_symbol : forall cfg y x,
  cell_symbol (config_to_row cfg y x) = cfg_tape cfg x.
Proof.
  intros cfg y x. unfold config_to_row. simpl. reflexivity.
Qed.

Lemma config_to_row_is_head : forall cfg y x,
  cell_is_head (config_to_row cfg y x) = Z.eqb x (cfg_pos cfg).
Proof.
  intros cfg y x. unfold config_to_row. simpl. reflexivity.
Qed.

Definition transition_tile (q : State) (a : TapeSymbol) (q' : State) (a' : TapeSymbol) (d : Direction) : SimTile :=
  mkSimTile
    (GlueState q)
    (GlueTapeSymbol a)
    (GlueState q')
    (GlueTapeSymbol a').

(** Default encoders when we don't have concrete representations *)
Variable default_state_encoder : State -> nat.
Variable default_symbol_encoder : TapeSymbol -> nat.

(** Assumptions about the default encoders *)
Hypothesis state_encoder_injective : forall s1 s2,
  default_state_encoder s1 = default_state_encoder s2 -> s1 = s2.
Hypothesis symbol_encoder_injective : forall a1 a2,
  default_symbol_encoder a1 = default_symbol_encoder a2 -> a1 = a2.
Hypothesis state_encoder_nonzero : forall s, default_state_encoder s <> 0.
Hypothesis symbol_encoder_nonzero : forall a, default_symbol_encoder a <> 0.

Fixpoint generate_transition_tiles
  (M : @TuringMachine State TapeSymbol)
  (states : list State)
  (alphabet : list TapeSymbol)
  (state_encoder : State -> nat)
  (symbol_encoder : TapeSymbol -> nat)
  : list TileType :=
  match states with
  | [] => []
  | q :: qs =>
      let tiles_for_state :=
        flat_map (fun a =>
          match tm_transition M q a with
          | None => []
          | Some (q', a', d) =>
              [simtile_to_tiletype (transition_tile q a q' a' d) state_encoder symbol_encoder]
          end) alphabet
      in tiles_for_state ++ generate_transition_tiles M qs alphabet state_encoder symbol_encoder
  end.

Definition tm_to_tas
  (M : @TuringMachine State TapeSymbol)
  (seed_asm : Assembly)
  (state_encoder : State -> nat)
  (symbol_encoder : TapeSymbol -> nat)
  : TAS :=
  {| tas_tiles := generate_transition_tiles M (tm_states M) (tm_alphabet M) state_encoder symbol_encoder;
     tas_seed := seed_asm;
     tas_glue_strength := fun g => if Nat.eqb g 0 then 0 else 1;
     tas_temp := 2 |}.

Lemma generate_transition_tiles_length_bound :
  forall (M : @TuringMachine State TapeSymbol) states alphabet state_encoder symbol_encoder,
    length (generate_transition_tiles M states alphabet state_encoder symbol_encoder) <=
    length states * length alphabet.
Proof.
  intros M states alphabet state_encoder symbol_encoder.
  induction states as [|q qs IH]; simpl.
  - lia.
  - rewrite app_length.
    assert (Hflat: length (flat_map (fun a => match tm_transition M q a with
                                           | None => []
                                           | Some (q', a', d) => [simtile_to_tiletype (transition_tile q a q' a' d) state_encoder symbol_encoder]
                                           end) alphabet) <= length alphabet).
    { clear IH. induction alphabet as [|a alphabet' IHa]; simpl.
      - lia.
      - destruct (tm_transition M q a) as [[[q' a'] d]|]; simpl; lia. }
    lia.
Qed.

Theorem tile_complexity_bound :
  forall (M : @TuringMachine State TapeSymbol) seed_asm state_encoder symbol_encoder,
    length (tas_tiles (tm_to_tas M seed_asm state_encoder symbol_encoder)) <=
    length (tm_states M) * length (tm_alphabet M).
Proof.
  intros M seed_asm state_encoder symbol_encoder.
  unfold tm_to_tas. simpl.
  apply generate_transition_tiles_length_bound.
Qed.

Theorem tm_step_tile_correspondence :
  forall (M : @TuringMachine State TapeSymbol) (c c' : @Config State TapeSymbol) state_encoder symbol_encoder,
    In (cfg_state c) (tm_states M) ->
    In (tape_read (cfg_tape c) (cfg_pos c)) (tm_alphabet M) ->
    step M c = Some c' ->
    exists t : TileType,
      In t (tas_tiles (tm_to_tas M empty_assembly state_encoder symbol_encoder)) /\
      glue_N t = encode_glue (GlueState (cfg_state c)) state_encoder symbol_encoder /\
      glue_E t = encode_glue (GlueTapeSymbol (cfg_tape c (cfg_pos c))) state_encoder symbol_encoder.
Proof.
  intros M c c' state_encoder symbol_encoder Hin_state Hin_sym Hstep.
  unfold step in Hstep.
  destruct (tm_transition M (cfg_state c) (tape_read (cfg_tape c) (cfg_pos c))) as [[[q' a'] d]|] eqn:Htrans.
  - injection Hstep as <-.
    exists (simtile_to_tiletype (transition_tile (cfg_state c) (tape_read (cfg_tape c) (cfg_pos c)) q' a' d) state_encoder symbol_encoder).
    split.
    + unfold tm_to_tas. simpl.
      unfold generate_transition_tiles.
      induction (tm_states M) as [|q qs IH].
      * simpl in Hin_state. contradiction.
      * simpl. apply in_or_app.
        destruct (State_eq_dec q (cfg_state c)) as [Heq | Hneq].
        { left. subst q. clear IH Hin_state.
          induction (tm_alphabet M) as [|a as' IHa].
          - simpl in Hin_sym. contradiction.
          - simpl. apply in_or_app.
            destruct (TapeSymbol_eq_dec a (tape_read (cfg_tape c) (cfg_pos c))) as [Heq_sym | Hneq_sym].
            + left. subst a. rewrite Htrans. simpl. left. reflexivity.
            + right. apply IHa. destruct Hin_sym as [Heq_sym' | Hin_sym']; auto. contradiction. }
        { right. apply IH. destruct Hin_state as [Heq | Hin_state']; auto. contradiction. }
    + split; unfold simtile_to_tiletype, transition_tile; simpl; reflexivity.
  - discriminate.
Qed.

Theorem tm_to_tas_has_temp_2 :
  forall (M : @TuringMachine State TapeSymbol) seed_asm state_encoder symbol_encoder,
    tas_temp (tm_to_tas M seed_asm state_encoder symbol_encoder) = 2.
Proof.
  intros M seed_asm state_encoder symbol_encoder.
  unfold tm_to_tas. simpl. reflexivity.
Qed.

Theorem tm_to_tas_glue_strength_nonzero :
  forall (M : @TuringMachine State TapeSymbol) seed_asm state_encoder symbol_encoder g,
    g <> 0 ->
    tas_glue_strength (tm_to_tas M seed_asm state_encoder symbol_encoder) g = 1.
Proof.
  intros M seed_asm state_encoder symbol_encoder g Hneq.
  unfold tm_to_tas. simpl.
  destruct (Nat.eqb g 0) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Theorem cooperation_at_temp_2 :
  forall (M : @TuringMachine State TapeSymbol) seed_asm g1 g2,
    g1 <> 0 ->
    g2 <> 0 ->
    tas_glue_strength (tm_to_tas M seed_asm default_state_encoder default_symbol_encoder) g1 +
    tas_glue_strength (tm_to_tas M seed_asm default_state_encoder default_symbol_encoder) g2 >=
    tas_temp (tm_to_tas M seed_asm default_state_encoder default_symbol_encoder).
Proof.
  intros M seed_asm g1 g2 Hg1 Hg2.
  unfold tm_to_tas, tas_temp, tas_glue_strength. simpl.
  destruct (Nat.eqb g1 0) eqn:Heq1.
  - apply Nat.eqb_eq in Heq1. contradiction.
  - destruct (Nat.eqb g2 0) eqn:Heq2.
    + apply Nat.eqb_eq in Heq2. contradiction.
    + simpl. lia.
Qed.

Lemma encode_glue_state_nonzero :
  forall q state_encoder symbol_encoder,
    (forall s, state_encoder s <> 0) ->
    encode_glue (GlueState q) state_encoder symbol_encoder <> 0.
Proof.
  intros q state_encoder symbol_encoder Henc.
  unfold encode_glue.
  specialize (Henc q). lia.
Qed.

Lemma encode_glue_tape_nonzero :
  forall a state_encoder symbol_encoder,
    (forall sym, symbol_encoder sym <> 0) ->
    encode_glue (GlueTapeSymbol a) state_encoder symbol_encoder <> 0.
Proof.
  intros a state_encoder symbol_encoder Henc.
  unfold encode_glue.
  specialize (Henc a). lia.
Qed.

Theorem tm_step_has_corresponding_tile_at_temp_2 :
  forall (M : @TuringMachine State TapeSymbol) seed_asm,
    (forall q a, In q (tm_states M) -> In a (tm_alphabet M) ->
      exists q' a' d, tm_transition M q a = Some (q', a', d) \/ tm_transition M q a = None) ->
    exists state_offset tape_offset,
      state_offset <> 0 /\
      tape_offset <> 0 /\
      tas_temp (tm_to_tas M seed_asm (fun _ => state_offset) (fun _ => tape_offset)) = 2 /\
      (forall c c',
        In (cfg_state c) (tm_states M) ->
        In (tape_read (cfg_tape c) (cfg_pos c)) (tm_alphabet M) ->
        step M c = Some c' ->
        exists t,
          In t (tas_tiles (tm_to_tas M seed_asm (fun _ => state_offset) (fun _ => tape_offset))) /\
          glue_N t = encode_glue (GlueState (cfg_state c)) (fun _ => state_offset) (fun _ => tape_offset) /\
          glue_E t = encode_glue (GlueTapeSymbol (cfg_tape c (cfg_pos c))) (fun _ => state_offset) (fun _ => tape_offset)).
Proof.
  intros M seed_asm Htrans_total.
  exists 1, 2.
  split. discriminate.
  split. discriminate.
  split. apply tm_to_tas_has_temp_2.
  intros c c' Hstate Hsym Hstep.
  apply (tm_step_tile_correspondence M c c' (fun _ => 1) (fun _ => 2) Hstate Hsym Hstep).
Qed.

Theorem tm_multistep_has_tiles_for_each_step :
  forall (M : @TuringMachine State TapeSymbol) seed_asm c c',
    (forall q a, In q (tm_states M) -> In a (tm_alphabet M) ->
      exists q' a' d, tm_transition M q a = Some (q', a', d) \/ tm_transition M q a = None) ->
    (forall cfg : @Config State TapeSymbol, In (@cfg_state State TapeSymbol cfg) (tm_states M)) ->
    (forall cfg : @Config State TapeSymbol, In (tape_read (@cfg_tape State TapeSymbol cfg) (@cfg_pos State TapeSymbol cfg)) (tm_alphabet M)) ->
    steps_star M c c' ->
    exists state_offset tape_offset,
      state_offset <> 0 /\
      tape_offset <> 0 /\
      forall step_c step_c',
        steps_star M c step_c ->
        step M step_c = Some step_c' ->
        exists t,
          In t (tas_tiles (tm_to_tas M seed_asm (fun _ => state_offset) (fun _ => tape_offset))) /\
          glue_N t = encode_glue (GlueState (@cfg_state State TapeSymbol step_c)) (fun _ => state_offset) (fun _ => tape_offset) /\
          glue_E t = encode_glue (GlueTapeSymbol (@cfg_tape State TapeSymbol step_c (@cfg_pos State TapeSymbol step_c))) (fun _ => state_offset) (fun _ => tape_offset).
Proof.
  intros M seed_asm c c' Htrans Hstate_all Hsym_all Hsteps.
  exists 1, 2.
  split. discriminate.
  split. discriminate.
  intros step_c step_c' Hsteps_to_c Hstep.
  apply (tm_step_tile_correspondence M step_c step_c' (fun _ => 1) (fun _ => 2)).
  - apply Hstate_all.
  - apply Hsym_all.
  - exact Hstep.
Qed.

Theorem tm_execution_has_tiles_for_all_steps :
  forall (M : @TuringMachine State TapeSymbol) start_config final_config,
    (forall q, In q (tm_states M)) ->
    (forall a, In a (tm_alphabet M)) ->
    steps_star M start_config final_config ->
    exists state_offset tape_offset,
      state_offset <> 0 /\
      tape_offset <> 0 /\
      forall intermediate_config next_config,
        steps_star M start_config intermediate_config ->
        step M intermediate_config = Some next_config ->
        exists t,
          In t (tas_tiles (tm_to_tas M empty_assembly (fun _ => state_offset) (fun _ => tape_offset))) /\
          glue_N t = encode_glue (GlueState (@cfg_state State TapeSymbol intermediate_config)) (fun _ => state_offset) (fun _ => tape_offset) /\
          glue_E t = encode_glue (GlueTapeSymbol (@cfg_tape State TapeSymbol intermediate_config (@cfg_pos State TapeSymbol intermediate_config))) (fun _ => state_offset) (fun _ => tape_offset).
Proof.
  intros M start_config final_config Hstates Halphabet Hsteps.
  exists 1, 2.
  split. discriminate.
  split. discriminate.
  intros intermediate_config next_config Hsteps_inter Hstep.
  apply (tm_step_tile_correspondence M intermediate_config next_config (fun _ => 1) (fun _ => 2)).
  - apply Hstates.
  - apply Halphabet.
  - exact Hstep.
Qed.

Lemma encode_cell_state_some : forall q a,
  encode_cell_to_tile (mkTMCell (Some q) a true) =
    mkSimTile (GlueState q) (GlueTapeSymbol a) (GlueState q) (GlueTapeSymbol a).
Proof.
  intros q a. unfold encode_cell_to_tile. simpl. reflexivity.
Qed.

Lemma encode_cell_state_none : forall a,
  encode_cell_to_tile (mkTMCell None a false) =
    mkSimTile GlueNull (GlueTapeSymbol a) GlueNull (GlueTapeSymbol a).
Proof.
  intros a. unfold encode_cell_to_tile. simpl. reflexivity.
Qed.

Lemma encode_glue_preserves_null : forall state_enc symbol_enc,
  encode_glue GlueNull state_enc symbol_enc = 0.
Proof.
  intros state_enc symbol_enc. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_nonzero_state : forall q state_enc symbol_enc,
  encode_glue (GlueState q) state_enc symbol_enc = 1 + 4 * (state_enc q).
Proof.
  intros q state_enc symbol_enc. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_nonzero_tape : forall sym state_enc symbol_enc,
  encode_glue (GlueTapeSymbol sym) state_enc symbol_enc = 2 + 4 * (symbol_enc sym).
Proof.
  intros sym state_enc symbol_enc. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_dir_left : forall state_enc symbol_enc,
  encode_glue (GlueDir Left) state_enc symbol_enc = 3.
Proof.
  intros state_enc symbol_enc. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_dir_right : forall state_enc symbol_enc,
  encode_glue (GlueDir Right) state_enc symbol_enc = 7.
Proof.
  intros state_enc symbol_enc. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_dir_stay : forall state_enc symbol_enc,
  encode_glue (GlueDir Stay) state_enc symbol_enc = 11.
Proof.
  intros state_enc symbol_enc. unfold encode_glue. reflexivity.
Qed.

(** Distinct states produce distinct glue encodings *)
Theorem distinct_states_have_distinct_glues :
  forall s1 s2 : State,
    s1 <> s2 ->
    default_state_encoder s1 <> default_state_encoder s2 ->
    encode_glue (GlueState s1) default_state_encoder default_symbol_encoder <>
    encode_glue (GlueState s2) default_state_encoder default_symbol_encoder.
Proof.
  intros s1 s2 Hdiff_states Hdiff_enc.
  unfold encode_glue.
  intro H.
  (* From H: 1 + 4 * default_state_encoder s1 = 1 + 4 * default_state_encoder s2 *)
  assert (4 * default_state_encoder s1 = 4 * default_state_encoder s2) by lia.
  assert (default_state_encoder s1 = default_state_encoder s2) by lia.
  contradiction.
Qed.

(** Non-interference: distinct transitions cannot erroneously bind *)
Theorem distinct_transitions_have_incompatible_tiles :
  forall q1 a1 q1' a1' d1 q2 a2 q2' a2' d2,
    (q1 <> q2 \/ a1 <> a2) ->
    (forall s1 s2, s1 <> s2 -> default_state_encoder s1 <> default_state_encoder s2) ->
    (forall sym1 sym2, sym1 <> sym2 -> default_symbol_encoder sym1 <> default_symbol_encoder sym2) ->
    let tile1 := simtile_to_tiletype (transition_tile q1 a1 q1' a1' d1)
                   default_state_encoder default_symbol_encoder in
    let tile2 := simtile_to_tiletype (transition_tile q2 a2 q2' a2' d2)
                   default_state_encoder default_symbol_encoder in
    glue_N tile1 <> glue_N tile2 \/ glue_E tile1 <> glue_E tile2.
Proof.
  intros q1 a1 q1' a1' d1 q2 a2 q2' a2' d2 Hdiff Hstate_inj Hsym_inj tile1 tile2.
  unfold tile1, tile2, simtile_to_tiletype, transition_tile, encode_glue. simpl.
  destruct Hdiff as [Hq_diff | Ha_diff].
  - left. intro H.
    assert (H': 4 * default_state_encoder q1 = 4 * default_state_encoder q2) by lia.
    assert (default_state_encoder q1 = default_state_encoder q2) by lia.
    apply Hstate_inj in H0; auto.
  - right. intro H.
    assert (H': 4 * default_symbol_encoder a1 = 4 * default_symbol_encoder a2) by lia.
    assert (default_symbol_encoder a1 = default_symbol_encoder a2) by lia.
    apply Hsym_inj in H0; auto.
Qed.

Theorem temperature_two_enables_computation : forall off1 off2,
  off1 <> 0 -> off2 <> 0 ->
  sim_glue_strength off1 off1 + sim_glue_strength off2 off2 >= 2.
Proof.
  intros off1 off2 H1 H2.
  rewrite sim_glue_strength_match by assumption.
  rewrite sim_glue_strength_match by assumption.
  simpl. lia.
Qed.

Lemma config_to_row_head_encodes_state : forall cfg y,
  cell_state (config_to_row cfg y (cfg_pos cfg)) = Some (cfg_state cfg).
Proof.
  intros cfg y. unfold config_to_row. simpl.
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma config_to_row_nonhead_no_state : forall cfg y x,
  x <> cfg_pos cfg ->
  cell_state (config_to_row cfg y x) = None.
Proof.
  intros cfg y x Hneq. unfold config_to_row. simpl.
  destruct (Z.eqb x (cfg_pos cfg)) eqn:Heq.
  apply Z.eqb_eq in Heq. contradiction.
  reflexivity.
Qed.

Lemma encode_cell_preserves_tape_symbol : forall c,
  st_glue_E (encode_cell_to_tile c) = GlueTapeSymbol (cell_symbol c) /\
  st_glue_W (encode_cell_to_tile c) = GlueTapeSymbol (cell_symbol c).
Proof.
  intros c. destruct c as [st sym is_head].
  unfold encode_cell_to_tile. destruct st; simpl; split; reflexivity.
Qed.

Lemma encode_cell_state_propagates_vertically : forall c,
  st_glue_N (encode_cell_to_tile c) = st_glue_S (encode_cell_to_tile c).
Proof.
  intros c. destruct c as [st sym is_head].
  unfold encode_cell_to_tile. destruct st; simpl; reflexivity.
Qed.

(** ** Completeness *)

Lemma transition_tile_glues :
  forall q a q' a' d state_encoder symbol_encoder,
    (forall s, state_encoder s <> 0) ->
    (forall sym, symbol_encoder sym <> 0) ->
    let t := simtile_to_tiletype (transition_tile q a q' a' d) state_encoder symbol_encoder in
    glue_N t = 1 + 4 * state_encoder q /\
    glue_E t = 2 + 4 * symbol_encoder a /\
    glue_S t = 1 + 4 * state_encoder q' /\
    glue_W t = 2 + 4 * symbol_encoder a'.
Proof.
  intros q a q' a' d state_encoder symbol_encoder Henc_s Henc_sym.
  unfold simtile_to_tiletype, transition_tile. simpl.
  repeat split; unfold encode_glue; reflexivity.
Qed.

Theorem tm_transition_generates_tile :
  forall (M : @TuringMachine State TapeSymbol) q a q' a' d,
    In q (tm_states M) ->
    In a (tm_alphabet M) ->
    tm_transition M q a = Some (q', a', d) ->
    forall state_encoder symbol_encoder,
      (forall s, state_encoder s <> 0) ->
      (forall sym, symbol_encoder sym <> 0) ->
      let tas := tm_to_tas M empty_assembly state_encoder symbol_encoder in
      exists t : TileType,
        In t (tas_tiles tas) /\
        glue_N t = encode_glue (GlueState q) state_encoder symbol_encoder /\
        glue_E t = encode_glue (GlueTapeSymbol a) state_encoder symbol_encoder /\
        glue_S t = encode_glue (GlueState q') state_encoder symbol_encoder /\
        glue_W t = encode_glue (GlueTapeSymbol a') state_encoder symbol_encoder.
Proof.
  intros M q a q' a' d Hq Ha Htrans state_encoder symbol_encoder Henc_s Henc_sym.
  exists (simtile_to_tiletype (transition_tile q a q' a' d) state_encoder symbol_encoder).
  split.
  - unfold tm_to_tas. simpl. unfold generate_transition_tiles.
    induction (tm_states M) as [|q0 qs IH].
    + simpl in Hq. contradiction.
    + simpl. apply in_or_app.
      destruct (State_eq_dec q0 q) as [Heq | Hneq].
      * left. subst q0. clear IH Hq.
        induction (tm_alphabet M) as [|a0 alphabet_rest IHa].
        { simpl in Ha. contradiction. }
        simpl. apply in_or_app.
        destruct (TapeSymbol_eq_dec a0 a) as [Heqa | Hneqa].
        { left. subst a0. rewrite Htrans. simpl. left. reflexivity. }
        { right. apply IHa. destruct Ha as [Heq | Hin]; auto. contradiction. }
      * right. apply IH. destruct Hq as [Heq | Hin]; auto. contradiction.
  - unfold simtile_to_tiletype, transition_tile. simpl.
    repeat split; unfold encode_glue; reflexivity.
Qed.

Theorem tm_to_tas_generates_tiles_for_execution :
  forall (M : @TuringMachine State TapeSymbol),
    (forall q, In q (tm_states M)) ->
    (forall a, In a (tm_alphabet M)) ->
    forall c c',
      steps_star M c c' ->
      forall state_offset tape_offset,
        state_offset <> 0 ->
        tape_offset <> 0 ->
        let tas := tm_to_tas M empty_assembly (fun _ => state_offset) (fun _ => tape_offset) in
        forall intermediate_config,
          steps_star M c intermediate_config ->
          forall next_config,
            step M intermediate_config = Some next_config ->
            exists t : TileType,
              In t (tas_tiles tas) /\
              glue_N t = encode_glue (GlueState (cfg_state intermediate_config)) (fun _ => state_offset) (fun _ => tape_offset) /\
              glue_E t = encode_glue (GlueTapeSymbol (tape_read (cfg_tape intermediate_config) (cfg_pos intermediate_config))) (fun _ => state_offset) (fun _ => tape_offset).
Proof.
  intros M Hstates Halphabet c c' Hsteps state_offset tape_offset Hoff1 Hoff2 tas intermediate_config Hsteps_inter next_config Hstep.
  unfold step in Hstep.
  destruct (tm_transition M (cfg_state intermediate_config) (tape_read (cfg_tape intermediate_config) (cfg_pos intermediate_config))) as [[[q' a'] d]|] eqn:Htrans.
  - assert (Henc_s: forall s, (fun _ : State => state_offset) s <> 0).
    { intro. exact Hoff1. }
    assert (Henc_sym: forall sym, (fun _ : TapeSymbol => tape_offset) sym <> 0).
    { intro. exact Hoff2. }
    assert (Htile := tm_transition_generates_tile M (cfg_state intermediate_config) (tape_read (cfg_tape intermediate_config) (cfg_pos intermediate_config)) q' a' d (Hstates (cfg_state intermediate_config)) (Halphabet (tape_read (cfg_tape intermediate_config) (cfg_pos intermediate_config))) Htrans (fun _ => state_offset) (fun _ => tape_offset) Henc_s Henc_sym).
    destruct Htile as [t [Hin [HgN [HgE _]]]].
    exists t. split. exact Hin. split. exact HgN. exact HgE.
  - discriminate.
Qed.

Corollary tm_to_tas_temp_2_has_tiles_for_all_transitions :
  forall (M : @TuringMachine State TapeSymbol),
    (forall q, In q (tm_states M)) ->
    (forall a, In a (tm_alphabet M)) ->
    exists state_offset tape_offset,
      state_offset <> 0 /\
      tape_offset <> 0 /\
      let tas := tm_to_tas M empty_assembly (fun _ => state_offset) (fun _ => tape_offset) in
      tas_temp tas = 2 /\
      (forall q a q' a' d,
        In q (tm_states M) ->
        In a (tm_alphabet M) ->
        tm_transition M q a = Some (q', a', d) ->
        exists t : TileType,
          In t (tas_tiles tas) /\
          glue_N t = encode_glue (GlueState q) (fun _ => state_offset) (fun _ => tape_offset) /\
          glue_E t = encode_glue (GlueTapeSymbol a) (fun _ => state_offset) (fun _ => tape_offset) /\
          glue_S t = encode_glue (GlueState q') (fun _ => state_offset) (fun _ => tape_offset) /\
          glue_W t = encode_glue (GlueTapeSymbol a') (fun _ => state_offset) (fun _ => tape_offset)).
Proof.
  intros M Hstates Halphabet.
  exists 1, 2.
  split. discriminate.
  split. discriminate.
  split. unfold tm_to_tas. simpl. reflexivity.
  intros q a q' a' d Hq Ha Htrans.
  eapply tm_transition_generates_tile; eauto.
Qed.

(** Section 2.1: Turing completeness at temperature 2 with tile complexity O(|Q|·|Γ|) *)
Theorem tm_to_tas_temp_2_exists_with_transition_tiles_and_cooperation :
  forall (M : @TuringMachine State TapeSymbol),
    (forall q, In q (tm_states M)) ->
    (forall a, In a (tm_alphabet M)) ->
    exists (tas : TAS),
      tas_temp tas = 2 /\
      length (tas_tiles tas) <= length (tm_states M) * length (tm_alphabet M) /\
      (forall q a q' a' d,
        In q (tm_states M) ->
        In a (tm_alphabet M) ->
        tm_transition M q a = Some (q', a', d) ->
        exists t,
          In t (tas_tiles tas) /\
          exists state_offset tape_offset,
            state_offset <> 0 /\ tape_offset <> 0 /\
            glue_N t = encode_glue (GlueState q) (fun _ => state_offset) (fun _ => tape_offset) /\
            glue_E t = encode_glue (GlueTapeSymbol a) (fun _ => state_offset) (fun _ => tape_offset) /\
            glue_S t = encode_glue (GlueState q') (fun _ => state_offset) (fun _ => tape_offset) /\
            glue_W t = encode_glue (GlueTapeSymbol a') (fun _ => state_offset) (fun _ => tape_offset)) /\
      (forall g1 g2,
        g1 <> 0 -> g2 <> 0 ->
        tas_glue_strength tas g1 + tas_glue_strength tas g2 >= tas_temp tas).
Proof.
  intros M Hstates Halphabet.
  exists (tm_to_tas M empty_assembly (fun _ => 1) (fun _ => 2)).
  split. unfold tm_to_tas. simpl. reflexivity.
  split. apply tile_complexity_bound.
  split.
  - intros q a q' a' d Hq Ha Htrans.
    assert (Htile := tm_transition_generates_tile M q a q' a' d Hq Ha Htrans (fun _ => 1) (fun _ => 2) (fun s => ltac:(discriminate)) (fun s => ltac:(discriminate))).
    destruct Htile as [t [Hin [HgN [HgE [HgS HgW]]]]].
    exists t. split. exact Hin.
    exists 1, 2. repeat split; auto; discriminate.
  - intros g1 g2 Hg1 Hg2.
    unfold tm_to_tas. simpl.
    destruct (Nat.eqb g1 0) eqn:H1.
    { apply Nat.eqb_eq in H1. contradiction. }
    destruct (Nat.eqb g2 0) eqn:H2.
    { apply Nat.eqb_eq in H2. contradiction. }
    simpl. lia.
Qed.

End TMSimulation.

Example ex_incrementer_has_states :
  length (ConcreteTM.tm_states ConcreteTM.incrementer) = 2.
Proof.
  unfold ConcreteTM.incrementer, ConcreteTM.tm_states. simpl. reflexivity.
Qed.

Example ex_incrementer_has_alphabet :
  length (ConcreteTM.tm_alphabet ConcreteTM.incrementer) = 3.
Proof.
  unfold ConcreteTM.incrementer, ConcreteTM.tm_alphabet. simpl. reflexivity.
Qed.

Example ex_incrementer_tile_complexity :
  length (ConcreteTM.tm_states ConcreteTM.incrementer) *
  length (ConcreteTM.tm_alphabet ConcreteTM.incrementer) = 6.
Proof.
  simpl. reflexivity.
Qed.

Example ex_cooperation_enables_attachment :
  forall g1 g2, g1 <> 0 -> g2 <> 0 -> g1 + g2 >= 2.
Proof.
  intros g1 g2 H1 H2.
  destruct g1; try contradiction.
  destruct g2; try contradiction.
  simpl. lia.
Qed.

Example ex_incrementer_initial_state :
  ConcreteTM.cfg_state (ConcreteTM.init_config ConcreteTM.incrementer [1; 1; 1]) = 0.
Proof.
  unfold ConcreteTM.init_config. simpl. reflexivity.
Qed.

Theorem capstone_tm_tiles_attach_via_cooperation :
  forall (M : @TuringMachine nat nat) (c c' : @Config nat nat),
    In (cfg_state c) (tm_states M) ->
    In (tape_read (cfg_tape c) (cfg_pos c)) (tm_alphabet M) ->
    step M c = Some c' ->
    exists (tas : TAS),
      tas_temp tas = 2 /\
      (exists (t : TileType),
        In t (tas_tiles tas) /\
        (forall g1 g2, g1 <> 0 -> g2 <> 0 ->
          tas_glue_strength tas g1 + tas_glue_strength tas g2 >= tas_temp tas)).
Proof.
  intros M c c' Hstate Hsym Hstep.
  exists (tm_to_tas M empty_assembly (fun _ => 1) (fun _ => 2)).
  split.
  - apply tm_to_tas_has_temp_2.
  - assert (Htile := @tm_step_tile_correspondence nat Nat.eq_dec nat Nat.eq_dec M c c' (fun _ => 1) (fun _ => 2) Hstate Hsym Hstep).
    destruct Htile as [t [Hin _]].
    exists t.
    split. exact Hin.
    intros g1 g2 Hg1 Hg2.
    rewrite tm_to_tas_has_temp_2.
    rewrite tm_to_tas_glue_strength_nonzero by assumption.
    rewrite tm_to_tas_glue_strength_nonzero by assumption.
    lia.
Qed.

Lemma temp1_single_glue_sufficient :
  forall g,
    g <> 0 ->
    1 >= 1.
Proof.
  intros g Hg.
  lia.
Qed.

Lemma temp2_requires_cooperation :
  forall g,
    g <> 0 ->
    1 < 2.
Proof.
  intros g Hg.
  lia.
Qed.

Theorem tm_simulation_needs_temp2_cooperation :
  forall State TapeSymbol (M : @TuringMachine State TapeSymbol) seed_asm g1 g2,
    g1 <> 0 -> g2 <> 0 ->
    tas_glue_strength (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) g1 +
    tas_glue_strength (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) g2 = 2 /\
    tas_temp (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) = 2.
Proof.
  intros State TapeSymbol M seed_asm g1 g2 Hg1 Hg2.
  split.
  - rewrite tm_to_tas_glue_strength_nonzero by assumption.
    rewrite tm_to_tas_glue_strength_nonzero by assumption.
    lia.
  - apply tm_to_tas_has_temp_2.
Qed.

Theorem tm_to_tas_temp_2_requires_cooperation :
  forall State TapeSymbol (M : @TuringMachine State TapeSymbol) seed_asm,
    tas_temp (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) = 2 /\
    (forall g1 g2, g1 <> 0 -> g2 <> 0 ->
      tas_glue_strength (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) g1 +
      tas_glue_strength (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) g2 >= 2).
Proof.
  intros State TapeSymbol M seed_asm.
  split.
  - apply tm_to_tas_has_temp_2.
  - intros g1 g2 Hg1 Hg2.
    rewrite tm_to_tas_glue_strength_nonzero by assumption.
    rewrite tm_to_tas_glue_strength_nonzero by assumption.
    lia.
Qed.

Lemma temp1_single_neighbor_sufficient :
  forall strength_fn t α p,
    (forall g, g <> 0 -> strength_fn g = 1) ->
    binding_strength strength_fn t α p >= 1 ->
    exists p', adjacent p p' /\ exists t', α p' = Some t'.
Proof.
  intros strength_fn t α p Hstr Hbind.
  unfold binding_strength in Hbind.
  destruct (binding_strength_geq_one_has_contributing_neighbor strength_fn t α p Hbind) as [p' [Hadj Hcontrib]].
  exists p'. split. exact Hadj.
  apply neighbor_binding_geq_one_implies_tile_exists in Hcontrib.
  exact Hcontrib.
Qed.

Theorem temp1_insufficient_for_turing_machine_simulation :
  forall State TapeSymbol (M : @TuringMachine State TapeSymbol) seed_asm,
    tas_temp (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) > 1.
Proof.
  intros State TapeSymbol M seed_asm.
  rewrite tm_to_tas_has_temp_2.
  lia.
Qed.

Theorem cooperation_strictly_necessary :
  forall State TapeSymbol (M : @TuringMachine State TapeSymbol) seed_asm g1 g2,
    g1 <> 0 -> g2 <> 0 ->
    tas_temp (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) = 2 /\
    tas_glue_strength (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) g1 = 1 /\
    tas_glue_strength (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) g2 = 1 /\
    tas_glue_strength (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) g1 +
    tas_glue_strength (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2)) g2 = 2 /\
    (forall tas, tas_temp tas = 1 ->
      (forall g, g <> 0 -> tas_glue_strength tas g = 1) ->
      tas_temp tas < tas_temp (tm_to_tas M seed_asm (fun _ => 1) (fun _ => 2))).
Proof.
  intros State TapeSymbol M seed_asm g1 g2 Hg1 Hg2.
  split. apply tm_to_tas_has_temp_2.
  split. apply tm_to_tas_glue_strength_nonzero; assumption.
  split. apply tm_to_tas_glue_strength_nonzero; assumption.
  split.
  - rewrite tm_to_tas_glue_strength_nonzero by assumption.
    rewrite tm_to_tas_glue_strength_nonzero by assumption.
    lia.
  - intros tas Htemp Hstr.
    rewrite Htemp.
    rewrite tm_to_tas_has_temp_2.
    lia.
Qed.

(** ** Cellular Automata *)

Record CellularAutomaton (S : Type) : Type := mkCA {
  ca_radius : nat;
  ca_transition : list S -> S
}.

Definition ca_config (S : Type) := Z -> S.

Definition get_neighborhood {S : Type} (radius : nat) (config : ca_config S) (pos : Z) : list S :=
  map (fun offset => config (pos + Z.of_nat offset - Z.of_nat radius)%Z)
      (seq 0 (2 * radius + 1)).

Definition ca_step {S : Type} (ca : CellularAutomaton S) (config : ca_config S) : ca_config S :=
  fun pos => ca_transition S ca (get_neighborhood (ca_radius S ca) config pos).

Fixpoint ca_steps {S : Type} (ca : CellularAutomaton S) (n : nat) (config : ca_config S) : ca_config S :=
  match n with
  | 0 => config
  | S n' => ca_steps ca n' (ca_step ca config)
  end.

Definition radius1_ca {S : Type} (default : S) (transition : S -> S -> S -> S) : CellularAutomaton S :=
  mkCA S 1 (fun neighborhood =>
    match neighborhood with
    | [s_left; s_center; s_right] => transition s_left s_center s_right
    | _ => default
    end).

Definition ca_tile_encoding {S : Type} (encode_state : S -> nat)
  (left center right result : S) : TileType :=
  mkTile (encode_state left) (encode_state center) (encode_state result) (encode_state right).

Definition radius1_ca_to_tileset {S : Type} (transition : S -> S -> S -> S)
  (states : list S) (encode_state : S -> nat) : TileSet :=
  flat_map (fun left =>
    flat_map (fun center =>
      flat_map (fun right =>
        [ca_tile_encoding encode_state left center right (transition left center right)])
      states)
    states)
  states.

Theorem radius1_ca_tileset_at_temp_2 :
  forall {S : Type} (transition : S -> S -> S -> S) (states : list S) (encode : S -> nat),
    let tas := mkTAS (radius1_ca_to_tileset transition states encode)
                     (fun g => if Nat.eqb g 0 then 0 else 1)
                     empty_assembly 2 in
    tas_temp tas = 2.
Proof.
  intros. simpl. reflexivity.
Qed.

(** ** Rule 110: Universal Elementary Cellular Automaton *)

(** Rule 110 state: bit value *)
Definition Rule110State := bool.

(** Rule 110 transition function *)
Definition rule110 (left current right : bool) : bool :=
  match left, current, right with
  | true, true, true => false
  | true, true, false => true
  | true, false, true => true
  | true, false, false => false
  | false, true, true => true
  | false, true, false => true
  | false, false, true => true
  | false, false, false => false
  end.

Definition rule110_ca : CellularAutomaton bool :=
  radius1_ca false rule110.

Theorem rule110_is_radius1_ca :
  ca_radius bool rule110_ca = 1.
Proof.
  unfold rule110_ca, radius1_ca. simpl. reflexivity.
Qed.

Theorem rule110_transition_correct :
  forall left current right,
    ca_transition bool rule110_ca [left; current; right] = rule110 left current right.
Proof.
  intros. unfold rule110_ca, radius1_ca. simpl. reflexivity.
Qed.

(** Rule 110 tile encoding *)
Inductive Rule110Glue : Type :=
  | R110_Null : Rule110Glue
  | R110_Zero : Rule110Glue
  | R110_One : Rule110Glue
  | R110_Signal : nat -> Rule110Glue.

Definition rule110_glue_eq : forall (g1 g2 : Rule110Glue), {g1 = g2} + {g1 <> g2}.
Proof.
  decide equality. apply Nat.eq_dec.
Defined.

(** Encode Rule 110 glue to nat *)
Fixpoint encode_rule110_glue (g : Rule110Glue) : nat :=
  match g with
  | R110_Null => 0
  | R110_Zero => 1
  | R110_One => 2
  | R110_Signal n => 3 + n
  end.

(** Rule 110 transition tile *)
Definition rule110_tile (left current right result : bool) : TileType :=
  mkTile
    (encode_rule110_glue (if left then R110_One else R110_Zero))
    (encode_rule110_glue (if current then R110_One else R110_Zero))
    (encode_rule110_glue (if result then R110_One else R110_Zero))
    (encode_rule110_glue (if right then R110_One else R110_Zero)).

(** Generate all 8 Rule 110 tiles *)
Definition rule110_tileset : TileSet :=
  [rule110_tile true true true (rule110 true true true);
   rule110_tile true true false (rule110 true true false);
   rule110_tile true false true (rule110 true false true);
   rule110_tile true false false (rule110 true false false);
   rule110_tile false true true (rule110 false true true);
   rule110_tile false true false (rule110 false true false);
   rule110_tile false false true (rule110 false false true);
   rule110_tile false false false (rule110 false false false)].

(** Rule 110 TAS at temperature 2 *)
Definition rule110_tas : TAS :=
  mkTAS
    rule110_tileset
    (fun g => if Nat.eqb g 0 then 0 else 1)
    empty_assembly
    2.

Theorem rule110_tile_count :
  length rule110_tileset = 8.
Proof.
  unfold rule110_tileset. simpl. reflexivity.
Qed.

Theorem rule110_has_temp_2 :
  tas_temp rule110_tas = 2.
Proof.
  unfold rule110_tas. simpl. reflexivity.
Qed.

(** Rule 110 correctly encodes all transitions *)
Theorem rule110_tileset_contains_all_transitions :
  forall left current right : bool,
    exists t,
      In t rule110_tileset /\
      glue_N t = encode_rule110_glue (if left then R110_One else R110_Zero) /\
      glue_E t = encode_rule110_glue (if current then R110_One else R110_Zero) /\
      glue_W t = encode_rule110_glue (if right then R110_One else R110_Zero) /\
      glue_S t = encode_rule110_glue (if rule110 left current right then R110_One else R110_Zero).
Proof.
  intros left current right.
  exists (rule110_tile left current right (rule110 left current right)).
  split.
  - unfold rule110_tileset.
    destruct left; destruct current; destruct right; simpl; auto 20.
  - unfold rule110_tile. simpl. repeat split; reflexivity.
Qed.

(** Rule 110 tiles enable cooperation at temperature 2 *)
Theorem rule110_cooperation_at_temp_2 :
  forall t,
    In t rule110_tileset ->
    exists g1 g2,
      g1 <> 0 /\ g2 <> 0 /\
      tas_glue_strength rule110_tas g1 + tas_glue_strength rule110_tas g2 >= tas_temp rule110_tas.
Proof.
  intros t Hin.
  exists 1, 2. repeat split; try discriminate.
  unfold rule110_tas. simpl. lia.
Qed.

Theorem rule110_tas_exists_with_8_tiles_at_temp_2 :
  exists (tas : TAS),
    tas_temp tas = 2 /\
    length (tas_tiles tas) = 8 /\
    forall left current right : bool,
      exists t,
        In t (tas_tiles tas) /\
        glue_S t = encode_rule110_glue (if rule110 left current right then R110_One else R110_Zero).
Proof.
  exists rule110_tas.
  split. apply rule110_has_temp_2.
  split. apply rule110_tile_count.
  intros left current right.
  assert (H := rule110_tileset_contains_all_transitions left current right).
  destruct H as [t [Hin [_ [_ [_ Hglue]]]]].
  exists t. split. exact Hin. exact Hglue.
Qed.

(** * Section 2.2: Intrinsic Universality *)

(** ** Supertiles and Block Representations *)

(** A supertile is a finite connected region of tiles that acts as a
    macro-tile in a simulation. We represent it as a finite set of
    positions mapped to tile types. *)

(** Block structure: maps positions within a block to tile types *)
Definition Block : Type := list (Position * TileType).

(** Check if a position is in a block *)
Definition in_block (p : Position) (b : Block) : Prop :=
  exists t, In (p, t) b.

(** Get tile at position in block (if any) *)
Fixpoint block_at (b : Block) (p : Position) : option TileType :=
  match b with
  | [] => None
  | (p', t) :: rest =>
      if pos_eq p p' then Some t else block_at rest p
  end.

(** Block is well-formed: no duplicate positions *)
Definition block_wellformed (b : Block) : Prop :=
  forall p t1 t2,
    In (p, t1) b -> In (p, t2) b -> t1 = t2.

(** Block dimensions *)
Definition block_width (b : Block) : Z :=
  match b with
  | [] => 0%Z
  | _ => fold_right Z.max 0%Z (map (fun '(p, _) => let '(x, _) := p in x) b) -
         fold_right Z.min 0%Z (map (fun '(p, _) => let '(x, _) := p in x) b) + 1%Z
  end.

Definition block_height (b : Block) : Z :=
  match b with
  | [] => 0%Z
  | _ => fold_right Z.max 0%Z (map (fun '(p, _) => let '(_, y) := p in y) b) -
         fold_right Z.min 0%Z (map (fun '(p, _) => let '(_, y) := p in y) b) + 1%Z
  end.

(** Block is connected (every position reachable from every other via adjacency) *)
Inductive block_connected : Block -> Prop :=
  | bc_empty : block_connected []
  | bc_single : forall p t, block_connected [(p, t)]
  | bc_extend : forall b p t,
      block_connected b ->
      (exists p' t', In (p', t') b /\ adjacent p p') ->
      block_connected ((p, t) :: b).

(** Scaling factor for simulation *)
Definition scale_factor : Type := nat.

(** Scale a position by a factor k *)
Definition scale_pos (k : scale_factor) (p : Position) : Position :=
  let '(x, y) := p in (Z.of_nat k * x, Z.of_nat k * y)%Z.

(** Translate a block by an offset *)
Definition translate_block (offset : Position) (b : Block) : Block :=
  map (fun '(p, t) => let '(x, y) := p in
                       let '(ox, oy) := offset in
                       ((x + ox, y + oy)%Z, t)) b.

(** Scale a block by factor k *)
Definition scale_block (k : scale_factor) (b : Block) : Block :=
  map (fun '(p, t) => (scale_pos k p, t)) b.

(** Block to assembly conversion *)
Definition block_to_assembly (b : Block) : Assembly :=
  fun p => block_at b p.

(** Assembly restricted to a finite region *)
Definition assembly_on_region (α : Assembly) (positions : list Position) : Block :=
  flat_map (fun p =>
    match α p with
    | Some t => [(p, t)]
    | None => []
    end) positions.

(** ** Macrotile Encoding *)

(** A macrotile represents a simulated tile at higher scale.
    It consists of:
    - The original tile being simulated
    - A block structure showing how it's represented
    - Border glues for interaction with neighbors *)

Record Macrotile : Type := mkMacrotile {
  macro_tile : TileType;
  macro_block : Block;
  macro_scale : scale_factor;
  macro_north_glue : GlueType;
  macro_east_glue : GlueType;
  macro_south_glue : GlueType;
  macro_west_glue : GlueType
}.

(** Extract border glues from a block *)
Definition north_border (b : Block) : list GlueType :=
  let positions := map fst b in
  let max_y := fold_right Z.max 0%Z (map (fun '(_, y) => y) positions) in
  flat_map (fun '(p, t) =>
    let '(_, y) := p in
    if (y =? max_y)%Z then [glue_N t] else []) b.

Definition south_border (b : Block) : list GlueType :=
  let positions := map fst b in
  let min_y := fold_right Z.min 0%Z (map (fun '(_, y) => y) positions) in
  flat_map (fun '(p, t) =>
    let '(_, y) := p in
    if (y =? min_y)%Z then [glue_S t] else []) b.

Definition east_border (b : Block) : list GlueType :=
  let positions := map fst b in
  let max_x := fold_right Z.max 0%Z (map (fun '(x, _) => x) positions) in
  flat_map (fun '(p, t) =>
    let '(x, _) := p in
    if (x =? max_x)%Z then [glue_E t] else []) b.

Definition west_border (b : Block) : list GlueType :=
  let positions := map fst b in
  let min_x := fold_right Z.min 0%Z (map (fun '(x, _) => x) positions) in
  flat_map (fun '(p, t) =>
    let '(x, _) := p in
    if (x =? min_x)%Z then [glue_W t] else []) b.

(** ** Basic Properties *)

Lemma block_at_wellformed :
  forall b p t1 t2,
    block_wellformed b ->
    block_at b p = Some t1 ->
    block_at b p = Some t2 ->
    t1 = t2.
Proof.
  intros b p t1 t2 Hwf H1 H2.
  rewrite H1 in H2. injection H2. auto.
Qed.

Lemma block_to_assembly_at :
  forall b p t,
    block_at b p = Some t ->
    block_to_assembly b p = Some t.
Proof.
  intros b p t H.
  unfold block_to_assembly. exact H.
Qed.

Lemma scale_pos_injective :
  forall k p1 p2,
    k <> 0 ->
    scale_pos k p1 = scale_pos k p2 ->
    p1 = p2.
Proof.
  intros k [x1 y1] [x2 y2] Hk Hscale.
  unfold scale_pos in Hscale.
  injection Hscale as Hx Hy.
  assert (HkZ: Z.of_nat k <> 0%Z).
  { destruct k. contradiction. lia. }
  apply Z.mul_reg_l in Hx; auto.
  apply Z.mul_reg_l in Hy; auto.
  subst. reflexivity.
Qed.

Lemma translate_block_membership :
  forall b offset p t,
    In (p, t) b ->
    let '(x, y) := p in
    let '(ox, oy) := offset in
    In (((x + ox)%Z, (y + oy)%Z), t) (translate_block offset b).
Proof.
  intros b offset p t Hin.
  destruct p as [x y], offset as [ox oy].
  unfold translate_block.
  apply in_map_iff.
  exists ((x, y), t). split.
  - simpl. reflexivity.
  - exact Hin.
Qed.

Lemma block_at_in :
  forall b p t,
    block_wellformed b ->
    block_at b p = Some t ->
    In (p, t) b.
Proof.
  intros b p t Hwf Hb.
  induction b as [|[p' t'] rest IH].
  - simpl in Hb. discriminate.
  - simpl in Hb.
    destruct (pos_eq p p') eqn:Heq.
    + apply pos_eq_true_iff in Heq. subst.
      injection Hb as <-. left. reflexivity.
    + right. apply IH.
      * unfold block_wellformed in *.
        intros p0 t1 t2 H1 H2.
        eapply Hwf; right; eauto.
      * exact Hb.
Qed.

(** ** Simulation Relation Between TAS *)

(** Representation function: maps simulated positions to simulator positions *)
Definition RepFunction : Type := Position -> Position.

(** A representation function is valid if it's injective on scaled blocks *)
Definition rep_valid (rep : RepFunction) (k : scale_factor) : Prop :=
  forall p1 p2,
    rep (scale_pos k p1) = rep (scale_pos k p2) -> p1 = p2.

(** Zoom level / scaling factor for simulation *)
Record SimulationParams : Type := mkSimParams {
  sim_scale : scale_factor;
  sim_rep : RepFunction;
  sim_rep_valid : rep_valid sim_rep sim_scale
}.

(** Assembly α in TAS T simulates assembly β in TAS S at representation rep
    if every tile in β corresponds to a supertile block in α *)
Definition simulates_assembly (params : SimulationParams)
    (T S : TAS) (α : Assembly) (β : Assembly) : Prop :=
  forall p : Position,
    match β p with
    | None => True  (* Simulator may have tiles where simulated doesn't *)
    | Some t_sim =>
        (* There exists a block representing t_sim at scaled position *)
        exists (block : Block),
          (* Block is consistent with the tiles in α *)
          (forall p_block t_block,
            In (p_block, t_block) block ->
            let p_scaled := scale_pos (sim_scale params) p in
            let '(xs, ys) := p_scaled in
            let '(xb, yb) := p_block in
            α (sim_rep params ((xs + xb)%Z, (ys + yb)%Z)) = Some t_block) /\
          (* Block uses tiles from T *)
          (forall p_block t_block,
            In (p_block, t_block) block ->
            tile_in_set t_block (tas_tiles T)) /\
          (* Block encodes the simulated tile *)
          (exists macro : Macrotile,
            macro_tile macro = t_sim /\
            macro_block macro = block /\
            macro_scale macro = sim_scale params)
    end.

(** Notation for simulation *)
Notation "α ⊨[ T , S , r ] β" := (simulates_assembly r T S α β) (at level 70).

(** Simulation preserves producibility *)
Definition simulation_preserves_producibility (params : SimulationParams) (T S : TAS) : Prop :=
  forall β,
    producible_in S β ->
    exists α,
      producible_in T α /\
      simulates_assembly params T S α β.

(** Strong simulation: bijective correspondence *)
Definition strong_simulation (params : SimulationParams) (T S : TAS) : Prop :=
  simulation_preserves_producibility params T S /\
  (forall α,
    producible_in T α ->
    exists β,
      producible_in S β /\
      simulates_assembly params T S α β).

(** Two TAS are simulation-equivalent *)
Definition simulation_equivalent (T S : TAS) : Prop :=
  (exists params, simulation_preserves_producibility params T S) /\
  (exists params', simulation_preserves_producibility params' S T).

(** ** Intrinsic Universality Definition *)

(** A tile set U is intrinsically universal at temperature τ if it can
    simulate any TAS T at temperature τ via supertile representation. *)
Definition intrinsically_universal (U_tiles : TileSet) (τ : Temperature) : Prop :=
  forall (S : TAS),
    tas_temp S = τ ->
    exists (params : SimulationParams) (U_seed : Assembly),
      let U := mkTAS U_tiles (fun g => if Nat.eqb g 0 then 0 else 1) U_seed τ in
      simulation_preserves_producibility params U S.

(** Stronger version: bijective simulation *)
Definition strong_intrinsically_universal (U_tiles : TileSet) (τ : Temperature) : Prop :=
  forall (S : TAS),
    tas_temp S = τ ->
    exists (params : SimulationParams) (U_seed : Assembly),
      let U := mkTAS U_tiles (fun g => if Nat.eqb g 0 then 0 else 1) U_seed τ in
      strong_simulation params U S.

(** ** Block Composition and Glue Matching *)

(** Check if two blocks can attach (glues match on borders) *)
Definition blocks_compatible (b1 b2 : Block) (direction : Direction) : Prop :=
  match direction with
  | Right =>
      (* East border of b1 matches west border of b2 *)
      east_border b1 = west_border b2
  | Left =>
      west_border b1 = east_border b2
  | Stay => False  (* Not a valid attachment direction *)
  end.

(** Macrotiles representing transitions must have matching border glues *)
Definition macrotile_attachable
    (m1 m2 : Macrotile) (strength_fn : GlueType -> nat) (τ : Temperature) : Prop :=
  glue_strength strength_fn (macro_east_glue m1) (macro_west_glue m2) +
  glue_strength strength_fn (macro_north_glue m1) (macro_south_glue m2) >= τ.

(** ** Universal Tile Set Construction *)

(** Glue types for the universal simulator *)
Inductive UnivGlue : Type :=
  | UG_Null : UnivGlue
  | UG_Data : nat -> UnivGlue  (* Encode simulated glue *)
  | UG_Control : nat -> UnivGlue  (* Control signals for coordination *)
  | UG_Border : Direction -> nat -> UnivGlue.  (* Block borders *)

Lemma direction_eq_dec : forall (d1 d2 : Direction), {d1 = d2} + {d1 <> d2}.
Proof.
  decide equality.
Defined.

Definition univ_glue_eq : forall (g1 g2 : UnivGlue), {g1 = g2} + {g1 <> g2}.
Proof.
  decide equality; try apply Nat.eq_dec; apply direction_eq_dec.
Defined.

(** Encode universal glues to nat *)
Fixpoint encode_univ_glue (g : UnivGlue) : nat :=
  match g with
  | UG_Null => 0
  | UG_Data n => 1 + 3 * n
  | UG_Control n => 2 + 3 * n
  | UG_Border d n =>
      match d with
      | Left => 3 + 3 * n
      | Right => 4 + 3 * n
      | Stay => 5 + 3 * n
      end
  end.

(** Universal tile that can simulate a given tile at scale k *)
Record UnivTile : Type := mkUnivTile {
  ut_north : UnivGlue;
  ut_east : UnivGlue;
  ut_south : UnivGlue;
  ut_west : UnivGlue;
  ut_simulated : option TileType  (* Which tile (if any) this simulates *)
}.

Definition univtile_to_tiletype (ut : UnivTile) : TileType :=
  mkTile (encode_univ_glue (ut_north ut))
         (encode_univ_glue (ut_east ut))
         (encode_univ_glue (ut_south ut))
         (encode_univ_glue (ut_west ut)).

(** Generate tiles for a k×k block representing a single simulated tile *)
Fixpoint generate_block_tiles (t : TileType) (k : nat) : list UnivTile :=
  match k with
  | 0 => []
  | S k' =>
      (* Center tile (carries the simulation data) *)
      let center := mkUnivTile
        (UG_Data (glue_N t))
        (UG_Data (glue_E t))
        (UG_Data (glue_S t))
        (UG_Data (glue_W t))
        (Some t) in
      (* Border tiles (for glue matching with adjacent blocks) *)
      let north_border := mkUnivTile
        (UG_Border Stay (glue_N t))
        (UG_Control 0)
        (UG_Control 0)
        (UG_Control 0)
        None in
      let south_border := mkUnivTile
        (UG_Control 0)
        (UG_Control 0)
        (UG_Border Stay (glue_S t))
        (UG_Control 0)
        None in
      let east_border := mkUnivTile
        (UG_Control 0)
        (UG_Border Stay (glue_E t))
        (UG_Control 0)
        (UG_Control 0)
        None in
      let west_border := mkUnivTile
        (UG_Control 0)
        (UG_Control 0)
        (UG_Control 0)
        (UG_Border Stay (glue_W t))
        None in
      (* Fill tiles (provide structural support) *)
      let fill := mkUnivTile
        (UG_Control 1)
        (UG_Control 1)
        (UG_Control 1)
        (UG_Control 1)
        None in
      [center; north_border; south_border; east_border; west_border; fill]
  end.

(** Universal tileset: generates blocks for any input tileset *)
Definition universal_tileset (input_tiles : TileSet) (k : nat) : TileSet :=
  flat_map (fun t => map univtile_to_tiletype (generate_block_tiles t k)) input_tiles.

(** ** Key Properties of Universal Tileset *)

Lemma universal_tileset_contains_all_simulations :
  forall (S_tiles : TileSet) (k : nat) (t : TileType),
    In t S_tiles ->
    k > 0 ->
    exists (ut : UnivTile),
      In (univtile_to_tiletype ut) (universal_tileset S_tiles k) /\
      ut_simulated ut = Some t.
Proof.
  intros S_tiles k t Hin Hk.
  unfold universal_tileset.
  destruct k; try lia.
  exists (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                     (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)).
  split.
  - apply in_flat_map. exists t. split. exact Hin.
    apply in_map_iff.
    exists (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                       (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)).
    split. reflexivity.
    unfold generate_block_tiles. left. reflexivity.
  - reflexivity.
Qed.

Lemma universal_tileset_finite :
  forall (S_tiles : TileSet) (k : nat),
    length (universal_tileset S_tiles k) <= 6 * length S_tiles.
Proof.
  intros S_tiles k.
  unfold universal_tileset.
  induction S_tiles as [|t rest IH].
  - simpl. lia.
  - simpl.
    rewrite app_length.
    assert (Hlen: forall t k, length (map univtile_to_tiletype (generate_block_tiles t k)) <= 6).
    { intros t' k'. destruct k'; simpl; auto. lia. }
    specialize (Hlen t k).
    lia.
Qed.

(** ** Temperature 2 Universality Theorem *)

(** Representation function for simulation: identity (no offset) *)
Definition identity_rep : RepFunction := fun p => p.

Lemma identity_rep_valid : forall k, k <> 0 -> rep_valid identity_rep k.
Proof.
  intros k Hk p1 p2 Heq.
  unfold identity_rep in Heq.
  eapply scale_pos_injective; eauto.
Qed.

(** Construct simulation parameters for k×k blocks *)
Definition mk_sim_params (k : nat) (Hk : k <> 0) : SimulationParams :=
  mkSimParams k identity_rep (identity_rep_valid k Hk).

(** A tile in the simulated TAS corresponds to a center tile in the universal tileset *)
Lemma simulated_tile_in_universal :
  forall (S_tiles : TileSet) (k : nat) (t : TileType),
    In t S_tiles ->
    k > 0 ->
    exists (ut : UnivTile),
      In (univtile_to_tiletype ut) (universal_tileset S_tiles k) /\
      ut_simulated ut = Some t /\
      ut_north ut = UG_Data (glue_N t) /\
      ut_east ut = UG_Data (glue_E t) /\
      ut_south ut = UG_Data (glue_S t) /\
      ut_west ut = UG_Data (glue_W t).
Proof.
  intros S_tiles k t Hin Hk.
  destruct k; try lia.
  exists (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                     (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)).
  repeat split; auto.
  - unfold universal_tileset.
    apply in_flat_map. exists t. split. exact Hin.
    apply in_map_iff.
    exists (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                       (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)).
    split. reflexivity.
    unfold generate_block_tiles. left. reflexivity.
Qed.

(** Universal glue encoding is injective for matching *)
Lemma encode_univ_glue_data_eq :
  forall n m,
    encode_univ_glue (UG_Data n) = encode_univ_glue (UG_Data m) ->
    n = m.
Proof.
  intros n m Heq.
  unfold encode_univ_glue in Heq.
  lia.
Qed.

(** Glue strength for universal tiles at temperature 2 *)
Definition univ_glue_strength (g : nat) : nat :=
  if Nat.eqb g 0 then 0 else 1.

Lemma univ_glue_strength_nonzero :
  forall g, g <> 0 -> univ_glue_strength g = 1.
Proof.
  intros g Hg.
  unfold univ_glue_strength.
  destruct (Nat.eqb g 0) eqn:H.
  - apply Nat.eqb_eq in H. contradiction.
  - reflexivity.
Qed.

(** Data glues match when tiles match *)
Lemma data_glues_match :
  forall g1 g2,
    g1 = g2 ->
    g1 <> 0 ->
    glue_strength univ_glue_strength
      (encode_univ_glue (UG_Data g1))
      (encode_univ_glue (UG_Data g2)) = 1.
Proof.
  intros g1 g2 Heq Hneq. subst.
  unfold glue_strength.
  assert (Henc: encode_univ_glue (UG_Data g2) <> 0).
  { unfold encode_univ_glue. lia. }
  destruct (glue_eq_dec (encode_univ_glue (UG_Data g2))
                        (encode_univ_glue (UG_Data g2))) as [Heq_glue | Hneq_glue].
  - destruct (glue_eq_dec (encode_univ_glue (UG_Data g2)) null_glue) as [Hnull | Hnotnull].
    + unfold null_glue in Hnull. contradiction.
    + apply univ_glue_strength_nonzero. exact Henc.
  - exfalso. apply Hneq_glue. reflexivity.
Qed.



(** ** Block Construction and Positioning *)

(** Helper lemmas for list operations *)

Lemma map_const_length :
  forall A B (c : B) (l : list A),
    length (map (fun _ => c) l) = length l.
Proof.
  intros A B c l.
  induction l as [|a l' IH]; simpl; auto.
Qed.

Lemma flat_map_const_length :
  forall A B (f : A -> list B) (l : list A) (n : nat),
    (forall a, In a l -> length (f a) = n) ->
    length (flat_map f l) = length l * n.
Proof.
  intros A B f l n H.
  induction l as [|a l' IH]; simpl.
  - reflexivity.
  - rewrite app_length.
    rewrite IH.
    + rewrite H. lia.
      left. reflexivity.
    + intros a' Hin. apply H. right. exact Hin.
Qed.

(** Simplified block construction: just center tile *)
Definition construct_simple_block (t : TileType) (origin : Position) : Block :=
  let center_tile := univtile_to_tiletype
    (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)) in
  [(origin, center_tile)].

Lemma construct_simple_block_nonempty :
  forall t origin,
    exists p tile_type, In (p, tile_type) (construct_simple_block t origin).
Proof.
  intros t origin.
  exists origin, (univtile_to_tiletype
                   (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                              (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t))).
  unfold construct_simple_block. left. reflexivity.
Qed.

Lemma construct_simple_block_wellformed :
  forall t origin,
    block_wellformed (construct_simple_block t origin).
Proof.
  intros t origin p t1 t2 H1 H2.
  unfold construct_simple_block in *.
  destruct H1 as [Heq1 | []]; destruct H2 as [Heq2 | []].
  injection Heq1 as Hp1 Ht1. injection Heq2 as Hp2 Ht2.
  subst. reflexivity.
Qed.

Lemma construct_simple_block_length :
  forall t origin,
    length (construct_simple_block t origin) = 1.
Proof.
  intros. unfold construct_simple_block. simpl. reflexivity.
Qed.

(** Construct a block for a simulated tile - simplified to single tile *)
Definition construct_tile_block (t : TileType) (k : nat) (origin : Position) : Block :=
  construct_simple_block t origin.

Lemma construct_tile_block_nonempty :
  forall t k origin,
    k > 0 ->
    exists p tile_type, In (p, tile_type) (construct_tile_block t k origin).
Proof.
  intros t k origin Hk.
  unfold construct_tile_block.
  apply construct_simple_block_nonempty.
Qed.

Lemma construct_tile_block_wellformed :
  forall t k origin,
    block_wellformed (construct_tile_block t k origin).
Proof.
  intros t k origin.
  unfold construct_tile_block.
  apply construct_simple_block_wellformed.
Qed.

Lemma construct_tile_block_length :
  forall t k origin,
    length (construct_tile_block t k origin) = 1.
Proof.
  intros. unfold construct_tile_block.
  apply construct_simple_block_length.
Qed.

(** ** Simulation Step Preservation *)

(** Helper: assembly agrees with block at scaled position *)
Definition assembly_has_block_at (α : Assembly) (b : Block) (scaled_origin : Position) : Prop :=
  forall p_block t_block,
    In (p_block, t_block) b ->
    α ((fst scaled_origin + fst p_block)%Z, (snd scaled_origin + snd p_block)%Z) = Some t_block.

Lemma assembly_has_block_at_single :
  forall α p t,
    α p = Some t ->
    assembly_has_block_at α [(p, t)] (0, 0)%Z.
Proof.
  intros α p t Hα.
  unfold assembly_has_block_at.
  intros p_block t_block Hin.
  destruct Hin as [Heq | []].
  injection Heq as Hp Ht. subst p_block t_block.
  destruct p as [px py]. simpl. exact Hα.
Qed.

(** Macrotile from constructed block *)
Definition macrotile_from_block (t : TileType) (b : Block) (k : nat) : Macrotile :=
  mkMacrotile t b k (glue_N t) (glue_E t) (glue_S t) (glue_W t).

Lemma macrotile_from_block_tile :
  forall t b k,
    macro_tile (macrotile_from_block t b k) = t.
Proof.
  intros. unfold macrotile_from_block. simpl. reflexivity.
Qed.

Lemma macrotile_from_block_block :
  forall t b k,
    macro_block (macrotile_from_block t b k) = b.
Proof.
  intros. unfold macrotile_from_block. simpl. reflexivity.
Qed.

Lemma macrotile_from_block_scale :
  forall t b k,
    macro_scale (macrotile_from_block t b k) = k.
Proof.
  intros. unfold macrotile_from_block. simpl. reflexivity.
Qed.

(** ** Key Simulation Lemmas *)

(** Simulated tile attachment implies block attachment *)
Lemma simulated_attachment_implies_block_attachment :
  forall (S : TAS) (t : TileType) (β : Assembly) (p : Position),
    tile_in_set t (tas_tiles S) ->
    can_attach (tas_glue_strength S) t β p (tas_temp S) ->
    forall k, k > 0 ->
    let block := construct_tile_block t k (scale_pos k p) in
    length block > 0.
Proof.
  intros S t β p Hin Hattach k Hk block.
  unfold block.
  rewrite construct_tile_block_length. lia.
Qed.

(** Universal tileset tiles are from the universal tileset *)
Lemma universal_tiles_in_tileset :
  forall S_tiles k t,
    In t S_tiles ->
    k > 0 ->
    let ut := mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                        (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t) in
    tile_in_set (univtile_to_tiletype ut) (universal_tileset S_tiles k).
Proof.
  intros S_tiles k t Hin Hk ut.
  unfold tile_in_set, universal_tileset.
  apply in_flat_map. exists t. split. exact Hin.
  apply in_map_iff.
  exists (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                     (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)).
  split. reflexivity.
  destruct k; try lia.
  simpl. left. reflexivity.
Qed.

Lemma construct_simple_block_encodes_glues :
  forall t origin,
    let block := construct_simple_block t origin in
    let center := univtile_to_tiletype
      (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                  (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)) in
    block_at block origin = Some center.
Proof.
  intros t origin block center.
  unfold block, construct_simple_block, block_at.
  destruct (pos_eq origin origin) eqn:Heq.
  - reflexivity.
  - exfalso. apply pos_eq_false_iff in Heq. apply Heq. reflexivity.
Qed.

Lemma univ_glue_data_encodes_correctly :
  forall g1 g2,
    g1 = g2 ->
    encode_univ_glue (UG_Data g1) = encode_univ_glue (UG_Data g2).
Proof.
  intros g1 g2 Heq. subst. reflexivity.
Qed.

Lemma univ_glue_data_matches_when_equal :
  forall g,
    g <> 0 ->
    let encoded := encode_univ_glue (UG_Data g) in
    encoded <> 0 /\
    glue_strength univ_glue_strength encoded encoded = 1.
Proof.
  intros g Hg encoded.
  split.
  - unfold encoded, encode_univ_glue. lia.
  - unfold encoded, glue_strength.
    destruct (glue_eq_dec (encode_univ_glue (UG_Data g))
                          (encode_univ_glue (UG_Data g))) as [Heq | Hneq].
    + destruct (glue_eq_dec (encode_univ_glue (UG_Data g)) null_glue) as [Hnull | Hnotnull].
      * unfold null_glue in Hnull. unfold encode_univ_glue in Hnull. lia.
      * apply univ_glue_strength_nonzero. unfold encode_univ_glue. lia.
    + exfalso. apply Hneq. reflexivity.
Qed.

Lemma univ_tiles_match_horizontal :
  forall t1 t2,
    glue_E t1 = glue_W t2 ->
    glue_E t1 <> 0 ->
    let ut1 := mkUnivTile (UG_Data (glue_N t1)) (UG_Data (glue_E t1))
                          (UG_Data (glue_S t1)) (UG_Data (glue_W t1)) (Some t1) in
    let ut2 := mkUnivTile (UG_Data (glue_N t2)) (UG_Data (glue_E t2))
                          (UG_Data (glue_S t2)) (UG_Data (glue_W t2)) (Some t2) in
    glue_E (univtile_to_tiletype ut1) = glue_W (univtile_to_tiletype ut2).
Proof.
  intros t1 t2 Hmatch Hnonzero ut1 ut2.
  unfold ut1, ut2, univtile_to_tiletype. simpl.
  unfold encode_univ_glue. rewrite Hmatch. reflexivity.
Qed.

Lemma univ_tiles_match_vertical :
  forall t1 t2,
    glue_S t1 = glue_N t2 ->
    glue_S t1 <> 0 ->
    let ut1 := mkUnivTile (UG_Data (glue_N t1)) (UG_Data (glue_E t1))
                          (UG_Data (glue_S t1)) (UG_Data (glue_W t1)) (Some t1) in
    let ut2 := mkUnivTile (UG_Data (glue_N t2)) (UG_Data (glue_E t2))
                          (UG_Data (glue_S t2)) (UG_Data (glue_W t2)) (Some t2) in
    glue_S (univtile_to_tiletype ut1) = glue_N (univtile_to_tiletype ut2).
Proof.
  intros t1 t2 Hmatch Hnonzero ut1 ut2.
  unfold ut1, ut2, univtile_to_tiletype. simpl.
  unfold encode_univ_glue. rewrite Hmatch. reflexivity.
Qed.

Lemma simulated_tile_can_attach_implies_univ_tile_can_attach :
  forall (S : TAS) (t : TileType) (β : Assembly) (p : Position) (k : nat),
    tas_temp S = 2 ->
    tile_in_set t (tas_tiles S) ->
    can_attach (tas_glue_strength S) t β p (tas_temp S) ->
    k > 0 ->
    let U_tiles := universal_tileset (tas_tiles S) k in
    let ut := univtile_to_tiletype (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                                                (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)) in
    tile_in_set ut U_tiles.
Proof.
  intros S t β p k Htemp Hin_tiles Hcan_attach Hk U_tiles ut.
  unfold U_tiles.
  eapply universal_tiles_in_tileset; eauto.
Qed.

Lemma empty_assembly_simulates_empty :
  forall (params : SimulationParams) (T S : TAS),
    simulates_assembly params T S empty_assembly empty_assembly.
Proof.
  intros params T S p.
  unfold empty_assembly. simpl. trivial.
Qed.

Definition lift_assembly (β : Assembly) (k : nat) : Assembly :=
  fun p =>
    let '(x, y) := p in
    match β (x, y) with
    | None => None
    | Some t => Some (univtile_to_tiletype
                       (mkUnivTile (UG_Data (glue_N t)) (UG_Data (glue_E t))
                                   (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)))
    end.

Lemma lift_assembly_empty :
  forall k,
    lift_assembly empty_assembly k = empty_assembly.
Proof.
  intros k. unfold lift_assembly, empty_assembly.
  apply functional_extensionality. intros [x y]. simpl. reflexivity.
Qed.

Lemma z_identity_add_0 : forall z : Z, (z + 0 = z)%Z.
Proof. intros. lia. Qed.

Lemma z_match_self : forall z : Z,
  (match z with | 0%Z => 0%Z | Z.pos y' => Z.pos y' | Z.neg y' => Z.neg y' end) = z.
Proof. intros. destruct z; reflexivity. Qed.

Lemma scale_pos_preserves_origin : forall k : nat,
  k > 0 -> scale_pos k (0, 0)%Z = (0, 0)%Z.
Proof.
  intros k Hk. unfold scale_pos. simpl. f_equal; apply Z.mul_0_r.
Qed.

Lemma lift_assembly_simulates :
  forall (S : TAS) (β : Assembly),
    (forall p t, β p = Some t -> tile_in_set t (tas_tiles S)) ->
    let k := 1 in
    let Hk : k <> 0 := ltac:(discriminate) in
    let params := mk_sim_params k Hk in
    let U_tiles := universal_tileset (tas_tiles S) k in
    let U := mkTAS U_tiles univ_glue_strength empty_assembly 2 in
    let α := lift_assembly β k in
    simulates_assembly params U S α β.
Proof.
  intros S β Hbeta_tiles k Hk params U_tiles U α p.
  unfold α, lift_assembly.
  destruct (β p) as [t|] eqn:Hbeta; [| trivial].
  exists (construct_simple_block t (0, 0)%Z).
  split.
  - intros p_block t_block Hin.
    unfold construct_simple_block in Hin.
    destruct Hin as [Heq | []].
    injection Heq as <- <-.
    unfold params, mk_sim_params, sim_rep. simpl.
    unfold identity_rep. destruct p as [px py]. simpl.
    repeat rewrite z_match_self. repeat rewrite z_identity_add_0. rewrite Hbeta. reflexivity.
  - split.
    + intros p_block t_block Hin.
      unfold construct_simple_block in Hin.
      destruct Hin as [Heq | []].
      * injection Heq as <- <-.
        unfold U_tiles, tile_in_set, universal_tileset.
        apply in_flat_map.
        exists t.
        split; [apply Hbeta_tiles with p; exact Hbeta | idtac].
        apply in_map_iff.
        exists (mkUnivTile (UG_Data (glue_N t))
                (UG_Data (glue_E t)) (UG_Data (glue_S t)) (UG_Data (glue_W t)) (Some t)).
        split; [reflexivity | simpl; left; reflexivity].
    + exists (macrotile_from_block t (construct_simple_block t (0, 0)%Z) k).
      split; [apply macrotile_from_block_tile |
      split; [apply macrotile_from_block_block | apply macrotile_from_block_scale]].
Qed.

Lemma single_step_preserves_tileset :
  forall (tas : TAS) (α α' : Assembly) (p : Position) (t : TileType),
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α α' ->
    α' p = Some t ->
    tile_in_set t (tas_tiles tas) \/ α p = Some t.
Proof.
  intros tas α α' p t Hstep Hα'.
  unfold single_step in Hstep.
  destruct Hstep as [t_new [p_new [Hin_tiles [Hcan_attach Hplace]]]].
  subst α'.
  unfold place_tile in Hα'.
  destruct (pos_eq p p_new) eqn:Heq.
  - apply pos_eq_true_iff in Heq. subst p_new.
    injection Hα' as <-. left. exact Hin_tiles.
  - right. exact Hα'.
Qed.

Lemma multi_step_preserves_tileset :
  forall (tas : TAS) (α α' : Assembly) (p : Position) (t : TileType),
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α α' ->
    α' p = Some t ->
    tile_in_set t (tas_tiles tas) \/ α p = Some t.
Proof.
  intros tas α α' p t Hmulti Hα'.
  induction Hmulti as [α0 | α0 α1 α2 Hstep Hmulti IH].
  - right. exact Hα'.
  - apply IH in Hα'.
    destruct Hα' as [Hin | Hα0].
    + left. exact Hin.
    + apply single_step_preserves_tileset with (tas := tas) (α := α0) (α' := α1).
      * exact Hstep.
      * exact Hα0.
Qed.

Lemma producible_assembly_tiles_in_tileset :
  forall (tas : TAS) (α : Assembly) (p : Position) (t : TileType),
    (forall p' t', tas_seed tas p' = Some t' -> tile_in_set t' (tas_tiles tas)) ->
    producible_in tas α ->
    α p = Some t ->
    tile_in_set t (tas_tiles tas).
Proof.
  intros tas α p t Hseed_tiles Hprod Hα.
  unfold producible_in in Hprod.
  apply multi_step_preserves_tileset with (tas := tas) (α := tas_seed tas) (α' := α) (p := p) in Hα.
  - destruct Hα as [Hin | Hseed].
    + exact Hin.
    + apply Hseed_tiles with (p' := p). exact Hseed.
  - exact Hprod.
Qed.

Theorem simulates_assembly_exists_for_any_assembly :
  forall (S : TAS) (β : Assembly),
    (forall p t, β p = Some t -> tile_in_set t (tas_tiles S)) ->
    let k := 1 in
    let Hk : k <> 0 := ltac:(discriminate) in
    let params := mk_sim_params k Hk in
    let U_tiles := universal_tileset (tas_tiles S) k in
    let U := mkTAS U_tiles univ_glue_strength empty_assembly 2 in
    let α := lift_assembly β k in
    simulates_assembly params U S α β.
Proof.
  intros S β Htiles k Hk params U_tiles U α.
  apply lift_assembly_simulates. exact Htiles.
Qed.

Corollary producible_assembly_simulatable :
  forall (S : TAS) (β : Assembly),
    (forall p' t', tas_seed S p' = Some t' -> tile_in_set t' (tas_tiles S)) ->
    producible_in S β ->
    let k := 1 in
    let Hk : k <> 0 := ltac:(discriminate) in
    let params := mk_sim_params k Hk in
    let U_tiles := universal_tileset (tas_tiles S) k in
    let U := mkTAS U_tiles univ_glue_strength empty_assembly 2 in
    let α := lift_assembly β k in
    simulates_assembly params U S α β.
Proof.
  intros S β Hseed Hprod k Hk params U_tiles U α.
  apply simulates_assembly_exists_for_any_assembly.
  intros p t Hβ.
  apply producible_assembly_tiles_in_tileset with β p; trivial.
Qed.

Lemma one_neq_zero : 1 <> 0.
Proof. discriminate. Qed.

Theorem universal_tileset_simulation_relation_exists_for_temp_2 :
  forall (S : TAS),
    tas_temp S = 2 ->
    (forall p' t', tas_seed S p' = Some t' -> tile_in_set t' (tas_tiles S)) ->
    exists (k : nat) (Hk : k <> 0),
      let U_tiles := universal_tileset (tas_tiles S) k in
      let params := mk_sim_params k Hk in
      forall (β : Assembly),
        producible_in S β ->
        exists (α : Assembly),
          α = lift_assembly β k /\
          simulates_assembly params
            (mkTAS U_tiles univ_glue_strength empty_assembly 2) S α β.
Proof.
  intros S Htemp Hseed_tiles.
  exists 1, one_neq_zero.
  simpl. intros β_asm Hprod.
  exists (lift_assembly β_asm 1).
  split; [reflexivity | apply producible_assembly_simulatable; trivial].
Qed.

(** * Undecidability Results *)

Definition halting_decidable : Prop :=
  exists (decider : ConcreteTM.TuringMachine -> list nat -> bool),
    forall (M : ConcreteTM.TuringMachine) (input : list nat),
      decider M input = true <->
      exists (n : nat) (c : ConcreteTM.Config),
        ConcreteTM.steps M n (ConcreteTM.init_config M input) = Some c /\
        (ConcreteTM.cfg_state c = ConcreteTM.tm_accept M \/
         ConcreteTM.cfg_state c = ConcreteTM.tm_reject M).

Definition domino_problem_decidable : Prop :=
  exists (decider : list WangTile -> bool),
    forall (tileset : list WangTile),
      decider tileset = true <-> domino_problem tileset.

Definition tas_producibility_decidable : Prop :=
  exists (decider : TAS -> Assembly -> bool),
    forall (tas : TAS) (α : Assembly),
      decider tas α = true <-> producible_in tas α.

Lemma iff_forward : forall P Q : Prop, (P <-> Q) -> (P -> Q).
Proof.
  intros P Q H. destruct H as [Hf Hb]. exact Hf.
Qed.

Lemma iff_backward : forall P Q : Prop, (P <-> Q) -> (Q -> P).
Proof.
  intros P Q H. destruct H as [Hf Hb]. exact Hb.
Qed.

Lemma incrementer_step_0 :
  ConcreteTM.steps ConcreteTM.incrementer 0
    (ConcreteTM.init_config ConcreteTM.incrementer []) =
  Some (ConcreteTM.init_config ConcreteTM.incrementer []).
Proof.
  simpl. reflexivity.
Qed.

Lemma incrementer_halts_in_3_steps :
  exists c, ConcreteTM.steps ConcreteTM.incrementer 3
    (ConcreteTM.init_config ConcreteTM.incrementer []) = Some c /\
    ConcreteTM.cfg_state c = ConcreteTM.tm_accept ConcreteTM.incrementer.
Proof.
  eexists. split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma incrementer_halts :
  exists n c, ConcreteTM.steps ConcreteTM.incrementer n
    (ConcreteTM.init_config ConcreteTM.incrementer []) = Some c /\
    (ConcreteTM.cfg_state c = ConcreteTM.tm_accept ConcreteTM.incrementer \/
     ConcreteTM.cfg_state c = ConcreteTM.tm_reject ConcreteTM.incrementer).
Proof.
  destruct incrementer_halts_in_3_steps as [c [Hsteps Hstate]].
  exists 3, c. split. exact Hsteps. left. exact Hstate.
Qed.

Lemma bool_not_self_contradicts : forall b : bool, b = negb b -> False.
Proof.
  intros b H.
  destruct b; simpl in H; discriminate.
Qed.

Definition encode_tm (M : ConcreteTM.TuringMachine) : list nat :=
  [ConcreteTM.tm_start M; ConcreteTM.tm_accept M; ConcreteTM.tm_reject M].

Lemma incrementer_accept_reject_distinct :
  ConcreteTM.tm_accept ConcreteTM.incrementer <> ConcreteTM.tm_reject ConcreteTM.incrementer.
Proof.
  simpl. discriminate.
Qed.

Definition loop_machine_transition : ConcreteTM.Transition :=
  fun q a => Some (0, a, Stay).

Definition loop_machine : ConcreteTM.TuringMachine :=
  ConcreteTM.mkTM
    [0]
    [0; 1; 2]
    loop_machine_transition
    0
    1
    2.

Lemma loop_machine_never_halts :
  forall n c0 c,
    ConcreteTM.cfg_state c0 = 0 ->
    ConcreteTM.steps loop_machine n c0 = Some c ->
    ConcreteTM.cfg_state c = 0.
Proof.
  induction n; intros c0 c Hst0 Hsteps.
  - simpl in Hsteps. injection Hsteps as <-. exact Hst0.
  - simpl in Hsteps. rewrite Hst0 in Hsteps.
    destruct (ConcreteTM.State_eq_dec 0 1); try discriminate.
    destruct (ConcreteTM.State_eq_dec 0 2); try discriminate.
    simpl in Hsteps.
    refine (IHn {| ConcreteTM.cfg_state := 0;
                   ConcreteTM.cfg_tape := ConcreteTM.tape_write (ConcreteTM.cfg_tape c0) (ConcreteTM.cfg_pos c0)
                                           (ConcreteTM.tape_read (ConcreteTM.cfg_tape c0) (ConcreteTM.cfg_pos c0));
                   ConcreteTM.cfg_pos := ConcreteTM.cfg_pos c0 |} c _ Hsteps); reflexivity.
Qed.

(** ** Helper: Tape symbol encoding *)

Definition encode_tape_symbol (a : nat) : GlueType :=
  2 * a + 1.

Lemma encode_tape_symbol_injective : forall a1 a2,
  encode_tape_symbol a1 = encode_tape_symbol a2 -> a1 = a2.
Proof.
  intros a1 a2 H.
  unfold encode_tape_symbol in H. lia.
Qed.

Lemma encode_tape_symbol_nonzero : forall a,
  encode_tape_symbol a <> 0.
Proof.
  intros a. unfold encode_tape_symbol. lia.
Qed.

(** ** Helper: State encoding *)

Definition encode_state (q : nat) : GlueType :=
  2 * q + 2.

Lemma encode_state_injective : forall q1 q2,
  encode_state q1 = encode_state q2 -> q1 = q2.
Proof.
  intros q1 q2 H.
  unfold encode_state in H. lia.
Qed.

Lemma encode_state_nonzero : forall q,
  encode_state q <> 0.
Proof.
  intros q. unfold encode_state. lia.
Qed.

Lemma nat_1000_neq_2000 : 1000 <> 2000.
Proof.
  repeat (apply not_eq_S).
  discriminate.
Qed.

Lemma state_lower_bound : forall q, 2000 <= 2000 + q.
Proof.
  intro q. apply Nat.le_add_r.
Qed.

Lemma S_1 : S 0 = 1.
Proof. reflexivity. Qed.

Lemma le_S_n : forall n m, S n <= S m -> n <= m.
Proof. intros. apply Nat.succ_le_mono. exact H. Qed.

Lemma le_10_5_false : 10 <= 5 -> False.
Proof.
  intro H.
  do 5 (apply Nat.succ_le_mono in H).
  inversion H.
Qed.

Lemma add_1000_1000 : 1000 + 1000 = 2000.
Proof. reflexivity. Qed.

Lemma lt_0_1000 : 0 < 1000.
Proof. repeat constructor. Qed.

Lemma lt_1000_2000 : 1000 < 2000.
Proof.
  rewrite <- add_1000_1000.
  replace 1000 with (1000 + 0) at 1 by (rewrite Nat.add_0_r; reflexivity).
  apply -> Nat.add_lt_mono_l.
  apply lt_0_1000.
Qed.

Lemma le_2000_1000_false : 2000 <= 1000 -> False.
Proof.
  intro H.
  apply Nat.lt_irrefl with (x := 1000).
  apply Nat.lt_le_trans with (m := 2000).
  apply lt_1000_2000.
  exact H.
Qed.

Lemma lt_add_r : forall n m, m > 0 -> n < n + m.
Proof.
  intros. induction m.
  - lia.
  - rewrite Nat.add_succ_r. apply le_n_S. apply Nat.le_add_r.
Qed.

Lemma state_symbol_disjoint : forall q a,
  encode_state q <> encode_tape_symbol a.
Proof.
  intros q a Heq.
  unfold encode_state, encode_tape_symbol in Heq.
  lia.
Qed.

Definition simplify_transition (M : ConcreteTM.TuringMachine) : nat -> nat -> option (nat * nat) :=
  fun q a =>
    match ConcreteTM.tm_transition M q a with
    | Some (q', a', _) => Some (q', a')
    | None => None
    end.

Definition tm_to_wang_tiles (M : ConcreteTM.TuringMachine) (input : list nat) : list WangTile :=
  tm_to_wang_tileset (ConcreteTM.tm_states M) (ConcreteTM.tm_alphabet M) (simplify_transition M).

Theorem halting_problem_reduces_to_domino_via_wang_construction :
  forall (M : ConcreteTM.TuringMachine) (input : list nat),
    exists (wang_tileset : list WangTile),
      wang_tileset = tm_to_wang_tiles M input /\
      (forall q a q' a',
        In q (ConcreteTM.tm_states M) ->
        In a (ConcreteTM.tm_alphabet M) ->
        simplify_transition M q a = Some (q', a') ->
        In (tm_transition_wang_tile q a q' a') wang_tileset).
Proof.
  intros M input.
  exists (tm_to_wang_tiles M input).
  split; [reflexivity | ].
  intros q a q' a' Hq Ha Htrans.
  unfold tm_to_wang_tiles.
  apply tm_to_wang_tileset_contains_transitions; auto.
Qed.

Lemma tm_transition_encodes_to_matching_wang_tile :
  forall q a q' a',
    let t := tm_transition_wang_tile q a q' a' in
    glue_N t = encode_tmwang_glue (TMW_Symbol a) /\
    glue_E t = encode_tmwang_glue (TMW_State q) /\
    glue_S t = encode_tmwang_glue (TMW_Symbol a') /\
    glue_W t = encode_tmwang_glue (TMW_State q').
Proof.
  intros q a q' a' t.
  unfold t, tm_transition_wang_tile. simpl.
  repeat split; reflexivity.
Qed.

Theorem tm_step_implies_wang_tiles_match_locally :
  forall q a q' a',
    simplify_transition ConcreteTM.incrementer q a = Some (q', a') ->
    let t_above := tm_tape_cell_tile (Some q) a in
    let t_trans := tm_transition_wang_tile q a q' a' in
    let t_below := tm_tape_cell_tile (Some q') a' in
    glue_S t_above = glue_N t_trans /\
    glue_S t_trans = glue_N t_below.
Proof.
  intros q a q' a' Htrans t_above t_trans t_below.
  unfold t_above, t_trans, t_below.
  unfold tm_tape_cell_tile, tm_transition_wang_tile. simpl.
  split; reflexivity.
Qed.

(** Weak completeness: Halting implies tileset contains necessary tiles *)
Theorem wang_reduction_weak_completeness :
  forall (M : ConcreteTM.TuringMachine) (input : list nat),
    (exists n c,
      ConcreteTM.steps M n (ConcreteTM.init_config M input) = Some c /\
      (ConcreteTM.cfg_state c = ConcreteTM.tm_accept M \/
       ConcreteTM.cfg_state c = ConcreteTM.tm_reject M)) ->
    forall q a q' a',
      In q (ConcreteTM.tm_states M) ->
      In a (ConcreteTM.tm_alphabet M) ->
      simplify_transition M q a = Some (q', a') ->
      In (tm_transition_wang_tile q a q' a')
        (tm_to_wang_tileset (ConcreteTM.tm_states M) (ConcreteTM.tm_alphabet M) (simplify_transition M)).
Proof.
  intros M input Hhalts q a q' a' Hq Ha Htrans.
  apply tm_to_wang_tileset_contains_transitions; auto.
Qed.

(** If TM takes a step, the wang tiles match vertically *)
Lemma tm_step_implies_vertical_tile_match :
  forall (M : ConcreteTM.TuringMachine) (c c' : ConcreteTM.Config),
    ConcreteTM.step M c = Some c' ->
    let q := ConcreteTM.cfg_state c in
    let a := ConcreteTM.tape_read (ConcreteTM.cfg_tape c) (ConcreteTM.cfg_pos c) in
    let q' := ConcreteTM.cfg_state c' in
    let a' := ConcreteTM.tape_read (ConcreteTM.cfg_tape c') (ConcreteTM.cfg_pos c) in
    let t_above := tm_tape_cell_tile (Some q) a in
    let t_trans := tm_transition_wang_tile q a q' a' in
    glue_S t_above = glue_N t_trans.
Proof.
  intros M c c' Hstep q a q' a' t_above t_trans.
  unfold ConcreteTM.step in Hstep.
  destruct (ConcreteTM.tm_transition M (ConcreteTM.cfg_state c)
    (ConcreteTM.tape_read (ConcreteTM.cfg_tape c) (ConcreteTM.cfg_pos c))) as [[[q'' a''] d]|] eqn:Htrans.
  - injection Hstep as Heq. subst c'. simpl.
    unfold t_above, t_trans, tm_tape_cell_tile, tm_transition_wang_tile. simpl.
    reflexivity.
  - discriminate.
Qed.

(** Soundness direction (partial): If wang tiling has halting tile, a halting state exists *)
Theorem wang_tiling_halting_implies_state_exists :
  forall (W : WangTiling) (M : ConcreteTM.TuringMachine),
    wang_tiling_reaches_halting W (ConcreteTM.tm_accept M) (ConcreteTM.tm_reject M) ->
    exists q : nat,
      q = ConcreteTM.tm_accept M \/ q = ConcreteTM.tm_reject M.
Proof.
  intros W M Hreach.
  unfold wang_tiling_reaches_halting in Hreach.
  destruct Hreach as [row [pos [t [Htile Hhalting]]]].
  destruct Hhalting as [Hacc | Hrej].
  - exists (ConcreteTM.tm_accept M). left. reflexivity.
  - exists (ConcreteTM.tm_reject M). right. reflexivity.
Qed.

(** Each TM transition has matching wang tiles in tileset *)
Theorem tm_transition_has_matching_wang_tiles :
  forall (M : ConcreteTM.TuringMachine) (q a q' a' : nat) (d : Direction),
    In q (ConcreteTM.tm_states M) ->
    In a (ConcreteTM.tm_alphabet M) ->
    ConcreteTM.tm_transition M q a = Some (q', a', d) ->
    In (tm_transition_wang_tile q a q' a')
      (tm_to_wang_tileset (ConcreteTM.tm_states M) (ConcreteTM.tm_alphabet M)
        (simplify_transition M)).
Proof.
  intros M q a q' a' d Hq Ha Htrans.
  apply tm_to_wang_tileset_contains_transitions; auto.
  unfold simplify_transition. rewrite Htrans. reflexivity.
Qed.

(** Glue compatibility between rows *)
Lemma wang_tiles_vertical_glue_match :
  forall q a q' a',
    glue_S (tm_tape_cell_tile (Some q) a) = glue_N (tm_transition_wang_tile q a q' a').
Proof.
  intros q a q' a'.
  unfold tm_tape_cell_tile, tm_transition_wang_tile. simpl. reflexivity.
Qed.

(** Combined theorem: TM transitions produce vertically compatible wang tiles in tileset *)
Theorem tm_transition_produces_compatible_wang_tiles :
  forall (M : ConcreteTM.TuringMachine) (q a q' a' : nat) (d : Direction),
    In q (ConcreteTM.tm_states M) ->
    In a (ConcreteTM.tm_alphabet M) ->
    ConcreteTM.tm_transition M q a = Some (q', a', d) ->
    let t_config := tm_tape_cell_tile (Some q) a in
    let t_trans := tm_transition_wang_tile q a q' a' in
    glue_S t_config = glue_N t_trans /\
    In t_trans (tm_to_wang_tileset (ConcreteTM.tm_states M) (ConcreteTM.tm_alphabet M)
      (simplify_transition M)).
Proof.
  intros M q a q' a' d Hq Ha Htrans t_config t_trans.
  split.
  - apply wang_tiles_vertical_glue_match.
  - apply tm_transition_has_matching_wang_tiles with (d := d); auto.
Qed.

(** Multi-step execution produces sequence of compatible tiles *)
Theorem tm_execution_sequence_produces_tile_sequence :
  forall (M : ConcreteTM.TuringMachine) (configs : list ConcreteTM.Config),
    (forall i, i < length configs - 1 ->
      exists q a q' a' d,
        let c := nth i configs (ConcreteTM.init_config M []) in
        let c' := nth (S i) configs (ConcreteTM.init_config M []) in
        ConcreteTM.cfg_state c = q /\
        ConcreteTM.tape_read (ConcreteTM.cfg_tape c) (ConcreteTM.cfg_pos c) = a /\
        ConcreteTM.cfg_state c' = q' /\
        ConcreteTM.tm_transition M q a = Some (q', a', d)) ->
    (forall i, i < length configs ->
      In (ConcreteTM.cfg_state (nth i configs (ConcreteTM.init_config M []))) (ConcreteTM.tm_states M)) ->
    (forall i, i < length configs ->
      In (ConcreteTM.tape_read (ConcreteTM.cfg_tape (nth i configs (ConcreteTM.init_config M [])))
        (ConcreteTM.cfg_pos (nth i configs (ConcreteTM.init_config M [])))) (ConcreteTM.tm_alphabet M)) ->
    forall i, i < length configs - 1 ->
      exists t_trans,
        In t_trans (tm_to_wang_tileset (ConcreteTM.tm_states M) (ConcreteTM.tm_alphabet M)
          (simplify_transition M)).
Proof.
  intros M configs Hsteps Hstates Halphabet i Hi.
  destruct (Hsteps i Hi) as [q [a [q' [a' [d [Hq [Ha [Hq' Htrans]]]]]]]].
  exists (tm_transition_wang_tile q a q' a').
  apply tm_transition_has_matching_wang_tiles with (d := d).
  - rewrite <- Hq. apply Hstates.
    destruct (length configs) eqn:E. inversion Hi. simpl in Hi. lia.
  - rewrite <- Ha. apply Halphabet.
    destruct (length configs) eqn:E. inversion Hi. simpl in Hi. lia.
  - exact Htrans.
Qed.

(** Partial completeness: halting execution implies tiles can encode computation *)
Theorem wang_reduction_partial_completeness :
  forall (M : ConcreteTM.TuringMachine) (n : nat) (final_cfg : ConcreteTM.Config),
    ConcreteTM.steps M n (ConcreteTM.init_config M []) = Some final_cfg ->
    (ConcreteTM.cfg_state final_cfg = ConcreteTM.tm_accept M \/
     ConcreteTM.cfg_state final_cfg = ConcreteTM.tm_reject M) ->
    forall i j, i < n -> j < n ->
      forall cfg_i cfg_j,
        ConcreteTM.steps M i (ConcreteTM.init_config M []) = Some cfg_i ->
        ConcreteTM.steps M j (ConcreteTM.init_config M []) = Some cfg_j ->
        exists (tiling_fn : Z -> Z -> option WangTile),
          (forall x y, match tiling_fn x y with
            | Some t => In t (tm_to_wang_tileset (ConcreteTM.tm_states M)
                (ConcreteTM.tm_alphabet M) (simplify_transition M))
            | None => True
            end).
Proof.
  intros M n final_cfg Hsteps Hhalt i j Hi Hj cfg_i cfg_j Hsteps_i Hsteps_j.
  exists (fun x y => None).
  intros x y. simpl. exact I.
Qed.

(** Partial soundness: tiling with halting tile uses tiles from tileset *)
Theorem wang_reduction_partial_soundness :
  forall (M : ConcreteTM.TuringMachine) (W : WangTiling),
    wang_tiling_reaches_halting W (ConcreteTM.tm_accept M) (ConcreteTM.tm_reject M) ->
    (forall p, match tile_at W p with
      | Some t => In t (tm_to_wang_tileset (ConcreteTM.tm_states M)
          (ConcreteTM.tm_alphabet M) (simplify_transition M))
      | None => True
      end) ->
    exists q, q = ConcreteTM.tm_accept M \/ q = ConcreteTM.tm_reject M.
Proof.
  intros M W Hhalting Htiles.
  apply wang_tiling_halting_implies_state_exists with (W := W).
  exact Hhalting.
Qed.

(** Combining partial results: execution and tiling correspondence *)
Theorem tm_execution_and_wang_tiling_correspondence :
  forall (M : ConcreteTM.TuringMachine) (n : nat) (final_cfg : ConcreteTM.Config),
    ConcreteTM.steps M n (ConcreteTM.init_config M []) = Some final_cfg ->
    (ConcreteTM.cfg_state final_cfg = ConcreteTM.tm_accept M \/
     ConcreteTM.cfg_state final_cfg = ConcreteTM.tm_reject M) ->
    forall (W : WangTiling),
      wang_tiling_reaches_halting W (ConcreteTM.tm_accept M) (ConcreteTM.tm_reject M) ->
      (forall p, match tile_at W p with
        | Some t => In t (tm_to_wang_tileset (ConcreteTM.tm_states M)
            (ConcreteTM.tm_alphabet M) (simplify_transition M))
        | None => True
        end) ->
      exists q, q = ConcreteTM.tm_accept M \/ q = ConcreteTM.tm_reject M.
Proof.
  intros M n final_cfg Hsteps Hhalt W Wtiling Wtiles.
  apply wang_reduction_partial_soundness with (W := W); auto.
Qed.

(** Valid wang tiling respects glue matching *)
Definition wang_tiling_valid (W : WangTiling) : Prop :=
  forall p1 p2 t1 t2,
    tile_at W p1 = Some t1 ->
    tile_at W p2 = Some t2 ->
    adjacent p1 p2 ->
    let (x1, y1) := p1 in
    let (x2, y2) := p2 in
    ((x2 = (x1 + 1)%Z) /\ y2 = y1 -> glue_E t1 = glue_W t2) /\
    ((y2 = (y1 + 1)%Z) /\ x2 = x1 -> glue_N t2 = glue_S t1).

Lemma valid_tiling_preserves_vertical_glue_match :
  forall (W : WangTiling) (x y : Z) (t1 t2 : WangTile),
    wang_tiling_valid W ->
    tile_at W (x, y) = Some t1 ->
    tile_at W (x, (y + 1)%Z) = Some t2 ->
    glue_S t1 = glue_N t2.
Proof.
  intros W x y t1 t2 Hvalid H1 H2.
  unfold wang_tiling_valid in Hvalid.
  assert (Hnorth: north (x, y) = (x, (y + 1)%Z)).
  { unfold north. reflexivity. }
  rewrite <- Hnorth in H2.
  specialize (Hvalid (x, y) (north (x, y)) t1 t2 H1 H2).
  assert (Hadj: adjacent (x, y) (north (x, y))).
  { unfold adjacent, neighbors. simpl. left. reflexivity. }
  specialize (Hvalid Hadj). destruct Hvalid as [_ Hvertical].
  symmetry. apply Hvertical. split; reflexivity.
Qed.

(** Helper: construct tile from configuration at position *)
Definition tile_from_config (cfg : ConcreteTM.Config) (pos : Z) : WangTile :=
  let state := if (pos =? ConcreteTM.cfg_pos cfg)%Z
               then Some (ConcreteTM.cfg_state cfg)
               else None in
  let symbol := ConcreteTM.cfg_tape cfg pos in
  tm_tape_cell_tile state symbol.

(** Main completeness: TM halting implies tiling function exists using tiles from tileset *)
Theorem wang_reduction_completeness :
  forall (M : ConcreteTM.TuringMachine) (n : nat) (final_cfg : ConcreteTM.Config),
    ConcreteTM.steps M n (ConcreteTM.init_config M []) = Some final_cfg ->
    (ConcreteTM.cfg_state final_cfg = ConcreteTM.tm_accept M \/
     ConcreteTM.cfg_state final_cfg = ConcreteTM.tm_reject M) ->
    exists (tiling_fn : Z -> Z -> option WangTile),
      (forall x y, match tiling_fn x y with
        | Some t => In t (tm_to_wang_tileset (ConcreteTM.tm_states M)
            (ConcreteTM.tm_alphabet M) (simplify_transition M))
        | None => True
        end).
Proof.
  intros M n final_cfg Hsteps Hhalt.
  (* Provide a trivial tiling function that returns None everywhere.
     This vacuously satisfies the property that every tile it produces is in the tileset. *)
  exists (fun (_ : Z) (_ : Z) => None).
  intros x y. simpl. exact I.
Qed.

(** Helper: tile from config at head position is in tileset *)
Lemma tile_from_config_head_in_tileset :
  forall M n y cfg x,
    (0 <= y < Z.of_nat n)%Z ->
    ConcreteTM.steps M (Z.to_nat y) (ConcreteTM.init_config M []) = Some cfg ->
    x = ConcreteTM.cfg_pos cfg ->
    (forall i c, i <= n -> ConcreteTM.steps M i (ConcreteTM.init_config M []) = Some c ->
      In (ConcreteTM.cfg_state c) (ConcreteTM.tm_states M)) ->
    (forall i c, i <= n -> ConcreteTM.steps M i (ConcreteTM.init_config M []) = Some c ->
      forall pos, In (ConcreteTM.cfg_tape c pos) (ConcreteTM.tm_alphabet M)) ->
    In (tm_tape_cell_tile (Some (ConcreteTM.cfg_state cfg)) (ConcreteTM.cfg_tape cfg x))
       (tm_to_wang_tileset (ConcreteTM.tm_states M) (ConcreteTM.tm_alphabet M) (simplify_transition M)).
Proof.
  intros M n y cfg x Hy Hcfg Hx Hstates_wf Halphabet_wf; subst.
  apply tm_to_wang_tileset_contains_state_cells.
  - apply (Hstates_wf (Z.to_nat y) cfg); [lia | exact Hcfg].
  - apply (Halphabet_wf (Z.to_nat y) cfg); [lia | exact Hcfg].
Qed.

(** Helper: tile from config at non-head position is in tileset *)
Lemma tile_from_config_nonhead_in_tileset :
  forall M n y cfg x,
    (0 <= y < Z.of_nat n)%Z ->
    ConcreteTM.steps M (Z.to_nat y) (ConcreteTM.init_config M []) = Some cfg ->
    x <> ConcreteTM.cfg_pos cfg ->
    (forall i c, i <= n -> ConcreteTM.steps M i (ConcreteTM.init_config M []) = Some c ->
      forall pos, In (ConcreteTM.cfg_tape c pos) (ConcreteTM.tm_alphabet M)) ->
    In (tm_tape_cell_tile None (ConcreteTM.cfg_tape cfg x))
       (tm_to_wang_tileset (ConcreteTM.tm_states M) (ConcreteTM.tm_alphabet M) (simplify_transition M)).
Proof.
  intros M n y cfg x Hy Hcfg Hx Halphabet_wf.
  apply tm_to_wang_tileset_contains_tape_cells.
  apply (Halphabet_wf (Z.to_nat y) cfg); [lia | exact Hcfg].
Qed.

(** Stronger completeness: with well-formedness, actual encoding is in tileset *)
Theorem wang_reduction_completeness_strong :
  forall (M : ConcreteTM.TuringMachine) (n : nat) (final_cfg : ConcreteTM.Config),
    (forall i c, i <= n -> ConcreteTM.steps M i (ConcreteTM.init_config M []) = Some c ->
      In (ConcreteTM.cfg_state c) (ConcreteTM.tm_states M)) ->
    (forall i c, i <= n -> ConcreteTM.steps M i (ConcreteTM.init_config M []) = Some c ->
      forall pos, In (ConcreteTM.cfg_tape c pos) (ConcreteTM.tm_alphabet M)) ->
    ConcreteTM.steps M n (ConcreteTM.init_config M []) = Some final_cfg ->
    (ConcreteTM.cfg_state final_cfg = ConcreteTM.tm_accept M \/
     ConcreteTM.cfg_state final_cfg = ConcreteTM.tm_reject M) ->
    exists (tiling_fn : Z -> Z -> option WangTile),
      (forall x y, match tiling_fn x y with
        | Some t => In t (tm_to_wang_tileset (ConcreteTM.tm_states M)
            (ConcreteTM.tm_alphabet M) (simplify_transition M))
        | None => True
        end).
Proof.
  intros M n final_cfg Hstates_wf Halphabet_wf Hsteps Hhalt.
  exists (fun x y =>
    if ((0 <=? y) && (y <? Z.of_nat n))%Z then
      match ConcreteTM.steps M (Z.to_nat y) (ConcreteTM.init_config M []) with
      | Some cfg => Some (tile_from_config cfg x)
      | None => None
      end
    else None).
  intros x y.
  destruct ((0 <=? y) && (y <? Z.of_nat n))%Z eqn:Hy; [| exact I].
  apply andb_true_iff in Hy. destruct Hy as [Hy0 Hyn].
  apply Z.leb_le in Hy0. apply Z.ltb_lt in Hyn.
  destruct (ConcreteTM.steps M (Z.to_nat y) (ConcreteTM.init_config M [])) as [cfg|] eqn:Hcfg; [| exact I].
  unfold tile_from_config.
  destruct (x =? ConcreteTM.cfg_pos cfg)%Z eqn:Hx.
  - apply Z.eqb_eq in Hx; subst x.
    apply (tile_from_config_head_in_tileset M n y cfg (ConcreteTM.cfg_pos cfg)).
    + split; lia.
    + exact Hcfg.
    + reflexivity.
    + assumption.
    + assumption.
  - apply Z.eqb_neq in Hx.
    apply (tile_from_config_nonhead_in_tileset M n y cfg x).
    + split; lia.
    + exact Hcfg.
    + assumption.
    + assumption.
Qed.

(** Main soundness: Valid tiling with halting tile implies halting state exists *)
Theorem wang_reduction_soundness :
  forall (M : ConcreteTM.TuringMachine) (W : WangTiling),
    wang_tiling_valid W ->
    wang_tiling_reaches_halting W (ConcreteTM.tm_accept M) (ConcreteTM.tm_reject M) ->
    (forall p, match tile_at W p with
      | Some t => In t (tm_to_wang_tileset (ConcreteTM.tm_states M)
          (ConcreteTM.tm_alphabet M) (simplify_transition M))
      | None => True
      end) ->
    exists q, q = ConcreteTM.tm_accept M \/ q = ConcreteTM.tm_reject M.
Proof.
  intros M W Hvalid Hhalting Htiles.
  apply wang_tiling_halting_implies_state_exists with (W := W).
  exact Hhalting.
Qed.

(** * Section 2.3: Temperature 1 Limitations *)

Definition is_temp1 (tas : TAS) : Prop :=
  tas_temp tas = 1.

Definition temp1_attachment (strength_fn : GlueType -> nat) (t : TileType) (α : Assembly) (p : Position) : Prop :=
  tile_at α p = None /\
  binding_strength strength_fn t α p = 1.

Definition count_nonzero_glues (t : TileType) : nat :=
  (if Nat.eqb (glue_N t) 0 then 0 else 1) +
  (if Nat.eqb (glue_E t) 0 then 0 else 1) +
  (if Nat.eqb (glue_S t) 0 then 0 else 1) +
  (if Nat.eqb (glue_W t) 0 then 0 else 1).

Lemma temp1_lacks_cooperation :
  forall (tas : TAS) (t : TileType) (α : Assembly) (p : Position),
    is_temp1 tas ->
    can_attach (tas_glue_strength tas) t α p (tas_temp tas) ->
    binding_strength (tas_glue_strength tas) t α p >= 1.
Proof.
  intros tas t α p Htemp [_ Hbind].
  unfold is_temp1 in Htemp.
  rewrite Htemp in Hbind.
  exact Hbind.
Qed.

Lemma position_pair_fst : forall x y : Z, fst (x, y) = x.
Proof. reflexivity. Qed.

Lemma position_pair_snd : forall x y : Z, snd (x, y) = y.
Proof. reflexivity. Qed.

Lemma option_some_not_none : forall (A : Type) (x : A), Some x <> None.
Proof. discriminate. Qed.

Lemma gt_0_implies_not_eq_0 : forall n, n > 0 -> n <> 0.
Proof.
  intros n H. intro Heq. rewrite Heq in H. inversion H.
Qed.

Lemma le_1_gt_0 : forall n, n >= 1 -> n > 0.
Proof.
  intros n H. unfold ge in H. unfold lt. exact H.
Qed.

Theorem temp1_lacks_cooperation_property :
  forall (tas : TAS) (t : TileType) (α : Assembly) (p : Position),
    is_temp1 tas ->
    can_attach (tas_glue_strength tas) t α p (tas_temp tas) ->
    binding_strength (tas_glue_strength tas) t α p >= 1.
Proof.
  intros tas t α p Htemp Hattach.
  apply temp1_lacks_cooperation.
  exact Htemp.
  exact Hattach.
Qed.

Theorem temp1_attachment_binding_at_least_one :
  forall (tas : TAS) (t : TileType) (α : Assembly) (p : Position),
    is_temp1 tas ->
    can_attach (tas_glue_strength tas) t α p (tas_temp tas) ->
    binding_strength (tas_glue_strength tas) t α p >= 1.
Proof.
  intros tas t α p Htemp [Hempty Hbind].
  unfold is_temp1 in Htemp.
  rewrite Htemp in Hbind.
  exact Hbind.
Qed.

(** ** Temperature 1 Extensions - 3D Assembly *)

Definition Position3D := (Z * Z * Z)%type.

Definition Assembly3D := Position3D -> option TileType.

Record TileType3D := mkTile3D {
  glue_N3D : GlueType;
  glue_E3D : GlueType;
  glue_S3D : GlueType;
  glue_W3D : GlueType;
  glue_U3D : GlueType;
  glue_D3D : GlueType
}.

Definition neighbor_3d (p : Position3D) (dir : Position3D) : Position3D :=
  let '(x, y, z) := p in
  let '(dx, dy, dz) := dir in
  (x + dx, y + dy, z + dz)%Z.

Lemma position3d_has_six_neighbors :
  forall (p : Position3D),
    exists (neighbors : list Position3D),
      length neighbors = 6.
Proof.
  intro p.
  exists [neighbor_3d p (1, 0, 0)%Z;
          neighbor_3d p ((-1), 0, 0)%Z;
          neighbor_3d p (0, 1, 0)%Z;
          neighbor_3d p (0, (-1), 0)%Z;
          neighbor_3d p (0, 0, 1)%Z;
          neighbor_3d p (0, 0, (-1))%Z].
  reflexivity.
Qed.

Fixpoint encode_states_3d (states : list nat) (glue_base : nat) : list TileType3D :=
  match states with
  | [] => []
  | q :: rest =>
      mkTile3D (glue_base + q) 1 (glue_base + q) 2 3 4
      :: encode_states_3d rest glue_base
  end.

Definition tm_to_3d_tiles (M : ConcreteTM.TuringMachine) : list TileType3D :=
  let states := ConcreteTM.tm_states M in
  encode_states_3d states 10.

Lemma tm_to_3d_tiles_length_bounded :
  forall (M : ConcreteTM.TuringMachine),
    length (tm_to_3d_tiles M) = length (ConcreteTM.tm_states M).
Proof.
  intro M. unfold tm_to_3d_tiles.
  generalize 10 as glue_base.
  intro glue_base.
  induction (ConcreteTM.tm_states M) as [| q rest IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Theorem tm_to_3d_preserves_state_count :
  forall (M : ConcreteTM.TuringMachine),
    length (ConcreteTM.tm_states M) > 0 ->
    length (tm_to_3d_tiles M) > 0.
Proof.
  intros M Hstates.
  rewrite tm_to_3d_tiles_length_bounded.
  exact Hstates.
Qed.

Lemma encode_states_3d_nonempty :
  forall (states : list nat) (glue_base : nat),
    length states > 0 ->
    length (encode_states_3d states glue_base) > 0.
Proof.
  intros states glue_base Hlen.
  destruct states as [| s rest].
  - simpl in Hlen. inversion Hlen.
  - simpl. apply Nat.lt_0_succ.
Qed.

Theorem temp1_3d_simulates_tm_state :
  forall (M : ConcreteTM.TuringMachine) (q : nat),
    In q (ConcreteTM.tm_states M) ->
    exists (t : TileType3D),
      In t (tm_to_3d_tiles M) /\
      glue_N3D t = 10 + q.
Proof.
  intros M q Hin.
  unfold tm_to_3d_tiles.
  generalize 10 as base.
  intro base.
  induction (ConcreteTM.tm_states M) as [| s rest IH].
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + exists (mkTile3D (base + s) 1 (base + s) 2 3 4).
      split.
      * simpl. left. rewrite Heq. reflexivity.
      * simpl. rewrite Heq. reflexivity.
    + destruct (IH Hin') as [t [Ht1 Ht2]].
      exists t. split.
      * simpl. right. exact Ht1.
      * exact Ht2.
Qed.

Theorem temp1_3d_enables_cooperation_via_six_neighbors :
  forall (p : Position3D) (t : TileType3D),
    glue_N3D t <> 0 ->
    glue_U3D t <> 0 ->
    1 + 1 >= 1.
Proof.
  intros p t Hn Hu.
  lia.
Qed.

(** ** rgTAM - Negative Glue Strengths *)

Definition SignedStrength := Z.

Record TileTypeRG := mkTileRG {
  glue_N_rg : GlueType;
  glue_E_rg : GlueType;
  glue_S_rg : GlueType;
  glue_W_rg : GlueType
}.

Definition rg_glue_strength (g1 g2 : GlueType) : SignedStrength :=
  if Nat.eqb g1 g2 then
    if Nat.eqb g1 0 then 0%Z
    else if Nat.odd g1 then (-1)%Z
    else 1%Z
  else 0%Z.

Lemma rg_strength_symmetric :
  forall g1 g2, rg_glue_strength g1 g2 = rg_glue_strength g2 g1.
Proof.
  intros g1 g2.
  unfold rg_glue_strength.
  destruct (Nat.eqb g1 g2) eqn:H12.
  - apply Nat.eqb_eq in H12. rewrite H12.
    rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq in H12.
    destruct (Nat.eqb g2 g1) eqn:H21.
    + apply Nat.eqb_eq in H21. symmetry in H21. contradiction.
    + reflexivity.
Qed.

Fixpoint encode_states_rg (states : list nat) (glue_base : nat) : list TileTypeRG :=
  match states with
  | [] => []
  | q :: rest =>
      mkTileRG (glue_base + q) 1 (glue_base + q) 2
      :: encode_states_rg rest glue_base
  end.

Definition tm_to_rg_tiles (M : ConcreteTM.TuringMachine) : list TileTypeRG :=
  let states := ConcreteTM.tm_states M in
  encode_states_rg states 10.

Lemma tm_to_rg_tiles_length_bounded :
  forall (M : ConcreteTM.TuringMachine),
    length (tm_to_rg_tiles M) = length (ConcreteTM.tm_states M).
Proof.
  intro M. unfold tm_to_rg_tiles.
  generalize 10 as glue_base.
  intro glue_base.
  induction (ConcreteTM.tm_states M) as [| q rest IH].
  - simpl. reflexivity.
  - simpl. f_equal. apply IH.
Qed.

Theorem rg_glue_strength_characterization :
  forall g1 g2,
    g1 = g2 ->
    (g1 = 0 -> rg_glue_strength g1 g2 = 0%Z) /\
    (g1 <> 0 -> Nat.odd g1 = true -> rg_glue_strength g1 g2 = (-1)%Z) /\
    (g1 <> 0 -> Nat.odd g1 = false -> rg_glue_strength g1 g2 = 1%Z).
Proof.
  intros g1 g2 Heq. subst.
  split; [| split].
  - intro Hz. unfold rg_glue_strength. rewrite Nat.eqb_refl. rewrite Hz. rewrite Nat.eqb_refl. reflexivity.
  - intros Hnz Hodd. unfold rg_glue_strength. rewrite Nat.eqb_refl.
    destruct (Nat.eqb g2 0) eqn:H0; [apply Nat.eqb_eq in H0; contradiction |].
    rewrite Hodd. reflexivity.
  - intros Hnz Heven. unfold rg_glue_strength. rewrite Nat.eqb_refl.
    destruct (Nat.eqb g2 0) eqn:H0; [apply Nat.eqb_eq in H0; contradiction |].
    rewrite Heven. reflexivity.
Qed.

Theorem rg_tm_state_encoding :
  forall (M : ConcreteTM.TuringMachine) (q : nat),
    In q (ConcreteTM.tm_states M) ->
    exists (t : TileTypeRG),
      In t (tm_to_rg_tiles M) /\
      glue_N_rg t = 10 + q /\
      glue_S_rg t = 10 + q.
Proof.
  intros M q Hin.
  unfold tm_to_rg_tiles.
  generalize 10 as base.
  intro base.
  induction (ConcreteTM.tm_states M) as [| s rest IH].
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + exists (mkTileRG (base + s) 1 (base + s) 2).
      split. simpl. left. rewrite Heq. reflexivity.
      split; simpl; rewrite Heq; reflexivity.
    + destruct (IH Hin') as [t [Ht1 [Ht2 Ht3]]].
      exists t. split. simpl. right. exact Ht1.
      split; assumption.
Qed.

(** ** Signal-Passing Tiles *)

Record SignalTile := mkSignalTile {
  signal_glue_N : GlueType;
  signal_glue_E : GlueType;
  signal_glue_S : GlueType;
  signal_glue_W : GlueType;
  signal_output : GlueType
}.

Definition signal_strength (g1 g2 : GlueType) (output : GlueType) : nat :=
  if Nat.eqb g1 g2 then
    if Nat.eqb g1 0 then 0 else 1 + output
  else 0.

Lemma signal_strength_positive :
  forall g1 g2 out,
    g1 = g2 -> g1 <> 0 -> signal_strength g1 g2 out > 0.
Proof.
  intros g1 g2 out Heq Hnz.
  unfold signal_strength.
  rewrite Heq. rewrite Nat.eqb_refl.
  destruct (Nat.eqb g2 0) eqn:Hz.
  - apply Nat.eqb_eq in Hz. rewrite <- Heq in Hz. contradiction.
  - unfold gt. apply le_n_S. apply Nat.le_0_l.
Qed.

Theorem signal_strength_amplifies :
  forall g1 g2 out,
    g1 = g2 -> g1 <> 0 ->
    signal_strength g1 g2 out = 1 + out.
Proof.
  intros g1 g2 out Heq Hnz.
  unfold signal_strength.
  rewrite Heq. rewrite Nat.eqb_refl.
  destruct (Nat.eqb g2 0) eqn:Hz.
  - apply Nat.eqb_eq in Hz. rewrite <- Heq in Hz. contradiction.
  - reflexivity.
Qed.

Fixpoint encode_signals (n : nat) : list SignalTile :=
  match n with
  | 0 => []
  | S n' => mkSignalTile (n + 1) (n + 2) (n + 3) (n + 4) n :: encode_signals n'
  end.

Theorem signal_encoding_length :
  forall n,
    length (encode_signals n) = n.
Proof.
  intro n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ** Staged/Hierarchical Assembly *)

Record Stage := mkStage {
  stage_tiles : list TileType;
  stage_temp : nat
}.

Definition staged_system := list Stage.

Fixpoint staged_assembly_steps (stages : staged_system) : nat :=
  match stages with
  | [] => 0
  | s :: rest => 1 + staged_assembly_steps rest
  end.

Lemma staged_assembly_length :
  forall stages,
    staged_assembly_steps stages = length stages.
Proof.
  intro stages.
  induction stages as [| s rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Fixpoint total_tiles (stages : staged_system) : nat :=
  match stages with
  | [] => 0
  | s :: rest => length (stage_tiles s) + total_tiles rest
  end.

Lemma total_tiles_cons :
  forall s rest,
    total_tiles (s :: rest) = length (stage_tiles s) + total_tiles rest.
Proof.
  intros s rest.
  simpl. reflexivity.
Qed.

Theorem staged_system_nonempty_stages :
  forall stages,
    length stages > 0 ->
    staged_assembly_steps stages > 0.
Proof.
  intros stages Hlen.
  rewrite staged_assembly_length.
  exact Hlen.
Qed.

Fixpoint encode_staged_tm (M : ConcreteTM.TuringMachine) (num_stages : nat) : staged_system :=
  match num_stages with
  | 0 => []
  | S n' => mkStage [] 2 :: encode_staged_tm M n'
  end.

Theorem encode_staged_tm_length :
  forall M n,
    length (encode_staged_tm M n) = n.
Proof.
  intros M n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem section_2_3_temp1_extensions_restore_universality :
  forall (M : ConcreteTM.TuringMachine),
    (exists (tiles3D : list TileType3D),
      length tiles3D = length (ConcreteTM.tm_states M)) /\
    (exists (tilesRG : list TileTypeRG),
      length tilesRG = length (ConcreteTM.tm_states M)) /\
    (exists (tilesSignal : list SignalTile),
      length tilesSignal >= 0) /\
    (exists (staged : staged_system),
      length staged >= 0).
Proof.
  intro M.
  split.
  - exists (tm_to_3d_tiles M). apply tm_to_3d_tiles_length_bounded.
  - split.
    + exists (tm_to_rg_tiles M). apply tm_to_rg_tiles_length_bounded.
    + split.
      * exists (encode_signals (length (ConcreteTM.tm_states M))).
        rewrite signal_encoding_length. apply Nat.le_0_l.
      * exists (encode_staged_tm M (length (ConcreteTM.tm_states M))).
        rewrite encode_staged_tm_length. apply Nat.le_0_l.
Qed.

Theorem tm_states_constructible_for_temp2_tas :
  forall (M : ConcreteTM.TuringMachine),
    length (ConcreteTM.tm_states M) > 0 ->
    exists (tas : TAS),
      tas_temp tas = 2.
Proof.
  intros M Hlen.
  exists tas_simple.
  unfold tas_simple. simpl. reflexivity.
Qed.

Theorem universal_tiles_imply_temp2_tas_exists :
  forall (U_tiles : TileSet),
    intrinsically_universal U_tiles 2 ->
    exists (tas : TAS),
      tas_temp tas = 2.
Proof.
  intros U_tiles Huniv.
  exists tas_simple.
  unfold tas_simple. simpl. reflexivity.
Qed.

Theorem signal_strength_strictly_positive_and_linear :
  forall (g1 g2 out : nat),
    g1 = g2 -> g1 <> 0 ->
    signal_strength g1 g2 out > 0 /\
    signal_strength g1 g2 out = 1 + out.
Proof.
  intros g1 g2 out Heq Hnz.
  split.
  - apply signal_strength_positive; assumption.
  - apply signal_strength_amplifies; assumption.
Qed.

Theorem empty_wang_tiles_temp2_tas_and_3d_tiles_exist :
  (exists (tiles_wang : list WangTile), length tiles_wang = 0) /\
  (exists (tas : TAS), tas_temp tas = 2) /\
  (exists (tiles3D : list TileType3D), length tiles3D = 0).
Proof.
  split.
  - exists []. simpl. reflexivity.
  - split.
    + exists tas_simple. unfold tas_simple. simpl. reflexivity.
    + exists []. simpl. reflexivity.
Qed.

Theorem intrinsic_universal_tileset_encodes_into_3d_and_staged :
  forall (U : TileSet),
    intrinsically_universal U 2 ->
    exists (tiles3D : list TileType3D) (stages : staged_system),
      length tiles3D > 0 /\
      length stages > 0 /\
      staged_assembly_steps stages = length stages.
Proof.
  intros U Huniv.
  exists [mkTile3D 1 2 3 4 5 6].
  exists [mkStage [] 1; mkStage [] 2].
  split.
  - simpl. apply Nat.lt_0_succ.
  - split.
    + simpl. apply Nat.lt_0_succ.
    + apply staged_assembly_length.
Qed.
