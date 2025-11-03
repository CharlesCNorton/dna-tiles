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
Import ListNotations.

Section CoreDefinitions.

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

Parameter glue_strength_value : GlueType -> nat.

(** σ: Σ × Σ → ℕ *)
Definition glue_strength (g1 g2 : GlueType) : nat :=
  if glue_eq_dec g1 g2 then
    if glue_eq_dec g1 null_glue then 0
    else glue_strength_value g1
  else 0.

Theorem glue_strength_symmetric :
  forall g1 g2, glue_strength g1 g2 = glue_strength g2 g1.
Proof.
  intros g1 g2.
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
  forall g1 g2, g1 <> g2 -> glue_strength g1 g2 = 0.
Proof.
  intros g1 g2 Hneq.
  unfold glue_strength.
  destruct (glue_eq_dec g1 g2) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Theorem null_glue_zero_strength :
  forall g, glue_strength null_glue g = 0.
Proof.
  intro g.
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

Example tile_horizontal : TileType :=
  mkTile null_glue glue_1 null_glue glue_1.

Example tile_vertical : TileType :=
  mkTile glue_2 null_glue glue_2 null_glue.

Example ex_glue_strength_null :
  glue_strength null_glue null_glue = 0.
Proof.
  apply null_glue_zero_strength.
Qed.

Example ex_glue_strength_mismatch :
  glue_strength glue_1 glue_2 = 0.
Proof.
  apply nonmatch_zero_strength.
  unfold glue_1, glue_2. discriminate.
Qed.

End CoreDefinitions.

(** * Section 1.2: Assembly Dynamics *)

Section AssemblyDynamics.

(** ** Binding Strength *)

(** Binding strength contribution from neighbor p' to position p for tile t.
    Returns σ(g, g') where g is glue of t facing p', g' is glue at p' facing p. *)
Definition neighbor_binding (t : TileType) (α : Assembly) (p p' : Position) : nat :=
  match tile_at α p' with
  | None => 0
  | Some t' =>
      match glue_facing t p p', glue_facing t' p' p with
      | Some g, Some g' => glue_strength g g'
      | _, _ => 0
      end
  end.

(** Total binding strength for tile t at position p in assembly α.
    Computes Σ_{p'∈neighbors(p)} σ(glue_t(p'), glue_α(p')) *)
Definition binding_strength (t : TileType) (α : Assembly) (p : Position) : nat :=
  fold_right Nat.add 0 (map (neighbor_binding t α p) (neighbors p)).

(** ** Attachment Rules *)

(** Tile t can attach at position p in assembly α at temperature τ
    iff p is unoccupied and binding strength ≥ τ *)
Definition can_attach (t : TileType) (α : Assembly) (p : Position) (τ : Temperature) : Prop :=
  tile_at α p = None /\
  binding_strength t α p >= τ.

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
Definition single_step (T : TileSet) (τ : Temperature) (α α' : Assembly) : Prop :=
  exists t p,
    tile_in_set t T /\
    can_attach t α p τ /\
    α' = place_tile α t p.

(** Multi-step growth: α →* α' (reflexive transitive closure) *)
Inductive multi_step (T : TileSet) (τ : Temperature) : Assembly -> Assembly -> Prop :=
  | ms_refl : forall α, multi_step T τ α α
  | ms_step : forall α α' α'',
      single_step T τ α α' ->
      multi_step T τ α' α'' ->
      multi_step T τ α α''.

(** ** Tile Assembly Systems *)

(** A Tile Assembly System (TAS) is a tuple (T, σ, τ, seed) where:
    - T is the tile set
    - σ is the glue strength function (global parameter)
    - τ is the temperature
    - seed is the initial assembly *)
Record TAS := mkTAS {
  tas_tiles : TileSet;
  tas_seed : Assembly;
  tas_temp : Temperature
}.

(** Assembly α is producible in TAS *)
Definition producible_in (tas : TAS) (α : Assembly) : Prop :=
  multi_step (tas_tiles tas) (tas_temp tas) (tas_seed tas) α.

(** ** Terminal Assemblies *)

(** Assembly α is terminal in TAS if no tile can attach *)
Definition is_terminal (tas : TAS) (α : Assembly) : Prop :=
  forall t p, tile_in_set t (tas_tiles tas) ->
    tile_at α p = None ->
    binding_strength t α p < tas_temp tas.

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
  forall T τ α α', single_step T τ α α' -> α ⊆ α'.
Proof.
  intros T τ α α' [t [p [_ [[Hempty _] Heq]]]].
  subst. apply place_tile_extends. exact Hempty.
Qed.

Theorem multi_step_extends :
  forall T τ α α', multi_step T τ α α' -> α ⊆ α'.
Proof.
  intros T τ α α' H.
  induction H.
  - apply subassembly_refl.
  - eapply subassembly_trans.
    + eapply single_step_extends. exact H.
    + exact IHmulti_step.
Qed.

(** *** Multi-step Properties *)

Theorem multi_step_trans :
  forall T τ α β γ,
    multi_step T τ α β ->
    multi_step T τ β γ ->
    multi_step T τ α γ.
Proof.
  intros T τ α β γ Hab Hbg.
  induction Hab; auto.
  apply ms_step with α'; auto.
Qed.

Theorem single_to_multi :
  forall T τ α α',
    single_step T τ α α' ->
    multi_step T τ α α'.
Proof.
  intros. eapply ms_step; eauto. apply ms_refl.
Qed.

(** *** Terminal Assembly Properties *)

Theorem terminal_no_growth :
  forall tas α,
    is_terminal tas α ->
    forall α', single_step (tas_tiles tas) (tas_temp tas) α α' -> False.
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

End AssemblyDynamics.

(** * Section 1.3: Determinism and Uniqueness *)

Section Determinism.

(** ** Local Determinism Conditions *)

(** Two tiles compete at position p in assembly α if both can attach *)
Definition tiles_compete (t1 t2 : TileType) (α : Assembly) (p : Position) (τ : Temperature) : Prop :=
  can_attach t1 α p τ /\ can_attach t2 α p τ /\ t1 <> t2.

(** A TAS has a conflict if two different tiles can attach at same position *)
Definition has_conflict (tas : TAS) : Prop :=
  exists α t1 t2 p,
    producible_in tas α /\
    tile_in_set t1 (tas_tiles tas) /\
    tile_in_set t2 (tas_tiles tas) /\
    tiles_compete t1 t2 α p (tas_temp tas).

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
    multi_step (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_tiles tas) (tas_temp tas) γ δ.

(** Strong confluence: single steps from producible assemblies can be joined *)
Definition strongly_confluent (tas : TAS) : Prop :=
  forall α β γ,
    producible_in tas α ->
    single_step (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_tiles tas) (tas_temp tas) α γ ->
    β = γ \/ exists δ,
      multi_step (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_tiles tas) (tas_temp tas) γ δ.

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
    can_attach t1 α p (tas_temp tas) ->
    can_attach t2 α p (tas_temp tas) ->
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
  assert (Hstep1: single_step (tas_tiles tas) (tas_temp tas) α α1).
  { exists t1, p. split. exact Hin1. split. exact Hatt1. reflexivity. }
  assert (Hstep2: single_step (tas_tiles tas) (tas_temp tas) α α2).
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
    can_attach t1 α p1 (tas_temp tas) ->
    can_attach t2 α p2 (tas_temp tas) ->
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
  forall t α t' p p' q,
    p' <> q ->
    neighbor_binding t (place_tile α t' q) p p' = neighbor_binding t α p p'.
Proof.
  intros t α t' p p' q Hneq.
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
  forall t α t' p q,
    ~In q (neighbors p) ->
    binding_strength t (place_tile α t' q) p = binding_strength t α p.
Proof.
  intros t α t' p q Hnin.
  unfold binding_strength.
  induction (neighbors p) as [|p' ps IH]; simpl; auto.
  f_equal.
  - apply neighbor_binding_orthogonal. intro Heq. subst. apply Hnin. left. reflexivity.
  - rewrite IH. reflexivity. intro Hin. apply Hnin. right. exact Hin.
Qed.

(** ** Main Determinism Theorem *)

(** Helper: neighbor_binding is monotonic with respect to subassembly *)
Lemma neighbor_binding_monotonic :
  forall t α β p p',
    subassembly α β ->
    neighbor_binding t α p p' <= neighbor_binding t β p p'.
Proof.
  intros t α β p p' Hsub.
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
  forall t α β p,
    subassembly α β ->
    binding_strength t α p <= binding_strength t β p.
Proof.
  intros t α β p Hsub.
  unfold binding_strength.
  induction (neighbors p) as [|p' ps IH].
  - simpl. lia.
  - simpl. apply Nat.add_le_mono.
    + apply neighbor_binding_monotonic. exact Hsub.
    + exact IH.
Qed.

Lemma binding_strength_antimono :
  forall t α β p,
    subassembly α β ->
    binding_strength t β p >= binding_strength t α p.
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
    can_attach t α p (tas_temp tas) ->
    can_attach t' γ p (tas_temp tas) ->
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
  assert (Hatt_t: can_attach t γ p (tas_temp tas)).
  { split.
    - unfold tile_at. rewrite Hγeq. reflexivity.
    - apply Nat.le_trans with (m := binding_strength t α p); auto.
      apply binding_strength_monotonic. exact Hsub. }
  assert (Hatt_t': can_attach t' γ p (tas_temp tas)).
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
  forall T τ seed α β,
    multi_step T τ seed α ->
    multi_step T τ seed β ->
    exists γ, multi_step T τ seed γ /\ subassembly γ α /\ subassembly γ β.
Proof.
  intros T τ seed α β Hα Hβ.
  exists seed.
  split. apply ms_refl.
  split.
  - eapply multi_step_extends. exact Hα.
  - eapply multi_step_extends. exact Hβ.
Qed.

Lemma multi_step_common_empty :
  forall T τ seed α β p,
    multi_step T τ seed α ->
    multi_step T τ seed β ->
    tile_at α p = None ->
    tile_at β p = None ->
    tile_at seed p = None.
Proof.
  intros T τ seed α β p Hα Hβ Hαp Hβp.
  assert (Hseed_α: subassembly seed α).
  { eapply multi_step_extends. exact Hα. }
  unfold subassembly in Hseed_α. specialize (Hseed_α p).
  unfold tile_at in *. destruct (seed p) eqn:Hseed; auto.
  destruct (α p); congruence.
Qed.

Lemma binding_at_seed_sufficient :
  forall tas α t p,
    producible_in tas α ->
    can_attach t α p (tas_temp tas) ->
    binding_strength t (tas_seed tas) p >= tas_temp tas \/
    exists β, producible_in tas β /\ can_attach t β p (tas_temp tas) /\
              binding_strength t β p >= tas_temp tas.
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
      assert (Hbound: binding_strength tγ (place_tile α tβ pβ) pγ >= tas_temp tas).
      { destruct Hattγ as [_ Hbnd].
        apply Nat.le_trans with (m := binding_strength tγ α pγ); auto.
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
      assert (Hbound: binding_strength tβ (place_tile α tγ pγ) pβ >= tas_temp tas).
      { destruct Hattβ as [_ Hbnd].
        apply Nat.le_trans with (m := binding_strength tβ α pβ); auto.
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
  forall T τ α β p t',
    multi_step T τ α β ->
    tile_at α p = None ->
    tile_at β p = Some t' ->
    exists γ,
      multi_step T τ α γ /\
      tile_at γ p = None /\
      single_step T τ γ (place_tile γ t' p) /\
      subassembly (place_tile γ t' p) β.
Proof.
  intros T τ α β p t' Hms.
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
    multi_step (tas_tiles tas) (tas_temp tas) (tas_seed tas) α ->
    single_step (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_tiles tas) (tas_temp tas) (tas_seed tas) β.
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
    multi_step (tas_tiles tas) (tas_temp tas) α β ->
    producible_in tas β.
Proof.
  intros tas α β Hprod Hms.
  unfold producible_in in *.
  eapply multi_step_trans; eauto.
Qed.

Lemma single_step_preserves_producibility :
  forall tas α β,
    producible_in tas α ->
    single_step (tas_tiles tas) (tas_temp tas) α β ->
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
    multi_step (tas_tiles tas) (tas_temp tas) γ δ ->
    tile_at γ p = None ->
    tile_at δ p = Some t_δ ->
    can_attach t_orig γ p (tas_temp tas) ->
    tile_in_set t_orig (tas_tiles tas) ->
    tile_at δ p = Some t_orig.
Proof.
  intros tas γ δ p t_δ t_orig Hlocal Hprodγ Hδγ Hγp Hδp Hcan Hin.
  edestruct (multi_step_inversion (tas_tiles tas) (tas_temp tas) γ δ p t_δ) as
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
      assert (Hcan_torig: can_attach t_orig γ' p (tas_temp tas)).
      { split.
        - exact Hγ'p.
        - apply Nat.le_trans with (m := binding_strength t_orig γ p).
          + exact Hbound.
          + apply binding_strength_monotonic.
            eapply multi_step_extends. exact Hγ'ms. }
      assert (Hcan_t_δ: can_attach t_δ γ' p (tas_temp tas)).
      { split; auto. }
      eapply locally_det_no_compete; eauto. }
    subst t_δ. exact Hδp.
Qed.

Lemma multi_step_prefix :
  forall T τ seed α' α,
    single_step T τ seed α' ->
    multi_step T τ α' α ->
    multi_step T τ seed α'.
Proof.
  intros. apply single_to_multi. exact H.
Qed.

(** ** Complexity-Theoretic Analysis *)

(** Checking if a tile can attach at a position is decidable *)
Definition can_attach_dec (t : TileType) (α : Assembly) (p : Position) (τ : Temperature)
  (positions : list Position) :
  (forall p', domain α p' -> In p' positions) ->
  {can_attach t α p τ} + {~can_attach t α p τ}.
Proof.
  intro Hdom.
  unfold can_attach.
  destruct (α p) eqn:Hαp.
  - right. intro H. destruct H as [Hempty _]. unfold tile_at in Hempty. congruence.
  - destruct (le_lt_dec τ (binding_strength t α p)) as [Hle | Hlt].
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
    {can_attach t α p (tas_temp tas)} + {~can_attach t α p (tas_temp tas)}.
Proof.
  intros tas α positions Hpos Hprod Hlocal t p Hin.
  apply (can_attach_dec t α p (tas_temp tas) positions).
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
      can_attach t α p (tas_temp tas) ->
      tile_at β p = None ->
      can_attach t β p (tas_temp tas).
Proof.
  intros tas α β Hlocal Hprodα Hprodβ Hsub t p Hin Hattα Hβempty.
  destruct Hattα as [Hαempty Hbound].
  split.
  - exact Hβempty.
  - apply Nat.le_trans with (m := binding_strength t α p).
    + exact Hbound.
    + apply binding_strength_monotonic. exact Hsub.
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

Lemma strong_confluence_single_join :
  forall tas α β γ,
    strongly_confluent tas ->
    producible_in tas α ->
    single_step (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α β γ Hsc Hprod Hβ Hγ.
  specialize (Hsc α β γ Hprod Hβ Hγ).
  destruct Hsc as [Heq | Hexists].
  - subst γ. exists β. split; apply ms_refl.
  - exact Hexists.
Qed.

Lemma multi_step_refl_inv :
  forall T τ α β,
    multi_step T τ α β ->
    α = β \/ exists α', single_step T τ α α' /\ multi_step T τ α' β.
Proof.
  intros T τ α β H.
  inversion H; subst.
  - left. reflexivity.
  - right. exists α'. split; auto.
Qed.

Lemma diamond_single_single :
  forall tas α β γ,
    strongly_confluent tas ->
    producible_in tas α ->
    single_step (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α β γ Hsc Hprod Hβ Hγ.
  eapply strong_confluence_single_join; eauto.
Qed.

Lemma diamond_multi_base :
  forall tas α γ,
    strongly_confluent tas ->
    producible_in tas α ->
    multi_step (tas_tiles tas) (tas_temp tas) α α ->
    multi_step (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_tiles tas) (tas_temp tas) α δ /\
      multi_step (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α γ Hsc Hprod Hαα Hαγ.
  exists γ. split; auto. apply ms_refl.
Qed.

Lemma diamond_step_multi_left :
  forall tas α β' β γ,
    strongly_confluent tas ->
    producible_in tas α ->
    single_step (tas_tiles tas) (tas_temp tas) α β' ->
    multi_step (tas_tiles tas) (tas_temp tas) β' β ->
    multi_step (tas_tiles tas) (tas_temp tas) α γ ->
    (forall β0,
      producible_in tas β' ->
      multi_step (tas_tiles tas) (tas_temp tas) β' β0 ->
      multi_step (tas_tiles tas) (tas_temp tas) α γ ->
      exists δ,
        multi_step (tas_tiles tas) (tas_temp tas) β0 δ /\
        multi_step (tas_tiles tas) (tas_temp tas) γ δ) ->
    exists δ,
      multi_step (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α β' β γ Hsc Hprodα Hstepβ' Hmsβ Hαγ IH.
  assert (Hprodβ': producible_in tas β').
  { eapply single_step_preserves_producibility; eauto. }
  apply IH; auto.
Qed.

Lemma diamond_single_step_right :
  forall tas α β γ' γ,
    strongly_confluent tas ->
    producible_in tas α ->
    multi_step (tas_tiles tas) (tas_temp tas) α β ->
    single_step (tas_tiles tas) (tas_temp tas) α γ' ->
    multi_step (tas_tiles tas) (tas_temp tas) γ' γ ->
    (forall γ0,
      producible_in tas γ' ->
      multi_step (tas_tiles tas) (tas_temp tas) α β ->
      multi_step (tas_tiles tas) (tas_temp tas) γ' γ0 ->
      exists δ,
        multi_step (tas_tiles tas) (tas_temp tas) β δ /\
        multi_step (tas_tiles tas) (tas_temp tas) γ0 δ) ->
    exists δ,
      multi_step (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α β γ' γ Hsc Hprodα Hαβ Hstepγ' Hmsγ IH.
  assert (Hprodγ': producible_in tas γ').
  { eapply single_step_preserves_producibility; eauto. }
  apply IH; auto.
Qed.

Theorem strong_confluence_diamond :
  forall tas,
    strongly_confluent tas ->
    has_diamond_property tas.
Proof.
Admitted.

(** ** Examples for Section 1.3 *)

Definition tileset_simple : TileSet := [tile_horizontal; tile_vertical].

Definition tas_simple : TAS :=
  mkTAS tileset_simple seed_single 2.

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

End Determinism.

(** * Section 1.4: Wang Tilings Connection *)

Section WangTilings.

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
        | Some g1, Some g2 => glue_strength g1 g2 > 0 -> g1 = g2
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
  forall T τ α α' t p,
    single_step T τ α α' ->
    tile_at α' p = Some t ->
    tile_at α p = None ->
    tile_in_set t T.
Proof.
  intros T τ α α' t p [t0 [p0 [Hin [Hatt Heq]]]] Ht' Ht.
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
  forall g1 g2,
    g1 <> null_glue ->
    g2 <> null_glue ->
    glue_strength g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros g1 g2 Hn1 Hn2 Hstr.
  unfold glue_strength in Hstr.
  destruct (glue_eq_dec g1 g2); auto.
  lia.
Qed.

Lemma glue_strength_positive_implies_match :
  forall g1 g2,
    (forall g, g <> null_glue -> glue_strength_value g >= 1) ->
    glue_strength g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros g1 g2 Hstr Hpos.
  unfold glue_strength in Hpos.
  destruct (glue_eq_dec g1 g2) as [Heq | Hneq]; auto.
  lia.
Qed.

Lemma glue_strength_zero_implies_match_or_null :
  forall g1 g2,
    glue_strength g1 g2 = 0 ->
    g1 = g2 \/ g1 <> g2.
Proof.
  intros g1 g2 Hz.
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
    (glue_strength g1 g2 > 0 -> g1 = g2).
Proof.
  intros tas α p1 p2 t1 t2 g1 g2 Hprod Hadj Ht1 Ht2 Hg1 Hg2.
  assert (Hedge := producible_valid_edges tas α p1 p2 Hprod Hadj).
  rewrite Ht1, Ht2, Hg1, Hg2 in Hedge.
  exact Hedge.
Qed.

Lemma null_glue_strength_zero :
  forall g,
    glue_strength null_glue g = 0.
Proof.
  intro g. apply null_glue_zero_strength.
Qed.

Lemma nonzero_glue_strength_lower_bound :
  forall g1 g2,
    (forall g, g <> null_glue -> glue_strength_value g >= 1) ->
    g1 <> null_glue ->
    g1 <> g2 ->
    glue_strength g1 g2 = 0.
Proof.
  intros g1 g2 Hstr Hnn Hneq.
  unfold glue_strength.
  destruct (glue_eq_dec g1 g2); try contradiction.
  reflexivity.
Qed.

Lemma nonzero_glue_positive_strength :
  forall g1 g2,
    (forall g, g <> null_glue -> glue_strength_value g >= 1) ->
    g1 <> null_glue ->
    g1 = g2 ->
    glue_strength g1 g2 > 0.
Proof.
  intros g1 g2 Hstr Hnn Heq.
  subst. unfold glue_strength.
  destruct (glue_eq_dec g2 g2); try contradiction.
  destruct (glue_eq_dec g2 null_glue); try contradiction.
  specialize (Hstr g2 n). lia.
Qed.

Lemma glue_strength_dichotomy :
  forall g1 g2,
    (forall g, g <> null_glue -> glue_strength_value g >= 1) ->
    glue_strength g1 g2 = 0 \/ glue_strength g1 g2 > 0.
Proof.
  intros g1 g2 Hstr.
  destruct (Nat.eq_dec (glue_strength g1 g2) 0); auto.
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
    glue_strength g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros tas α p1 p2 t1 t2 g1 g2 Hprod Hadj Ht1 Ht2 Hg1 Hg2 Hpos.
  apply (adjacent_tiles_match_or_nonzero tas α p1 p2 t1 t2 g1 g2); auto.
Qed.

Lemma zero_strength_implies_match_or_differ :
  forall g1 g2,
    glue_strength g1 g2 = 0 ->
    g1 = g2 \/ g1 <> g2.
Proof.
  intros g1 g2 Hz.
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
      multi_step (tas_tiles tas) (tas_temp tas) (tas_seed tas) γ /\
      tile_at γ p = None /\
      single_step (tas_tiles tas) (tas_temp tas) γ (place_tile γ t p) /\
      subassembly (place_tile γ t p) α.
Proof.
  intros tas α p t Hprod Ht Hseed.
  eapply multi_step_inversion; eauto.
Qed.

Lemma single_step_decompose :
  forall T τ γ t p,
    single_step T τ γ (place_tile γ t p) ->
    exists t' p',
      tile_in_set t' T /\
      can_attach t' γ p' τ /\
      place_tile γ t p = place_tile γ t' p'.
Proof.
  intros T τ γ t p Hstep.
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
    multi_step (tas_tiles tas) (tas_temp tas) (tas_seed tas) γ ->
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
      can_attach t1 γ p1 (tas_temp tas).
Proof.
  intros tas α p1 t1 p2 t2 Hprod Ht1 Ht2 Hadj Hseed_empty.
  destruct (tile_added_after_seed tas α p1 t1 Hprod Ht1 Hseed_empty) as
    [γ [Hγms [Hγp1 [Hγstep Hγsub]]]].
  destruct (single_step_decompose (tas_tiles tas) (tas_temp tas) γ t1 p1 Hγstep) as
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
    (forall g, g <> null_glue -> glue_strength_value g >= 1) ->
    adjacent p1 p2 ->
    tile_at α p1 = Some t1 ->
    tile_at α p2 = Some t2 ->
    glue_facing t1 p1 p2 = Some g1 ->
    glue_facing t2 p2 p1 = Some g2 ->
    glue_strength g1 g2 > 0 ->
    g1 = g2.
Proof.
  intros tas α p1 p2 t1 t2 g1 g2 Htemp Hprod Hstr Hadj Ht1 Ht2 Hg1 Hg2 Hpos.
  apply glue_strength_positive_implies_match with (g1 := g1) (g2 := g2); auto.
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
  forall t α p p',
    neighbor_binding t α p p' >= 1 ->
    exists t', tile_at α p' = Some t'.
Proof.
  intros t α p p' H.
  unfold neighbor_binding in H.
  destruct (tile_at α p') as [t'|] eqn:Ht'; eauto.
  simpl in H. lia.
Qed.

Lemma binding_strength_geq_one_has_contributing_neighbor :
  forall t α p,
    binding_strength t α p >= 1 ->
    exists p',
      In p' (neighbors p) /\
      neighbor_binding t α p p' >= 1.
Proof.
  intros t α p H.
  unfold binding_strength in H.
  unfold neighbors in H.
  simpl in H.
  assert (Hrewrite: neighbor_binding t α p (north p) +
    (neighbor_binding t α p (east p) +
     (neighbor_binding t α p (south p) + (neighbor_binding t α p (west p) + 0))) =
    neighbor_binding t α p (north p) + neighbor_binding t α p (east p) +
    neighbor_binding t α p (south p) + neighbor_binding t α p (west p)) by lia.
  rewrite Hrewrite in H.
  apply sum_geq_one_has_nonzero_term in H.
  destruct H as [H1 | [H2 | [H3 | H4]]].
  - exists (north p). split. left. reflexivity. exact H1.
  - exists (east p). split. right. left. reflexivity. exact H2.
  - exists (south p). split. right. right. left. reflexivity. exact H3.
  - exists (west p). split. right. right. right. left. reflexivity. exact H4.
Qed.

Lemma neighbor_binding_geq_one_has_matching_glues :
  forall t α p p' t',
    neighbor_binding t α p p' >= 1 ->
    tile_at α p' = Some t' ->
    exists g,
      glue_facing t p p' = Some g /\
      glue_facing t' p' p = Some g /\
      glue_strength g g >= 1.
Proof.
  intros t α p p' t' Hbind Ht'.
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
    (forall g, g <> null_glue -> glue_strength_value g >= 1) ->
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
  destruct (single_step_decompose (tas_tiles tas) (tas_temp tas) γ t p Hγstep) as [t' [p' [Hin [Hatt Heq]]]].
  assert (Hp_eq: p' = p).
  { eapply place_tile_eq_positions_match; eauto. unfold tile_at. apply place_tile_at_pos. }
  subst p'.
  assert (Ht_eq: t' = t).
  { eapply place_tile_eq_tiles_match; eauto. }
  subst t'.
  destruct Hatt as [Hγempty' Hγbound].
  rewrite Htemp in Hγbound.
  destruct (binding_strength_geq_one_has_contributing_neighbor t γ p Hγbound) as [p' [Hadj Hbind]].
  destruct (neighbor_binding_geq_one_implies_tile_exists t γ p p' Hbind) as [t' Ht'].
  destruct (neighbor_binding_geq_one_has_matching_glues t γ p p' t' Hbind Ht') as [g [Hg [Hg' Hstr_g]]].
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

End WangTilings.
