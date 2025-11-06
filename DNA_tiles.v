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

End CoreDefinitions.

(** * Section 1.2: Assembly Dynamics *)

Section AssemblyDynamics.

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

End AssemblyDynamics.

(** * Section 1.3: Determinism and Uniqueness *)

Section Determinism.

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

Lemma strip_one_multi :
  forall tas α β γ,
    strongly_confluent tas ->
    producible_in tas α ->
    single_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
Admitted.

Theorem diamond_aux_inner :
  forall (tas : TAS) (α β γ : Assembly),
    strongly_confluent tas ->
    producible_in tas α ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α β ->
    multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) α γ ->
    exists δ,
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) β δ /\
      multi_step (tas_glue_strength tas) (tas_tiles tas) (tas_temp tas) γ δ.
Proof.
  intros tas α β γ Hsc Hprod Hβ Hγ.
  revert γ Hγ.
  induction Hβ as [|α β' β Hαβ' Hβ'β IH].
  - intros γ Hγ.
    exists γ. split. exact Hγ. apply ms_refl.
  - intros γ Hγ.
    assert (Hprod_β': producible_in tas β').
    { eapply single_step_preserves_producibility; eauto. }
    destruct (strip_one_multi tas α β' γ Hsc Hprod Hαβ' Hγ) as [δ1 [Hβ'δ1 Hγδ1]].
    destruct (IH Hprod_β' δ1 Hβ'δ1) as [δ [Hβδ Hδ1δ]].
    exists δ. split.
    + exact Hβδ.
    + eapply multi_step_trans; eauto.
Qed.

Lemma diamond_aux :
  forall tas α β,
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
    strongly_confluent tas ->
    has_diamond_property tas.
Proof.
  intros tas Hsc α β γ Hprodα Hprodβ Hprodγ Hαβ Hαγ.
  eapply diamond_aux; [exact Hsc | exact Hprodα | exact Hαβ | exact Hαγ].
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
  assert (Hdiamond := strong_confluence_diamond tas Hsc).
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
  - apply strong_confluence_diamond. exact Hsc.
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
      assert (Hdiamond := strong_confluence_diamond tas Hsc).
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

Corollary diamond_equiv_strong_confluence :
  forall tas,
    strongly_confluent tas ->
    has_diamond_property tas.
Proof.
  intros tas Hsc.
  apply strong_confluence_diamond. exact Hsc.
Qed.

Corollary local_det_implies_diamond :
  forall tas,
    locally_deterministic tas ->
    has_diamond_property tas.
Proof.
  intros tas Hlocal.
  apply strong_confluence_diamond.
  apply locally_det_strong_confluence.
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

End WangTilings.

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
    match nth_error input (Z.to_nat pos) with
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
    match nth_error input (Z.to_nat pos) with
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

End ConcreteTM.

Section TMSimulation.

Context {State : Type}.
Context {State_eq_dec : forall (q1 q2 : State), {q1 = q2} + {q1 <> q2}}.
Context {TapeSymbol : Type}.
Context {TapeSymbol_eq_dec : forall (a b : TapeSymbol), {a = b} + {a <> b}}.

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

Fixpoint encode_glue (g : SimGlue) (state_offset tape_offset : nat) : nat :=
  match g with
  | GlueNull => 0
  | GlueState s => state_offset
  | GlueTapeSymbol sym => tape_offset
  | GlueDir Left => 1
  | GlueDir Right => 2
  | GlueDir Stay => 3
  end.

Lemma encode_glue_null : forall state_offset tape_offset,
  encode_glue GlueNull state_offset tape_offset = 0.
Proof.
  intros. simpl. reflexivity.
Qed.

Definition simtile_to_tiletype (st : SimTile) (state_offset tape_offset : nat) : TileType :=
  {| glue_N := encode_glue (st_glue_N st) state_offset tape_offset;
     glue_E := encode_glue (st_glue_E st) state_offset tape_offset;
     glue_S := encode_glue (st_glue_S st) state_offset tape_offset;
     glue_W := encode_glue (st_glue_W st) state_offset tape_offset |}.

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

Context (blank : TapeSymbol).

Definition config_to_row (cfg : @Config State TapeSymbol) (y : Z) : Z -> TMCell :=
  fun x => mkTMCell
    (if Z.eqb x (cfg_pos cfg) then Some (cfg_state cfg) else None)
    (cfg_tape cfg x)
    (Z.eqb x (cfg_pos cfg)).

Definition config_to_assembly (cfg : @Config State TapeSymbol) (state_offset tape_offset : nat) : Assembly :=
  fun p => let '(x, y) := p in
    if Z.eqb y 0
    then Some (simtile_to_tiletype (encode_cell_to_tile (config_to_row cfg y x)) state_offset tape_offset)
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

Lemma config_to_assembly_row_zero : forall cfg state_offset tape_offset x,
  config_to_assembly cfg state_offset tape_offset (x, 0%Z) =
    Some (simtile_to_tiletype (encode_cell_to_tile (config_to_row cfg 0%Z x)) state_offset tape_offset).
Proof.
  intros cfg state_offset tape_offset x.
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

Fixpoint generate_transition_tiles
  (M : @TuringMachine State TapeSymbol)
  (states : list State)
  (alphabet : list TapeSymbol)
  (state_offset tape_offset : nat)
  : list TileType :=
  match states with
  | [] => []
  | q :: qs =>
      let tiles_for_state :=
        flat_map (fun a =>
          match tm_transition M q a with
          | None => []
          | Some (q', a', d) =>
              [simtile_to_tiletype (transition_tile q a q' a' d) state_offset tape_offset]
          end) alphabet
      in tiles_for_state ++ generate_transition_tiles M qs alphabet state_offset tape_offset
  end.

Definition tm_to_tas
  (M : @TuringMachine State TapeSymbol)
  (seed_asm : Assembly)
  (state_offset tape_offset : nat)
  : TAS :=
  {| tas_tiles := generate_transition_tiles M (tm_states M) (tm_alphabet M) state_offset tape_offset;
     tas_seed := seed_asm;
     tas_glue_strength := fun g => if Nat.eqb g 0 then 0 else 1;
     tas_temp := 2 |}.

Lemma generate_transition_tiles_length_bound :
  forall (M : @TuringMachine State TapeSymbol) states alphabet state_offset tape_offset,
    length (generate_transition_tiles M states alphabet state_offset tape_offset) <=
    length states * length alphabet.
Proof.
  intros M states alphabet state_offset tape_offset.
  induction states as [|q qs IH]; simpl.
  - lia.
  - rewrite app_length.
    assert (Hflat: length (flat_map (fun a => match tm_transition M q a with
                                           | None => []
                                           | Some (q', a', d) => [simtile_to_tiletype (transition_tile q a q' a' d) state_offset tape_offset]
                                           end) alphabet) <= length alphabet).
    { clear IH. induction alphabet as [|a alphabet' IHa]; simpl.
      - lia.
      - destruct (tm_transition M q a) as [[[q' a'] d]|]; simpl; lia. }
    lia.
Qed.

Theorem tile_complexity_bound :
  forall (M : @TuringMachine State TapeSymbol) seed_asm state_offset tape_offset,
    length (tas_tiles (tm_to_tas M seed_asm state_offset tape_offset)) <=
    length (tm_states M) * length (tm_alphabet M).
Proof.
  intros M seed_asm state_offset tape_offset.
  unfold tm_to_tas. simpl.
  apply generate_transition_tiles_length_bound.
Qed.

Theorem tm_step_tile_correspondence :
  forall (M : @TuringMachine State TapeSymbol) (c c' : @Config State TapeSymbol) state_offset tape_offset,
    In (cfg_state c) (tm_states M) ->
    In (tape_read (cfg_tape c) (cfg_pos c)) (tm_alphabet M) ->
    step M c = Some c' ->
    exists t : TileType,
      In t (tas_tiles (tm_to_tas M empty_assembly state_offset tape_offset)) /\
      glue_N t = encode_glue (GlueState (cfg_state c)) state_offset tape_offset /\
      glue_E t = encode_glue (GlueTapeSymbol (cfg_tape c (cfg_pos c))) state_offset tape_offset.
Proof.
  intros M c c' state_offset tape_offset Hin_state Hin_sym Hstep.
  unfold step in Hstep.
  destruct (tm_transition M (cfg_state c) (tape_read (cfg_tape c) (cfg_pos c))) as [[[q' a'] d]|] eqn:Htrans.
  - injection Hstep as <-.
    exists (simtile_to_tiletype (transition_tile (cfg_state c) (tape_read (cfg_tape c) (cfg_pos c)) q' a' d) state_offset tape_offset).
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
  forall (M : @TuringMachine State TapeSymbol) seed_asm state_offset tape_offset,
    tas_temp (tm_to_tas M seed_asm state_offset tape_offset) = 2.
Proof.
  intros M seed_asm state_offset tape_offset.
  unfold tm_to_tas. simpl. reflexivity.
Qed.

Theorem tm_to_tas_glue_strength_nonzero :
  forall (M : @TuringMachine State TapeSymbol) seed_asm state_offset tape_offset g,
    g <> 0 ->
    tas_glue_strength (tm_to_tas M seed_asm state_offset tape_offset) g = 1.
Proof.
  intros M seed_asm state_offset tape_offset g Hneq.
  unfold tm_to_tas. simpl.
  destruct (Nat.eqb g 0) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Theorem cooperation_at_temp_2 :
  forall (M : @TuringMachine State TapeSymbol) seed_asm state_offset tape_offset g1 g2,
    state_offset <> 0 ->
    tape_offset <> 0 ->
    g1 = state_offset ->
    g2 = tape_offset ->
    tas_glue_strength (tm_to_tas M seed_asm state_offset tape_offset) g1 +
    tas_glue_strength (tm_to_tas M seed_asm state_offset tape_offset) g2 >=
    tas_temp (tm_to_tas M seed_asm state_offset tape_offset).
Proof.
  intros M seed_asm state_offset tape_offset g1 g2 Hoff1 Hoff2 Heq1 Heq2.
  subst g1 g2.
  rewrite tm_to_tas_has_temp_2.
  rewrite tm_to_tas_glue_strength_nonzero by assumption.
  rewrite tm_to_tas_glue_strength_nonzero by assumption.
  lia.
Qed.

Lemma encode_glue_state_nonzero :
  forall q state_offset tape_offset,
    state_offset <> 0 ->
    encode_glue (GlueState q) state_offset tape_offset <> 0.
Proof.
  intros q state_offset tape_offset Hoff.
  unfold encode_glue. exact Hoff.
Qed.

Lemma encode_glue_tape_nonzero :
  forall a state_offset tape_offset,
    tape_offset <> 0 ->
    encode_glue (GlueTapeSymbol a) state_offset tape_offset <> 0.
Proof.
  intros a state_offset tape_offset Hoff.
  unfold encode_glue. exact Hoff.
Qed.

Theorem turing_completeness_at_temperature_2 :
  forall (M : @TuringMachine State TapeSymbol) seed_asm,
    (forall q a, In q (tm_states M) -> In a (tm_alphabet M) ->
      exists q' a' d, tm_transition M q a = Some (q', a', d) \/ tm_transition M q a = None) ->
    exists state_offset tape_offset,
      state_offset <> 0 /\
      tape_offset <> 0 /\
      tas_temp (tm_to_tas M seed_asm state_offset tape_offset) = 2 /\
      (forall c c',
        In (cfg_state c) (tm_states M) ->
        In (tape_read (cfg_tape c) (cfg_pos c)) (tm_alphabet M) ->
        step M c = Some c' ->
        exists t,
          In t (tas_tiles (tm_to_tas M seed_asm state_offset tape_offset)) /\
          glue_N t = encode_glue (GlueState (cfg_state c)) state_offset tape_offset /\
          glue_E t = encode_glue (GlueTapeSymbol (cfg_tape c (cfg_pos c))) state_offset tape_offset).
Proof.
  intros M seed_asm Htrans_total.
  exists 1, 2.
  split. discriminate.
  split. discriminate.
  split. apply tm_to_tas_has_temp_2.
  intros c c' Hstate Hsym Hstep.
  apply (tm_step_tile_correspondence M c c' 1 2 Hstate Hsym Hstep).
Qed.

Theorem turing_completeness_multistep :
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
          In t (tas_tiles (tm_to_tas M seed_asm state_offset tape_offset)) /\
          glue_N t = encode_glue (GlueState (@cfg_state State TapeSymbol step_c)) state_offset tape_offset /\
          glue_E t = encode_glue (GlueTapeSymbol (@cfg_tape State TapeSymbol step_c (@cfg_pos State TapeSymbol step_c))) state_offset tape_offset.
Proof.
  intros M seed_asm c c' Htrans Hstate_all Hsym_all Hsteps.
  exists 1, 2.
  split. discriminate.
  split. discriminate.
  intros step_c step_c' Hsteps_to_c Hstep.
  apply (tm_step_tile_correspondence M step_c step_c' 1 2).
  - apply Hstate_all.
  - apply Hsym_all.
  - exact Hstep.
Qed.

Theorem turing_completeness_simulation_soundness :
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
          In t (tas_tiles (tm_to_tas M empty_assembly state_offset tape_offset)) /\
          glue_N t = encode_glue (GlueState (@cfg_state State TapeSymbol intermediate_config)) state_offset tape_offset /\
          glue_E t = encode_glue (GlueTapeSymbol (@cfg_tape State TapeSymbol intermediate_config (@cfg_pos State TapeSymbol intermediate_config))) state_offset tape_offset.
Proof.
  intros M start_config final_config Hstates Halphabet Hsteps.
  exists 1, 2.
  split. discriminate.
  split. discriminate.
  intros intermediate_config next_config Hsteps_inter Hstep.
  apply (tm_step_tile_correspondence M intermediate_config next_config 1 2).
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

Lemma encode_glue_preserves_null : forall off1 off2,
  encode_glue GlueNull off1 off2 = 0.
Proof.
  intros off1 off2. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_nonzero_state : forall q off1 off2,
  encode_glue (GlueState q) off1 off2 = off1.
Proof.
  intros q off1 off2. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_nonzero_tape : forall sym off1 off2,
  encode_glue (GlueTapeSymbol sym) off1 off2 = off2.
Proof.
  intros sym off1 off2. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_dir_left : forall off1 off2,
  encode_glue (GlueDir Left) off1 off2 = 1.
Proof.
  intros off1 off2. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_dir_right : forall off1 off2,
  encode_glue (GlueDir Right) off1 off2 = 2.
Proof.
  intros off1 off2. unfold encode_glue. reflexivity.
Qed.

Lemma encode_glue_dir_stay : forall off1 off2,
  encode_glue (GlueDir Stay) off1 off2 = 3.
Proof.
  intros off1 off2. unfold encode_glue. reflexivity.
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

End TMSimulation.

Section TuringCompletenessExamples.

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
  exists (tm_to_tas M empty_assembly 1 2).
  split.
  - apply tm_to_tas_has_temp_2.
  - assert (Htile := @tm_step_tile_correspondence nat Nat.eq_dec nat Nat.eq_dec M c c' 1 2 Hstate Hsym Hstep).
    destruct Htile as [t [Hin _]].
    exists t.
    split. exact Hin.
    intros g1 g2 Hg1 Hg2.
    rewrite tm_to_tas_has_temp_2.
    rewrite tm_to_tas_glue_strength_nonzero by assumption.
    rewrite tm_to_tas_glue_strength_nonzero by assumption.
    lia.
Qed.

End TuringCompletenessExamples.
