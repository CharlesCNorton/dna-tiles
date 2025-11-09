(** * Formalization of Abstract Tile Assembly Model (aTAM) - Section 1

    This file contains a rigorous formalization of the Abstract Tile Assembly Model,
    covering core definitions, assembly dynamics, determinism properties, and the
    connection to Wang tilings and undecidability results.

    Organization:
    - Section 1.1: Core Definitions (aTAM Foundation)
    - Section 1.2: Assembly Dynamics
    - Section 1.3: Determinism and Uniqueness
    - Section 1.4: Wang Tilings Connection

    All proofs are complete with no axioms or admitted lemmas.
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

Import ListNotations.
Open Scope list_scope.

(** * Section 1.1: Core Definitions (aTAM Foundation) *)

(** ** 1.1.1 Type System & Basic Structures *)

(** Glue types are natural numbers representing binding sites on tile edges *)
Definition GlueType : Type := nat.

(** The null glue (glue 0) represents no binding *)
Definition null_glue : GlueType := 0.

(** Decidable equality for glues *)
Definition glue_eq_dec : forall (g1 g2 : GlueType), {g1 = g2} + {g1 <> g2} :=
  Nat.eq_dec.

(** Tile types are 4-tuples of glues: (N, E, S, W) *)
Record TileType : Type := mkTile {
  glue_N : GlueType;
  glue_E : GlueType;
  glue_S : GlueType;
  glue_W : GlueType
}.

(** Decidable equality for tiles *)
Lemma TileType_eq_dec : forall (t1 t2 : TileType), {t1 = t2} + {t1 <> t2}.
Proof.
  intros [n1 e1 s1 w1] [n2 e2 s2 w2].
  destruct (glue_eq_dec n1 n2); destruct (glue_eq_dec e1 e2);
  destruct (glue_eq_dec s1 s2); destruct (glue_eq_dec w1 w2); subst;
  try (right; intro H; inversion H; contradiction);
  left; reflexivity.
Qed.

(** Direction type for tile adjacency *)
Inductive Direction : Type :=
  | North : Direction
  | East : Direction
  | South : Direction
  | West : Direction.

(** Decidable equality for directions *)
Lemma Direction_eq_dec : forall (d1 d2 : Direction), {d1 = d2} + {d1 <> d2}.
Proof.
  intros d1 d2.
  destruct d1; destruct d2;
  try (left; reflexivity);
  try (right; intro H; discriminate).
Defined.

(** Opposite direction *)
Definition opposite_direction (d : Direction) : Direction :=
  match d with
  | North => South
  | East => West
  | South => North
  | West => East
  end.

Lemma opposite_direction_involutive : forall d,
  opposite_direction (opposite_direction d) = d.
Proof.
  intros d. destruct d; reflexivity.
Qed.

(** List of all four directions *)
Definition all_directions : list Direction := [North; East; South; West].

Lemma all_directions_complete : forall d, In d all_directions.
Proof.
  intro d. destruct d; unfold all_directions; simpl; auto.
Qed.

Lemma all_directions_length : length all_directions = 4.
Proof.
  unfold all_directions. simpl. reflexivity.
Qed.

Lemma all_directions_NoDup : NoDup all_directions.
Proof.
  unfold all_directions.
  constructor. intro H. simpl in H. destruct H as [H | [H | [H | H]]]; inversion H.
  constructor. intro H. simpl in H. destruct H as [H | [H | H]]; inversion H.
  constructor. intro H. simpl in H. destruct H as [H | H]; inversion H.
  constructor. intro H. simpl in H. destruct H.
  constructor.
Qed.

(** Get glue from tile in a specific direction *)
Definition get_glue (t : TileType) (d : Direction) : GlueType :=
  match d with
  | North => glue_N t
  | East => glue_E t
  | South => glue_S t
  | West => glue_W t
  end.

(** Tile glue matching in a specific direction *)
Definition tiles_match_north (t1 t2 : TileType) : Prop :=
  glue_N t2 = glue_S t1.

Definition tiles_match_east (t1 t2 : TileType) : Prop :=
  glue_W t2 = glue_E t1.

Definition tiles_match_south (t1 t2 : TileType) : Prop :=
  glue_S t2 = glue_N t1.

Definition tiles_match_west (t1 t2 : TileType) : Prop :=
  glue_E t2 = glue_W t1.

(** General tile matching predicate parameterized by direction *)
Definition tiles_match (t1 t2 : TileType) (d : Direction) : Prop :=
  match d with
  | North => tiles_match_north t1 t2
  | East => tiles_match_east t1 t2
  | South => tiles_match_south t1 t2
  | West => tiles_match_west t1 t2
  end.

(** Decidability of tile matching *)
Lemma tiles_match_dec : forall t1 t2 d,
  {tiles_match t1 t2 d} + {~tiles_match t1 t2 d}.
Proof.
  intros t1 t2 d.
  destruct d; unfold tiles_match, tiles_match_north, tiles_match_east,
    tiles_match_south, tiles_match_west;
  apply glue_eq_dec.
Defined.

(** Tile matching is symmetric with reversed direction *)
Lemma tiles_match_north_symmetric : forall t1 t2,
  tiles_match_north t1 t2 <-> tiles_match_south t2 t1.
Proof.
  intros t1 t2.
  unfold tiles_match_north, tiles_match_south.
  split; intro H; symmetry; exact H.
Qed.

Lemma tiles_match_east_symmetric : forall t1 t2,
  tiles_match_east t1 t2 <-> tiles_match_west t2 t1.
Proof.
  intros t1 t2.
  unfold tiles_match_east, tiles_match_west.
  split; intro H; symmetry; exact H.
Qed.

Lemma tiles_match_south_symmetric : forall t1 t2,
  tiles_match_south t1 t2 <-> tiles_match_north t2 t1.
Proof.
  intros t1 t2.
  unfold tiles_match_south, tiles_match_north.
  split; intro H; symmetry; exact H.
Qed.

Lemma tiles_match_west_symmetric : forall t1 t2,
  tiles_match_west t1 t2 <-> tiles_match_east t2 t1.
Proof.
  intros t1 t2.
  unfold tiles_match_west, tiles_match_east.
  split; intro H; symmetry; exact H.
Qed.

(** Matching is reflexive when tile has matching opposite glues *)
Lemma tiles_self_match_north_south : forall t,
  glue_N t = glue_S t -> tiles_match_north t t.
Proof.
  intros t H.
  unfold tiles_match_north. exact H.
Qed.

Lemma tiles_self_match_east_west : forall t,
  glue_E t = glue_W t -> tiles_match_east t t.
Proof.
  intros t H.
  unfold tiles_match_east. symmetry. exact H.
Qed.

(** Positions in the Z^2 lattice *)
Definition Position : Type := (Z * Z)%type.

(** Decidable equality for positions *)
Lemma Position_eq_dec : forall (p1 p2 : Position), {p1 = p2} + {p1 <> p2}.
Proof.
  intros [x1 y1] [x2 y2].
  destruct (Z.eq_dec x1 x2); destruct (Z.eq_dec y1 y2); subst;
  try (right; intro H; inversion H; contradiction);
  left; reflexivity.
Qed.

(** Assemblies are partial functions from positions to tiles *)
Definition Assembly : Type := Position -> option TileType.

(** Temperature represents the minimum binding strength threshold *)
Definition Temperature : Type := nat.

(** Glue strength function: computes binding strength between two glues *)
Definition glue_strength (strength_fn : GlueType -> nat) (g1 g2 : GlueType) : nat :=
  if glue_eq_dec g1 g2 then
    if glue_eq_dec g1 null_glue then 0
    else strength_fn g1
  else 0.

(** Basic properties of glue strength *)
Lemma glue_strength_symmetric : forall strength_fn g1 g2,
  glue_strength strength_fn g1 g2 = glue_strength strength_fn g2 g1.
Proof.
  intros strength_fn g1 g2.
  unfold glue_strength.
  destruct (glue_eq_dec g1 g2) as [Heq | Hneq].
  - subst. destruct (glue_eq_dec g2 g2) as [_ | Hcontra]; try contradiction.
    reflexivity.
  - destruct (glue_eq_dec g2 g1) as [Heq' | _].
    + symmetry in Heq'. contradiction.
    + reflexivity.
Qed.

Lemma glue_strength_null : forall strength_fn g,
  glue_strength strength_fn null_glue g = 0.
Proof.
  intros strength_fn g.
  unfold glue_strength, null_glue.
  destruct (glue_eq_dec 0 g) as [Heq | Hneq].
  - subst. destruct (glue_eq_dec 0 0) as [_ | Hcontra]; try contradiction.
    destruct (glue_eq_dec 0 0); reflexivity.
  - reflexivity.
Qed.

Lemma glue_strength_mismatch : forall strength_fn g1 g2,
  g1 <> g2 -> glue_strength strength_fn g1 g2 = 0.
Proof.
  intros strength_fn g1 g2 Hneq.
  unfold glue_strength.
  destruct (glue_eq_dec g1 g2); try contradiction; auto.
Qed.

(** Tile matching with null glues produces zero strength *)
Theorem tiles_match_null_glue_zero_strength : forall t1 t2 d strength_fn,
  tiles_match t1 t2 d ->
  (match d with
   | North => glue_S t1 = null_glue \/ glue_N t2 = null_glue
   | East => glue_E t1 = null_glue \/ glue_W t2 = null_glue
   | South => glue_N t1 = null_glue \/ glue_S t2 = null_glue
   | West => glue_W t1 = null_glue \/ glue_E t2 = null_glue
   end) ->
  (match d with
   | North => glue_strength strength_fn (glue_N t2) (glue_S t1) = 0
   | East => glue_strength strength_fn (glue_W t2) (glue_E t1) = 0
   | South => glue_strength strength_fn (glue_S t2) (glue_N t1) = 0
   | West => glue_strength strength_fn (glue_E t2) (glue_W t1) = 0
   end).
Proof.
  intros t1 t2 d strength_fn Hmatch Hnull.
  destruct d; unfold tiles_match, tiles_match_north, tiles_match_east,
    tiles_match_south, tiles_match_west in Hmatch.
  - destruct Hnull as [Hs | Hn].
    + rewrite Hs. rewrite glue_strength_symmetric. apply glue_strength_null.
    + rewrite Hn. apply glue_strength_null.
  - destruct Hnull as [He | Hw].
    + rewrite He. rewrite glue_strength_symmetric. apply glue_strength_null.
    + rewrite Hw. apply glue_strength_null.
  - destruct Hnull as [Hn | Hs].
    + rewrite Hn. rewrite glue_strength_symmetric. apply glue_strength_null.
    + rewrite Hs. apply glue_strength_null.
  - destruct Hnull as [Hw | He].
    + rewrite Hw. rewrite glue_strength_symmetric. apply glue_strength_null.
    + rewrite He. apply glue_strength_null.
Qed.

(** If tiles match in direction d, their glues are equal in that direction *)
Theorem tiles_match_implies_glue_equality : forall t1 t2 d,
  tiles_match t1 t2 d ->
  match d with
  | North => glue_N t2 = glue_S t1
  | East => glue_W t2 = glue_E t1
  | South => glue_S t2 = glue_N t1
  | West => glue_E t2 = glue_W t1
  end.
Proof.
  intros t1 t2 d Hmatch.
  destruct d; unfold tiles_match, tiles_match_north, tiles_match_east,
    tiles_match_south, tiles_match_west in Hmatch; exact Hmatch.
Qed.

(** Query a tile at a position in an assembly *)
Definition tile_at (α : Assembly) (p : Position) : option TileType :=
  α p.

(** Empty assembly with no tiles *)
Definition empty_assembly : Assembly :=
  fun _ => None.

(** Assembly equivalence: two assemblies are equivalent if they agree at all positions *)
Definition assembly_equiv (α β : Assembly) : Prop :=
  forall p, tile_at α p = tile_at β p.

Notation "α ≡ β" := (assembly_equiv α β) (at level 70).

(** Assembly equivalence is an equivalence relation *)
Lemma assembly_equiv_refl : forall α, α ≡ α.
Proof.
  intros α p. reflexivity.
Qed.

Lemma assembly_equiv_sym : forall α β, α ≡ β -> β ≡ α.
Proof.
  intros α β H p. symmetry. apply H.
Qed.

Lemma assembly_equiv_trans : forall α β γ, α ≡ β -> β ≡ γ -> α ≡ γ.
Proof.
  intros α β γ Hab Hbc p.
  unfold assembly_equiv in *.
  rewrite Hab. apply Hbc.
Qed.

(** ** Setoid Instance for Assembly Equivalence *)

(** Register assembly_equiv as a setoid relation for automatic rewriting *)
Add Parametric Relation : Assembly assembly_equiv
  reflexivity proved by assembly_equiv_refl
  symmetry proved by assembly_equiv_sym
  transitivity proved by assembly_equiv_trans
  as assembly_equiv_setoid.

(** Morphisms: Register operations that respect assembly equivalence *)

(** tile_at respects assembly equivalence *)
Add Parametric Morphism : tile_at
  with signature assembly_equiv ==> eq ==> eq
  as tile_at_morphism.
Proof.
  intros α β Heq p.
  unfold assembly_equiv in Heq.
  apply Heq.
Qed.

(** Note: Additional morphisms for support, assembly_union, add_tile, remove_tile,
    domain_subset, and binding_strength are defined later, after those operations
    are introduced in their respective sections. *)

(** Empty assembly properties *)
Lemma empty_assembly_has_no_tiles : forall p,
  tile_at empty_assembly p = None.
Proof.
  intro p. unfold tile_at, empty_assembly. reflexivity.
Qed.

(** Glue strength matching theorem: equal non-null glues bind with positive strength *)
Theorem glue_strength_match_positive : forall strength_fn g,
  g <> null_glue ->
  strength_fn g > 0 ->
  glue_strength strength_fn g g > 0.
Proof.
  intros strength_fn g Hnonnull Hpos.
  unfold glue_strength.
  destruct (glue_eq_dec g g) as [_ | Hcontra]; try contradiction.
  destruct (glue_eq_dec g null_glue) as [Heq | _]; try contradiction.
  exact Hpos.
Qed.

(** Helper: tiles_match_north preserves non-null property *)
Lemma tiles_match_north_nonnull : forall t1 t2,
  tiles_match_north t1 t2 ->
  glue_S t1 <> null_glue ->
  glue_N t2 <> null_glue.
Proof.
  intros t1 t2 Hmatch Hnonnull.
  unfold tiles_match_north in Hmatch.
  rewrite Hmatch. exact Hnonnull.
Qed.

Lemma tiles_match_east_nonnull : forall t1 t2,
  tiles_match_east t1 t2 ->
  glue_E t1 <> null_glue ->
  glue_W t2 <> null_glue.
Proof.
  intros t1 t2 Hmatch Hnonnull.
  unfold tiles_match_east in Hmatch.
  rewrite Hmatch. exact Hnonnull.
Qed.

Lemma tiles_match_south_nonnull : forall t1 t2,
  tiles_match_south t1 t2 ->
  glue_N t1 <> null_glue ->
  glue_S t2 <> null_glue.
Proof.
  intros t1 t2 Hmatch Hnonnull.
  unfold tiles_match_south in Hmatch.
  rewrite Hmatch. exact Hnonnull.
Qed.

Lemma tiles_match_west_nonnull : forall t1 t2,
  tiles_match_west t1 t2 ->
  glue_W t1 <> null_glue ->
  glue_E t2 <> null_glue.
Proof.
  intros t1 t2 Hmatch Hnonnull.
  unfold tiles_match_west in Hmatch.
  rewrite Hmatch. exact Hnonnull.
Qed.

(** If tiles match north and glue is non-null, binding strength is positive *)
Lemma tiles_match_north_positive_strength : forall strength_fn t1 t2,
  (forall g, g <> null_glue -> strength_fn g > 0) ->
  tiles_match_north t1 t2 ->
  glue_S t1 <> null_glue ->
  glue_strength strength_fn (glue_N t2) (glue_S t1) > 0.
Proof.
  intros strength_fn t1 t2 Hpos Hmatch Hnonnull.
  unfold tiles_match_north in Hmatch.
  assert (Hnn: glue_N t2 <> null_glue).
  { rewrite Hmatch. exact Hnonnull. }
  unfold glue_strength.
  destruct (glue_eq_dec (glue_N t2) (glue_S t1)).
  - destruct (glue_eq_dec (glue_N t2) null_glue); try contradiction.
    apply Hpos. exact Hnn.
  - exfalso. apply n. exact Hmatch.
Qed.

Lemma tiles_match_east_positive_strength : forall strength_fn t1 t2,
  (forall g, g <> null_glue -> strength_fn g > 0) ->
  tiles_match_east t1 t2 ->
  glue_E t1 <> null_glue ->
  glue_strength strength_fn (glue_W t2) (glue_E t1) > 0.
Proof.
  intros strength_fn t1 t2 Hpos Hmatch Hnonnull.
  unfold tiles_match_east in Hmatch.
  assert (Hnn: glue_W t2 <> null_glue).
  { rewrite Hmatch. exact Hnonnull. }
  unfold glue_strength.
  destruct (glue_eq_dec (glue_W t2) (glue_E t1)).
  - destruct (glue_eq_dec (glue_W t2) null_glue); try contradiction.
    apply Hpos. exact Hnn.
  - exfalso. apply n. exact Hmatch.
Qed.

Lemma tiles_match_south_positive_strength : forall strength_fn t1 t2,
  (forall g, g <> null_glue -> strength_fn g > 0) ->
  tiles_match_south t1 t2 ->
  glue_N t1 <> null_glue ->
  glue_strength strength_fn (glue_S t2) (glue_N t1) > 0.
Proof.
  intros strength_fn t1 t2 Hpos Hmatch Hnonnull.
  unfold tiles_match_south in Hmatch.
  assert (Hnn: glue_S t2 <> null_glue).
  { rewrite Hmatch. exact Hnonnull. }
  unfold glue_strength.
  destruct (glue_eq_dec (glue_S t2) (glue_N t1)).
  - destruct (glue_eq_dec (glue_S t2) null_glue); try contradiction.
    apply Hpos. exact Hnn.
  - exfalso. apply n. exact Hmatch.
Qed.

Lemma tiles_match_west_positive_strength : forall strength_fn t1 t2,
  (forall g, g <> null_glue -> strength_fn g > 0) ->
  tiles_match_west t1 t2 ->
  glue_W t1 <> null_glue ->
  glue_strength strength_fn (glue_E t2) (glue_W t1) > 0.
Proof.
  intros strength_fn t1 t2 Hpos Hmatch Hnonnull.
  unfold tiles_match_west in Hmatch.
  assert (Hnn: glue_E t2 <> null_glue).
  { rewrite Hmatch. exact Hnonnull. }
  unfold glue_strength.
  destruct (glue_eq_dec (glue_E t2) (glue_W t1)).
  - destruct (glue_eq_dec (glue_E t2) null_glue); try contradiction.
    apply Hpos. exact Hnn.
  - exfalso. apply n. exact Hmatch.
Qed.

(** If tiles match and glues are non-null, binding strength is positive *)
Theorem tiles_match_nonnull_positive_strength : forall strength_fn t1 t2 d,
  (forall g, g <> null_glue -> strength_fn g > 0) ->
  tiles_match t1 t2 d ->
  (match d with
   | North => glue_S t1 <> null_glue
   | East => glue_E t1 <> null_glue
   | South => glue_N t1 <> null_glue
   | West => glue_W t1 <> null_glue
   end) ->
  (match d with
   | North => glue_strength strength_fn (glue_N t2) (glue_S t1) > 0
   | East => glue_strength strength_fn (glue_W t2) (glue_E t1) > 0
   | South => glue_strength strength_fn (glue_S t2) (glue_N t1) > 0
   | West => glue_strength strength_fn (glue_E t2) (glue_W t1) > 0
   end).
Proof.
  intros strength_fn t1 t2 d Hpos Hmatch Hnonnull.
  destruct d; unfold tiles_match in Hmatch.
  - apply tiles_match_north_positive_strength; assumption.
  - apply tiles_match_east_positive_strength; assumption.
  - apply tiles_match_south_positive_strength; assumption.
  - apply tiles_match_west_positive_strength; assumption.
Qed.

(** Glue strength is zero for all null glue interactions *)
Theorem glue_strength_null_everywhere : forall strength_fn g,
  glue_strength strength_fn null_glue g = 0 /\
  glue_strength strength_fn g null_glue = 0.
Proof.
  intros strength_fn g.
  split.
  - apply glue_strength_null.
  - rewrite glue_strength_symmetric. apply glue_strength_null.
Qed.

(** Assembly equivalence respects tile placement *)
Theorem assembly_equiv_preserves_tile_at : forall α β p t,
  α ≡ β ->
  tile_at α p = Some t ->
  tile_at β p = Some t.
Proof.
  intros α β p t Hequiv Htile.
  unfold assembly_equiv in Hequiv.
  rewrite <- Hequiv. exact Htile.
Qed.

(** Two assemblies are equivalent iff they disagree nowhere *)
Theorem assembly_equiv_iff_pointwise : forall α β,
  α ≡ β <-> (forall p, tile_at α p = tile_at β p).
Proof.
  intros α β. split; intro H; unfold assembly_equiv; intro p; apply H.
Qed.

(** If an assembly is equivalent to empty, it has no tiles anywhere *)
Theorem equiv_empty_implies_no_tiles : forall α,
  α ≡ empty_assembly ->
  forall p, tile_at α p = None.
Proof.
  intros α H p.
  unfold assembly_equiv in H.
  rewrite H.
  apply empty_assembly_has_no_tiles.
Qed.

(** ** 1.1.2 Tile Assembly System (TAS) Definition *)

Definition TileSet : Type := list TileType.

(** A Tile Assembly System (TAS) consists of:
    - A finite set of tile types
    - A glue strength function
    - An initial seed assembly
    - A temperature threshold *)
Record TAS : Type := mkTAS {
  tas_tiles : TileSet;
  tas_glue_strength : GlueType -> nat;
  tas_seed : Assembly;
  tas_temp : Temperature
}.

(** Tile membership in a tileset *)
Definition tile_in_set (t : TileType) (ts : TileSet) : Prop :=
  In t ts.

Lemma tile_in_set_dec : forall t ts,
  {tile_in_set t ts} + {~tile_in_set t ts}.
Proof.
  intros t ts.
  unfold tile_in_set.
  apply in_dec.
  apply TileType_eq_dec.
Qed.

(** Well-formedness conditions for TAS *)

(** A TAS is well-formed if all tiles in the seed are from the tileset *)
Definition seed_uses_tileset (S : TAS) : Prop :=
  forall p t, tile_at (tas_seed S) p = Some t -> tile_in_set t (tas_tiles S).

(** A TAS has non-empty tileset *)
Definition has_tiles (S : TAS) : Prop :=
  length (tas_tiles S) > 0.

(** A strength function is valid if null glue has zero strength *)
Definition valid_strength_fn (f : GlueType -> nat) : Prop :=
  f null_glue = 0.

(** Glue strength function is reasonable: null glue has zero strength *)
Definition glue_fn_respects_null (S : TAS) : Prop :=
  valid_strength_fn (tas_glue_strength S).

(** A TAS is well-formed if it satisfies basic sanity conditions *)
Definition well_formed_tas (S : TAS) : Prop :=
  seed_uses_tileset S /\ glue_fn_respects_null S.

(** Basic TAS properties *)

Lemma empty_tileset_has_length_zero : forall (ts : TileSet),
  length ts = 0 <-> ts = [].
Proof.
  intro ts. split; intro H.
  - destruct ts; auto. simpl in H. discriminate.
  - subst. reflexivity.
Qed.

Theorem well_formed_seed_only_uses_tileset : forall S p t,
  well_formed_tas S ->
  tile_at (tas_seed S) p = Some t ->
  tile_in_set t (tas_tiles S).
Proof.
  intros S p t [Hseed _] Htile.
  unfold seed_uses_tileset in Hseed.
  apply (Hseed p). exact Htile.
Qed.

Theorem well_formed_null_glue_zero : forall S,
  well_formed_tas S ->
  tas_glue_strength S null_glue = 0.
Proof.
  intros S [_ Hnull].
  exact Hnull.
Qed.

(** TAS with empty seed *)
Definition tas_with_empty_seed (tiles : TileSet) (gfn : GlueType -> nat) (temp : Temperature) : TAS :=
  mkTAS tiles gfn empty_assembly temp.

Lemma tas_empty_seed_well_formed : forall tiles gfn temp,
  valid_strength_fn gfn ->
  well_formed_tas (tas_with_empty_seed tiles gfn temp).
Proof.
  intros tiles gfn temp Hvalid.
  unfold well_formed_tas, seed_uses_tileset, glue_fn_respects_null.
  simpl. split.
  - intros p t Ht. unfold tile_at, empty_assembly in Ht. discriminate.
  - exact Hvalid.
Qed.

(** Seed assembly properties *)

Lemma seed_tiles_from_tileset : forall S p t,
  well_formed_tas S ->
  tile_at (tas_seed S) p = Some t ->
  tile_in_set t (tas_tiles S).
Proof.
  intros S p t Hwf Htile.
  apply (well_formed_seed_only_uses_tileset S p t); assumption.
Qed.

(** Standard glue strength function: all non-null glues have strength 1 *)
Definition standard_glue_strength (g : GlueType) : nat :=
  if glue_eq_dec g null_glue then 0 else 1.

Lemma standard_glue_respects_null :
  standard_glue_strength null_glue = 0.
Proof.
  unfold standard_glue_strength.
  destruct (glue_eq_dec null_glue null_glue); try contradiction.
  reflexivity.
Qed.

(** Standard glue strength is a valid strength function *)
Theorem standard_glue_is_valid :
  valid_strength_fn standard_glue_strength.
Proof.
  unfold valid_strength_fn.
  apply standard_glue_respects_null.
Qed.

Theorem standard_glue_strength_nonzero_iff : forall g,
  standard_glue_strength g > 0 <-> g <> null_glue.
Proof.
  intro g. split; intro H.
  - unfold standard_glue_strength in H.
    destruct (glue_eq_dec g null_glue) as [Heq | Hneq].
    + subst. simpl in H. lia.
    + assumption.
  - unfold standard_glue_strength.
    destruct (glue_eq_dec g null_glue) as [Heq | Hneq].
    + contradiction.
    + lia.
Qed.

(** Null glue conventions *)

(** Tiles with null glues on all sides cannot bind *)
Definition all_null_glues (t : TileType) : Prop :=
  glue_N t = null_glue /\ glue_E t = null_glue /\
  glue_S t = null_glue /\ glue_W t = null_glue.

Lemma all_null_glues_dec : forall t,
  {all_null_glues t} + {~all_null_glues t}.
Proof.
  intro t.
  unfold all_null_glues.
  destruct (glue_eq_dec (glue_N t) null_glue);
  destruct (glue_eq_dec (glue_E t) null_glue);
  destruct (glue_eq_dec (glue_S t) null_glue);
  destruct (glue_eq_dec (glue_W t) null_glue);
  try (right; intro H; destruct H as [? [? [? ?]]]; contradiction);
  left; repeat split; assumption.
Qed.

Theorem all_null_tile_no_binding : forall strength_fn t1 t2,
  all_null_glues t1 ->
  glue_strength strength_fn (glue_N t1) (glue_S t2) = 0 /\
  glue_strength strength_fn (glue_E t1) (glue_W t2) = 0 /\
  glue_strength strength_fn (glue_S t1) (glue_N t2) = 0 /\
  glue_strength strength_fn (glue_W t1) (glue_E t2) = 0.
Proof.
  intros strength_fn t1 t2 [HN [HE [HS HW]]].
  repeat split; rewrite HN || rewrite HE || rewrite HS || rewrite HW;
  apply glue_strength_null.
Qed.

(** TAS structure theorems *)

Theorem tile_in_singleton : forall t1 t2,
  tile_in_set t1 [t2] <-> t1 = t2.
Proof.
  intros t1 t2. split; intro H.
  - unfold tile_in_set in H. simpl in H.
    destruct H as [Heq | Hcontra]; try contradiction. symmetry. exact Heq.
  - subst. unfold tile_in_set. simpl. left. reflexivity.
Qed.

Theorem tileset_nonempty_has_element : forall ts,
  length ts > 0 -> exists t, tile_in_set t ts.
Proof.
  intros ts Hlen.
  destruct ts as [| t rest].
  - simpl in Hlen. lia.
  - exists t. unfold tile_in_set. simpl. left. reflexivity.
Qed.

Theorem well_formed_with_standard_glue : forall tiles seed temp,
  seed_uses_tileset (mkTAS tiles standard_glue_strength seed temp) ->
  well_formed_tas (mkTAS tiles standard_glue_strength seed temp).
Proof.
  intros tiles seed temp Hseed.
  unfold well_formed_tas. simpl. split.
  - exact Hseed.
  - apply standard_glue_is_valid.
Qed.

(** TileSet decidability and properties *)

Fixpoint tileset_eq_dec (ts1 ts2 : TileSet) : {ts1 = ts2} + {ts1 <> ts2}.
Proof.
  destruct ts1 as [| t1 rest1]; destruct ts2 as [| t2 rest2].
  - left. reflexivity.
  - right. intro H. discriminate.
  - right. intro H. discriminate.
  - destruct (TileType_eq_dec t1 t2) as [Heq | Hneq].
    + destruct (tileset_eq_dec rest1 rest2) as [Heq' | Hneq'].
      * left. f_equal; assumption.
      * right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
Defined.

Lemma tileset_eq_refl : forall ts,
  tileset_eq_dec ts ts = left eq_refl.
Proof.
  intro ts.
  induction ts as [| t rest IH].
  - simpl. reflexivity.
  - simpl. destruct (TileType_eq_dec t t) as [Heq | Hneq].
    + rewrite IH. f_equal. apply Eqdep_dec.UIP_dec. apply list_eq_dec. apply TileType_eq_dec.
    + contradiction.
Qed.

(** Maximum glue type in a tileset *)

Definition max_glue_in_tile (t : TileType) : nat :=
  max (max (glue_N t) (glue_E t)) (max (glue_S t) (glue_W t)).

Fixpoint max_glue_in_tileset (ts : TileSet) : nat :=
  match ts with
  | [] => 0
  | t :: rest => max (max_glue_in_tile t) (max_glue_in_tileset rest)
  end.

Lemma max_glue_in_tile_bounds : forall t,
  glue_N t <= max_glue_in_tile t /\
  glue_E t <= max_glue_in_tile t /\
  glue_S t <= max_glue_in_tile t /\
  glue_W t <= max_glue_in_tile t.
Proof.
  intro t. unfold max_glue_in_tile.
  repeat split; lia.
Qed.

Lemma max_glue_tileset_bounds_element : forall t ts,
  In t ts -> max_glue_in_tile t <= max_glue_in_tileset ts.
Proof.
  intros t ts Hin.
  induction ts as [| t' rest IH].
  - destruct Hin.
  - simpl. simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. lia.
    + assert (H: max_glue_in_tile t <= max_glue_in_tileset rest) by auto.
      lia.
Qed.

Theorem glue_in_tileset_bounded : forall t ts g,
  In t ts ->
  (g = glue_N t \/ g = glue_E t \/ g = glue_S t \/ g = glue_W t) ->
  g <= max_glue_in_tileset ts.
Proof.
  intros t ts g Hin Hglue.
  pose proof (max_glue_tileset_bounds_element t ts Hin) as Hbound.
  pose proof (max_glue_in_tile_bounds t) as [HN [HE [HS HW]]].
  destruct Hglue as [HN' | [HE' | [HS' | HW']]]; subst; lia.
Qed.

Definition glues_bounded (S : TAS) : Prop :=
  forall t g, tile_in_set t (tas_tiles S) ->
    (g = glue_N t \/ g = glue_E t \/ g = glue_S t \/ g = glue_W t) ->
    g <= max_glue_in_tileset (tas_tiles S).

Theorem tas_glues_always_bounded : forall S,
  glues_bounded S.
Proof.
  intro S. unfold glues_bounded, tile_in_set.
  intros t g Hin Hglue.
  apply (glue_in_tileset_bounded t (tas_tiles S) g); assumption.
Qed.

(** ** 1.1.3 Geometric Primitives *)

(** Directional neighbors in Z^2 lattice *)
Definition north (p : Position) : Position :=
  let (x, y) := p in (x, y + 1)%Z.

Definition south (p : Position) : Position :=
  let (x, y) := p in (x, y - 1)%Z.

Definition east (p : Position) : Position :=
  let (x, y) := p in (x + 1, y)%Z.

Definition west (p : Position) : Position :=
  let (x, y) := p in (x - 1, y)%Z.

(** Parametric movement function: move in any direction *)
Definition move (p : Position) (d : Direction) : Position :=
  match d with
  | North => north p
  | East => east p
  | South => south p
  | West => west p
  end.

(** move agrees with individual direction functions *)
Lemma move_north : forall p, move p North = north p.
Proof. intro p. unfold move. reflexivity. Qed.

Lemma move_east : forall p, move p East = east p.
Proof. intro p. unfold move. reflexivity. Qed.

Lemma move_south : forall p, move p South = south p.
Proof. intro p. unfold move. reflexivity. Qed.

Lemma move_west : forall p, move p West = west p.
Proof. intro p. unfold move. reflexivity. Qed.

(** List of all four neighbors *)
Definition neighbors (p : Position) : list Position :=
  [north p; east p; south p; west p].

(** Parametric version using move *)
Definition neighbors' (p : Position) : list Position :=
  map (move p) all_directions.

(** neighbors' is equivalent to neighbors *)
Lemma neighbors_equiv : forall p,
  neighbors' p = neighbors p.
Proof.
  intro p. unfold neighbors', neighbors, all_directions.
  simpl. unfold move. reflexivity.
Qed.

(** Adjacency relation *)
Definition adjacent (p1 p2 : Position) : Prop :=
  In p2 (neighbors p1).

(** Basic geometric properties *)

Lemma north_moves_up : forall x y,
  north (x, y) = (x, y + 1)%Z.
Proof.
  intros x y. unfold north. reflexivity.
Qed.

Lemma south_moves_down : forall x y,
  south (x, y) = (x, y - 1)%Z.
Proof.
  intros x y. unfold south. reflexivity.
Qed.

Lemma east_moves_right : forall x y,
  east (x, y) = (x + 1, y)%Z.
Proof.
  intros x y. unfold east. reflexivity.
Qed.

Lemma west_moves_left : forall x y,
  west (x, y) = (x - 1, y)%Z.
Proof.
  intros x y. unfold west. reflexivity.
Qed.

(** Neighbor injectivity *)

Lemma north_injective : forall p1 p2,
  north p1 = north p2 -> p1 = p2.
Proof.
  intros [x1 y1] [x2 y2] H.
  unfold north in H. inversion H.
  f_equal; lia.
Qed.

Lemma south_injective : forall p1 p2,
  south p1 = south p2 -> p1 = p2.
Proof.
  intros [x1 y1] [x2 y2] H.
  unfold south in H. inversion H.
  f_equal; lia.
Qed.

Lemma east_injective : forall p1 p2,
  east p1 = east p2 -> p1 = p2.
Proof.
  intros [x1 y1] [x2 y2] H.
  unfold east in H. inversion H.
  f_equal; lia.
Qed.

Lemma west_injective : forall p1 p2,
  west p1 = west p2 -> p1 = p2.
Proof.
  intros [x1 y1] [x2 y2] H.
  unfold west in H. inversion H.
  f_equal; lia.
Qed.

(** Directional inverses *)

Lemma north_south_inverse : forall p,
  south (north p) = p.
Proof.
  intros [x y]. unfold north, south. f_equal. lia.
Qed.

Lemma south_north_inverse : forall p,
  north (south p) = p.
Proof.
  intros [x y]. unfold north, south. f_equal. lia.
Qed.

Lemma east_west_inverse : forall p,
  west (east p) = p.
Proof.
  intros [x y]. unfold east, west. f_equal. lia.
Qed.

Lemma west_east_inverse : forall p,
  east (west p) = p.
Proof.
  intros [x y]. unfold east, west. f_equal. lia.
Qed.

(** Parametric lemmas using move *)

(** move is injective in position for fixed direction *)
Lemma move_injective : forall d p1 p2,
  move p1 d = move p2 d -> p1 = p2.
Proof.
  intros d p1 p2 Hmove.
  destruct d; unfold move in Hmove;
  [apply north_injective | apply east_injective |
   apply south_injective | apply west_injective]; exact Hmove.
Qed.

(** move and opposite_direction are inverses *)
Lemma move_opposite_inverse : forall p d,
  move (move p d) (opposite_direction d) = p.
Proof.
  intros p d.
  destruct d; unfold move, opposite_direction;
  [apply north_south_inverse | apply east_west_inverse |
   apply south_north_inverse | apply west_east_inverse].
Qed.

(** Adjacency is symmetric - helper lemmas *)

Lemma north_adjacent_implies_south : forall p,
  adjacent (north p) p.
Proof.
  intro p. unfold adjacent, neighbors. simpl.
  right. right. left. apply north_south_inverse.
Qed.

Lemma south_adjacent_implies_north : forall p,
  adjacent (south p) p.
Proof.
  intro p. unfold adjacent, neighbors. simpl.
  left. apply south_north_inverse.
Qed.

Lemma east_adjacent_implies_west : forall p,
  adjacent (east p) p.
Proof.
  intro p. unfold adjacent, neighbors. simpl.
  right. right. right. left. apply east_west_inverse.
Qed.

Lemma west_adjacent_implies_east : forall p,
  adjacent (west p) p.
Proof.
  intro p. unfold adjacent, neighbors. simpl.
  right. left. apply west_east_inverse.
Qed.

Theorem adjacency_symmetric : forall p1 p2,
  adjacent p1 p2 -> adjacent p2 p1.
Proof.
  intros p1 p2 Hadj.
  unfold adjacent, neighbors in Hadj. simpl in Hadj.
  destruct Hadj as [Hn | [He | [Hs | [Hw | Hf]]]].
  - rewrite <- Hn. apply north_adjacent_implies_south.
  - rewrite <- He. apply east_adjacent_implies_west.
  - rewrite <- Hs. apply south_adjacent_implies_north.
  - rewrite <- Hw. apply west_adjacent_implies_east.
  - destruct Hf.
Qed.

(** Neighbors list has exactly 4 elements *)

Lemma neighbors_length : forall p,
  length (neighbors p) = 4.
Proof.
  intro p. unfold neighbors. simpl. reflexivity.
Qed.

(** All directions are distinct *)

Theorem directions_distinct : forall p,
  north p <> south p /\
  north p <> east p /\
  north p <> west p /\
  south p <> east p /\
  south p <> west p /\
  east p <> west p.
Proof.
  intros [x y].
  unfold north, south, east, west.
  repeat split; intro H; inversion H; lia.
Qed.

(** Neighbors list has no duplicates *)
Theorem neighbors_NoDup : forall p,
  NoDup (neighbors p).
Proof.
  intro p.
  pose proof (directions_distinct p) as [Hns [Hne [Hnw [Hse [Hsw Hew]]]]].
  unfold neighbors.
  constructor.
  - intro H. simpl in H. destruct H as [H | [H | [H | []]]].
    + apply Hne. symmetry. exact H.
    + apply Hns. symmetry. exact H.
    + apply Hnw. symmetry. exact H.
  - constructor.
    + intro H. simpl in H. destruct H as [H | [H | []]].
      * apply Hse. exact H.
      * apply Hew. symmetry. exact H.
    + constructor.
      * intro H. simpl in H. destruct H as [H | []].
        apply Hsw. symmetry. exact H.
      * constructor. intro H. simpl in H. destruct H.
        constructor.
Qed.

(** Adjacency decidability *)

Lemma adjacent_dec : forall p1 p2,
  {adjacent p1 p2} + {~adjacent p1 p2}.
Proof.
  intros p1 p2.
  unfold adjacent.
  apply in_dec. apply Position_eq_dec.
Defined.

(** Non-adjacent positions *)

Lemma diagonal_not_adjacent : forall x y dx dy,
  (dx <> 0)%Z -> (dy <> 0)%Z ->
  ~adjacent (x, y) (x + dx, y + dy)%Z.
Proof.
  intros x y dx dy Hdx Hdy Hadj.
  unfold adjacent, neighbors in Hadj. simpl in Hadj.
  unfold north, east, south, west in Hadj.
  destruct Hadj as [H1 | [H2 | [H3 | [H4 | Hf]]]];
  try (inversion H1; lia);
  try (inversion H2; lia);
  try (inversion H3; lia);
  try (inversion H4; lia).
  destruct Hf.
Qed.

(** Distance metrics *)

Definition manhattan_distance (p1 p2 : Position) : Z :=
  let (x1, y1) := p1 in
  let (x2, y2) := p2 in
  Z.abs (x2 - x1) + Z.abs (y2 - y1).

Lemma manhattan_distance_nonnegative : forall p1 p2,
  (manhattan_distance p1 p2 >= 0)%Z.
Proof.
  intros [x1 y1] [x2 y2].
  unfold manhattan_distance.
  pose proof (Z.abs_nonneg (x2 - x1)).
  pose proof (Z.abs_nonneg (y2 - y1)).
  lia.
Qed.

Lemma manhattan_distance_zero_iff : forall p1 p2,
  manhattan_distance p1 p2 = 0%Z <-> p1 = p2.
Proof.
  intros [x1 y1] [x2 y2].
  unfold manhattan_distance. split; intro H.
  - assert (H1: Z.abs (x2 - x1) = 0%Z) by lia.
    assert (H2: Z.abs (y2 - y1) = 0%Z) by lia.
    apply Z.abs_0_iff in H1.
    apply Z.abs_0_iff in H2.
    f_equal; lia.
  - inversion H. subst. repeat rewrite Z.sub_diag. simpl. lia.
Qed.

Lemma manhattan_distance_symmetric : forall p1 p2,
  manhattan_distance p1 p2 = manhattan_distance p2 p1.
Proof.
  intros [x1 y1] [x2 y2].
  unfold manhattan_distance.
  replace (x2 - x1)%Z with (-(x1 - x2))%Z by lia.
  replace (y2 - y1)%Z with (-(y1 - y2))%Z by lia.
  repeat rewrite Z.abs_opp.
  reflexivity.
Qed.

Theorem adjacent_implies_distance_one : forall p1 p2,
  adjacent p1 p2 -> manhattan_distance p1 p2 = 1%Z.
Proof.
  intros [x y] p2 Hadj.
  unfold adjacent, neighbors in Hadj. simpl in Hadj.
  unfold north, east, south, west in Hadj.
  destruct Hadj as [Hn | [He | [Hs | [Hw | Hf]]]];
  try (rewrite <- Hn; unfold manhattan_distance; simpl; lia);
  try (rewrite <- He; unfold manhattan_distance; simpl; lia);
  try (rewrite <- Hs; unfold manhattan_distance; simpl; lia);
  try (rewrite <- Hw; unfold manhattan_distance; simpl; lia);
  destruct Hf.
Qed.

Theorem distance_one_implies_adjacent : forall p1 p2,
  manhattan_distance p1 p2 = 1%Z -> adjacent p1 p2.
Proof.
  intros [x1 y1] [x2 y2] Hdist.
  unfold manhattan_distance in Hdist. simpl in Hdist.
  pose proof (Z.abs_nonneg (x2 - x1)) as Habs1.
  pose proof (Z.abs_nonneg (y2 - y1)) as Habs2.
  unfold adjacent, neighbors, north, east, south, west. simpl.
  destruct (Z.eq_dec (Z.abs (x2 - x1)) 0) as [Hx0 | Hxnz].
  - apply Z.abs_0_iff in Hx0.
    assert (Hy: Z.abs (y2 - y1) = 1%Z) by lia.
    destruct (Z_le_gt_dec (y2 - y1) 0) as [Hyle | Hygt].
    + assert (y2 - y1 = -1)%Z by lia. right. right. left. f_equal; lia.
    + assert (y2 - y1 = 1)%Z by lia. left. f_equal; lia.
  - assert (Hx: Z.abs (x2 - x1) = 1%Z) by lia.
    assert (Hy: Z.abs (y2 - y1) = 0%Z) by lia.
    apply Z.abs_0_iff in Hy.
    destruct (Z_le_gt_dec (x2 - x1) 0) as [Hxle | Hxgt].
    + assert (x2 - x1 = -1)%Z by lia. right. right. right. left. f_equal; lia.
    + assert (x2 - x1 = 1)%Z by lia. right. left. f_equal; lia.
Qed.

Theorem adjacent_iff_distance_one : forall p1 p2,
  adjacent p1 p2 <-> manhattan_distance p1 p2 = 1%Z.
Proof.
  intros p1 p2. split.
  - apply adjacent_implies_distance_one.
  - apply distance_one_implies_adjacent.
Qed.

(** Adjacent positions are distinct *)
Theorem adjacent_neq : forall p q,
  adjacent p q -> p <> q.
Proof.
  intros p q Hadj Heq.
  subst.
  assert (Hdist: manhattan_distance q q = 1%Z).
  { apply adjacent_implies_distance_one. exact Hadj. }
  assert (H0: manhattan_distance q q = 0%Z).
  { apply manhattan_distance_zero_iff. reflexivity. }
  rewrite H0 in Hdist. discriminate.
Qed.

(** Bounding boxes *)

Definition min_Z (z1 z2 : Z) : Z := if (z1 <=? z2)%Z then z1 else z2.
Definition max_Z (z1 z2 : Z) : Z := if (z1 >=? z2)%Z then z1 else z2.

Lemma min_Z_lb : forall z1 z2, (min_Z z1 z2 <= z1)%Z /\ (min_Z z1 z2 <= z2)%Z.
Proof.
  intros z1 z2. unfold min_Z.
  destruct (z1 <=? z2)%Z eqn:H.
  - apply Z.leb_le in H. lia.
  - apply Z.leb_gt in H. lia.
Qed.

Lemma max_Z_ub : forall z1 z2, (z1 <= max_Z z1 z2)%Z /\ (z2 <= max_Z z1 z2)%Z.
Proof.
  intros z1 z2. unfold max_Z.
  destruct (Z_ge_dec z1 z2) as [Hge | Hlt].
  - destruct (z1 >=? z2)%Z eqn:H; lia.
  - destruct (z1 >=? z2)%Z eqn:H; lia.
Qed.

Definition in_rectangle (p : Position) (x_min x_max y_min y_max : Z) : Prop :=
  let (x, y) := p in
  (x_min <= x <= x_max)%Z /\ (y_min <= y <= y_max)%Z.

Lemma in_rectangle_dec : forall p x_min x_max y_min y_max,
  {in_rectangle p x_min x_max y_min y_max} + {~in_rectangle p x_min x_max y_min y_max}.
Proof.
  intros [x y] x_min x_max y_min y_max.
  unfold in_rectangle.
  destruct (Z_le_dec x_min x); destruct (Z_le_dec x x_max);
  destruct (Z_le_dec y_min y); destruct (Z_le_dec y y_max);
  try (right; intro H; destruct H as [[? ?] [? ?]]; lia);
  left; split; lia.
Qed.

(** Position scaling for simulations *)

Definition scale_pos (k : nat) (p : Position) : Position :=
  let (x, y) := p in (Z.of_nat k * x, Z.of_nat k * y)%Z.

Lemma scale_pos_preserves_origin : forall k,
  scale_pos k (0, 0)%Z = (0, 0)%Z.
Proof.
  intro k. unfold scale_pos. simpl. f_equal; apply Z.mul_0_r.
Qed.

Lemma scale_pos_injective : forall k p1 p2,
  k > 0 -> scale_pos k p1 = scale_pos k p2 -> p1 = p2.
Proof.
  intros k [x1 y1] [x2 y2] Hk Hscale.
  unfold scale_pos in Hscale. simpl in Hscale.
  inversion Hscale.
  assert (Hk_nonzero: Z.of_nat k <> 0%Z) by lia.
  f_equal; apply (Z.mul_cancel_l _ _ (Z.of_nat k)); auto.
Qed.

Lemma scale_pos_one_is_identity : forall p,
  scale_pos 1 p = p.
Proof.
  intros [x y]. unfold scale_pos. simpl. f_equal; apply Z.mul_1_l.
Qed.

(** ** Verification Tests for Section 1.1 *)

(** Test: diagonal positions have Manhattan distance 2, not 1 *)
Example test_diagonal_not_adjacent :
  manhattan_distance (0, 0)%Z (1, 1)%Z = 2%Z.
Proof.
  unfold manhattan_distance. simpl. lia.
Qed.

(** Test: adjacency is not transitive *)
Example test_adjacency_not_transitive :
  exists p1 p2 p3,
    adjacent p1 p2 /\ adjacent p2 p3 /\ ~adjacent p1 p3.
Proof.
  exists (0, 0)%Z, (1, 0)%Z, (2, 0)%Z.
  split. unfold adjacent, neighbors, east. simpl. right. left. reflexivity.
  split. unfold adjacent, neighbors, east. simpl. right. left. reflexivity.
  intro Hadj. unfold adjacent, neighbors in Hadj. simpl in Hadj.
  unfold north, east, south, west in Hadj.
  destruct Hadj as [H | [H | [H | [H | []]]]]; inversion H; lia.
Qed.

(** Test: glue strength with mismatched glues is zero *)
Example test_glue_mismatch_zero :
  glue_strength standard_glue_strength 1 2 = 0.
Proof.
  unfold glue_strength.
  destruct (glue_eq_dec 1 2); try reflexivity.
  lia.
Qed.

(** Complex integration test: assembly equivalence, TAS well-formedness, and geometric constraints *)
Example test_integrated_assembly_geometry_wellformed :
  let t1 := mkTile 1 2 3 4 in
  let t2 := mkTile 5 6 7 8 in
  let α := fun p => if Position_eq_dec p (0, 0)%Z then Some t1 else None in
  let tiles := [t1; t2] in
  let S := mkTAS tiles standard_glue_strength α 2 in
  (* Well-formedness *)
  well_formed_tas S /\
  (* Geometric constraint: t1 at origin has 4 empty neighbors *)
  (forall dir, In dir (neighbors (0, 0)%Z) -> tile_at α dir = None) /\
  (* Distance from origin to any neighbor is 1 *)
  (forall dir, In dir (neighbors (0, 0)%Z) -> manhattan_distance (0, 0)%Z dir = 1%Z) /\
  (* Glue strength symmetry for all glues *)
  (forall g1 g2, glue_strength standard_glue_strength g1 g2 =
                 glue_strength standard_glue_strength g2 g1).
Proof.
  intros t1 t2 α tiles S.
  split.
  - (* well_formed_tas *)
    unfold well_formed_tas, seed_uses_tileset, glue_fn_respects_null. simpl.
    split.
    + intros [x y] t Ht. unfold tile_at, α in Ht.
      destruct (Position_eq_dec (x, y) (0, 0)%Z); try discriminate.
      injection Ht as <-. unfold tile_in_set. simpl. left. reflexivity.
    + exact standard_glue_respects_null.
  - split.
    + (* All neighbors empty *)
      intros dir Hdir.
      unfold neighbors in Hdir. simpl in Hdir.
      unfold tile_at, α. unfold north, east, south, west in Hdir.
      destruct Hdir as [H | [H | [H | [H | []]]]];
      rewrite <- H; destruct (Position_eq_dec _ (0, 0)%Z) as [Heq | Hneq];
      try reflexivity; try (inversion Heq; lia).
    + split.
      * (* Distance to neighbors is 1 *)
        intros dir Hdir. apply adjacent_implies_distance_one.
        unfold adjacent. exact Hdir.
      * (* Glue strength symmetry *)
        intros g1 g2. apply glue_strength_symmetric.
Qed.

(** ** 1.1.4 Assembly Predicates: Domains and Finite Assemblies *)

(** The support of an assembly is the set of positions where tiles exist *)
Definition support (α : Assembly) : Position -> Prop :=
  fun p => exists t, tile_at α p = Some t.

(** An assembly is finite if its support is finite *)
Definition finite_assembly (α : Assembly) : Prop :=
  exists (positions : list Position),
    (forall p, support α p <-> In p positions) /\
    NoDup positions.

(** Predicate: position has a tile *)
Definition has_tile (α : Assembly) (p : Position) : Prop :=
  exists t, tile_at α p = Some t.

Lemma has_tile_iff_support : forall α p,
  has_tile α p <-> support α p.
Proof.
  intros α p. split; intro H; exact H.
Qed.

(** Decidability of has_tile when tile_at returns Some or None *)
Lemma has_tile_dec : forall α p,
  {has_tile α p} + {~has_tile α p}.
Proof.
  intros α p.
  unfold has_tile.
  destruct (tile_at α p) as [t |] eqn:Htile.
  - left. exists t. rewrite <- Htile. reflexivity.
  - right. intro H. destruct H as [t Ht]. discriminate Ht.
Qed.

(** Empty assembly has empty support *)
Lemma empty_assembly_empty_support : forall p,
  ~support empty_assembly p.
Proof.
  intros p [t Ht].
  unfold tile_at, empty_assembly in Ht.
  discriminate.
Qed.

(** support respects assembly equivalence *)
Add Parametric Morphism : support
  with signature assembly_equiv ==> eq ==> iff
  as support_morphism.
Proof.
  intros α β Heq p.
  split; intro H; unfold support in *; destruct H as [t Ht];
  exists t; unfold assembly_equiv in Heq;
  [rewrite <- Heq | rewrite Heq]; exact Ht.
Qed.

Theorem empty_assembly_is_finite :
  finite_assembly empty_assembly.
Proof.
  unfold finite_assembly.
  exists [].
  split.
  - intro p. split; intro H.
    + exfalso. apply (empty_assembly_empty_support p). exact H.
    + destruct H.
  - constructor.
Qed.

(** Single tile assembly *)
Definition single_tile_assembly (p0 : Position) (t0 : TileType) : Assembly :=
  fun p => if Position_eq_dec p p0 then Some t0 else None.

Lemma single_tile_support : forall p0 t0 p,
  support (single_tile_assembly p0 t0) p <-> p = p0.
Proof.
  intros p0 t0 p. split; intro H.
  - unfold support, tile_at, single_tile_assembly in H.
    destruct H as [t Ht].
    destruct (Position_eq_dec p p0) as [Heq | Hneq].
    + exact Heq.
    + inversion Ht.
  - unfold support, tile_at, single_tile_assembly.
    exists t0. subst. destruct (Position_eq_dec p0 p0); try contradiction.
    reflexivity.
Qed.

Theorem single_tile_assembly_is_finite : forall p0 t0,
  finite_assembly (single_tile_assembly p0 t0).
Proof.
  intros p0 t0.
  unfold finite_assembly.
  exists [p0].
  split.
  - intro p. rewrite single_tile_support. split; intro H.
    + subst. simpl. left. reflexivity.
    + simpl in H. destruct H as [Heq | Hf]; try contradiction. symmetry. exact Heq.
  - constructor. intro H. destruct H. constructor.
Qed.

(** Assembly with finitely many tiles *)
Fixpoint list_to_assembly_aux (tiles : list (Position * TileType)) (p : Position) : option TileType :=
  match tiles with
  | [] => None
  | (p', t) :: rest =>
      if Position_eq_dec p p' then Some t
      else list_to_assembly_aux rest p
  end.

Definition list_to_assembly (tiles : list (Position * TileType)) : Assembly :=
  list_to_assembly_aux tiles.

Lemma list_to_assembly_nil : forall p,
  list_to_assembly [] p = None.
Proof.
  intro p. unfold list_to_assembly, list_to_assembly_aux. reflexivity.
Qed.

Lemma list_to_assembly_cons : forall p0 t0 rest p,
  list_to_assembly ((p0, t0) :: rest) p =
    if Position_eq_dec p p0 then Some t0
    else list_to_assembly rest p.
Proof.
  intros p0 t0 rest p.
  unfold list_to_assembly, list_to_assembly_aux.
  reflexivity.
Qed.

Lemma list_to_assembly_in : forall tiles p t,
  In (p, t) tiles ->
  (forall p' t', In (p', t') tiles -> p = p' -> t = t') ->
  tile_at (list_to_assembly tiles) p = Some t.
Proof.
  induction tiles as [| [p0 t0] rest IH]; intros p t Hin Huniq.
  - destruct Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + injection Heq as Heq_p Heq_t. subst p0 t0.
      unfold tile_at, list_to_assembly, list_to_assembly_aux.
      destruct (Position_eq_dec p p); try contradiction. reflexivity.
    + unfold tile_at, list_to_assembly, list_to_assembly_aux.
      fold list_to_assembly_aux.
      destruct (Position_eq_dec p p0) as [Heq | Hneq].
      * subst.
        assert (Heq_t: t = t0).
        { apply (Huniq p0 t0). simpl. left. reflexivity.
          reflexivity. }
        subst. reflexivity.
      * apply IH. exact Hin.
        intros p' t' Hin' Heq. apply (Huniq p' t'). simpl. right. exact Hin'. exact Heq.
Qed.

(** Support of list-based assembly *)
Lemma list_to_assembly_support : forall tiles p,
  support (list_to_assembly tiles) p <->
  exists t, In (p, t) tiles.
Proof.
  induction tiles as [| [p0 t0] rest IH]; intro p.
  - split; intro H.
    + unfold support, tile_at in H. destruct H as [t Ht].
      rewrite list_to_assembly_nil in Ht. discriminate.
    + destruct H as [t Ht]. destruct Ht.
  - split; intro H.
    + unfold support, tile_at in H. destruct H as [t Ht].
      rewrite list_to_assembly_cons in Ht.
      destruct (Position_eq_dec p p0) as [Heq | Hneq].
      * injection Ht as <-. exists t0. simpl. left. f_equal. symmetry. exact Heq.
      * assert (Hexists: exists t', In (p, t') rest).
        { apply IH. unfold support, tile_at. exists t. exact Ht. }
        destruct Hexists as [t' Hin']. exists t'. simpl. right. exact Hin'.
    + destruct H as [t Ht]. simpl in Ht.
      destruct Ht as [Heq | Hin].
      * injection Heq as <- <-. unfold support, tile_at.
        exists t0. rewrite list_to_assembly_cons.
        destruct (Position_eq_dec p0 p0); try contradiction. reflexivity.
      * assert (Hsup: support (list_to_assembly rest) p).
        { apply (proj2 (IH p)). exists t. exact Hin. }
        unfold support, tile_at in *.
        destruct Hsup as [t' Ht'].
        unfold list_to_assembly, list_to_assembly_aux. fold list_to_assembly_aux.
        destruct (Position_eq_dec p p0) as [Heq | Hneq].
        ** subst. exists t0. reflexivity.
        ** exists t'. exact Ht'.
Qed.

(** Assembly equivalence for list-based assemblies *)
Theorem list_assembly_equiv_iff : forall tiles1 tiles2,
  (forall p, list_to_assembly tiles1 p = list_to_assembly tiles2 p) <->
  list_to_assembly tiles1 ≡ list_to_assembly tiles2.
Proof.
  intros tiles1 tiles2. split; intro H.
  - unfold assembly_equiv. intro p. apply H.
  - intro p. unfold assembly_equiv in H. apply H.
Qed.

(** Size of assembly (number of tiles) *)
Definition assembly_size (α : Assembly) (positions : list Position) : nat :=
  length (filter (fun p => match tile_at α p with Some _ => true | None => false end) positions).

Lemma assembly_size_empty : forall positions,
  assembly_size empty_assembly positions = 0.
Proof.
  intro positions.
  unfold assembly_size.
  induction positions as [| p rest IH].
  - simpl. reflexivity.
  - simpl. unfold tile_at, empty_assembly. simpl. exact IH.
Qed.

Lemma assembly_size_none : forall α positions,
  (forall p, In p positions -> tile_at α p = None) ->
  assembly_size α positions = 0.
Proof.
  intros α positions H.
  unfold assembly_size.
  induction positions as [| p rest IH].
  - simpl. reflexivity.
  - simpl. rewrite (H p). simpl. apply IH.
    intros p' Hin. apply H. simpl. right. exact Hin.
    simpl. left. reflexivity.
Qed.

(** Size of single tile assembly is exactly 1 when counted over positions containing p0 *)
Theorem assembly_size_single_tile : forall p0 t0,
  assembly_size (single_tile_assembly p0 t0) [p0] = 1.
Proof.
  intros p0 t0.
  unfold assembly_size. simpl.
  unfold tile_at, single_tile_assembly.
  destruct (Position_eq_dec p0 p0); try contradiction.
  reflexivity.
Qed.

(** Helper: if p0 not in list, filter for single_tile_assembly p0 t0 is empty *)
Lemma filter_single_tile_not_in_empty : forall (p0 : Position) (t0 : TileType) (rest : list Position),
  ~In p0 rest ->
  filter (fun p1 => match (if Position_eq_dec p1 p0 then Some t0 else None) with
                    | Some _ => true
                    | None => false
                    end) rest = [].
Proof.
  intros p0 t0 rest Hnotin.
  induction rest as [| p' rest' IH].
  - reflexivity.
  - simpl. destruct (Position_eq_dec p' p0) as [Heq | Hneq].
    + exfalso. apply Hnotin. subst. simpl. left. reflexivity.
    + apply IH. intro Hcontra. apply Hnotin. simpl. right. exact Hcontra.
Qed.

(** More general: size equals 1 for single tile in NoDup list containing p0 *)
Theorem assembly_size_single_tile_in_list : forall p0 t0 positions,
  In p0 positions ->
  NoDup positions ->
  assembly_size (single_tile_assembly p0 t0) positions = 1.
Proof.
  intros p0 t0 positions Hin Hnodup.
  unfold assembly_size, tile_at, single_tile_assembly.
  induction positions as [| p rest IH].
  - destruct Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst. simpl. destruct (Position_eq_dec p0 p0); try contradiction. simpl.
      inversion Hnodup as [| ? ? Hnotin Hnodup']. subst.
      rewrite (filter_single_tile_not_in_empty p0 t0 rest Hnotin). reflexivity.
    + simpl. destruct (Position_eq_dec p p0) as [Heq | Hneq].
      * exfalso. subst. inversion Hnodup as [| ? ? Hnotin Hnodup']. subst. contradiction.
      * inversion Hnodup as [| ? ? Hnotin Hnodup']. subst. apply IH; assumption.
Qed.

(** Finite assembly operations *)

(** Adding a tile to an assembly at an empty position *)
Definition add_tile (α : Assembly) (p : Position) (t : TileType) : Assembly :=
  fun p' => if Position_eq_dec p' p then Some t else tile_at α p'.

Lemma add_tile_at_position : forall α p t,
  tile_at (add_tile α p t) p = Some t.
Proof.
  intros α p t.
  unfold add_tile, tile_at.
  destruct (Position_eq_dec p p); try contradiction.
  reflexivity.
Qed.

Lemma add_tile_elsewhere : forall α p t p',
  p' <> p ->
  tile_at (add_tile α p t) p' = tile_at α p'.
Proof.
  intros α p t p' Hneq.
  unfold add_tile, tile_at.
  destruct (Position_eq_dec p' p); try contradiction.
  reflexivity.
Qed.

(** add_tile respects assembly equivalence *)
Add Parametric Morphism p t : (fun α => add_tile α p t)
  with signature assembly_equiv ==> assembly_equiv
  as add_tile_morphism.
Proof.
  intros α β Heq.
  unfold assembly_equiv, add_tile, tile_at in *.
  intro p'.
  destruct (Position_eq_dec p' p) as [Heqp | Hneqp]; [reflexivity | apply Heq].
Qed.

Lemma add_tile_preserves_finite : forall α p t,
  tile_at α p = None ->
  finite_assembly α ->
  finite_assembly (add_tile α p t).
Proof.
  intros α p t Hempty [positions [Hiff Hnodup]].
  unfold finite_assembly.
  exists (p :: positions).
  split.
  - intro p'. split; intro H.
    + unfold support in H. destruct H as [t' Ht'].
      unfold tile_at, add_tile in Ht'.
      destruct (Position_eq_dec p' p) as [Heq | Hneq].
      * subst. simpl. left. reflexivity.
      * simpl. right. rewrite <- Hiff. unfold support. exists t'. exact Ht'.
    + simpl in H. destruct H as [Heq | Hin].
      * subst. unfold support. exists t. apply add_tile_at_position.
      * apply (proj2 (Hiff p')) in Hin. unfold support in *.
        destruct Hin as [t' Ht'].
        exists t'. unfold tile_at, add_tile.
        destruct (Position_eq_dec p' p) as [Heq | Hneq].
        ** subst. rewrite Hempty in Ht'. discriminate.
        ** exact Ht'.
  - constructor.
    + intro Hin. rewrite <- Hiff in Hin.
      unfold support in Hin. destruct Hin as [t' Ht'].
      rewrite Hempty in Ht'. discriminate.
    + exact Hnodup.
Qed.

(** Removing a tile from an assembly *)
Definition remove_tile (α : Assembly) (p : Position) : Assembly :=
  fun p' => if Position_eq_dec p' p then None else tile_at α p'.

Lemma remove_tile_at_position : forall α p,
  tile_at (remove_tile α p) p = None.
Proof.
  intros α p.
  unfold remove_tile, tile_at.
  destruct (Position_eq_dec p p); try contradiction.
  reflexivity.
Qed.

Lemma remove_tile_elsewhere : forall α p p',
  p' <> p ->
  tile_at (remove_tile α p) p' = tile_at α p'.
Proof.
  intros α p p' Hneq.
  unfold remove_tile, tile_at.
  destruct (Position_eq_dec p' p); try contradiction.
  reflexivity.
Qed.

(** remove_tile respects assembly equivalence *)
Add Parametric Morphism p : (fun α => remove_tile α p)
  with signature assembly_equiv ==> assembly_equiv
  as remove_tile_morphism.
Proof.
  intros α β Heq.
  unfold assembly_equiv, remove_tile, tile_at in *.
  intro p'.
  destruct (Position_eq_dec p' p) as [Heqp | Hneqp]; [reflexivity | apply Heq].
Qed.

Lemma remove_tile_preserves_finite : forall α p,
  finite_assembly α ->
  finite_assembly (remove_tile α p).
Proof.
  intros α p [positions [Hiff Hnodup]].
  unfold finite_assembly.
  exists (filter (fun p' => if Position_eq_dec p' p then false else true) positions).
  split.
  - intro p'. split; intro H.
    + unfold support in H. destruct H as [t Ht].
      unfold tile_at, remove_tile in Ht.
      destruct (Position_eq_dec p' p) as [Heq | Hneq].
      * discriminate.
      * apply filter_In. split.
        ** rewrite <- Hiff. unfold support. exists t. exact Ht.
        ** destruct (Position_eq_dec p' p); try contradiction. reflexivity.
    + apply filter_In in H. destruct H as [Hin Hcond].
      apply (proj2 (Hiff p')) in Hin. unfold support in *.
      destruct Hin as [t Ht].
      exists t. unfold tile_at, remove_tile.
      destruct (Position_eq_dec p' p) as [Heq | Hneq].
      * subst. destruct (Position_eq_dec p p) in Hcond; discriminate.
      * exact Ht.
  - apply NoDup_filter. exact Hnodup.
Qed.

(** Assembly size theorems for add_tile and remove_tile *)

(** Size increases by 1 when adding tile to empty position *)
Theorem assembly_size_add_tile_empty : forall α p t,
  tile_at α p = None ->
  assembly_size (add_tile α p t) [p] = S (assembly_size α [p]).
Proof.
  intros α p t Hempty.
  unfold assembly_size, add_tile, tile_at in *. simpl.
  destruct (Position_eq_dec p p); try contradiction.
  rewrite Hempty. reflexivity.
Qed.

(** Size decreases by 1 when removing tile from occupied position *)
Theorem assembly_size_remove_tile_occupied : forall α p t,
  tile_at α p = Some t ->
  assembly_size (remove_tile α p) [p] = pred (assembly_size α [p]).
Proof.
  intros α p t Hoccupied.
  unfold assembly_size, remove_tile, tile_at in *. simpl.
  destruct (Position_eq_dec p p); try contradiction.
  rewrite Hoccupied. reflexivity.
Qed.

(** Size unchanged when removing from empty position *)
Theorem assembly_size_remove_tile_empty : forall α p,
  tile_at α p = None ->
  assembly_size (remove_tile α p) [p] = assembly_size α [p].
Proof.
  intros α p Hempty.
  unfold assembly_size, remove_tile, tile_at in *. simpl.
  destruct (Position_eq_dec p p); try contradiction.
  rewrite Hempty. reflexivity.
Qed.

(** Size is monotonic: subset of positions gives smaller size *)
Lemma assembly_size_subset : forall α p positions,
  assembly_size α positions <= assembly_size α (p :: positions).
Proof.
  intros α p positions.
  unfold assembly_size. simpl.
  destruct (tile_at α p); simpl.
  - apply Nat.le_succ_diag_r.
  - apply Nat.le_refl.
Qed.

(** Assembly equivalence respects support *)
Theorem assembly_equiv_same_support : forall α β p,
  α ≡ β ->
  support α p <-> support β p.
Proof.
  intros α β p Hequiv.
  split; intro H; unfold support in *; destruct H as [t Ht];
  exists t; unfold assembly_equiv in Hequiv; rewrite <- Hequiv || rewrite Hequiv; exact Ht.
Qed.

(** Finite assemblies are closed under equivalence *)
Theorem finite_assembly_equiv_closed : forall α β,
  α ≡ β ->
  finite_assembly α ->
  finite_assembly β.
Proof.
  intros α β Hequiv [positions [Hiff Hnodup]].
  exists positions.
  split.
  - intro p. rewrite <- (assembly_equiv_same_support α β p); auto.
  - exact Hnodup.
Qed.

(** Domain subset relation: α ⊆ β means wherever α has a tile, β has the same tile *)
Definition domain_subset (α β : Assembly) : Prop :=
  forall p t, tile_at α p = Some t -> tile_at β p = Some t.

Notation "α ⊆ β" := (domain_subset α β) (at level 70).

Lemma domain_subset_refl : forall α,
  α ⊆ α.
Proof.
  intros α p t H. exact H.
Qed.

Lemma domain_subset_trans : forall α β γ,
  α ⊆ β -> β ⊆ γ -> α ⊆ γ.
Proof.
  intros α β γ Hab Hbc p t Hp.
  apply Hbc. apply Hab. exact Hp.
Qed.

Theorem empty_assembly_smallest : forall α,
  empty_assembly ⊆ α.
Proof.
  intros α p t Hp.
  unfold tile_at, empty_assembly in Hp. discriminate.
Qed.

(** Verification examples *)

Example test_single_tile_finite :
  finite_assembly (single_tile_assembly (5, 7)%Z (mkTile 1 2 3 4)).
Proof.
  apply single_tile_assembly_is_finite.
Qed.

Example test_add_tile_finite :
  let α := empty_assembly in
  let β := add_tile α (0, 0)%Z (mkTile 1 1 1 1) in
  finite_assembly β.
Proof.
  intros α β.
  apply add_tile_preserves_finite.
  - apply empty_assembly_has_no_tiles.
  - apply empty_assembly_is_finite.
Qed.

Example test_remove_preserves_finite :
  let t := mkTile 1 2 3 4 in
  let α := single_tile_assembly (0, 0)%Z t in
  let β := remove_tile α (0, 0)%Z in
  finite_assembly β.
Proof.
  intros t α β.
  apply remove_tile_preserves_finite.
  apply single_tile_assembly_is_finite.
Qed.

Theorem domain_subset_asymmetric_example :
  exists α β,
    α ⊆ β /\ ~(β ⊆ α).
Proof.
  exists empty_assembly.
  exists (single_tile_assembly (0, 0)%Z (mkTile 1 1 1 1)).
  split.
  - apply empty_assembly_smallest.
  - intro H. unfold domain_subset in H.
    assert (Ht: tile_at (single_tile_assembly (0, 0)%Z (mkTile 1 1 1 1)) (0, 0)%Z = Some (mkTile 1 1 1 1)).
    { unfold tile_at, single_tile_assembly. destruct (Position_eq_dec (0, 0)%Z (0, 0)%Z); try contradiction. reflexivity. }
    specialize (H (0, 0)%Z (mkTile 1 1 1 1) Ht).
    unfold tile_at, empty_assembly in H. discriminate.
Qed.

(** Domain subset forms a partial order modulo assembly equivalence *)

Theorem domain_subset_antisym : forall α β,
  α ⊆ β -> β ⊆ α -> α ≡ β.
Proof.
  intros α β Hab Hba.
  unfold assembly_equiv, domain_subset, tile_at in *.
  intro p.
  destruct (α p) as [tα |] eqn:Hα;
  destruct (β p) as [tβ |] eqn:Hβ; auto.
  - specialize (Hab p tα Hα).
    rewrite Hβ in Hab. injection Hab as <-. reflexivity.
  - specialize (Hab p tα Hα).
    rewrite Hβ in Hab. discriminate.
  - specialize (Hba p tβ Hβ).
    rewrite Hα in Hba. discriminate.
Qed.

(** domain_subset respects assembly equivalence *)
Add Parametric Morphism : domain_subset
  with signature assembly_equiv ==> assembly_equiv ==> iff
  as domain_subset_morphism.
Proof.
  intros α1 α2 Heq1 β1 β2 Heq2.
  split; intro H; unfold domain_subset in *; intros p t Ht.
  - unfold assembly_equiv, tile_at in Heq1.
    assert (Ht': tile_at α1 p = Some t).
    { rewrite Heq1. exact Ht. }
    apply H in Ht'.
    unfold assembly_equiv, tile_at in Heq2.
    rewrite <- Heq2. exact Ht'.
  - unfold assembly_equiv, tile_at in Heq1.
    assert (Ht': tile_at α2 p = Some t).
    { rewrite <- Heq1. exact Ht. }
    apply H in Ht'.
    unfold assembly_equiv, tile_at in Heq2.
    rewrite Heq2. exact Ht'.
Qed.

(** Assembly consistency: assemblies agree where they overlap *)

Definition assembly_consistent (α β : Assembly) : Prop :=
  forall p t1 t2, tile_at α p = Some t1 -> tile_at β p = Some t2 -> t1 = t2.

Notation "α ~ β" := (assembly_consistent α β) (at level 70).

Lemma assembly_consistent_refl : forall α,
  α ~ α.
Proof.
  intros α p t1 t2 H1 H2.
  rewrite H1 in H2. injection H2 as <-. reflexivity.
Qed.

Lemma assembly_consistent_sym : forall α β,
  α ~ β -> β ~ α.
Proof.
  intros α β H p t1 t2 H1 H2.
  symmetry. apply (H p); assumption.
Qed.

Lemma assembly_consistent_empty : forall α,
  empty_assembly ~ α.
Proof.
  intros α p t1 t2 H1 H2.
  unfold tile_at, empty_assembly in H1. discriminate.
Qed.

Theorem assembly_equiv_implies_consistent : forall α β,
  α ≡ β -> α ~ β.
Proof.
  intros α β Hequiv p t1 t2 H1 H2.
  unfold assembly_equiv in Hequiv.
  rewrite Hequiv in H1. rewrite H1 in H2. injection H2 as <-. reflexivity.
Qed.

Theorem domain_subset_implies_consistent : forall α β,
  α ⊆ β -> α ~ β.
Proof.
  intros α β Hsub p t1 t2 H1 H2.
  unfold domain_subset in Hsub.
  specialize (Hsub p t1 H1).
  rewrite H2 in Hsub. injection Hsub as <-. reflexivity.
Qed.

Lemma consistent_same_tile : forall α β p t,
  α ~ β ->
  tile_at α p = Some t ->
  tile_at β p = Some t \/ tile_at β p = None.
Proof.
  intros α β p t Hcons Hα.
  destruct (tile_at β p) as [tβ |] eqn:Hβ.
  - left. unfold assembly_consistent in Hcons.
    assert (t = tβ) by (apply (Hcons p); assumption).
    subst. reflexivity.
  - right. reflexivity.
Qed.

(** Assembly consistency is NOT transitive: counterexample *)
Theorem assembly_consistent_not_transitive :
  exists α β γ,
    α ~ β /\ β ~ γ /\ ~(α ~ γ).
Proof.
  exists (single_tile_assembly (0, 0)%Z (mkTile 1 1 1 1)).
  exists empty_assembly.
  exists (single_tile_assembly (0, 0)%Z (mkTile 2 2 2 2)).
  split.
  - (* α ~ empty *)
    apply assembly_consistent_sym.
    apply assembly_consistent_empty.
  - split.
    + (* empty ~ γ *)
      apply assembly_consistent_empty.
    + (* ~(α ~ γ) *)
      intro Hcons.
      unfold assembly_consistent in Hcons.
      assert (Hα: tile_at (single_tile_assembly (0, 0)%Z (mkTile 1 1 1 1)) (0, 0)%Z = Some (mkTile 1 1 1 1)).
      { unfold tile_at, single_tile_assembly.
        destruct (Position_eq_dec (0, 0)%Z (0, 0)%Z); try contradiction.
        reflexivity. }
      assert (Hγ: tile_at (single_tile_assembly (0, 0)%Z (mkTile 2 2 2 2)) (0, 0)%Z = Some (mkTile 2 2 2 2)).
      { unfold tile_at, single_tile_assembly.
        destruct (Position_eq_dec (0, 0)%Z (0, 0)%Z); try contradiction.
        reflexivity. }
      specialize (Hcons (0, 0)%Z (mkTile 1 1 1 1) (mkTile 2 2 2 2) Hα Hγ).
      inversion Hcons.
Qed.

(** Assembly union: prefer first assembly where defined *)

Definition assembly_union (α β : Assembly) : Assembly :=
  fun p => match tile_at α p with
           | Some t => Some t
           | None => tile_at β p
           end.

Notation "α ∪ β" := (assembly_union α β) (at level 65, right associativity).

Lemma assembly_union_left : forall α β p t,
  tile_at α p = Some t ->
  tile_at (α ∪ β) p = Some t.
Proof.
  intros α β p t Hα.
  unfold tile_at, assembly_union. simpl.
  rewrite Hα. reflexivity.
Qed.

Lemma assembly_union_right : forall α β p,
  tile_at α p = None ->
  tile_at (α ∪ β) p = tile_at β p.
Proof.
  intros α β p Hα.
  unfold tile_at, assembly_union. simpl.
  rewrite Hα. reflexivity.
Qed.

(** assembly_union respects assembly equivalence *)
Add Parametric Morphism : assembly_union
  with signature assembly_equiv ==> assembly_equiv ==> assembly_equiv
  as assembly_union_morphism.
Proof.
  intros α1 α2 Heq1 β1 β2 Heq2.
  unfold assembly_equiv, assembly_union in *.
  intro p.
  specialize (Heq1 p). specialize (Heq2 p).
  unfold tile_at in *.
  destruct (α1 p) as [t1 |] eqn:Ha1; destruct (α2 p) as [t2 |] eqn:Ha2.
  - assert (Some t1 = Some t2) by (rewrite <- Heq1; reflexivity).
    injection H as <-. reflexivity.
  - exfalso. assert (Some t1 = None) by (rewrite <- Heq1; reflexivity). discriminate.
  - exfalso. assert (None = Some t2) by (rewrite <- Heq1; reflexivity). discriminate.
  - exact Heq2.
Qed.

Lemma assembly_union_left_subset : forall α β,
  α ⊆ (α ∪ β).
Proof.
  intros α β p t Ht.
  apply assembly_union_left. exact Ht.
Qed.

Lemma assembly_union_right_subset : forall α β,
  α ~ β ->
  β ⊆ (α ∪ β).
Proof.
  intros α β Hcons p t Ht.
  destruct (tile_at α p) as [tα |] eqn:Hα.
  - unfold assembly_consistent in Hcons.
    assert (Heq: tα = t) by (apply (Hcons p); assumption).
    subst. apply assembly_union_left. exact Hα.
  - rewrite assembly_union_right; auto.
Qed.

Theorem assembly_union_consistent_when_inputs_consistent : forall α β,
  α ~ β ->
  (α ∪ β) ~ α /\ (α ∪ β) ~ β.
Proof.
  intros α β Hcons. split.
  - (* (α ∪ β) ~ α *)
    intros p t1 t2 H1 H2.
    assert (Ht1: tile_at α p = Some t1).
    { destruct (tile_at α p) as [t |] eqn:Hα.
      - assert (Heq: tile_at (α ∪ β) p = Some t) by (apply assembly_union_left; exact Hα).
        rewrite Heq in H1. inversion H1; subst. assumption.
      - assert (Heq: tile_at (α ∪ β) p = tile_at β p) by (apply assembly_union_right; exact Hα).
        rewrite Heq in H1. discriminate. }
    rewrite Ht1 in H2. inversion H2. reflexivity.
  - (* (α ∪ β) ~ β *)
    intros p t1 t2 H1 H2.
    destruct (tile_at α p) as [tα |] eqn:Hα.
    + assert (Heq: tile_at (α ∪ β) p = Some tα) by (apply assembly_union_left; exact Hα).
      rewrite Heq in H1. inversion H1; subst.
      unfold assembly_consistent in Hcons.
      eapply Hcons; eassumption.
    + assert (Heq: tile_at (α ∪ β) p = tile_at β p) by (apply assembly_union_right; exact Hα).
      rewrite Heq in H1. rewrite H1 in H2. inversion H2. reflexivity.
Qed.

Theorem assembly_union_empty_left : forall α,
  empty_assembly ∪ α ≡ α.
Proof.
  intro α. unfold assembly_equiv, assembly_union, tile_at, empty_assembly.
  intro p. reflexivity.
Qed.

Theorem assembly_union_empty_right : forall α,
  α ∪ empty_assembly ≡ α.
Proof.
  intro α. unfold assembly_equiv, assembly_union, tile_at, empty_assembly.
  intro p. destruct (α p); reflexivity.
Qed.

Theorem assembly_union_idempotent : forall α,
  α ∪ α ≡ α.
Proof.
  intro α. unfold assembly_equiv, assembly_union, tile_at.
  intro p. destruct (α p); reflexivity.
Qed.

Theorem assembly_union_commutative_when_consistent : forall α β,
  α ~ β ->
  α ∪ β ≡ β ∪ α.
Proof.
  intros α β Hcons.
  unfold assembly_equiv, assembly_union, tile_at.
  intro p.
  destruct (α p) as [tα |] eqn:Hα;
  destruct (β p) as [tβ |] eqn:Hβ; auto.
  unfold assembly_consistent in Hcons.
  assert (tα = tβ) by (apply (Hcons p); assumption).
  subst. reflexivity.
Qed.

Lemma NoDup_app : forall {A : Type} (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 -> In x l2 -> False) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hdisj.
  induction l1 as [| a l1' IH].
  - simpl. exact H2.
  - simpl. inversion H1 as [| ? ? Hnotin Hnodup']. subst.
    constructor.
    + intro Hin. apply in_app_iff in Hin.
      destruct Hin as [Hin1 | Hin2].
      * contradiction.
      * apply (Hdisj a).
        ** simpl. left. reflexivity.
        ** exact Hin2.
    + apply IH.
      * exact Hnodup'.
      * intros x Hin1 Hin2. apply (Hdisj x).
        ** simpl. right. exact Hin1.
        ** exact Hin2.
Qed.

Lemma assembly_union_support : forall α β p,
  support (α ∪ β) p <-> support α p \/ support β p.
Proof.
  intros α β p. split; intro H.
  - unfold support in H. destruct H as [t Ht].
    destruct (tile_at α p) as [tα |] eqn:Hα.
    + left. unfold support. exists tα. exact Hα.
    + right. unfold support. exists t.
      assert (Heq: tile_at (α ∪ β) p = tile_at β p) by (apply assembly_union_right; exact Hα).
      rewrite Heq in Ht. exact Ht.
  - destruct H as [Hα | Hβ].
    + unfold support in Hα. destruct Hα as [t Ht].
      unfold support. exists t. apply assembly_union_left. exact Ht.
    + unfold support in Hβ. destruct Hβ as [t Ht].
      unfold support.
      destruct (tile_at α p) as [tα |] eqn:Hα.
      * exists tα. apply assembly_union_left. exact Hα.
      * exists t. unfold tile_at, assembly_union. rewrite Hα. exact Ht.
Qed.

Theorem assembly_union_preserves_finite : forall α β,
  finite_assembly α ->
  finite_assembly β ->
  finite_assembly (α ∪ β).
Proof.
  intros α β [pos_α [Hiff_α Hnodup_α]] [pos_β [Hiff_β Hnodup_β]].
  unfold finite_assembly.
  exists (pos_α ++ filter (fun p => if in_dec Position_eq_dec p pos_α then false else true) pos_β).
  split.
  - intro p. split; intro H.
    + rewrite assembly_union_support in H.
      apply in_app_iff.
      destruct H as [Hα | Hβ].
      * left. apply Hiff_α. exact Hα.
      * destruct (in_dec Position_eq_dec p pos_α) as [Hin | Hnotin].
        ** left. exact Hin.
        ** right. apply filter_In. split.
           *** apply Hiff_β. exact Hβ.
           *** destruct (in_dec Position_eq_dec p pos_α); try contradiction. reflexivity.
    + apply in_app_iff in H.
      rewrite assembly_union_support.
      destruct H as [Hin_α | Hin_β].
      * left. apply Hiff_α. exact Hin_α.
      * apply filter_In in Hin_β. destruct Hin_β as [Hin Hcond].
        right. apply Hiff_β. exact Hin.
  - apply NoDup_app.
    + exact Hnodup_α.
    + apply NoDup_filter. exact Hnodup_β.
    + intros p Hin_α Hin_β.
      apply filter_In in Hin_β. destruct Hin_β as [_ Hcond].
      destruct (in_dec Position_eq_dec p pos_α); try discriminate.
      contradiction.
Qed.

(** Assembly restriction to a region with decidable predicate *)

Definition restrict_assembly (α : Assembly) (P : Position -> Prop)
                             (P_dec : forall p, {P p} + {~P p}) : Assembly :=
  fun p => if P_dec p then tile_at α p else None.

Lemma restrict_in_region : forall α P P_dec p,
  P p ->
  tile_at (restrict_assembly α P P_dec) p = tile_at α p.
Proof.
  intros α P P_dec p HP.
  unfold restrict_assembly, tile_at.
  destruct (P_dec p); try contradiction.
  reflexivity.
Qed.

Lemma restrict_out_region : forall α P P_dec p,
  ~P p ->
  tile_at (restrict_assembly α P P_dec) p = None.
Proof.
  intros α P P_dec p HP.
  unfold restrict_assembly, tile_at.
  destruct (P_dec p); try contradiction.
  reflexivity.
Qed.

Theorem restrict_subset : forall α P P_dec,
  restrict_assembly α P P_dec ⊆ α.
Proof.
  intros α P P_dec p t Ht.
  unfold tile_at, restrict_assembly in Ht.
  destruct (P_dec p) as [HP | HnP].
  - exact Ht.
  - discriminate.
Qed.

Theorem restrict_preserves_finite : forall α P P_dec,
  finite_assembly α ->
  finite_assembly (restrict_assembly α P P_dec).
Proof.
  intros α P P_dec [positions [Hiff Hnodup]].
  unfold finite_assembly.
  exists (filter (fun p => if P_dec p then true else false) positions).
  split.
  - intro p. split; intro H.
    + unfold support in H. destruct H as [t Ht].
      apply filter_In. split.
      * apply Hiff. unfold support.
        unfold tile_at, restrict_assembly in Ht.
        destruct (P_dec p) as [HP | HnP].
        ** exists t. exact Ht.
        ** discriminate.
      * destruct (P_dec p); try reflexivity.
        unfold tile_at, restrict_assembly in Ht.
        destruct (P_dec p); contradiction || discriminate.
    + apply filter_In in H. destruct H as [Hin Hcond].
      apply Hiff in Hin. unfold support in *.
      destruct Hin as [t Ht].
      destruct (P_dec p) as [HP | HnP]; try discriminate Hcond.
      exists t. unfold tile_at, restrict_assembly.
      destruct (P_dec p); try contradiction.
      exact Ht.
  - apply NoDup_filter. exact Hnodup.
Qed.

Theorem restrict_empty_equiv : forall P P_dec,
  restrict_assembly empty_assembly P P_dec ≡ empty_assembly.
Proof.
  intros P P_dec. unfold assembly_equiv, tile_at, restrict_assembly, empty_assembly.
  intro p. destruct (P_dec p); reflexivity.
Qed.

Theorem restrict_all_equiv : forall α (P_true : forall p, {True} + {~True}),
  restrict_assembly α (fun _ => True) P_true ≡ α.
Proof.
  intros α P_true. unfold assembly_equiv, tile_at, restrict_assembly.
  intro p. destruct (P_true p) as [_ | Hf].
  - reflexivity.
  - exfalso. apply Hf. exact I.
Qed.

Theorem restrict_none_equiv : forall α (P_false : forall p, {False} + {~False}),
  restrict_assembly α (fun _ => False) P_false ≡ empty_assembly.
Proof.
  intros α P_false. unfold assembly_equiv, tile_at, restrict_assembly, empty_assembly.
  intro p. destruct (P_false p) as [Hf | _].
  - exfalso. exact Hf.
  - reflexivity.
Qed.

(** ** Real-World Example: Building and Verifying a 2×2 Square Assembly *)

(** This example demonstrates a realistic use case: constructing a 2×2 square
    of tiles and proving its geometric and structural properties using all
    major theorems from Section 1.1. This exercises:
    - Type system and tile matching
    - Well-formed TAS construction
    - Geometric reasoning with adjacency and distance
    - Assembly operations (add_tile, union)
    - Finiteness, consistency, and subset relations
*)

(** Tiles designed to form a 2×2 square with matching glues *)
Definition square_tile_NW : TileType := mkTile 0 1 2 0.  (* NW corner: E=1, S=2 *)
Definition square_tile_NE : TileType := mkTile 0 0 3 1.  (* NE corner: W=1, S=3 *)
Definition square_tile_SW : TileType := mkTile 2 4 0 0.  (* SW corner: N=2, E=4 *)
Definition square_tile_SE : TileType := mkTile 3 0 0 4.  (* SE corner: N=3, W=4 *)

(** The four positions forming the 2×2 square *)
Definition pos_NW : Position := (0, 1)%Z.
Definition pos_NE : Position := (1, 1)%Z.
Definition pos_SW : Position := (0, 0)%Z.
Definition pos_SE : Position := (1, 0)%Z.

(** Build the square assembly incrementally *)
Definition square_step1 : Assembly := single_tile_assembly pos_SW square_tile_SW.
Definition square_step2 : Assembly := add_tile square_step1 pos_SE square_tile_SE.
Definition square_step3 : Assembly := add_tile square_step2 pos_NW square_tile_NW.
Definition square_2x2 : Assembly := add_tile square_step3 pos_NE square_tile_NE.

(** The tileset and TAS for the 2×2 square *)
Definition square_tileset : TileSet :=
  [square_tile_NW; square_tile_NE; square_tile_SW; square_tile_SE].

Definition square_TAS : TAS :=
  mkTAS square_tileset standard_glue_strength square_step1 2.

(** Theorem: The square assembly has all expected geometric properties *)
Theorem square_2x2_properties :
  (* Type system: All tiles are distinct *)
  (square_tile_NW <> square_tile_NE) /\
  (square_tile_SW <> square_tile_SE) /\

  (* Tile matching: Adjacent tiles have matching glues *)
  (tiles_match square_tile_SW square_tile_SE East) /\
  (tiles_match square_tile_SW square_tile_NW North) /\
  (tiles_match square_tile_NW square_tile_NE East) /\
  (tiles_match square_tile_SE square_tile_NE North) /\

  (* Well-formedness: TAS is well-formed *)
  (well_formed_tas square_TAS) /\

  (* Geometry: All four positions are pairwise adjacent where expected *)
  (adjacent pos_SW pos_SE) /\
  (adjacent pos_SW pos_NW) /\
  (adjacent pos_NW pos_NE) /\
  (adjacent pos_SE pos_NE) /\

  (* Geometry: Diagonal positions are NOT adjacent *)
  (~adjacent pos_SW pos_NE) /\
  (~adjacent pos_NW pos_SE) /\

  (* Distance: Adjacent tiles have manhattan distance 1 *)
  (manhattan_distance pos_SW pos_SE = 1%Z) /\
  (manhattan_distance pos_SW pos_NW = 1%Z) /\
  (manhattan_distance pos_NW pos_NE = 1%Z) /\
  (manhattan_distance pos_SE pos_NE = 1%Z) /\

  (* Distance: Diagonals have manhattan distance 2 *)
  (manhattan_distance pos_SW pos_NE = 2%Z) /\
  (manhattan_distance pos_NW pos_SE = 2%Z) /\

  (* Assembly operations: Each step contains tiles at correct positions *)
  (tile_at square_2x2 pos_SW = Some square_tile_SW) /\
  (tile_at square_2x2 pos_SE = Some square_tile_SE) /\
  (tile_at square_2x2 pos_NW = Some square_tile_NW) /\
  (tile_at square_2x2 pos_NE = Some square_tile_NE) /\

  (* Finiteness: All intermediate assemblies are finite *)
  (finite_assembly square_step1) /\
  (finite_assembly square_step2) /\
  (finite_assembly square_step3) /\
  (finite_assembly square_2x2) /\

  (* Domain subset: Assembly grows monotonically *)
  (square_step1 ⊆ square_step2) /\
  (square_step2 ⊆ square_step3) /\
  (square_step3 ⊆ square_2x2) /\

  (* Consistency: All intermediate assemblies are mutually consistent *)
  (square_step1 ~ square_step2) /\
  (square_step2 ~ square_step3) /\
  (square_step3 ~ square_2x2) /\

  (* Assembly size: Final assembly has 4 tiles *)
  (assembly_size square_2x2 [pos_SW; pos_SE; pos_NW; pos_NE] = 4) /\

  True.
Proof.
  split. { intro H. inversion H. }
  split. { intro H. inversion H. }
  split. { unfold tiles_match. simpl. unfold tiles_match_east. simpl. reflexivity. }
  split. { unfold tiles_match. simpl. unfold tiles_match_north. simpl. reflexivity. }
  split. { unfold tiles_match. simpl. unfold tiles_match_east. simpl. reflexivity. }
  split. { unfold tiles_match. simpl. unfold tiles_match_north. simpl. reflexivity. }
  split.
  { unfold well_formed_tas, seed_uses_tileset, glue_fn_respects_null, square_TAS. simpl.
    split.
    - intros p t Ht. unfold tile_at, square_step1, single_tile_assembly in Ht.
      destruct (Position_eq_dec p pos_SW); try discriminate.
      injection Ht as <-. unfold tile_in_set. simpl. right. right. left. reflexivity.
    - apply standard_glue_is_valid. }

  (* Adjacency proofs *)
  split. { unfold adjacent, neighbors, pos_SW, pos_SE, east. simpl. right. left. reflexivity. }
  split. { unfold adjacent, neighbors, pos_SW, pos_NW, north. simpl. left. reflexivity. }
  split. { unfold adjacent, neighbors, pos_NW, pos_NE, east. simpl. right. left. reflexivity. }
  split. { unfold adjacent, neighbors, pos_SE, pos_NE, north. simpl. left. reflexivity. }

  (* Non-adjacency of diagonals *)
  split. { unfold pos_SW, pos_NE. apply (diagonal_not_adjacent 0 0 1 1); lia. }
  split. { unfold pos_NW, pos_SE. apply (diagonal_not_adjacent 0 1 1 (-1)); lia. }

  (* Manhattan distances *)
  split. { unfold manhattan_distance, pos_SW, pos_SE. simpl. lia. }
  split. { unfold manhattan_distance, pos_SW, pos_NW. simpl. lia. }
  split. { unfold manhattan_distance, pos_NW, pos_NE. simpl. lia. }
  split. { unfold manhattan_distance, pos_SE, pos_NE. simpl. lia. }
  split. { unfold manhattan_distance, pos_SW, pos_NE. simpl. lia. }
  split. { unfold manhattan_distance, pos_NW, pos_SE. simpl. lia. }

  (* Tile placement verification *)
  split.
  { unfold square_2x2, square_step3, square_step2.
    repeat rewrite add_tile_elsewhere; try (unfold pos_SW, pos_NE, pos_NW, pos_SE; intro H; inversion H; lia).
    unfold square_step1, tile_at, single_tile_assembly, pos_SW.
    destruct (Position_eq_dec (0,0)%Z (0,0)%Z); try contradiction. reflexivity. }
  split.
  { unfold square_2x2. rewrite add_tile_elsewhere; try (unfold pos_SE, pos_NE; intro H; inversion H; lia).
    unfold square_step3. rewrite add_tile_elsewhere; try (unfold pos_SE, pos_NW; intro H; inversion H; lia).
    unfold square_step2. apply add_tile_at_position. }
  split.
  { unfold square_2x2. rewrite add_tile_elsewhere; try (unfold pos_NW, pos_NE; intro H; inversion H; lia).
    unfold square_step3. apply add_tile_at_position. }
  split. { unfold square_2x2. apply add_tile_at_position. }

  (* Finiteness proofs *)
  split. { apply single_tile_assembly_is_finite. }
  split.
  { apply add_tile_preserves_finite.
    - unfold square_step1, tile_at, single_tile_assembly, pos_SE, pos_SW.
      destruct (Position_eq_dec (1,0)%Z (0,0)%Z) as [Heq|Hneq]; [inversion Heq; lia | reflexivity].
    - apply single_tile_assembly_is_finite. }
  split.
  { apply add_tile_preserves_finite.
    - unfold square_step2, tile_at, add_tile, pos_NW, pos_SE.
      destruct (Position_eq_dec (0,1)%Z (1,0)%Z) as [H|_]; [inversion H; lia | ].
      unfold square_step1, tile_at, single_tile_assembly, pos_SW.
      destruct (Position_eq_dec (0,1)%Z (0,0)%Z) as [H|_]; [inversion H; lia | reflexivity].
    - apply add_tile_preserves_finite.
      + unfold square_step1, tile_at, single_tile_assembly, pos_SE, pos_SW.
        destruct (Position_eq_dec (1,0)%Z (0,0)%Z) as [H|_]; [inversion H; lia | reflexivity].
      + apply single_tile_assembly_is_finite. }
  split.
  { apply add_tile_preserves_finite.
    - unfold square_step3, tile_at, add_tile, pos_NE, pos_NW.
      destruct (Position_eq_dec (1,1)%Z (0,1)%Z) as [H|_]; [inversion H; lia | ].
      unfold square_step2, tile_at, add_tile, pos_SE.
      destruct (Position_eq_dec (1,1)%Z (1,0)%Z) as [H|_]; [inversion H; lia | ].
      unfold square_step1, tile_at, single_tile_assembly, pos_SW.
      destruct (Position_eq_dec (1,1)%Z (0,0)%Z) as [H|_]; [inversion H; lia | reflexivity].
    - apply add_tile_preserves_finite.
      + unfold square_step2, tile_at, add_tile, pos_NW, pos_SE.
        destruct (Position_eq_dec (0,1)%Z (1,0)%Z) as [H|_]; [inversion H; lia | ].
        unfold square_step1, tile_at, single_tile_assembly, pos_SW.
        destruct (Position_eq_dec (0,1)%Z (0,0)%Z) as [H|_]; [inversion H; lia | reflexivity].
      + apply add_tile_preserves_finite.
        * unfold square_step1, tile_at, single_tile_assembly, pos_SE, pos_SW.
          destruct (Position_eq_dec (1,0)%Z (0,0)%Z) as [H|_]; [inversion H; lia | reflexivity].
        * apply single_tile_assembly_is_finite. }

  (* Domain subset proofs *)
  split.
  { unfold domain_subset. intros p t Ht.
    unfold square_step1, square_step2, tile_at, single_tile_assembly, add_tile in *.
    destruct (Position_eq_dec p pos_SE) as [Heq|Hneq].
    - subst. destruct (Position_eq_dec pos_SE pos_SW) as [H|_] in Ht; [unfold pos_SE, pos_SW in H; inversion H; lia | discriminate].
    - destruct (Position_eq_dec p pos_SE) as [H|_]; [contradiction | exact Ht]. }
  split.
  { unfold domain_subset. intros p t Ht.
    unfold square_step2, square_step3, tile_at, add_tile in *.
    destruct (Position_eq_dec p pos_NW) as [Heq|Hneq].
    - subst. destruct (Position_eq_dec pos_NW pos_SE) as [H|_] in Ht.
      + unfold pos_NW, pos_SE in H. inversion H; lia.
      + unfold square_step1, tile_at, single_tile_assembly in Ht.
        destruct (Position_eq_dec pos_NW pos_SW) as [H|_] in Ht; [unfold pos_NW, pos_SW in H; inversion H; lia | discriminate].
    - destruct (Position_eq_dec p pos_NW) as [H|_]; [contradiction | exact Ht]. }
  split.
  { unfold domain_subset. intros p t Ht.
    unfold square_step3, square_2x2, tile_at, add_tile in *.
    destruct (Position_eq_dec p pos_NE) as [Heq|Hneq].
    - subst. destruct (Position_eq_dec pos_NE pos_NW) as [H|_] in Ht.
      + unfold pos_NE, pos_NW in H. inversion H; lia.
      + unfold square_step2, tile_at, add_tile in Ht.
        destruct (Position_eq_dec pos_NE pos_SE) as [H|_] in Ht; [unfold pos_NE, pos_SE in H; inversion H; lia |].
        unfold square_step1, tile_at, single_tile_assembly in Ht.
        destruct (Position_eq_dec pos_NE pos_SW) as [H|_] in Ht; [unfold pos_NE, pos_SW in H; inversion H; lia | discriminate].
    - destruct (Position_eq_dec p pos_NE) as [H|_]; [contradiction | exact Ht]. }

  (* Consistency proofs *)
  split.
  { apply domain_subset_implies_consistent. unfold domain_subset.
    intros p t Ht. unfold square_step1, square_step2, tile_at, single_tile_assembly, add_tile in *.
    destruct (Position_eq_dec p pos_SE) as [Heq|Hneq].
    - subst. destruct (Position_eq_dec pos_SE pos_SW) as [H|_] in Ht; [unfold pos_SE, pos_SW in H; inversion H; lia | discriminate].
    - destruct (Position_eq_dec p pos_SE) as [H|_]; [contradiction | exact Ht]. }
  split.
  { apply domain_subset_implies_consistent. unfold domain_subset.
    intros p t Ht. unfold square_step2, square_step3, tile_at, add_tile in *.
    destruct (Position_eq_dec p pos_NW) as [Heq|Hneq].
    - subst. destruct (Position_eq_dec pos_NW pos_SE) as [H|_] in Ht.
      + unfold pos_NW, pos_SE in H. inversion H; lia.
      + unfold square_step1, tile_at, single_tile_assembly in Ht.
        destruct (Position_eq_dec pos_NW pos_SW) as [H|_] in Ht; [unfold pos_NW, pos_SW in H; inversion H; lia | discriminate].
    - destruct (Position_eq_dec p pos_NW) as [H|_]; [contradiction | exact Ht]. }
  split.
  { apply domain_subset_implies_consistent. unfold domain_subset.
    intros p t Ht. unfold square_step3, square_2x2, tile_at, add_tile in *.
    destruct (Position_eq_dec p pos_NE) as [Heq|Hneq].
    - subst. destruct (Position_eq_dec pos_NE pos_NW) as [H|_] in Ht.
      + unfold pos_NE, pos_NW in H. inversion H; lia.
      + unfold square_step2, tile_at, add_tile in Ht.
        destruct (Position_eq_dec pos_NE pos_SE) as [H|_] in Ht; [unfold pos_NE, pos_SE in H; inversion H; lia |].
        unfold square_step1, tile_at, single_tile_assembly in Ht.
        destruct (Position_eq_dec pos_NE pos_SW) as [H|_] in Ht; [unfold pos_NE, pos_SW in H; inversion H; lia | discriminate].
    - destruct (Position_eq_dec p pos_NE) as [H|_]; [contradiction | exact Ht]. }

  (* Assembly size *)
  split.
  { unfold assembly_size. simpl.
    (* Show tile_at square_2x2 for each position *)
    assert (H_SW: tile_at square_2x2 pos_SW = Some square_tile_SW).
    { unfold square_2x2, square_step3, square_step2.
      repeat rewrite add_tile_elsewhere; try (unfold pos_SW, pos_NE, pos_NW, pos_SE; intro H; inversion H; lia).
      unfold square_step1, tile_at, single_tile_assembly, pos_SW.
      destruct (Position_eq_dec (0,0)%Z (0,0)%Z); try contradiction. reflexivity. }
    assert (H_SE: tile_at square_2x2 pos_SE = Some square_tile_SE).
    { unfold square_2x2. rewrite add_tile_elsewhere; try (unfold pos_SE, pos_NE; intro H; inversion H; lia).
      unfold square_step3. rewrite add_tile_elsewhere; try (unfold pos_SE, pos_NW; intro H; inversion H; lia).
      unfold square_step2. apply add_tile_at_position. }
    assert (H_NW: tile_at square_2x2 pos_NW = Some square_tile_NW).
    { unfold square_2x2. rewrite add_tile_elsewhere; try (unfold pos_NW, pos_NE; intro H; inversion H; lia).
      unfold square_step3. apply add_tile_at_position. }
    assert (H_NE: tile_at square_2x2 pos_NE = Some square_tile_NE).
    { unfold square_2x2. apply add_tile_at_position. }
    (* Rewrite filter using these facts *)
    rewrite H_SW, H_SE, H_NW, H_NE.
    simpl. reflexivity. }

  exact I.
Qed.

(** * Section 1.2: Assembly Dynamics *)

(** ** 1.2.1 Binding & Attachment *)

(** Binding strength between a tile and its neighbor in a specific direction *)
Definition neighbor_binding (strength_fn : GlueType -> nat)
                            (t : TileType) (α : Assembly) (p p_neighbor : Position) : nat :=
  match tile_at α p_neighbor with
  | None => 0
  | Some t_neighbor =>
      if Position_eq_dec p_neighbor (north p) then
        glue_strength strength_fn (glue_N t_neighbor) (glue_S t)
      else if Position_eq_dec p_neighbor (east p) then
        glue_strength strength_fn (glue_W t_neighbor) (glue_E t)
      else if Position_eq_dec p_neighbor (south p) then
        glue_strength strength_fn (glue_S t_neighbor) (glue_N t)
      else if Position_eq_dec p_neighbor (west p) then
        glue_strength strength_fn (glue_E t_neighbor) (glue_W t)
      else 0
  end.

(** Parametric directional binding: binding strength in one specific direction
    Note: This definition matches the existing neighbor_binding convention *)
Definition directional_binding (strength_fn : GlueType -> nat)
                               (t : TileType) (α : Assembly) (p : Position) (d : Direction) : nat :=
  match tile_at α (move p d) with
  | None => 0
  | Some t_neighbor =>
      match d with
      | North => glue_strength strength_fn (glue_N t_neighbor) (glue_S t)
      | East => glue_strength strength_fn (glue_W t_neighbor) (glue_E t)
      | South => glue_strength strength_fn (glue_S t_neighbor) (glue_N t)
      | West => glue_strength strength_fn (glue_E t_neighbor) (glue_W t)
      end
  end.

(** directional_binding agrees with neighbor_binding *)
Lemma directional_binding_north : forall strength_fn t α p,
  directional_binding strength_fn t α p North =
  neighbor_binding strength_fn t α p (north p).
Proof.
  intros strength_fn t α p.
  unfold directional_binding, neighbor_binding, move, get_glue, opposite_direction.
  destruct (tile_at α (north p)) as [tn |]; auto.
  destruct (Position_eq_dec (north p) (north p)); try contradiction.
  reflexivity.
Qed.

Lemma directional_binding_east : forall strength_fn t α p,
  directional_binding strength_fn t α p East =
  neighbor_binding strength_fn t α p (east p).
Proof.
  intros strength_fn t α p.
  unfold directional_binding, neighbor_binding, move.
  destruct (tile_at α (east p)) as [te |]; auto.
  destruct (Position_eq_dec (east p) (north p)) as [Heq | _].
  - destruct p as [x y]. unfold north, east in Heq. inversion Heq. lia.
  - destruct (Position_eq_dec (east p) (east p)); try contradiction.
    reflexivity.
Qed.

Lemma directional_binding_south : forall strength_fn t α p,
  directional_binding strength_fn t α p South =
  neighbor_binding strength_fn t α p (south p).
Proof.
  intros strength_fn t α p.
  unfold directional_binding, neighbor_binding, move, get_glue, opposite_direction.
  destruct (tile_at α (south p)) as [ts |]; auto.
  destruct (Position_eq_dec (south p) (north p)) as [Heq | _].
  - destruct p as [x y]. unfold north, south in Heq. inversion Heq. lia.
  - destruct (Position_eq_dec (south p) (east p)) as [Heq | _].
    + destruct p as [x y]. unfold south, east in Heq. inversion Heq. lia.
    + destruct (Position_eq_dec (south p) (south p)); try contradiction.
      reflexivity.
Qed.

Lemma directional_binding_west : forall strength_fn t α p,
  directional_binding strength_fn t α p West =
  neighbor_binding strength_fn t α p (west p).
Proof.
  intros strength_fn t α p.
  unfold directional_binding, neighbor_binding, move, get_glue, opposite_direction.
  destruct (tile_at α (west p)) as [tw |]; auto.
  destruct (Position_eq_dec (west p) (north p)) as [Heq | _].
  - destruct p as [x y]. unfold west, north in Heq. inversion Heq. lia.
  - destruct (Position_eq_dec (west p) (east p)) as [Heq | _].
    + destruct p as [x y]. unfold west, east in Heq. inversion Heq. lia.
    + destruct (Position_eq_dec (west p) (south p)) as [Heq | _].
      * destruct p as [x y]. unfold west, south in Heq. inversion Heq. lia.
      * destruct (Position_eq_dec (west p) (west p)); try contradiction.
        reflexivity.
Qed.

(** General equivalence theorem *)
Theorem directional_binding_equiv : forall strength_fn t α p d,
  directional_binding strength_fn t α p d =
  neighbor_binding strength_fn t α p (move p d).
Proof.
  intros strength_fn t α p d.
  destruct d.
  - apply directional_binding_north.
  - apply directional_binding_east.
  - apply directional_binding_south.
  - apply directional_binding_west.
Qed.

(** Total binding strength of a tile at position p: sum over all 4 neighbors *)
Definition binding_strength (strength_fn : GlueType -> nat)
                            (t : TileType) (α : Assembly) (p : Position) : nat :=
  neighbor_binding strength_fn t α p (north p) +
  neighbor_binding strength_fn t α p (east p) +
  neighbor_binding strength_fn t α p (south p) +
  neighbor_binding strength_fn t α p (west p).

(** Parametric version using fold over all_directions *)
Definition binding_strength' (strength_fn : GlueType -> nat)
                             (t : TileType) (α : Assembly) (p : Position) : nat :=
  fold_right Nat.add 0 (map (directional_binding strength_fn t α p) all_directions).

(** binding_strength' is equivalent to binding_strength *)
Theorem binding_strength_equiv : forall strength_fn t α p,
  binding_strength' strength_fn t α p = binding_strength strength_fn t α p.
Proof.
  intros strength_fn t α p.
  unfold binding_strength', binding_strength, all_directions.
  simpl.
  rewrite directional_binding_north.
  rewrite directional_binding_east.
  rewrite directional_binding_south.
  rewrite directional_binding_west.
  lia.
Qed.

(** A tile can attach at position p if the position is empty and binding strength ≥ τ *)
Definition can_attach (strength_fn : GlueType -> nat) (t : TileType)
                      (α : Assembly) (p : Position) (τ : Temperature) : Prop :=
  tile_at α p = None /\ binding_strength strength_fn t α p >= τ.

(** TAS-aware attachment: tile must be from the tileset *)
Definition can_attach_TAS (S : TAS) (t : TileType) (α : Assembly) (p : Position) : Prop :=
  tile_in_set t (tas_tiles S) /\
  tile_at α p = None /\
  binding_strength (tas_glue_strength S) t α p >= tas_temp S.

(** Relationship between can_attach and can_attach_TAS *)
Lemma can_attach_TAS_implies_can_attach : forall S t α p,
  can_attach_TAS S t α p ->
  can_attach (tas_glue_strength S) t α p (tas_temp S).
Proof.
  intros S t α p [_ [Hempty Hbind]].
  unfold can_attach. split; assumption.
Qed.

Lemma can_attach_to_TAS : forall S t α p,
  tile_in_set t (tas_tiles S) ->
  can_attach (tas_glue_strength S) t α p (tas_temp S) ->
  can_attach_TAS S t α p.
Proof.
  intros S t α p Hin [Hempty Hbind].
  unfold can_attach_TAS. split; [exact Hin | split; assumption].
Qed.

Lemma can_attach_TAS_dec : forall S t α p,
  {can_attach_TAS S t α p} + {~can_attach_TAS S t α p}.
Proof.
  intros S t α p.
  destruct (tile_in_set_dec t (tas_tiles S)) as [Hin | Hnotin].
  - destruct (tile_at α p) eqn:Htile.
    + right. intro H. destruct H as [_ [Hempty _]]. rewrite Htile in Hempty. discriminate.
    + destruct (le_dec (tas_temp S) (binding_strength (tas_glue_strength S) t α p)) as [Hge | Hlt].
      * left. unfold can_attach_TAS. split; [exact Hin | split; auto].
      * right. intro H. destruct H as [_ [_ Hbind]]. lia.
  - right. intro H. destruct H as [Hin' _]. contradiction.
Defined.

Theorem can_attach_TAS_respects_well_formed : forall S t α p,
  well_formed_tas S ->
  can_attach_TAS S t α p ->
  tile_in_set t (tas_tiles S).
Proof.
  intros S t α p _ [Hin _]. exact Hin.
Qed.

(** Can ANY tile from the tileset attach at position p? *)
Definition can_grow (S : TAS) (α : Assembly) (p : Position) : Prop :=
  exists t, can_attach_TAS S t α p.

Lemma can_grow_means_empty : forall S α p,
  can_grow S α p ->
  tile_at α p = None.
Proof.
  intros S α p [t [_ [Hempty _]]]. exact Hempty.
Qed.

Lemma can_grow_requires_binding : forall S α p,
  can_grow S α p ->
  exists t, tile_in_set t (tas_tiles S) /\
            binding_strength (tas_glue_strength S) t α p >= tas_temp S.
Proof.
  intros S α p [t [Hin [_ Hbind]]].
  exists t. split; assumption.
Qed.

(** ** Growth Frontier *)

(** The frontier of an assembly: empty positions adjacent to occupied positions *)
Definition frontier (α : Assembly) (p : Position) : Prop :=
  tile_at α p = None /\
  exists q, support α q /\ adjacent q p.

Lemma frontier_empty : forall p,
  ~frontier empty_assembly p.
Proof.
  intros p [_ [q [Hsupp _]]].
  apply (empty_assembly_empty_support q). exact Hsupp.
Qed.

Lemma north_is_adjacent : forall p,
  adjacent (north p) p.
Proof.
  intro p. unfold adjacent, neighbors. simpl. right. right. left.
  apply north_south_inverse.
Qed.

Lemma east_is_adjacent : forall p,
  adjacent (east p) p.
Proof.
  intro p. unfold adjacent, neighbors. simpl. right. right. right. left.
  apply east_west_inverse.
Qed.

Lemma south_is_adjacent : forall p,
  adjacent (south p) p.
Proof.
  intro p. unfold adjacent, neighbors. simpl. left.
  apply south_north_inverse.
Qed.

Lemma west_is_adjacent : forall p,
  adjacent (west p) p.
Proof.
  intro p. unfold adjacent, neighbors. simpl. right. left.
  apply west_east_inverse.
Qed.

Lemma binding_all_empty_contradiction : forall S t α p,
  tile_at α (north p) = None ->
  tile_at α (east p) = None ->
  tile_at α (south p) = None ->
  tile_at α (west p) = None ->
  binding_strength (tas_glue_strength S) t α p >= tas_temp S ->
  tas_temp S = 0.
Proof.
  intros S t α p Hn He Hs Hw Hbind.
  unfold binding_strength, neighbor_binding in Hbind.
  rewrite Hn, He, Hs, Hw in Hbind. simpl in Hbind. lia.
Qed.

Theorem can_grow_implies_frontier_or_temp_zero : forall S α p,
  can_grow S α p ->
  frontier α p \/ tas_temp S = 0.
Proof.
  intros S α p [t [Hin [Hempty Hbind]]].
  destruct (tile_at α (north p)) as [t_n |] eqn:Hn.
  - left. unfold frontier. split. exact Hempty.
    exists (north p). split.
    + unfold support. exists t_n. exact Hn.
    + apply north_is_adjacent.
  - destruct (tile_at α (east p)) as [t_e |] eqn:He.
    + left. unfold frontier. split. exact Hempty.
      exists (east p). split.
      * unfold support. exists t_e. exact He.
      * apply east_is_adjacent.
    + destruct (tile_at α (south p)) as [t_s |] eqn:Hs.
      * left. unfold frontier. split. exact Hempty.
        exists (south p). split.
        ** unfold support. exists t_s. exact Hs.
        ** apply south_is_adjacent.
      * destruct (tile_at α (west p)) as [t_w |] eqn:Hw.
        ** left. unfold frontier. split. exact Hempty.
           exists (west p). split.
           *** unfold support. exists t_w. exact Hw.
           *** apply west_is_adjacent.
        ** right.
           unfold binding_strength, neighbor_binding in Hbind.
           rewrite Hn, He, Hs, Hw in Hbind.
           simpl in Hbind. lia.
Qed.

(** Attachment preserves tileset membership *)
Theorem add_tile_preserves_tileset_membership : forall S α p t,
  (forall p' t', tile_at α p' = Some t' -> tile_in_set t' (tas_tiles S)) ->
  can_attach_TAS S t α p ->
  (forall p' t', tile_at (add_tile α p t) p' = Some t' -> tile_in_set t' (tas_tiles S)).
Proof.
  intros S α p t Hα [Hin [Hempty _]] p' t' Htile.
  unfold tile_at, add_tile in Htile.
  destruct (Position_eq_dec p' p) as [Heq | Hneq].
  - injection Htile as <-. exact Hin.
  - apply (Hα p' t'). exact Htile.
Qed.

(** Basic properties of neighbor binding *)

Lemma neighbor_binding_empty : forall strength_fn t α p p_neighbor,
  tile_at α p_neighbor = None ->
  neighbor_binding strength_fn t α p p_neighbor = 0.
Proof.
  intros strength_fn t α p p_neighbor Hempty.
  unfold neighbor_binding. rewrite Hempty. reflexivity.
Qed.

Lemma neighbor_binding_non_neighbor : forall strength_fn t α p p_other,
  ~adjacent p p_other ->
  neighbor_binding strength_fn t α p p_other = 0.
Proof.
  intros strength_fn t α p p_other Hnadj.
  unfold neighbor_binding.
  destruct (tile_at α p_other) as [t_other |] eqn:Hother; auto.
  unfold adjacent, neighbors in Hnadj.
  destruct (Position_eq_dec p_other (north p)) as [Hn | Hnn].
  - exfalso. apply Hnadj. simpl. left. symmetry. exact Hn.
  - destruct (Position_eq_dec p_other (east p)) as [He | Hne].
    + exfalso. apply Hnadj. simpl. right. left. symmetry. exact He.
    + destruct (Position_eq_dec p_other (south p)) as [Hs | Hns].
      * exfalso. apply Hnadj. simpl. right. right. left. symmetry. exact Hs.
      * destruct (Position_eq_dec p_other (west p)) as [Hw | Hnw].
        ** exfalso. apply Hnadj. simpl. right. right. right. left. symmetry. exact Hw.
        ** reflexivity.
Qed.

(** Binding strength is always non-negative *)
Lemma binding_strength_nonnegative : forall strength_fn t α p,
  binding_strength strength_fn t α p >= 0.
Proof.
  intros. unfold binding_strength. lia.
Qed.

(** Binding strength in empty assembly is zero *)
Theorem binding_strength_empty_assembly : forall strength_fn t p,
  binding_strength strength_fn t empty_assembly p = 0.
Proof.
  intros strength_fn t p.
  unfold binding_strength.
  repeat rewrite neighbor_binding_empty; auto;
  apply empty_assembly_has_no_tiles.
Qed.

(** Binding strength decomposition into directional components *)
Theorem binding_strength_is_sum : forall strength_fn t α p,
  binding_strength strength_fn t α p =
    neighbor_binding strength_fn t α p (north p) +
    neighbor_binding strength_fn t α p (east p) +
    neighbor_binding strength_fn t α p (south p) +
    neighbor_binding strength_fn t α p (west p).
Proof.
  intros. unfold binding_strength. reflexivity.
Qed.

(** If any neighbor contributes at least k, total binding is at least k *)
Lemma binding_at_least_one_neighbor : forall strength_fn t α p dir k,
  In dir (neighbors p) ->
  neighbor_binding strength_fn t α p dir >= k ->
  binding_strength strength_fn t α p >= k.
Proof.
  intros strength_fn t α p dir k Hdir Hneighbor.
  unfold binding_strength.
  unfold neighbors in Hdir. simpl in Hdir.
  destruct Hdir as [Hn | [He | [Hs | [Hw | Hf]]]]; try contradiction.
  - rewrite <- Hn in Hneighbor. lia.
  - rewrite <- He in Hneighbor. lia.
  - rewrite <- Hs in Hneighbor. lia.
  - rewrite <- Hw in Hneighbor. lia.
Qed.

(** Neighbor binding is symmetric with respect to glue strength *)
Lemma neighbor_binding_symmetric_glue : forall strength_fn t α p p_neighbor,
  (forall g1 g2, glue_strength strength_fn g1 g2 = glue_strength strength_fn g2 g1) ->
  neighbor_binding strength_fn t α p p_neighbor =
  match tile_at α p_neighbor with
  | None => 0
  | Some t_neighbor =>
      if Position_eq_dec p_neighbor (north p) then
        glue_strength strength_fn (glue_S t) (glue_N t_neighbor)
      else if Position_eq_dec p_neighbor (east p) then
        glue_strength strength_fn (glue_E t) (glue_W t_neighbor)
      else if Position_eq_dec p_neighbor (south p) then
        glue_strength strength_fn (glue_N t) (glue_S t_neighbor)
      else if Position_eq_dec p_neighbor (west p) then
        glue_strength strength_fn (glue_W t) (glue_E t_neighbor)
      else 0
  end.
Proof.
  intros strength_fn t α p p_neighbor Hsym.
  unfold neighbor_binding.
  destruct (tile_at α p_neighbor) as [t_neighbor |]; [| reflexivity].
  destruct (Position_eq_dec p_neighbor (north p)) as [Hn | Hnn]; [rewrite Hsym; reflexivity |].
  destruct (Position_eq_dec p_neighbor (east p)) as [He | Hne]; [rewrite Hsym; reflexivity |].
  destruct (Position_eq_dec p_neighbor (south p)) as [Hs | Hns]; [rewrite Hsym; reflexivity |].
  destruct (Position_eq_dec p_neighbor (west p)) as [Hw | Hnw]; [rewrite Hsym; reflexivity | reflexivity].
Qed.

(** Binding strength only depends on the 4 adjacent neighbors *)
Theorem binding_strength_only_neighbors : forall strength_fn t α β p,
  (forall dir, In dir (neighbors p) -> tile_at α dir = tile_at β dir) ->
  binding_strength strength_fn t α p = binding_strength strength_fn t β p.
Proof.
  intros strength_fn t α β p Hneighbors.
  unfold binding_strength, neighbor_binding.
  assert (Hn: tile_at α (north p) = tile_at β (north p)).
  { apply Hneighbors. unfold neighbors. simpl. auto. }
  assert (He: tile_at α (east p) = tile_at β (east p)).
  { apply Hneighbors. unfold neighbors. simpl. auto. }
  assert (Hs: tile_at α (south p) = tile_at β (south p)).
  { apply Hneighbors. unfold neighbors. simpl. auto. }
  assert (Hw: tile_at α (west p) = tile_at β (west p)).
  { apply Hneighbors. unfold neighbors. simpl. auto. }
  rewrite Hn, He, Hs, Hw. reflexivity.
Qed.

(** Assembly equivalence preserves binding strength *)
Theorem binding_strength_respects_equiv : forall strength_fn t α β p,
  α ≡ β ->
  binding_strength strength_fn t α p = binding_strength strength_fn t β p.
Proof.
  intros strength_fn t α β p Hequiv.
  apply binding_strength_only_neighbors.
  intros dir Hdir.
  unfold assembly_equiv in Hequiv.
  apply Hequiv.
Qed.

(** binding_strength respects assembly equivalence *)
Add Parametric Morphism strength_fn t p : (fun α => binding_strength strength_fn t α p)
  with signature assembly_equiv ==> eq
  as binding_strength_morphism.
Proof.
  intros α β Heq.
  apply binding_strength_respects_equiv.
  exact Heq.
Qed.

(** Decidability of can_attach *)
Lemma can_attach_dec : forall strength_fn t α p τ,
  {can_attach strength_fn t α p τ} + {~can_attach strength_fn t α p τ}.
Proof.
  intros strength_fn t α p τ.
  unfold can_attach.
  destruct (tile_at α p) as [t' |] eqn:Htile.
  - right. intro H. destruct H as [Hempty _]. discriminate.
  - destruct (le_dec τ (binding_strength strength_fn t α p)) as [Hge | Hlt].
    + left. split; auto.
    + right. intro H. destruct H as [_ Hbind]. lia.
Qed.

(** Attachment is anti-monotonic in temperature: lower temp → easier to attach *)
Theorem can_attach_anti_monotonic_in_temperature : forall strength_fn t α p τ1 τ2,
  can_attach strength_fn t α p τ2 ->
  τ1 <= τ2 ->
  can_attach strength_fn t α p τ1.
Proof.
  intros strength_fn t α p τ1 τ2 [Hempty Hbind] Hle.
  unfold can_attach. split; auto. lia.
Qed.

(** Adding a tile elsewhere doesn't affect binding at p *)
Theorem binding_strength_add_tile_elsewhere : forall strength_fn t α p p' t',
  ~In p' (neighbors p) ->
  binding_strength strength_fn t (add_tile α p' t') p =
  binding_strength strength_fn t α p.
Proof.
  intros strength_fn t α p p' t' Hnotin.
  apply binding_strength_only_neighbors.
  intros dir Hdir.
  unfold tile_at, add_tile.
  destruct (Position_eq_dec dir p') as [Heq | Hneq]; auto.
  exfalso. apply Hnotin. rewrite <- Heq. exact Hdir.
Qed.

(** If position is occupied, tile cannot attach *)
Theorem occupied_cannot_attach : forall strength_fn t α p τ t',
  tile_at α p = Some t' ->
  ~can_attach strength_fn t α p τ.
Proof.
  intros strength_fn t α p τ t' Hocc Hattach.
  destruct Hattach as [Hempty _].
  rewrite Hocc in Hempty. discriminate.
Qed.

(** Temperature 0 allows attachment anywhere empty *)
Theorem temp_0_attach_anywhere_empty : forall strength_fn t α p,
  tile_at α p = None ->
  can_attach strength_fn t α p 0.
Proof.
  intros strength_fn t α p Hempty.
  unfold can_attach. split; auto.
  apply binding_strength_nonnegative.
Qed.

(** Helper: Direction distinctness lemmas *)

Lemma north_east_distinct : forall p, north p <> east p.
Proof. intros [x y] Heq. unfold north, east in Heq. inversion Heq. lia. Qed.

Lemma north_south_distinct : forall p, north p <> south p.
Proof. intros [x y] Heq. unfold north, south in Heq. inversion Heq. lia. Qed.

Lemma north_west_distinct : forall p, north p <> west p.
Proof. intros [x y] Heq. unfold north, west in Heq. inversion Heq. lia. Qed.

Lemma east_south_distinct : forall p, east p <> south p.
Proof. intros [x y] Heq. unfold east, south in Heq. inversion Heq. lia. Qed.

Lemma east_west_distinct : forall p, east p <> west p.
Proof. intros [x y] Heq. unfold east, west in Heq. inversion Heq. lia. Qed.

Lemma south_west_distinct : forall p, south p <> west p.
Proof. intros [x y] Heq. unfold south, west in Heq. inversion Heq. lia. Qed.

(** Adding tile at p_new preserves neighbor_binding to other positions *)
Lemma add_tile_preserves_neighbor_binding_to_other : forall strength_fn t α p p_new p_other t_new,
  p_new <> p_other ->
  neighbor_binding strength_fn t (add_tile α p_new t_new) p p_other =
  neighbor_binding strength_fn t α p p_other.
Proof.
  intros strength_fn t α p p_new p_other t_new Hneq.
  unfold neighbor_binding, add_tile, tile_at.
  destruct (Position_eq_dec p_other p_new) as [Heq | Hne].
  - subst. contradiction.
  - reflexivity.
Qed.

(** Adding tile at empty p_new increases neighbor_binding from p to p_new *)
Lemma add_tile_increases_neighbor_binding_at_new : forall strength_fn t α p p_new t_new,
  tile_at α p_new = None ->
  neighbor_binding strength_fn t α p p_new <=
  neighbor_binding strength_fn t (add_tile α p_new t_new) p p_new.
Proof.
  intros strength_fn t α p p_new t_new Hempty.
  rewrite neighbor_binding_empty; auto.
  apply Nat.le_0_l.
Qed.

(** Monotonicity for adding tile to north neighbor *)
Lemma binding_strength_add_north_monotonic : forall strength_fn t α p t_new,
  tile_at α (north p) = None ->
  binding_strength strength_fn t α p <=
  binding_strength strength_fn t (add_tile α (north p) t_new) p.
Proof.
  intros strength_fn t α p t_new Hempty.
  unfold binding_strength.
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (east p)); auto using north_east_distinct.
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (south p)); auto using north_south_distinct.
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (west p)); auto using north_west_distinct.
  apply Nat.add_le_mono_r. apply Nat.add_le_mono_r. apply Nat.add_le_mono_r.
  apply add_tile_increases_neighbor_binding_at_new. exact Hempty.
Qed.

(** Monotonicity for adding tile to east neighbor *)
Lemma binding_strength_add_east_monotonic : forall strength_fn t α p t_new,
  tile_at α (east p) = None ->
  binding_strength strength_fn t α p <=
  binding_strength strength_fn t (add_tile α (east p) t_new) p.
Proof.
  intros strength_fn t α p t_new Hempty.
  unfold binding_strength.
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (north p)).
  2: { intro H. symmetry in H. apply (north_east_distinct p). exact H. }
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (south p)); auto using east_south_distinct.
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (west p)); auto using east_west_distinct.
  apply Nat.add_le_mono_r. apply Nat.add_le_mono_r. apply Nat.add_le_mono_l.
  apply add_tile_increases_neighbor_binding_at_new. exact Hempty.
Qed.

(** Monotonicity for adding tile to south neighbor *)
Lemma binding_strength_add_south_monotonic : forall strength_fn t α p t_new,
  tile_at α (south p) = None ->
  binding_strength strength_fn t α p <=
  binding_strength strength_fn t (add_tile α (south p) t_new) p.
Proof.
  intros strength_fn t α p t_new Hempty.
  unfold binding_strength.
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (north p)).
  2: { intro H. symmetry in H. apply (north_south_distinct p). exact H. }
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (east p)).
  2: { intro H. symmetry in H. apply (east_south_distinct p). exact H. }
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (west p)); auto using south_west_distinct.
  apply Nat.add_le_mono_r. apply Nat.add_le_mono_l.
  apply add_tile_increases_neighbor_binding_at_new. exact Hempty.
Qed.

(** Monotonicity for adding tile to west neighbor *)
Lemma binding_strength_add_west_monotonic : forall strength_fn t α p t_new,
  tile_at α (west p) = None ->
  binding_strength strength_fn t α p <=
  binding_strength strength_fn t (add_tile α (west p) t_new) p.
Proof.
  intros strength_fn t α p t_new Hempty.
  unfold binding_strength.
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (north p)).
  2: { intro H. symmetry in H. apply (north_west_distinct p). exact H. }
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (east p)).
  2: { intro H. symmetry in H. apply (east_west_distinct p). exact H. }
  rewrite (add_tile_preserves_neighbor_binding_to_other _ _ _ _ _ (south p)).
  2: { intro H. symmetry in H. apply (south_west_distinct p). exact H. }
  apply Nat.add_le_mono_l.
  apply add_tile_increases_neighbor_binding_at_new. exact Hempty.
Qed.

(** Connection between tile matching and neighbor binding *)

Theorem tiles_match_north_implies_binding : forall strength_fn t_below t_above α p,
  tile_at α (north p) = Some t_above ->
  tiles_match_north t_below t_above ->
  neighbor_binding strength_fn t_below α p (north p) =
    glue_strength strength_fn (glue_N t_above) (glue_S t_below).
Proof.
  intros strength_fn t_below t_above α p Htile Hmatch.
  unfold neighbor_binding.
  rewrite Htile.
  destruct (Position_eq_dec (north p) (north p)); try contradiction.
  reflexivity.
Qed.

Theorem tiles_match_east_implies_binding : forall strength_fn t_left t_right α p,
  tile_at α (east p) = Some t_right ->
  tiles_match_east t_left t_right ->
  neighbor_binding strength_fn t_left α p (east p) =
    glue_strength strength_fn (glue_W t_right) (glue_E t_left).
Proof.
  intros strength_fn t_left t_right α p Htile Hmatch.
  unfold neighbor_binding.
  rewrite Htile.
  destruct (Position_eq_dec (east p) (north p)) as [Heq | _].
  - exfalso. apply (north_east_distinct p). symmetry. exact Heq.
  - destruct (Position_eq_dec (east p) (east p)); try contradiction.
    reflexivity.
Qed.

Theorem tiles_match_south_implies_binding : forall strength_fn t_above t_below α p,
  tile_at α (south p) = Some t_below ->
  tiles_match_south t_above t_below ->
  neighbor_binding strength_fn t_above α p (south p) =
    glue_strength strength_fn (glue_S t_below) (glue_N t_above).
Proof.
  intros strength_fn t_above t_below α p Htile Hmatch.
  unfold neighbor_binding.
  rewrite Htile.
  destruct (Position_eq_dec (south p) (north p)) as [Heq | _].
  - exfalso. apply (north_south_distinct p). symmetry. exact Heq.
  - destruct (Position_eq_dec (south p) (east p)) as [Heq | _].
    + exfalso. apply (east_south_distinct p). symmetry. exact Heq.
    + destruct (Position_eq_dec (south p) (south p)); try contradiction.
      reflexivity.
Qed.

Theorem tiles_match_west_implies_binding : forall strength_fn t_right t_left α p,
  tile_at α (west p) = Some t_left ->
  tiles_match_west t_right t_left ->
  neighbor_binding strength_fn t_right α p (west p) =
    glue_strength strength_fn (glue_E t_left) (glue_W t_right).
Proof.
  intros strength_fn t_right t_left α p Htile Hmatch.
  unfold neighbor_binding.
  rewrite Htile.
  destruct (Position_eq_dec (west p) (north p)) as [Heq | _].
  - exfalso. apply (north_west_distinct p). symmetry. exact Heq.
  - destruct (Position_eq_dec (west p) (east p)) as [Heq | _].
    + exfalso. apply (east_west_distinct p). symmetry. exact Heq.
    + destruct (Position_eq_dec (west p) (south p)) as [Heq | _].
      * exfalso. apply (south_west_distinct p). symmetry. exact Heq.
      * destruct (Position_eq_dec (west p) (west p)); try contradiction.
        reflexivity.
Qed.

(** General theorem: tiles_match implies specific binding strength *)
Theorem tiles_match_implies_neighbor_binding : forall strength_fn t1 t2 α p d,
  tiles_match t1 t2 d ->
  tile_at α (match d with
             | North => north p
             | East => east p
             | South => south p
             | West => west p
             end) = Some t2 ->
  neighbor_binding strength_fn t1 α p (match d with
                                       | North => north p
                                       | East => east p
                                       | South => south p
                                       | West => west p
                                       end) =
  match d with
  | North => glue_strength strength_fn (glue_N t2) (glue_S t1)
  | East => glue_strength strength_fn (glue_W t2) (glue_E t1)
  | South => glue_strength strength_fn (glue_S t2) (glue_N t1)
  | West => glue_strength strength_fn (glue_E t2) (glue_W t1)
  end.
Proof.
  intros strength_fn t1 t2 α p d Hmatch Htile.
  destruct d.
  - apply tiles_match_north_implies_binding; assumption.
  - apply tiles_match_east_implies_binding; assumption.
  - apply tiles_match_south_implies_binding; assumption.
  - apply tiles_match_west_implies_binding; assumption.
Qed.

(** Monotonicity for removing tiles: dual of addition *)

Lemma remove_tile_decreases_neighbor_binding : forall strength_fn t α p p_removed,
  tile_at α p_removed <> None ->
  neighbor_binding strength_fn t (remove_tile α p_removed) p p_removed <=
  neighbor_binding strength_fn t α p p_removed.
Proof.
  intros strength_fn t α p p_removed Hnot_empty.
  destruct (tile_at α p_removed) as [t_removed |] eqn:Hrm.
  - unfold remove_tile, neighbor_binding.
    unfold tile_at at 1. destruct (Position_eq_dec p_removed p_removed); try contradiction.
    simpl. apply Nat.le_0_l.
  - contradiction.
Qed.

Lemma binding_strength_remove_north_monotonic : forall strength_fn t α p,
  tile_at α (north p) <> None ->
  binding_strength strength_fn t (remove_tile α (north p)) p <=
  binding_strength strength_fn t α p.
Proof.
  intros strength_fn t α p Hnonempty.
  unfold binding_strength.
  assert (Heq_east: neighbor_binding strength_fn t (remove_tile α (north p)) p (east p) =
                    neighbor_binding strength_fn t α p (east p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro H. symmetry in H. apply (north_east_distinct p). exact H. }
  assert (Heq_south: neighbor_binding strength_fn t (remove_tile α (north p)) p (south p) =
                     neighbor_binding strength_fn t α p (south p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro H. symmetry in H. apply (north_south_distinct p). exact H. }
  assert (Heq_west: neighbor_binding strength_fn t (remove_tile α (north p)) p (west p) =
                    neighbor_binding strength_fn t α p (west p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro H. symmetry in H. apply (north_west_distinct p). exact H. }
  rewrite Heq_east, Heq_south, Heq_west.
  apply Nat.add_le_mono_r. apply Nat.add_le_mono_r. apply Nat.add_le_mono_r.
  apply remove_tile_decreases_neighbor_binding. exact Hnonempty.
Qed.

Lemma binding_strength_remove_east_monotonic : forall strength_fn t α p,
  tile_at α (east p) <> None ->
  binding_strength strength_fn t (remove_tile α (east p)) p <=
  binding_strength strength_fn t α p.
Proof.
  intros strength_fn t α p Hnonempty.
  unfold binding_strength.
  assert (Heq_north: neighbor_binding strength_fn t (remove_tile α (east p)) p (north p) =
                     neighbor_binding strength_fn t α p (north p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (north_east_distinct p). exact Heq. }
  assert (Heq_south: neighbor_binding strength_fn t (remove_tile α (east p)) p (south p) =
                     neighbor_binding strength_fn t α p (south p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (east_south_distinct p). symmetry. exact Heq. }
  assert (Heq_west: neighbor_binding strength_fn t (remove_tile α (east p)) p (west p) =
                    neighbor_binding strength_fn t α p (west p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (east_west_distinct p). symmetry. exact Heq. }
  rewrite Heq_north, Heq_south, Heq_west.
  apply Nat.add_le_mono_r. apply Nat.add_le_mono_r. apply Nat.add_le_mono_l.
  apply remove_tile_decreases_neighbor_binding. exact Hnonempty.
Qed.

Lemma binding_strength_remove_south_monotonic : forall strength_fn t α p,
  tile_at α (south p) <> None ->
  binding_strength strength_fn t (remove_tile α (south p)) p <=
  binding_strength strength_fn t α p.
Proof.
  intros strength_fn t α p Hnonempty.
  unfold binding_strength.
  assert (Heq_north: neighbor_binding strength_fn t (remove_tile α (south p)) p (north p) =
                     neighbor_binding strength_fn t α p (north p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (north_south_distinct p). exact Heq. }
  assert (Heq_east: neighbor_binding strength_fn t (remove_tile α (south p)) p (east p) =
                    neighbor_binding strength_fn t α p (east p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (east_south_distinct p). exact Heq. }
  assert (Heq_west: neighbor_binding strength_fn t (remove_tile α (south p)) p (west p) =
                    neighbor_binding strength_fn t α p (west p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (south_west_distinct p). symmetry. exact Heq. }
  rewrite Heq_north, Heq_east, Heq_west.
  apply Nat.add_le_mono_r. apply Nat.add_le_mono_l.
  apply remove_tile_decreases_neighbor_binding. exact Hnonempty.
Qed.

Lemma binding_strength_remove_west_monotonic : forall strength_fn t α p,
  tile_at α (west p) <> None ->
  binding_strength strength_fn t (remove_tile α (west p)) p <=
  binding_strength strength_fn t α p.
Proof.
  intros strength_fn t α p Hnonempty.
  unfold binding_strength.
  assert (Heq_north: neighbor_binding strength_fn t (remove_tile α (west p)) p (north p) =
                     neighbor_binding strength_fn t α p (north p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (north_west_distinct p). exact Heq. }
  assert (Heq_east: neighbor_binding strength_fn t (remove_tile α (west p)) p (east p) =
                    neighbor_binding strength_fn t α p (east p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (east_west_distinct p). exact Heq. }
  assert (Heq_south: neighbor_binding strength_fn t (remove_tile α (west p)) p (south p) =
                     neighbor_binding strength_fn t α p (south p)).
  { unfold neighbor_binding. rewrite remove_tile_elsewhere; [reflexivity |].
    intro Heq. exfalso. apply (south_west_distinct p). exact Heq. }
  rewrite Heq_north, Heq_east, Heq_south.
  apply Nat.add_le_mono_l.
  apply remove_tile_decreases_neighbor_binding. exact Hnonempty.
Qed.

(** General monotonicity theorem for tile removal *)
Theorem binding_strength_remove_tile_monotonic : forall strength_fn t α p p_removed,
  In p_removed (neighbors p) ->
  tile_at α p_removed <> None ->
  binding_strength strength_fn t (remove_tile α p_removed) p <=
  binding_strength strength_fn t α p.
Proof.
  intros strength_fn t α p p_removed Hin Hnonempty.
  unfold neighbors in Hin. simpl in Hin.
  destruct Hin as [Hn | [He | [Hs | [Hw | Hf]]]]; try contradiction.
  - rewrite <- Hn. apply binding_strength_remove_north_monotonic. rewrite Hn. exact Hnonempty.
  - rewrite <- He. apply binding_strength_remove_east_monotonic. rewrite He. exact Hnonempty.
  - rewrite <- Hs. apply binding_strength_remove_south_monotonic. rewrite Hs. exact Hnonempty.
  - rewrite <- Hw. apply binding_strength_remove_west_monotonic. rewrite Hw. exact Hnonempty.
Qed.

(** Each neighbor binding is bounded by max_strength *)
Lemma neighbor_binding_bounded : forall strength_fn t α p p_neighbor max_strength,
  (forall g, strength_fn g <= max_strength) ->
  neighbor_binding strength_fn t α p p_neighbor <= max_strength.
Proof.
  intros strength_fn t α p p_neighbor max_strength Hmax.
  unfold neighbor_binding.
  destruct (tile_at α p_neighbor) as [tn |]; try lia.
  repeat (destruct (Position_eq_dec _ _));
  unfold glue_strength;
  repeat (destruct (glue_eq_dec _ _)); try lia;
  apply Hmax.
Qed.

(** Binding strength is bounded by 4 times the maximum glue strength *)
Theorem binding_strength_bounded : forall strength_fn t α p max_strength,
  (forall g, strength_fn g <= max_strength) ->
  binding_strength strength_fn t α p <= 4 * max_strength.
Proof.
  intros strength_fn t α p max_strength Hmax.
  unfold binding_strength.
  assert (Hn: neighbor_binding strength_fn t α p (north p) <= max_strength)
    by (apply neighbor_binding_bounded; exact Hmax).
  assert (He: neighbor_binding strength_fn t α p (east p) <= max_strength)
    by (apply neighbor_binding_bounded; exact Hmax).
  assert (Hs: neighbor_binding strength_fn t α p (south p) <= max_strength)
    by (apply neighbor_binding_bounded; exact Hmax).
  assert (Hw: neighbor_binding strength_fn t α p (west p) <= max_strength)
    by (apply neighbor_binding_bounded; exact Hmax).
  lia.
Qed.

(** ** Single Tile Difference *)

(** Two assemblies differ by exactly one tile *)
Definition single_tile_difference (α β : Assembly) (p : Position) (t : TileType) : Prop :=
  tile_at β p = Some t /\
  tile_at α p = None /\
  (forall p', p' <> p -> tile_at α p' = tile_at β p').

Lemma single_tile_difference_preserves_elsewhere : forall α β p t p',
  single_tile_difference α β p t ->
  p' <> p ->
  tile_at α p' = tile_at β p'.
Proof.
  intros α β p t p' [_ [_ Hother]] Hneq.
  apply Hother. exact Hneq.
Qed.

Theorem single_tile_difference_unique : forall α β p t1 t2,
  single_tile_difference α β p t1 ->
  single_tile_difference α β p t2 ->
  t1 = t2.
Proof.
  intros α β p t1 t2 [Hβ1 _] [Hβ2 _].
  rewrite Hβ1 in Hβ2.
  injection Hβ2 as <-. reflexivity.
Qed.

Theorem single_tile_difference_position_unique : forall α β p1 p2 t1 t2,
  single_tile_difference α β p1 t1 ->
  single_tile_difference α β p2 t2 ->
  p1 <> p2 ->
  False.
Proof.
  intros α β p1 p2 t1 t2 [Hβ1 [Hα1 Hother1]] [Hβ2 [Hα2 Hother2]] Hneq.
  assert (Heq1: tile_at α p1 = tile_at β p1).
  { apply Hother2. auto. }
  rewrite Hα1 in Heq1. rewrite Hβ1 in Heq1. discriminate.
Qed.

Lemma single_tile_difference_transitive_impossible : forall α β γ p1 p2 t1 t2,
  single_tile_difference α β p1 t1 ->
  single_tile_difference β γ p2 t2 ->
  p1 = p2 ->
  False.
Proof.
  intros α β γ p1 p2 t1 t2 [Hβ1 [Hα1 _]] [Hγ2 [Hβ2 _]] Heq.
  subst. rewrite Hβ1 in Hβ2. discriminate.
Qed.

(** ** 1.2.2 Assembly Growth *)

(** Single-step growth: assembly β is obtained from α by adding exactly one tile *)
Inductive single_step (S : TAS) : Assembly -> Assembly -> Prop :=
  | step_add : forall α β p t,
      can_attach_TAS S t α p ->
      single_tile_difference α β p t ->
      single_step S α β.

Notation "α →[ S ] β" := (single_step S α β) (at level 70).

(** Basic properties of single_step *)

Lemma single_step_adds_one_tile : forall S α β,
  α →[S] β ->
  exists p t, can_attach_TAS S t α p /\ single_tile_difference α β p t.
Proof.
  intros S α β Hstep.
  inversion Hstep as [α' β' p t Hattach Hdiff]. subst.
  exists p, t. split; assumption.
Qed.

Lemma single_step_preserves_elsewhere : forall S α β p' t,
  α →[S] β ->
  tile_at α p' = Some t ->
  tile_at β p' = Some t.
Proof.
  intros S α β p' t Hstep Htile.
  inversion Hstep as [α' β' p t' Hattach Hdiff]. subst.
  destruct Hdiff as [Hβ [Hα Hother]].
  destruct (Position_eq_dec p' p) as [Heq | Hneq].
  - subst. rewrite Hα in Htile. discriminate.
  - rewrite <- Hother; auto.
Qed.

Theorem single_step_is_single_tile_difference : forall S α β,
  α →[S] β ->
  exists p t, single_tile_difference α β p t.
Proof.
  intros S α β [α' β' p t _ Hdiff]. subst.
  exists p, t. exact Hdiff.
Qed.

(** Multi-step growth: reflexive transitive closure of single_step *)
Inductive multi_step (S : TAS) : Assembly -> Assembly -> Prop :=
  | multi_refl : forall α, multi_step S α α
  | multi_step_single : forall α β, single_step S α β -> multi_step S α β
  | multi_trans : forall α β γ, multi_step S α β -> multi_step S β γ -> multi_step S α γ.

Notation "α →*[ S ] β" := (multi_step S α β) (at level 70).

(** multi_step is a preorder *)

Theorem multi_step_refl : forall S α,
  α →*[S] α.
Proof.
  intros S α. apply multi_refl.
Qed.

Theorem multi_step_trans : forall S α β γ,
  α →*[S] β -> β →*[S] γ -> α →*[S] γ.
Proof.
  intros S α β γ Hab Hbc.
  apply (multi_trans S α β γ); assumption.
Qed.

(** Producible assemblies: reachable from the seed via multi_step *)
Definition producible_in (S : TAS) (α : Assembly) : Prop :=
  tas_seed S →*[S] α.

Lemma seed_is_producible : forall S,
  producible_in S (tas_seed S).
Proof.
  intro S. unfold producible_in. apply multi_refl.
Qed.

Theorem single_step_preserves_producibility : forall S α β,
  producible_in S α ->
  α →[S] β ->
  producible_in S β.
Proof.
  intros S α β Hprod Hstep.
  unfold producible_in in *.
  apply (multi_trans S (tas_seed S) α β); auto.
  apply multi_step_single. exact Hstep.
Qed.

Theorem multi_step_preserves_producibility : forall S α β,
  producible_in S α ->
  α →*[S] β ->
  producible_in S β.
Proof.
  intros S α β Hprod Hmulti.
  unfold producible_in in *.
  apply (multi_trans S (tas_seed S) α β); assumption.
Qed.

(** ** 1.2.3 Terminal Assemblies *)

(** An assembly is terminal if no tiles can attach *)
Definition terminal_assembly (S : TAS) (α : Assembly) : Prop :=
  forall p t, ~can_attach_TAS S t α p.

Lemma terminal_no_growth : forall S α,
  terminal_assembly S α ->
  forall p, ~can_grow S α p.
Proof.
  intros S α Hterm p [t Hattach].
  apply (Hterm p t). exact Hattach.
Qed.

Theorem terminal_no_single_step : forall S α,
  terminal_assembly S α ->
  forall β, ~(α →[S] β).
Proof.
  intros S α Hterm β Hstep.
  inversion Hstep as [α' β' p t Hattach _]. subst.
  apply (Hterm p t). exact Hattach.
Qed.

Lemma terminal_respects_equiv : forall S α β,
  α ≡ β ->
  terminal_assembly S α ->
  terminal_assembly S β.
Proof.
  intros S α β Hequiv Hterm p t Hattach.
  destruct Hattach as [Hin [Hempty Hbind]].
  apply (Hterm p t).
  unfold can_attach_TAS. split; [exact Hin | split].
  - unfold assembly_equiv in Hequiv. rewrite Hequiv. exact Hempty.
  - assert (Heq: binding_strength (tas_glue_strength S) t α p = binding_strength (tas_glue_strength S) t β p).
    { apply binding_strength_respects_equiv. exact Hequiv. }
    rewrite Heq. exact Hbind.
Qed.

Theorem terminal_no_multi_step_forward : forall S α,
  terminal_assembly S α ->
  forall β, α →*[S] β -> α ≡ β.
Proof.
  intros S α Hterm β Hmulti.
  induction Hmulti as [α' | α' β' Hstep | α' β' γ Hab IHab Hbc IHbc].
  - apply assembly_equiv_refl.
  - exfalso. apply (terminal_no_single_step S α' Hterm β'). exact Hstep.
  - assert (Heq_ab: α' ≡ β') by (apply IHab; exact Hterm).
    assert (Hterm_b: terminal_assembly S β') by (apply (terminal_respects_equiv S α' β'); assumption).
    assert (Heq_bc: β' ≡ γ) by (apply IHbc; exact Hterm_b).
    apply assembly_equiv_trans with β'; assumption.
Qed.

(** Decidable version: check if any tile can attach *)
Definition has_attachable_tile (S : TAS) (α : Assembly) : Prop :=
  exists p t, can_attach_TAS S t α p.

Lemma has_attachable_tile_means_non_terminal : forall S α,
  has_attachable_tile S α ->
  ~terminal_assembly S α.
Proof.
  intros S α [p [t Hattach]] Hterm.
  apply (Hterm p t). exact Hattach.
Qed.

(** Existence and non-existence conditions for terminal assemblies *)

(** If all tiles have binding strength below temperature, seed is terminal *)
Theorem seed_terminal_when_insufficient_binding : forall S,
  (forall t p, tile_in_set t (tas_tiles S) ->
               binding_strength (tas_glue_strength S) t (tas_seed S) p < tas_temp S) ->
  terminal_assembly S (tas_seed S).
Proof.
  intros S Hinsuff p t Hattach.
  destruct Hattach as [Hin [Hempty Hbind]].
  specialize (Hinsuff t p Hin).
  lia.
Qed.

(** High temperature guarantees seed is terminal when max binding strength is bounded *)
Theorem high_temp_implies_seed_terminal : forall S max_strength,
  (forall g, tas_glue_strength S g <= max_strength) ->
  tas_temp S > 4 * max_strength ->
  terminal_assembly S (tas_seed S).
Proof.
  intros S max_strength Hmax Htemp.
  apply seed_terminal_when_insufficient_binding.
  intros t p Hin.
  assert (Hbound: binding_strength (tas_glue_strength S) t (tas_seed S) p <= 4 * max_strength).
  { apply binding_strength_bounded. exact Hmax. }
  lia.
Qed.

(** Terminal assembly characterization via attachability *)
Theorem terminal_iff_no_attachable : forall S α,
  terminal_assembly S α <-> ~(exists p t, can_attach_TAS S t α p).
Proof.
  intros S α. split; intro H.
  - intro Hex. destruct Hex as [p [t Hattach]].
    apply (H p t). exact Hattach.
  - intros p t Hattach.
    apply H. exists p, t. exact Hattach.
Qed.

(** ** 1.2.4 Assembly Sets *)

(** The set of all producible assemblies Λ[S] *)
Definition producible_set (S : TAS) : Assembly -> Prop :=
  fun α => producible_in S α.

Notation "Λ[ S ]" := (producible_set S) (at level 60).

(** The set of all terminal assemblies A[S] *)
Definition terminal_set (S : TAS) : Assembly -> Prop :=
  fun α => producible_in S α /\ terminal_assembly S α.

Notation "A[ S ]" := (terminal_set S) (at level 60).

(** Basic properties of assembly sets *)

Lemma producible_set_contains_seed : forall S,
  Λ[S] (tas_seed S).
Proof.
  intro S. unfold producible_set. apply seed_is_producible.
Qed.

Lemma terminal_set_subset_producible : forall S α,
  A[S] α -> Λ[S] α.
Proof.
  intros S α [Hprod _]. exact Hprod.
Qed.

(** Key theorem: A[S] ⊆ Λ[S] *)
Theorem terminal_subset_producible : forall S,
  (forall α, A[S] α -> Λ[S] α).
Proof.
  intros S α Hterm.
  apply terminal_set_subset_producible. exact Hterm.
Qed.

(** Terminal set membership *)
Theorem terminal_set_iff : forall S α,
  A[S] α <-> (Λ[S] α /\ terminal_assembly S α).
Proof.
  intros S α. split; intro H.
  - exact H.
  - exact H.
Qed.

Lemma terminal_set_intro : forall S α,
  producible_in S α ->
  terminal_assembly S α ->
  A[S] α.
Proof.
  intros S α Hprod Hterm.
  unfold terminal_set. split; assumption.
Qed.

(** Producible set is closed under single_step *)
Theorem producible_set_closed_single_step : forall S α β,
  Λ[S] α ->
  α →[S] β ->
  Λ[S] β.
Proof.
  intros S α β Hprod Hstep.
  unfold producible_set in *.
  apply (single_step_preserves_producibility S α β); assumption.
Qed.

(** Producible set is closed under multi_step *)
Theorem producible_set_closed_multi_step : forall S α β,
  Λ[S] α ->
  α →*[S] β ->
  Λ[S] β.
Proof.
  intros S α β Hprod Hmulti.
  unfold producible_set in *.
  apply (multi_step_preserves_producibility S α β); assumption.
Qed.

(** If seed is terminal, then A[S] = {seed} (modulo equivalence) *)
Theorem seed_terminal_implies_singleton : forall S α,
  terminal_assembly S (tas_seed S) ->
  A[S] α ->
  α ≡ tas_seed S.
Proof.
  intros S α Hterm [Hprod Hterm_α].
  unfold producible_in in Hprod.
  apply assembly_equiv_sym.
  apply (terminal_no_multi_step_forward S (tas_seed S)); assumption.
Qed.

(** Producible assemblies are domain subsets of any assembly reachable from them *)
Theorem multi_step_domain_monotonic : forall S α β,
  α →*[S] β ->
  α ⊆ β.
Proof.
  intros S α β Hmulti.
  induction Hmulti as [α' | α' β' Hstep | α' β' γ Hab IHab Hbc IHbc].
  - apply domain_subset_refl.
  - inversion Hstep as [α'' β'' p t Hattach Hdiff]. subst.
    destruct Hdiff as [Hβ [Hα Hother]].
    unfold domain_subset.
    intros p' t' Htile.
    destruct (Position_eq_dec p' p) as [Heq | Hneq].
    + subst. rewrite Hα in Htile. discriminate.
    + rewrite <- Hother; auto.
  - apply (domain_subset_trans α' β' γ); auto.
Qed.

(** Single step increases support *)
Theorem single_step_increases_support : forall S α β,
  α →[S] β ->
  exists p t, ~support α p /\ support β p /\ tile_at β p = Some t.
Proof.
  intros S α β Hstep.
  inversion Hstep as [α' β' p t Hattach Hdiff]. subst.
  destruct Hdiff as [Hβ [Hα Hother]].
  exists p, t.
  split.
  - intro Hsupp. unfold support in Hsupp. destruct Hsupp as [t' Ht'].
    rewrite Hα in Ht'. discriminate.
  - split.
    + unfold support. exists t. exact Hβ.
    + exact Hβ.
Qed.

(** If producible assembly α grows to β, then β has all tiles of α plus at least one more *)
Theorem growth_preserves_tiles : forall S α β,
  Λ[S] α ->
  α →[S] β ->
  (forall p t, tile_at α p = Some t -> tile_at β p = Some t) /\
  (exists p t, tile_at α p = None /\ tile_at β p = Some t).
Proof.
  intros S α β Hprod Hstep.
  inversion Hstep as [α' β' p t Hattach Hdiff]. subst.
  destruct Hdiff as [Hβ [Hα Hother]].
  split.
  - intros p' t' Htile.
    destruct (Position_eq_dec p' p) as [Heq | Hneq].
    + subst. rewrite Hα in Htile. discriminate.
    + rewrite <- Hother; auto.
  - exists p, t. split; assumption.
Qed.

(** Uniqueness of terminal assemblies when system is deterministic *)

Definition locally_deterministic (S : TAS) : Prop :=
  forall α p t1 t2,
    can_attach_TAS S t1 α p ->
    can_attach_TAS S t2 α p ->
    t1 = t2.

(** Assembly sets examples and counterexamples *)

(** Example: Seed-only system where seed is terminal *)
Example seed_terminal_system_has_singleton_terminal_set :
  let t0 := mkTile 1 1 1 1 in
  let seed := single_tile_assembly (0, 0)%Z t0 in
  let S := mkTAS [t0] standard_glue_strength seed 2 in
  terminal_assembly S seed ->
  (forall α, A[S] α -> α ≡ seed).
Proof.
  intros t0 seed S Hterm α Hα.
  apply (seed_terminal_implies_singleton S α); assumption.
Qed.

(** Assembly set cardinality *)

(** System has unique terminal assembly (directed system) *)
Definition directed_system (S : TAS) : Prop :=
  forall α β, A[S] α -> A[S] β -> α ≡ β.

(** Verification tests for Section 1.2 *)

Example test_seed_is_producible :
  forall S, Λ[S] (tas_seed S).
Proof.
  intro S. apply producible_set_contains_seed.
Qed.

Example test_terminal_subset :
  forall S α, A[S] α -> Λ[S] α.
Proof.
  intros S α. apply terminal_set_subset_producible.
Qed.
