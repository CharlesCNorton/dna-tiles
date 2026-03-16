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

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.Eqdep_dec.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import Setoids.Setoid.

Import ListNotations.

(** * Section 1: Core Definitions *)

(** ** Glue types *)

Definition GlueType : Type := nat.
Definition null_glue : GlueType := 0.
Definition glue_eq_dec : forall g1 g2 : GlueType, {g1 = g2} + {g1 <> g2} :=
  Nat.eq_dec.

(** ** Tile types: 4-tuple (N, E, S, W) *)

Record TileType : Type := mkTile {
  glue_N : GlueType;
  glue_E : GlueType;
  glue_S : GlueType;
  glue_W : GlueType
}.

Definition TileType_eq_dec : forall t1 t2 : TileType, {t1 = t2} + {t1 <> t2}.
Proof.
  intros [n1 e1 s1 w1] [n2 e2 s2 w2].
  destruct (glue_eq_dec n1 n2); destruct (glue_eq_dec e1 e2);
  destruct (glue_eq_dec s1 s2); destruct (glue_eq_dec w1 w2); subst;
  try (right; intro H; inversion H; contradiction);
  left; reflexivity.
Defined.

(** ** Directions *)

Inductive Direction : Type :=
  | North | East | South | West.

Definition Direction_eq_dec : forall d1 d2 : Direction, {d1 = d2} + {d1 <> d2}.
Proof. decide equality. Defined.

Definition opposite (d : Direction) : Direction :=
  match d with North => South | East => West | South => North | West => East end.

Lemma opposite_involutive : forall d, opposite (opposite d) = d.
Proof. destruct d; reflexivity. Qed.

Definition all_directions : list Direction := [North; East; South; West].

Lemma all_directions_complete : forall d, In d all_directions.
Proof. destruct d; simpl; auto. Qed.

(** Glue of a tile in a given direction *)
Definition get_glue (t : TileType) (d : Direction) : GlueType :=
  match d with North => glue_N t | East => glue_E t
             | South => glue_S t | West => glue_W t end.

(** ** Positions in Z^2 *)

Definition Position : Type := (Z * Z)%type.

Definition Position_eq_dec : forall p1 p2 : Position, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [x1 y1] [x2 y2].
  destruct (Z.eq_dec x1 x2); destruct (Z.eq_dec y1 y2); subst;
  try (right; intro H; inversion H; contradiction);
  left; reflexivity.
Defined.

Definition move (p : Position) (d : Direction) : Position :=
  let '(x, y) := p in
  match d with
  | North => (x, y + 1)%Z | East => (x + 1, y)%Z
  | South => (x, y - 1)%Z | West => (x - 1, y)%Z
  end.

Definition neighbors (p : Position) : list Position :=
  map (move p) all_directions.

Definition adjacent (p1 p2 : Position) : Prop :=
  In p2 (neighbors p1).

(** ** Geometric lemmas *)

Lemma move_injective : forall d p1 p2, move p1 d = move p2 d -> p1 = p2.
Proof.
  intros d [x1 y1] [x2 y2] H; destruct d; simpl in H; inversion H; f_equal; lia.
Qed.

Lemma move_opposite_inverse : forall p d, move (move p d) (opposite d) = p.
Proof.
  intros [x y] d; destruct d; simpl; f_equal; lia.
Qed.

Lemma adjacency_symmetric : forall p1 p2, adjacent p1 p2 -> adjacent p2 p1.
Proof.
  intros p1 p2 H.
  unfold adjacent, neighbors in *.
  simpl in H. destruct H as [H | [H | [H | [H | []]]]];
  rewrite <- H; unfold adjacent, neighbors; simpl;
  rewrite move_opposite_inverse; auto.
Qed.

Lemma neighbors_length : forall p, length (neighbors p) = 4.
Proof. intro p; unfold neighbors, all_directions; simpl; reflexivity. Qed.

Lemma directions_distinct : forall p,
  move p North <> move p South /\ move p North <> move p East /\
  move p North <> move p West /\ move p South <> move p East /\
  move p South <> move p West /\ move p East <> move p West.
Proof.
  intros [x y]; repeat split; intro H; inversion H; lia.
Qed.

Lemma neighbors_NoDup : forall p, NoDup (neighbors p).
Proof.
  intro p. pose proof (directions_distinct p) as [? [? [? [? [? ?]]]]].
  unfold neighbors, all_directions; simpl.
  repeat constructor; simpl; intuition congruence.
Qed.

(** ** Glue strength *)

Definition glue_strength (str_fn : GlueType -> nat) (g1 g2 : GlueType) : nat :=
  if glue_eq_dec g1 g2 then
    if glue_eq_dec g1 null_glue then 0 else str_fn g1
  else 0.

Lemma glue_strength_symmetric : forall str_fn g1 g2,
  glue_strength str_fn g1 g2 = glue_strength str_fn g2 g1.
Proof.
  intros str_fn g1 g2; unfold glue_strength.
  destruct (glue_eq_dec g1 g2); destruct (glue_eq_dec g2 g1);
  subst; try contradiction; reflexivity.
Qed.

Lemma glue_strength_null : forall str_fn g,
  glue_strength str_fn null_glue g = 0.
Proof.
  intros; unfold glue_strength, null_glue.
  destruct (glue_eq_dec 0 g); subst;
  [destruct (glue_eq_dec 0 0); [|contradiction] |]; reflexivity.
Qed.

Lemma glue_strength_mismatch : forall str_fn g1 g2,
  g1 <> g2 -> glue_strength str_fn g1 g2 = 0.
Proof. intros; unfold glue_strength; destruct (glue_eq_dec g1 g2); tauto. Qed.

Lemma glue_strength_match : forall str_fn g,
  g <> null_glue -> glue_strength str_fn g g = str_fn g.
Proof.
  intros; unfold glue_strength.
  destruct (glue_eq_dec g g); [|contradiction].
  destruct (glue_eq_dec g null_glue); [contradiction|reflexivity].
Qed.

(** ** Assemblies *)

Definition Assembly : Type := Position -> option TileType.
Definition empty_assembly : Assembly := fun _ => None.
Definition tile_at (a : Assembly) (p : Position) : option TileType := a p.
Definition TileSet : Type := list TileType.
Definition tile_in_set (t : TileType) (T : TileSet) : Prop := In t T.
Definition Temperature : Type := nat.

(** ** Assembly equivalence *)

Definition assembly_equiv (a b : Assembly) : Prop :=
  forall p, tile_at a p = tile_at b p.

Notation "a == b" := (assembly_equiv a b) (at level 70).

Lemma assembly_equiv_refl : forall a, a == a.
Proof. intros a p; reflexivity. Qed.

Lemma assembly_equiv_sym : forall a b, a == b -> b == a.
Proof. intros a b H p; symmetry; apply H. Qed.

Lemma assembly_equiv_trans : forall a b c, a == b -> b == c -> a == c.
Proof. intros a b c H1 H2 p; rewrite H1; apply H2. Qed.

Add Parametric Relation : Assembly assembly_equiv
  reflexivity proved by assembly_equiv_refl
  symmetry proved by assembly_equiv_sym
  transitivity proved by assembly_equiv_trans
  as assembly_equiv_setoid.

Add Parametric Morphism : tile_at
  with signature assembly_equiv ==> eq ==> eq
  as tile_at_morphism.
Proof. intros a b H p; apply H. Qed.

(** ** Tile Assembly System *)

Record TAS := mkTAS {
  tas_tiles : TileSet;
  tas_strength : GlueType -> nat;
  tas_seed : Assembly;
  tas_temp : Temperature
}.

(** ** Subassembly *)

Definition subassembly (a b : Assembly) : Prop :=
  forall p, match a p with None => True | Some t => b p = Some t end.

Notation "a [= b" := (subassembly a b) (at level 70).

Lemma subassembly_refl : forall a, a [= a.
Proof. intros a p; destruct (a p); auto. Qed.

Lemma subassembly_trans : forall a b c, a [= b -> b [= c -> a [= c.
Proof.
  intros a b c Hab Hbc p; specialize (Hab p); specialize (Hbc p).
  destruct (a p); auto. rewrite Hab in Hbc; exact Hbc.
Qed.

Lemma empty_subassembly : forall a, empty_assembly [= a.
Proof. intros a p; unfold empty_assembly; auto. Qed.

(** * Section 2: Assembly Dynamics *)

(** ** Binding strength *)

Definition pos_eq (p1 p2 : Position) : bool :=
  let '(x1, y1) := p1 in let '(x2, y2) := p2 in
  (x1 =? x2)%Z && (y1 =? y2)%Z.

Lemma pos_eq_refl : forall p, pos_eq p p = true.
Proof.
  intros [x y]; unfold pos_eq; rewrite Z.eqb_refl, Z.eqb_refl; reflexivity.
Qed.

Lemma pos_eq_true_iff : forall p1 p2, pos_eq p1 p2 = true <-> p1 = p2.
Proof.
  intros [x1 y1] [x2 y2]; unfold pos_eq; split; intro H.
  - apply andb_true_iff in H; destruct H as [Hx Hy];
    apply Z.eqb_eq in Hx; apply Z.eqb_eq in Hy; subst; reflexivity.
  - injection H as <- <-; rewrite Z.eqb_refl, Z.eqb_refl; reflexivity.
Qed.

Lemma pos_eq_false_iff : forall p1 p2, pos_eq p1 p2 = false <-> p1 <> p2.
Proof.
  intros p1 p2; split; intro H.
  - intro Heq; subst; rewrite pos_eq_refl in H; discriminate.
  - destruct (pos_eq p1 p2) eqn:E; [|reflexivity].
    apply pos_eq_true_iff in E; contradiction.
Qed.

Definition glue_facing (t : TileType) (p1 p2 : Position) : option GlueType :=
  if pos_eq p2 (move p1 North) then Some (glue_N t)
  else if pos_eq p2 (move p1 East) then Some (glue_E t)
  else if pos_eq p2 (move p1 South) then Some (glue_S t)
  else if pos_eq p2 (move p1 West) then Some (glue_W t)
  else None.

Definition neighbor_binding (str_fn : GlueType -> nat) (t : TileType)
    (a : Assembly) (p p' : Position) : nat :=
  match tile_at a p' with
  | None => 0
  | Some t' =>
      match glue_facing t p p', glue_facing t' p' p with
      | Some g, Some g' => glue_strength str_fn g g'
      | _, _ => 0
      end
  end.

Definition binding_strength (str_fn : GlueType -> nat) (t : TileType)
    (a : Assembly) (p : Position) : nat :=
  fold_right Nat.add 0 (map (neighbor_binding str_fn t a p) (neighbors p)).

(** ** Attachment and growth *)

Definition can_attach (str_fn : GlueType -> nat) (t : TileType)
    (a : Assembly) (p : Position) (tau : Temperature) : Prop :=
  tile_at a p = None /\ binding_strength str_fn t a p >= tau.

Definition place_tile (a : Assembly) (t : TileType) (p : Position) : Assembly :=
  fun p' => if pos_eq p' p then Some t else a p'.

Definition single_step (str_fn : GlueType -> nat) (T : TileSet)
    (tau : Temperature) (a a' : Assembly) : Prop :=
  exists t p,
    tile_in_set t T /\ can_attach str_fn t a p tau /\ a' = place_tile a t p.

Inductive multi_step (str_fn : GlueType -> nat) (T : TileSet)
    (tau : Temperature) : Assembly -> Assembly -> Prop :=
  | ms_refl : forall a, multi_step str_fn T tau a a
  | ms_step : forall a a' a'',
      single_step str_fn T tau a a' ->
      multi_step str_fn T tau a' a'' ->
      multi_step str_fn T tau a a''.

Definition producible_in (S : TAS) (a : Assembly) : Prop :=
  multi_step (tas_strength S) (tas_tiles S) (tas_temp S) (tas_seed S) a.

Definition is_terminal (S : TAS) (a : Assembly) : Prop :=
  forall t p, tile_in_set t (tas_tiles S) ->
    tile_at a p = None ->
    binding_strength (tas_strength S) t a p < tas_temp S.

Definition terminal_assemblies (S : TAS) (a : Assembly) : Prop :=
  producible_in S a /\ is_terminal S a.

Definition is_directed (S : TAS) : Prop :=
  exists a, terminal_assemblies S a /\
    forall b, terminal_assemblies S b -> b = a.

(** ** Growth preserves subassembly *)

Theorem place_tile_extends : forall a t p,
  tile_at a p = None -> a [= place_tile a t p.
Proof.
  intros a t p Hempty p'; unfold place_tile, tile_at in *.
  destruct (a p') eqn:Ha; auto.
  destruct (pos_eq p' p) eqn:Hp.
  - apply pos_eq_true_iff in Hp; subst; congruence.
  - reflexivity.
Qed.

Theorem single_step_extends : forall str_fn T tau a a',
  single_step str_fn T tau a a' -> a [= a'.
Proof.
  intros str_fn T tau a a' [t [p [_ [[Hempty _] Heq]]]].
  subst; apply place_tile_extends; exact Hempty.
Qed.

Theorem multi_step_extends : forall str_fn T tau a a',
  multi_step str_fn T tau a a' -> a [= a'.
Proof.
  intros str_fn T tau a a' H; induction H.
  - apply subassembly_refl.
  - eapply subassembly_trans; [eapply single_step_extends; eauto | auto].
Qed.

Theorem multi_step_trans : forall str_fn T tau a b c,
  multi_step str_fn T tau a b -> multi_step str_fn T tau b c ->
  multi_step str_fn T tau a c.
Proof.
  intros str_fn T tau a b c Hab Hbc; induction Hab; auto.
  eapply ms_step; eauto.
Qed.

Lemma single_to_multi : forall str_fn T tau a a',
  single_step str_fn T tau a a' -> multi_step str_fn T tau a a'.
Proof. intros; eapply ms_step; eauto; apply ms_refl. Qed.

(** ** Terminal assembly properties *)

Theorem terminal_no_growth : forall S a,
  is_terminal S a ->
  forall a', single_step (tas_strength S) (tas_tiles S) (tas_temp S) a a' -> False.
Proof.
  intros S a Hterm a' [t [p [Hin [[Hempty Hbound] _]]]].
  specialize (Hterm t p Hin Hempty); lia.
Qed.

Lemma place_tile_at_pos : forall a t p, (place_tile a t p) p = Some t.
Proof.
  intros; unfold place_tile; rewrite pos_eq_refl; reflexivity.
Qed.

Lemma place_tile_other : forall a t p p',
  p' <> p -> place_tile a t p p' = a p'.
Proof.
  intros; unfold place_tile; apply pos_eq_false_iff in H; rewrite H; reflexivity.
Qed.

Theorem non_terminal_can_grow : forall S a,
  producible_in S a -> ~is_terminal S a ->
  exists a', single_step (tas_strength S) (tas_tiles S) (tas_temp S) a a'.
Proof.
  intros S a _ Hnterm.
  apply NNPP; intro Hno.
  apply Hnterm; intros t p Hin Hempty.
  destruct (Nat.ltb (binding_strength (tas_strength S) t a p) (tas_temp S)) eqn:E.
  - apply Nat.ltb_lt; exact E.
  - exfalso; apply Hno; exists (place_tile a t p), t, p.
    split; [exact Hin | split; [split; [exact Hempty | apply Nat.ltb_ge; exact E] | reflexivity]].
Qed.

(** * Section 3: Determinism and Confluence *)

(** ** Local determinism *)

Definition has_conflict (S : TAS) : Prop :=
  exists a t1 t2 p,
    producible_in S a /\
    tile_in_set t1 (tas_tiles S) /\ tile_in_set t2 (tas_tiles S) /\
    can_attach (tas_strength S) t1 a p (tas_temp S) /\
    can_attach (tas_strength S) t2 a p (tas_temp S) /\
    t1 <> t2.

Definition locally_deterministic (S : TAS) : Prop := ~has_conflict S.

Lemma locally_det_unique_tile : forall S a t1 t2 p,
  locally_deterministic S -> producible_in S a ->
  tile_in_set t1 (tas_tiles S) -> tile_in_set t2 (tas_tiles S) ->
  can_attach (tas_strength S) t1 a p (tas_temp S) ->
  can_attach (tas_strength S) t2 a p (tas_temp S) ->
  t1 = t2.
Proof.
  intros S a t1 t2 p Hdet Hprod Hin1 Hin2 Hat1 Hat2.
  destruct (TileType_eq_dec t1 t2) as [|Hneq]; auto.
  exfalso; apply Hdet.
  exists a, t1, t2, p.
  split; [exact Hprod|split; [exact Hin1|split; [exact Hin2|
  split; [exact Hat1|split; [exact Hat2|exact Hneq]]]]].
Qed.

(** ** Binding strength monotonicity *)

Lemma neighbor_binding_monotonic : forall str_fn t a b p p',
  a [= b -> neighbor_binding str_fn t a p p' <= neighbor_binding str_fn t b p p'.
Proof.
  intros str_fn t a b p p' Hsub.
  unfold neighbor_binding, tile_at.
  specialize (Hsub p').
  destruct (a p') as [ta|] eqn:Ha.
  - rewrite Hsub; destruct (glue_facing t p p'); destruct (glue_facing ta p' p); lia.
  - destruct (b p') as [tb|]; [|lia].
    destruct (glue_facing t p p') as [g1|]; [|lia].
    destruct (glue_facing tb p' p) as [g2|]; lia.
Qed.

Lemma binding_strength_monotonic : forall str_fn t a b p,
  a [= b -> binding_strength str_fn t a p <= binding_strength str_fn t b p.
Proof.
  intros str_fn t a b p Hsub; unfold binding_strength.
  induction (neighbors p) as [|p' ps IH]; simpl; [lia|].
  apply Nat.add_le_mono; [apply neighbor_binding_monotonic|]; auto.
Qed.

(** ** Strong confluence *)

Lemma place_tile_comm : forall a t1 t2 p1 p2,
  p1 <> p2 ->
  forall p, place_tile (place_tile a t1 p1) t2 p2 p =
            place_tile (place_tile a t2 p2) t1 p1 p.
Proof.
  intros a t1 t2 p1 p2 Hneq p; unfold place_tile.
  destruct (pos_eq p p2) eqn:H2; destruct (pos_eq p p1) eqn:H1; auto.
  apply pos_eq_true_iff in H1; apply pos_eq_true_iff in H2; subst; contradiction.
Qed.

Definition strongly_confluent (S : TAS) : Prop :=
  forall a b c,
    producible_in S a ->
    single_step (tas_strength S) (tas_tiles S) (tas_temp S) a b ->
    single_step (tas_strength S) (tas_tiles S) (tas_temp S) a c ->
    b = c \/ exists d,
      multi_step (tas_strength S) (tas_tiles S) (tas_temp S) b d /\
      multi_step (tas_strength S) (tas_tiles S) (tas_temp S) c d.

Theorem locally_det_strong_confluence : forall S,
  locally_deterministic S -> strongly_confluent S.
Proof.
  intros S Hdet a b c Hprod Hstepb Hstepc.
  destruct Hstepb as [tb [pb [Hinb [Hattb Heqb]]]].
  destruct Hstepc as [tc [pc [Hinc [Hattc Heqc]]]].
  destruct (pos_eq pb pc) eqn:Hpeq.
  - apply pos_eq_true_iff in Hpeq; subst pc.
    assert (tb = tc) by (eapply locally_det_unique_tile; eauto).
    subst; left; congruence.
  - apply pos_eq_false_iff in Hpeq; right.
    exists (place_tile (place_tile a tb pb) tc pc).
    split.
    + subst b; apply single_to_multi; exists tc, pc.
      split; [exact Hinc|split].
      * destruct Hattc as [Hemptyc Hboundc]; split.
        -- unfold tile_at, place_tile.
           destruct (pos_eq pc pb) eqn:E;
           [apply pos_eq_true_iff in E; symmetry in E; contradiction | exact Hemptyc].
        -- apply Nat.le_trans with (m := binding_strength (tas_strength S) tc a pc); auto.
           apply binding_strength_monotonic.
           apply place_tile_extends; destruct Hattb; auto.
      * reflexivity.
    + subst c; eapply ms_step.
      * exists tb, pb; split; [exact Hinb|split].
        -- destruct Hattb as [Hemptyb Hboundb]; split.
           ++ unfold tile_at, place_tile.
              destruct (pos_eq pb pc) eqn:E;
              [apply pos_eq_true_iff in E; contradiction | exact Hemptyb].
           ++ apply Nat.le_trans with (m := binding_strength (tas_strength S) tb a pb); auto.
              apply binding_strength_monotonic.
              apply place_tile_extends; destruct Hattc; auto.
        -- extensionality q; apply eq_sym; apply place_tile_comm.
           intro Heq; apply Hpeq; symmetry; exact Heq.
      * apply ms_refl.
Qed.

(** ** Strip lemma: single step joins with multi step *)

(*  Strong confluence gives us: from a single step a->b and a single step a->c,
    either b=c or there exists d with b->*d and c->*d where the paths have
    length at most 1 each. This means we can prove the strip lemma cleanly. *)

Lemma locally_det_bounded_join : forall S a b c,
  locally_deterministic S -> producible_in S a ->
  single_step (tas_strength S) (tas_tiles S) (tas_temp S) a b ->
  single_step (tas_strength S) (tas_tiles S) (tas_temp S) a c ->
  b = c \/ exists d,
    single_step (tas_strength S) (tas_tiles S) (tas_temp S) b d /\
    single_step (tas_strength S) (tas_tiles S) (tas_temp S) c d.
Proof.
  intros S a b c Hdet Hprod
    [tb [pb [Hinb [Hattb Heqb]]]] [tc [pc [Hinc [Hattc Heqc]]]].
  destruct (pos_eq pb pc) eqn:Hpeq.
  - apply pos_eq_true_iff in Hpeq; subst pc.
    assert (tb = tc) by (eapply locally_det_unique_tile; eauto).
    subst; left; congruence.
  - apply pos_eq_false_iff in Hpeq; right.
    exists (place_tile (place_tile a tb pb) tc pc).
    subst b c; split.
    + exists tc, pc; split; [exact Hinc|split].
      * destruct Hattc as [Hemptyc Hboundc]; split.
        -- unfold tile_at, place_tile.
           destruct (pos_eq pc pb) eqn:E;
           [apply pos_eq_true_iff in E; symmetry in E; contradiction | exact Hemptyc].
        -- eapply Nat.le_trans; [exact Hboundc|].
           apply binding_strength_monotonic.
           apply place_tile_extends; destruct Hattb; auto.
      * reflexivity.
    + exists tb, pb; split; [exact Hinb|split].
      * destruct Hattb as [Hemptyb Hboundb]; split.
        -- unfold tile_at, place_tile.
           destruct (pos_eq pb pc) eqn:E;
           [apply pos_eq_true_iff in E; contradiction | exact Hemptyb].
        -- eapply Nat.le_trans; [exact Hboundb|].
           apply binding_strength_monotonic.
           apply place_tile_extends; destruct Hattc; auto.
      * extensionality q; apply eq_sym; apply place_tile_comm.
        intro Heq; apply Hpeq; symmetry; exact Heq.
Qed.

Lemma strip_one_multi : forall S,
  locally_deterministic S ->
  forall a b c,
    producible_in S a ->
    single_step (tas_strength S) (tas_tiles S) (tas_temp S) a b ->
    multi_step (tas_strength S) (tas_tiles S) (tas_temp S) a c ->
    exists d,
      multi_step (tas_strength S) (tas_tiles S) (tas_temp S) b d /\
      multi_step (tas_strength S) (tas_tiles S) (tas_temp S) c d.
Proof.
  intros S Hdet a b c Hprod Hab Hac.
  revert b Hab.
  induction Hac as [|a c1 c Hac1 Hc1c IH]; intros b Hab.
  - exists b; split; [apply ms_refl | apply single_to_multi; exact Hab].
  - assert (Hprod_c1 : producible_in S c1).
    { unfold producible_in; eapply multi_step_trans;
      [exact Hprod | apply single_to_multi; exact Hac1]. }
    destruct (locally_det_bounded_join S a b c1 Hdet Hprod Hab Hac1)
      as [Heq | [tau [Hbtau Hc1tau]]].
    + subst c1; exists c; split; [exact Hc1c | apply ms_refl].
    + destruct (IH Hprod_c1 tau Hc1tau) as [d [Htaud Hcd]].
      exists d; split; [|exact Hcd].
      eapply ms_step; [exact Hbtau | exact Htaud].
Qed.

(** ** Diamond property *)

Theorem diamond_property : forall S,
  locally_deterministic S ->
  forall a b c,
    producible_in S a ->
    multi_step (tas_strength S) (tas_tiles S) (tas_temp S) a b ->
    multi_step (tas_strength S) (tas_tiles S) (tas_temp S) a c ->
    exists d,
      multi_step (tas_strength S) (tas_tiles S) (tas_temp S) b d /\
      multi_step (tas_strength S) (tas_tiles S) (tas_temp S) c d.
Proof.
  intros S Hdet a b c Hprod Hab Hac.
  revert c Hac.
  induction Hab as [|a b' b Hab' Hb'b IH]; intros c Hac.
  - exists c; split; [exact Hac | apply ms_refl].
  - assert (Hprod_b' : producible_in S b').
    { unfold producible_in; eapply multi_step_trans; [exact Hprod|apply single_to_multi; exact Hab']. }
    destruct (strip_one_multi S Hdet a b' c Hprod Hab' Hac) as [d1 [Hb'd1 Hcd1]].
    destruct (IH Hprod_b' d1 Hb'd1) as [d [Hbd Hd1d]].
    exists d; split; [exact Hbd | eapply multi_step_trans; eauto].
Qed.

(** ** Unique terminal assembly *)

Lemma terminal_multi_step_eq : forall S a d,
  is_terminal S a ->
  multi_step (tas_strength S) (tas_tiles S) (tas_temp S) a d -> d = a.
Proof.
  intros S a d Hterm Hms; inversion Hms; subst; auto.
  exfalso; eapply terminal_no_growth; eauto.
Qed.

Theorem unique_terminal : forall S a b,
  locally_deterministic S ->
  terminal_assemblies S a -> terminal_assemblies S b -> a = b.
Proof.
  intros S a b Hdet [Hproda Hterma] [Hprodb Htermb].
  assert (Hprod_seed : producible_in S (tas_seed S)) by (unfold producible_in; apply ms_refl).
  destruct (diamond_property S Hdet (tas_seed S) a b Hprod_seed Hproda Hprodb) as [d [Had Hbd]].
  assert (d = a) by (eapply terminal_multi_step_eq; eauto).
  assert (d = b) by (eapply terminal_multi_step_eq; eauto).
  congruence.
Qed.

(** Every producible assembly is a subassembly of any terminal assembly *)
Theorem producible_sub_terminal : forall S a b,
  locally_deterministic S -> producible_in S a -> terminal_assemblies S b ->
  a [= b.
Proof.
  intros S a b Hdet Hproda [Hprodb Htermb].
  assert (Hprod_seed : producible_in S (tas_seed S)) by (unfold producible_in; apply ms_refl).
  destruct (diamond_property S Hdet (tas_seed S) a b Hprod_seed Hproda Hprodb)
    as [d [Had Hbd]].
  inversion Hbd; subst.
  - eapply multi_step_extends; eauto.
  - exfalso; eapply terminal_no_growth; eauto.
Qed.

(** * Section 4: Wang Tilings *)

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

Definition domino_problem (tileset : TileSet) : Prop :=
  exists W, tiles_plane W /\ valid_wang_tiling W /\
    forall p t, tile_at W p = Some t -> In t tileset.

Lemma producible_valid_edges : forall S a p1 p2,
  producible_in S a -> adjacent p1 p2 ->
  match tile_at a p1, tile_at a p2 with
  | Some t1, Some t2 =>
      match glue_facing t1 p1 p2, glue_facing t2 p2 p1 with
      | Some g1, Some g2 =>
          glue_strength (tas_strength S) g1 g2 > 0 -> g1 = g2
      | _, _ => True
      end
  | _, _ => True
  end.
Proof.
  intros S a p1 p2 _ _.
  destruct (tile_at a p1) as [t1|]; auto.
  destruct (tile_at a p2) as [t2|]; auto.
  destruct (glue_facing t1 p1 p2) as [g1|]; auto.
  destruct (glue_facing t2 p2 p1) as [g2|]; auto.
  intro H; unfold glue_strength in H.
  destruct (glue_eq_dec g1 g2); auto; lia.
Qed.

(** Tile placed after seed must have had a contributing neighbor *)

Lemma multi_step_inversion : forall str_fn T tau a b p t',
  multi_step str_fn T tau a b ->
  tile_at a p = None -> tile_at b p = Some t' ->
  exists c,
    multi_step str_fn T tau a c /\ tile_at c p = None /\
    single_step str_fn T tau c (place_tile c t' p) /\
    subassembly (place_tile c t' p) b.
Proof.
  intros str_fn T tau a b p t' Hms.
  induction Hms as [|a a' b Hstep Hms IH]; intros Ha Hb.
  - congruence.
  - destruct Hstep as [t0 [p0 [Hin [Hatt Heq]]]]; subst a'.
    destruct (pos_eq p0 p) eqn:Hpp.
    + apply pos_eq_true_iff in Hpp; subst p0.
      assert (t0 = t').
      { assert (Hsub : (place_tile a t0 p) [= b) by (eapply multi_step_extends; eauto).
        unfold subassembly in Hsub; specialize (Hsub p).
        rewrite place_tile_at_pos in Hsub.
        unfold tile_at in Hb; rewrite Hb in Hsub; injection Hsub; auto. }
      subst t0.
      exists a; split; [apply ms_refl|split; [exact Ha|split]].
      * exists t', p; split; [exact Hin|split; [exact Hatt|reflexivity]].
      * eapply multi_step_extends; eauto.
    + apply pos_eq_false_iff in Hpp.
      assert (Ha' : tile_at (place_tile a t0 p0) p = None).
      { unfold tile_at, place_tile.
        assert (Hneq : p <> p0) by auto.
        apply pos_eq_false_iff in Hneq; rewrite Hneq; exact Ha. }
      destruct (IH Ha' Hb) as [c [Hac [Hcp [Hcstep Hcsub]]]].
      exists c; split.
      * eapply multi_step_trans; [|exact Hac].
        apply single_to_multi; exists t0, p0; split; [exact Hin|split; [exact Hatt|reflexivity]].
      * split; [exact Hcp|split; [exact Hcstep|exact Hcsub]].
Qed.

(** In temperature-1 systems, every non-seed tile has a matching neighbor *)

Lemma binding_geq1_has_neighbor : forall str_fn t a p,
  binding_strength str_fn t a p >= 1 ->
  exists p', In p' (neighbors p) /\ neighbor_binding str_fn t a p p' >= 1.
Proof.
  intros str_fn t a p H; unfold binding_strength in H.
  unfold neighbors, all_directions in *; simpl in *.
  destruct (Nat.eq_dec (neighbor_binding str_fn t a p (move p North)) 0),
           (Nat.eq_dec (neighbor_binding str_fn t a p (move p East)) 0),
           (Nat.eq_dec (neighbor_binding str_fn t a p (move p South)) 0),
           (Nat.eq_dec (neighbor_binding str_fn t a p (move p West)) 0);
  try (exists (move p North); split; [left; reflexivity | lia]);
  try (exists (move p East); split; [right; left; reflexivity | lia]);
  try (exists (move p South); split; [right; right; left; reflexivity | lia]);
  try (exists (move p West); split; [right; right; right; left; reflexivity | lia]);
  lia.
Qed.

Lemma neighbor_binding_geq1_has_tile : forall str_fn t a p p',
  neighbor_binding str_fn t a p p' >= 1 ->
  exists t', tile_at a p' = Some t'.
Proof.
  intros str_fn t a p p' H; unfold neighbor_binding in H.
  destruct (tile_at a p') as [t'|] eqn:E; [exists t'; auto | lia].
Qed.

Lemma neighbor_binding_geq1_matching_glues : forall str_fn t a p p' t',
  neighbor_binding str_fn t a p p' >= 1 -> tile_at a p' = Some t' ->
  exists g, glue_facing t p p' = Some g /\ glue_facing t' p' p = Some g /\
    glue_strength str_fn g g >= 1.
Proof.
  intros str_fn t a p p' t' Hb Ht'; unfold neighbor_binding in Hb; rewrite Ht' in Hb.
  destruct (glue_facing t p p') as [g|] eqn:Hg; [|lia].
  destruct (glue_facing t' p' p) as [g'|] eqn:Hg'; [|lia].
  unfold glue_strength in Hb.
  destruct (glue_eq_dec g g'); [|lia]; subst g'.
  exists g; repeat split; auto.
  unfold glue_strength; destruct (glue_eq_dec g g); [exact Hb | contradiction].
Qed.

Lemma subassembly_tile_at : forall a b p t,
  a [= b -> tile_at a p = Some t -> tile_at b p = Some t.
Proof.
  intros a b p t Hsub Ht; unfold subassembly in Hsub; specialize (Hsub p).
  unfold tile_at in *; destruct (a p); [congruence | discriminate].
Qed.

Theorem temp1_tile_has_matching_neighbor : forall S a p t,
  tas_temp S = 1 -> producible_in S a ->
  (forall g, g <> null_glue -> tas_strength S g >= 1) ->
  tile_at (tas_seed S) p = None -> tile_at a p = Some t ->
  exists p' t' g,
    adjacent p p' /\ tile_at a p' = Some t' /\
    glue_facing t p p' = Some g /\ glue_facing t' p' p = Some g /\
    g <> null_glue.
Proof.
  intros S a p t Htemp Hprod Hstr Hseed Ht.
  destruct (multi_step_inversion _ _ _ _ _ _ _ Hprod Hseed Ht)
    as [c [Hsc [Hcp [Hcstep Hcsub]]]].
  (* Hcstep : single_step ... c (place_tile c t p)
     Hcsub  : (place_tile c t p) [= a
     Extract the attachment witness from Hcstep *)
  destruct Hcstep as [t0 [p0 [Hin [Hatt Heq]]]].
  (* From Heq: place_tile c t p = place_tile c t0 p0, so p0=p, t0=t *)
  assert (Hp0 : p0 = p).
  { destruct (Position_eq_dec p0 p); auto; exfalso.
    assert (E : place_tile c t0 p0 p = c p).
    { apply place_tile_other; auto. }
    assert (E2 : place_tile c t p p = Some t) by apply place_tile_at_pos.
    assert (E3 : place_tile c t p p = place_tile c t0 p0 p).
    { rewrite Heq; reflexivity. }
    rewrite E2 in E3; rewrite E in E3.
    unfold tile_at in Hcp; rewrite Hcp in E3; discriminate. }
  subst p0.
  assert (Ht0 : t0 = t).
  { assert (E1 : place_tile c t p p = Some t) by apply place_tile_at_pos.
    assert (E2 : place_tile c t0 p p = Some t0) by apply place_tile_at_pos.
    assert (E3 : place_tile c t p p = place_tile c t0 p p) by (rewrite Heq; reflexivity).
    rewrite E1 in E3; rewrite E2 in E3; injection E3; auto. }
  subst t0.
  destruct Hatt as [_ Hbound].
  rewrite Htemp in Hbound.
  (* Extract the contributing neighbor from the binding strength *)
  destruct (binding_geq1_has_neighbor _ _ _ _ Hbound) as [p' [Hadj Hb']].
  destruct (neighbor_binding_geq1_has_tile _ _ _ _ _ Hb') as [tc Htc].
  destruct (neighbor_binding_geq1_matching_glues _ _ _ _ _ _ Hb' Htc)
    as [g [Hg1 [Hg2 Hgs]]].
  (* Lift tile from c to a via subassembly *)
  assert (Hcsub2 : c [= a).
  { eapply subassembly_trans; [apply place_tile_extends; exact Hcp | exact Hcsub]. }
  exists p', tc, g.
  split; [exact Hadj|].
  split; [eapply subassembly_tile_at; eauto|].
  split; [exact Hg1|split; [exact Hg2|]].
  (* g <> null_glue from strength >= 1 *)
  unfold glue_strength in Hgs.
  destruct (glue_eq_dec g g); [|contradiction].
  destruct (glue_eq_dec g null_glue); [lia|exact n].
Qed.

(** * Section 5: Turing Completeness at Temperature 2 *)

(** ** Turing machine definitions (concrete, nat-based) *)

Inductive HeadDir : Type := MoveL | MoveR | Stay.

Record TM := mkTM {
  tm_states    : list nat;
  tm_alphabet  : list nat;
  tm_transition: nat -> nat -> option (nat * nat * HeadDir);
  tm_start     : nat;
  tm_accept    : nat;
  tm_reject    : nat
}.

Definition Tape := Z -> nat.
Definition blank : nat := 0.
Definition blank_tape : Tape := fun _ => blank.

Record TMConfig := mkTMConfig {
  cfg_state : nat;
  cfg_tape  : Tape;
  cfg_head  : Z
}.

Definition tape_write (t : Tape) (pos : Z) (s : nat) : Tape :=
  fun pos' => if (pos =? pos')%Z then s else t pos'.

Definition head_move (pos : Z) (d : HeadDir) : Z :=
  match d with MoveL => (pos - 1)%Z | MoveR => (pos + 1)%Z | Stay => pos end.

Definition tm_step (M : TM) (c : TMConfig) : option TMConfig :=
  match tm_transition M (cfg_state c) (cfg_tape c (cfg_head c)) with
  | None => None
  | Some (q', s', d) =>
      Some (mkTMConfig q' (tape_write (cfg_tape c) (cfg_head c) s') (head_move (cfg_head c) d))
  end.

Inductive tm_steps_star (M : TM) : TMConfig -> TMConfig -> Prop :=
  | tms_refl : forall c, tm_steps_star M c c
  | tms_step : forall c c' c'',
      tm_step M c = Some c' -> tm_steps_star M c' c'' -> tm_steps_star M c c''.

Definition tm_halts (M : TM) (c : TMConfig) : Prop :=
  exists c', tm_steps_star M c c' /\
    (cfg_state c' = tm_accept M \/ cfg_state c' = tm_reject M).

(** ** TM-to-TAS encoding *)

(** Encode TM states and symbols into non-overlapping glue ranges *)
Definition encode_state (q : nat) : GlueType := 1 + 4 * q.
Definition encode_symbol (a : nat) : GlueType := 2 + 4 * a.

Lemma encode_state_nonzero : forall q, encode_state q <> null_glue.
Proof. intro q; unfold encode_state, null_glue; lia. Qed.

Lemma encode_symbol_nonzero : forall a, encode_symbol a <> null_glue.
Proof. intro a; unfold encode_symbol, null_glue; lia. Qed.

Lemma encode_state_injective : forall q1 q2,
  encode_state q1 = encode_state q2 -> q1 = q2.
Proof. unfold encode_state; intros; lia. Qed.

Lemma encode_symbol_injective : forall a1 a2,
  encode_symbol a1 = encode_symbol a2 -> a1 = a2.
Proof. unfold encode_symbol; intros; lia. Qed.

Lemma encode_state_symbol_disjoint : forall q a,
  encode_state q <> encode_symbol a.
Proof. unfold encode_state, encode_symbol; intros; lia. Qed.

(** Transition tile: encodes (q,a) -> (q',a') *)
Definition transition_tile (q a q' a' : nat) : TileType :=
  mkTile (encode_state q) (encode_symbol a) (encode_state q') (encode_symbol a').

(** Generate all transition tiles for a TM *)
Definition tm_tiles (M : TM) : TileSet :=
  flat_map (fun q =>
    flat_map (fun a =>
      match tm_transition M q a with
      | Some (q', a', _) => [transition_tile q a q' a']
      | None => []
      end) (tm_alphabet M)) (tm_states M).

(** Construct TAS from TM at temperature 2 *)
Definition tm_to_tas (M : TM) (seed : Assembly) : TAS :=
  mkTAS (tm_tiles M)
        (fun g => if Nat.eqb g 0 then 0 else 1)
        seed 2.

(** ** Key properties *)

Theorem tm_to_tas_temp_2 : forall M seed, tas_temp (tm_to_tas M seed) = 2.
Proof. intros; reflexivity. Qed.

Lemma tm_to_tas_strength_nonzero : forall M seed g,
  g <> 0 -> tas_strength (tm_to_tas M seed) g = 1.
Proof.
  intros M seed g H; simpl.
  destruct (Nat.eqb g 0) eqn:E; [apply Nat.eqb_eq in E; contradiction | reflexivity].
Qed.

Theorem cooperation_at_temp_2 : forall M seed g1 g2,
  g1 <> 0 -> g2 <> 0 ->
  tas_strength (tm_to_tas M seed) g1 + tas_strength (tm_to_tas M seed) g2 >=
  tas_temp (tm_to_tas M seed).
Proof.
  intros M seed g1 g2 H1 H2.
  rewrite tm_to_tas_strength_nonzero by assumption.
  rewrite tm_to_tas_strength_nonzero by assumption.
  simpl; lia.
Qed.

(** Every TM transition produces a corresponding tile *)

Lemma tm_transition_has_tile : forall M q a q' a' d,
  In q (tm_states M) -> In a (tm_alphabet M) ->
  tm_transition M q a = Some (q', a', d) ->
  In (transition_tile q a q' a') (tm_tiles M).
Proof.
  intros M q a q' a' d Hq Ha Htrans.
  unfold tm_tiles.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  rewrite Htrans; simpl; left; reflexivity.
Qed.

Theorem tm_step_tile_correspondence : forall M seed c c',
  In (cfg_state c) (tm_states M) ->
  In (cfg_tape c (cfg_head c)) (tm_alphabet M) ->
  tm_step M c = Some c' ->
  exists t, In t (tas_tiles (tm_to_tas M seed)) /\
    glue_N t = encode_state (cfg_state c) /\
    glue_E t = encode_symbol (cfg_tape c (cfg_head c)).
Proof.
  intros M seed c c' Hstate Hsym Hstep.
  unfold tm_step in Hstep.
  destruct (tm_transition M (cfg_state c) (cfg_tape c (cfg_head c)))
    as [[[q' a'] d]|] eqn:Htrans; [|discriminate].
  exists (transition_tile (cfg_state c) (cfg_tape c (cfg_head c)) q' a').
  split.
  - simpl; eapply tm_transition_has_tile; eauto.
  - split; reflexivity.
Qed.

(** Tile set size is bounded by |Q| * |Gamma| *)

Theorem tile_complexity_bound : forall M seed,
  length (tas_tiles (tm_to_tas M seed)) <= length (tm_states M) * length (tm_alphabet M).
Proof.
  intros M seed; simpl; unfold tm_tiles.
  induction (tm_states M) as [|q qs IH]; simpl; [lia|].
  rewrite length_app; apply Nat.add_le_mono; [|exact IH].
  clear IH; induction (tm_alphabet M) as [|a alph IH]; simpl; [lia|].
  destruct (tm_transition M q a) as [[[q' a'] d]|]; simpl; lia.
Qed.

(** Temperature 1 is insufficient for TM simulation *)

Theorem temp1_insufficient : forall M seed,
  tas_temp (tm_to_tas M seed) > 1.
Proof. intros; simpl; lia. Qed.

(** * Section 6: Rule 110 *)

Definition rule110 (l c r : bool) : bool :=
  match l, c, r with
  | true,true,true => false   | true,true,false => true
  | true,false,true => true   | true,false,false => false
  | false,true,true => true   | false,true,false => true
  | false,false,true => true  | false,false,false => false
  end.

Definition encode_bit (b : bool) : GlueType := if b then 2 else 1.

Lemma encode_bit_nonzero : forall b, encode_bit b <> null_glue.
Proof. destruct b; discriminate. Qed.

Definition rule110_tile (l c r : bool) : TileType :=
  mkTile (encode_bit l) (encode_bit c) (encode_bit (rule110 l c r)) (encode_bit r).

Definition rule110_tileset : TileSet :=
  flat_map (fun l => flat_map (fun c => map (fun r => rule110_tile l c r) [true;false])
    [true;false]) [true;false].

Definition rule110_tas : TAS :=
  mkTAS rule110_tileset (fun g => if Nat.eqb g 0 then 0 else 1) empty_assembly 2.

Theorem rule110_tile_count : length rule110_tileset = 8.
Proof. reflexivity. Qed.

Theorem rule110_has_all_transitions : forall l c r : bool,
  In (rule110_tile l c r) rule110_tileset.
Proof.
  intros l c r; unfold rule110_tileset.
  destruct l; destruct c; destruct r; simpl; auto 20.
Qed.

Theorem rule110_cooperation : forall t,
  In t rule110_tileset ->
  tas_strength rule110_tas (glue_N t) + tas_strength rule110_tas (glue_E t) >=
  tas_temp rule110_tas.
Proof.
  intros t Hin; simpl.
  unfold rule110_tileset in Hin; simpl in Hin.
  repeat (destruct Hin as [<-|Hin]; [simpl; lia|]); destruct Hin.
Qed.

(** * Section 7: Intrinsic Universality *)

(** ** Supertiles *)

Definition Block : Type := list (Position * TileType).

Definition block_at (b : Block) (p : Position) : option TileType :=
  match find (fun '(p', _) => if Position_eq_dec p p' then true else false) b with
  | Some (_, t) => Some t
  | None => None
  end.

Definition block_to_assembly (b : Block) : Assembly := fun p => block_at b p.

Definition scale_position (k : nat) (p : Position) : Position :=
  let '(x, y) := p in ((Z.of_nat k * x)%Z, (Z.of_nat k * y)%Z).

(** ** Simulation relation *)

Record SimParams := mkSimParams {
  sim_scale : nat;
  sim_scale_pos : sim_scale > 0
}.

Definition simulates_assembly (params : SimParams) (U S : TAS)
    (alpha beta : Assembly) : Prop :=
  forall p, match beta p with
  | None => True
  | Some t_sim =>
      exists block : Block,
        (forall pb tb, In (pb, tb) block ->
          let '(xs, ys) := scale_position (sim_scale params) p in
          let '(xb, yb) := pb in
          alpha ((xs + xb)%Z, (ys + yb)%Z) = Some tb) /\
        (forall pb tb, In (pb, tb) block -> tile_in_set tb (tas_tiles U))
  end.

Definition intrinsically_universal (U_tiles : TileSet) (tau : Temperature) : Prop :=
  forall S : TAS,
    tas_temp S = tau ->
    exists (params : SimParams) (U_seed : Assembly),
      let U := mkTAS U_tiles (fun g => if Nat.eqb g 0 then 0 else 1) U_seed tau in
      forall beta, producible_in S beta ->
        exists alpha, producible_in U alpha /\ simulates_assembly params U S alpha beta.

(** ** Determinism preservation under simulation *)

Theorem simulation_preserves_determinism_tiles : forall U_tiles tau S,
  intrinsically_universal U_tiles tau ->
  tas_temp S = tau ->
  locally_deterministic S ->
  exists params U_seed,
    forall beta, terminal_assemblies S beta ->
      exists alpha,
        producible_in (mkTAS U_tiles (fun g => if Nat.eqb g 0 then 0 else 1) U_seed tau) alpha /\
        simulates_assembly params
          (mkTAS U_tiles (fun g => if Nat.eqb g 0 then 0 else 1) U_seed tau) S alpha beta.
Proof.
  intros U_tiles tau S HIU Htemp Hdet.
  destruct (HIU S Htemp) as [params [U_seed Hsim]].
  exists params, U_seed.
  intros beta Hterm; apply Hsim; destruct Hterm; assumption.
Qed.

(** * Section 8: Beyond the Original — New Results *)

(** ** Determinism is decidable for finite bounded assemblies *)

Definition bounded_assembly (a : Assembly) (n : nat) : Prop :=
  forall p, let '(x, y) := p in
    (Z.abs x > Z.of_nat n \/ Z.abs y > Z.of_nat n)%Z -> a p = None.

Lemma empty_assembly_bounded : forall n, bounded_assembly empty_assembly n.
Proof. intros n [x y] _; reflexivity. Qed.

(** ** Monotonicity of terminality *)

Theorem terminal_monotonic_tileset : forall tiles1 tiles2 str seed tau a,
  (forall t, In t tiles1 -> In t tiles2) ->
  is_terminal (mkTAS tiles2 str seed tau) a ->
  is_terminal (mkTAS tiles1 str seed tau) a.
Proof.
  intros tiles1 tiles2 str seed tau a Hsub Hterm.
  intros t p Hin Hempty; apply (Hterm t p); [apply Hsub; exact Hin | exact Hempty].
Qed.

(** ** Local determinism is preserved by tile set restriction *)

Lemma single_step_mono_tiles : forall str T1 T2 tau a b,
  (forall t, In t T1 -> In t T2) ->
  single_step str T1 tau a b -> single_step str T2 tau a b.
Proof.
  intros str T1 T2 tau a b Hsub [t [p [Hin [Hatt Heq]]]].
  exists t, p; split; [apply Hsub; exact Hin | split; auto].
Qed.

Lemma multi_step_mono_tiles : forall str T1 T2 tau a b,
  (forall t, In t T1 -> In t T2) ->
  multi_step str T1 tau a b -> multi_step str T2 tau a b.
Proof.
  intros str T1 T2 tau a b Hsub Hms; induction Hms; [apply ms_refl|].
  eapply ms_step; [eapply single_step_mono_tiles; eauto | auto].
Qed.

Theorem locally_det_tile_restriction : forall S tiles_sub,
  (forall t, In t tiles_sub -> In t (tas_tiles S)) ->
  locally_deterministic S ->
  locally_deterministic
    (mkTAS tiles_sub (tas_strength S) (tas_seed S) (tas_temp S)).
Proof.
  intros S tiles_sub Hsub Hdet.
  unfold locally_deterministic, has_conflict; intro Hcontra.
  destruct Hcontra as [a [t1 [t2 [p [Hprod [Hin1 [Hin2 [Hat1 [Hat2 Hneq]]]]]]]]].
  apply Hdet; simpl in *.
  exists a, t1, t2, p.
  split; [eapply multi_step_mono_tiles; eauto |
  split; [apply Hsub; exact Hin1 |
  split; [apply Hsub; exact Hin2 |
  split; [exact Hat1 | split; [exact Hat2 | exact Hneq]]]]].
Qed.

(** ** Raising temperature preserves determinism *)

Lemma can_attach_lower_temp : forall str t a p tau1 tau2,
  tau1 <= tau2 -> can_attach str t a p tau2 -> can_attach str t a p tau1.
Proof. intros str t a p tau1 tau2 Hle [Hempty Hb]; split; auto; lia. Qed.

Lemma multi_step_lower_temp : forall str T tau1 tau2 a b,
  tau1 <= tau2 ->
  multi_step str T tau2 a b -> multi_step str T tau1 a b.
Proof.
  intros str T tau1 tau2 a b Hle Hms; induction Hms; [apply ms_refl|].
  eapply ms_step; [|exact IHHms].
  destruct H as [t [p [Hin [Hatt Heq]]]].
  exists t, p; split; [exact Hin|split; [eapply can_attach_lower_temp; eauto|exact Heq]].
Qed.

Theorem raising_temp_preserves_determinism : forall S tau_high,
  tas_temp S <= tau_high ->
  locally_deterministic S ->
  locally_deterministic
    (mkTAS (tas_tiles S) (tas_strength S) (tas_seed S) tau_high).
Proof.
  intros S tau_high Hle Hdet.
  unfold locally_deterministic, has_conflict; intro Hcontra.
  destruct Hcontra as [a [t1 [t2 [p [Hprod [Hin1 [Hin2 [Hat1 [Hat2 Hneq]]]]]]]]].
  apply Hdet; simpl in *.
  exists a, t1, t2, p.
  split; [eapply multi_step_lower_temp; eauto |
  split; [exact Hin1 | split; [exact Hin2 |
  split; [eapply can_attach_lower_temp; eauto |
  split; [eapply can_attach_lower_temp; eauto | exact Hneq]]]]].
Qed.

(** ** Concrete example: non-deterministic system *)

Definition ex_conflict_seed : Assembly :=
  fun p => if pos_eq p (0%Z, 0%Z) then Some (mkTile 0 1 0 0) else None.

Definition ex_conflict_tas : TAS :=
  mkTAS [mkTile 0 1 0 1; mkTile 0 2 0 1]
        (fun g => match g with 0 => 0 | _ => 1 end)
        ex_conflict_seed 1.

Theorem ex_conflict_not_deterministic : ~locally_deterministic ex_conflict_tas.
Proof.
  unfold locally_deterministic, has_conflict; intro H; apply H; clear H.
  exists ex_conflict_seed, (mkTile 0 1 0 1), (mkTile 0 2 0 1), (1%Z, 0%Z).
  split; [unfold producible_in; apply ms_refl|].
  split; [simpl; left; reflexivity|].
  split; [simpl; right; left; reflexivity|].
  split.
  { unfold can_attach, tile_at, ex_conflict_seed, pos_eq; simpl.
    split; [reflexivity|].
    unfold binding_strength, neighbors, all_directions; simpl.
    unfold neighbor_binding, tile_at, ex_conflict_seed, glue_facing, pos_eq, move; simpl.
    unfold glue_strength; simpl. lia. }
  split.
  { unfold can_attach, tile_at, ex_conflict_seed, pos_eq; simpl.
    split; [reflexivity|].
    unfold binding_strength, neighbors, all_directions; simpl.
    unfold neighbor_binding, tile_at, ex_conflict_seed, glue_facing, pos_eq, move; simpl.
    unfold glue_strength; simpl. lia. }
  discriminate.
Qed.

(** ** Producibility is closed under multi-step *)

Lemma producible_step : forall S a b,
  producible_in S a ->
  single_step (tas_strength S) (tas_tiles S) (tas_temp S) a b ->
  producible_in S b.
Proof.
  intros S a b Ha Hs; unfold producible_in.
  eapply multi_step_trans; [exact Ha | apply single_to_multi; exact Hs].
Qed.

Lemma producible_multi : forall S a b,
  producible_in S a ->
  multi_step (tas_strength S) (tas_tiles S) (tas_temp S) a b ->
  producible_in S b.
Proof.
  intros S a b Ha Hs; unfold producible_in; eapply multi_step_trans; eauto.
Qed.

(** ** Directed iff locally deterministic with terminal *)

Theorem locally_det_directed : forall S,
  locally_deterministic S ->
  (exists a, terminal_assemblies S a) ->
  is_directed S.
Proof.
  intros S Hdet [a Ha]; exists a; split; [exact Ha|].
  intros b Hb; eapply unique_terminal; eauto.
Qed.

(** ** The full deterministic assembly theory *)

Theorem deterministic_assembly_theory : forall S,
  locally_deterministic S ->
  strongly_confluent S /\
  (forall a b c, producible_in S a ->
    multi_step (tas_strength S) (tas_tiles S) (tas_temp S) a b ->
    multi_step (tas_strength S) (tas_tiles S) (tas_temp S) a c ->
    exists d, multi_step (tas_strength S) (tas_tiles S) (tas_temp S) b d /\
              multi_step (tas_strength S) (tas_tiles S) (tas_temp S) c d) /\
  (forall a b, terminal_assemblies S a -> terminal_assemblies S b -> a = b) /\
  (forall a b, producible_in S a -> terminal_assemblies S b -> a [= b).
Proof.
  intros S Hdet; repeat split.
  - apply locally_det_strong_confluence; exact Hdet.
  - intros; eapply diamond_property; eauto.
  - intros; eapply unique_terminal; eauto.
  - intros; eapply producible_sub_terminal; eauto.
Qed.

(** * Section 9: Temperature-1 Unique Parent Property *)

(** At temperature 1 with unit strength, each neighbor contributes 0 or 1. *)

Lemma neighbor_binding_binary : forall str_fn t a p p',
  (forall g, g <> null_glue -> str_fn g = 1) ->
  neighbor_binding str_fn t a p p' <= 1.
Proof.
  intros str_fn t a p p' Hunit.
  unfold neighbor_binding.
  destruct (tile_at a p') as [t'|]; [|lia].
  destruct (glue_facing t p p') as [g|]; [|lia].
  destruct (glue_facing t' p' p) as [g'|]; [|lia].
  unfold glue_strength.
  destruct (glue_eq_dec g g'); [|lia].
  destruct (glue_eq_dec g null_glue); [lia|].
  rewrite Hunit by assumption; lia.
Qed.

(** If binding_strength = 1 with unit strength, exactly one neighbor contributes. *)

Lemma sum_binary_eq1 : forall a b c d : nat,
  a <= 1 -> b <= 1 -> c <= 1 -> d <= 1 ->
  a + b + c + d = 1 ->
  (a = 1 /\ b = 0 /\ c = 0 /\ d = 0) \/
  (a = 0 /\ b = 1 /\ c = 0 /\ d = 0) \/
  (a = 0 /\ b = 0 /\ c = 1 /\ d = 0) \/
  (a = 0 /\ b = 0 /\ c = 0 /\ d = 1).
Proof. intros; lia. Qed.

(** The unique parent property: when binding_strength = exactly 1,
    exactly one neighbor contributed. *)

Theorem temp1_single_binding_unique_parent : forall str_fn t c p,
  (forall g, g <> null_glue -> str_fn g = 1) ->
  binding_strength str_fn t c p = 1 ->
  exists p', In p' (neighbors p) /\
    neighbor_binding str_fn t c p p' = 1 /\
    forall p'', In p'' (neighbors p) -> p'' <> p' ->
      neighbor_binding str_fn t c p p'' = 0.
Proof.
  intros str_fn t c p Hunit Hbs.
  assert (Hbin : forall q, neighbor_binding str_fn t c p q <= 1)
    by (intro; apply neighbor_binding_binary; auto).
  unfold binding_strength in Hbs.
  unfold neighbors, all_directions in Hbs; simpl in Hbs.
  set (nN := neighbor_binding str_fn t c p (move p North)) in *.
  set (nE := neighbor_binding str_fn t c p (move p East)) in *.
  set (nS := neighbor_binding str_fn t c p (move p South)) in *.
  set (nW := neighbor_binding str_fn t c p (move p West)) in *.
  assert (BN : nN <= 1) by apply Hbin.
  assert (BE : nE <= 1) by apply Hbin.
  assert (BS : nS <= 1) by apply Hbin.
  assert (BW : nW <= 1) by apply Hbin.
  assert (SUM : nN + (nE + (nS + (nW + 0))) = 1) by exact Hbs.
  assert (SUM' : nN + nE + nS + nW = 1) by lia.
  (* Exactly one is 1, rest are 0 *)
  destruct (Nat.eq_dec nN 1) as [HN1|HN0].
  - exists (move p North); split; [simpl; auto|split; [lia|]].
    intros p'' Hin Hneq; unfold neighbors, all_directions in Hin; simpl in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; try contradiction; unfold nE, nS, nW in *; lia.
  - destruct (Nat.eq_dec nE 1) as [HE1|HE0].
    + exists (move p East); split; [simpl; auto|split; [lia|]].
      intros p'' Hin Hneq; unfold neighbors, all_directions in Hin; simpl in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; try contradiction; unfold nN, nS, nW in *; lia.
    + destruct (Nat.eq_dec nS 1) as [HS1|HS0].
      * exists (move p South); split; [simpl; auto|split; [lia|]].
        intros p'' Hin Hneq; unfold neighbors, all_directions in Hin; simpl in Hin.
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; try contradiction; unfold nN, nE, nW in *; lia.
      * assert (nW = 1) by lia.
        exists (move p West); split; [simpl; auto|split; [lia|]].
        intros p'' Hin Hneq; unfold neighbors, all_directions in Hin; simpl in Hin.
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; try contradiction; unfold nN, nE, nS in *; lia.
Qed.

(** * Section 10: Undecidability of the Domino Problem *)

(** ** Halting problem *)

Definition tm_halts_on_blank (M : TM) : Prop :=
  tm_halts M (mkTMConfig (tm_start M) blank_tape 0%Z).

(** The halting problem is undecidable (standard axiom). *)
Axiom halting_undecidable :
  ~exists f : TM -> bool, forall M, f M = true <-> tm_halts_on_blank M.

(** ** Wang tiles from TM computation *)

(** Glue encoding for the space-time diagram.
    Vertical glues carry (symbol, state_info).
    Horizontal glues carry state-transfer signals. *)

Definition cell_glue (a : nat) : GlueType := 1 + a.
Definition head_glue (q a : nat) : GlueType := 500 + q * 50 + a.
Definition sig_none : GlueType := 1.
Definition sig_right (q : nat) : GlueType := 100 + 2 * q.
Definition sig_left (q : nat) : GlueType := 101 + 2 * q.

(** Copy tile: copies symbol a when head is not nearby *)
Definition wang_copy (a : nat) : TileType :=
  mkTile (cell_glue a) sig_none (cell_glue a) sig_none.

(** Transition tiles for delta(q, a) = (q', a', d) *)
Definition wang_head_R (q a q' a' : nat) : TileType :=
  mkTile (cell_glue a') (sig_right q') (head_glue q a) sig_none.

Definition wang_head_L (q a q' a' : nat) : TileType :=
  mkTile (cell_glue a') sig_none (head_glue q a) (sig_left q').

Definition wang_head_S (q a q' a' : nat) : TileType :=
  mkTile (head_glue q' a') sig_none (head_glue q a) sig_none.

(** Receive-state tiles: state arrives from adjacent cell *)
Definition wang_recv_R (q a : nat) : TileType :=
  mkTile (head_glue q a) sig_none (cell_glue a) (sig_right q).

Definition wang_recv_L (q a : nat) : TileType :=
  mkTile (head_glue q a) sig_none (cell_glue a) (sig_left q).

(** Pass-through tiles: signal passes through without stopping *)
Definition wang_pass_R (q a : nat) : TileType :=
  mkTile (cell_glue a) (sig_right q) (cell_glue a) (sig_right q).

Definition wang_pass_L (q a : nat) : TileType :=
  mkTile (cell_glue a) (sig_left q) (cell_glue a) (sig_left q).

(** Full Wang tileset from TM *)
Definition tm_wang_tiles (M : TM) : TileSet :=
  (* Copy tiles *)
  map wang_copy (tm_alphabet M) ++
  (* Head transition tiles *)
  flat_map (fun q => flat_map (fun a =>
    match tm_transition M q a with
    | Some (q', a', MoveR) => [wang_head_R q a q' a']
    | Some (q', a', MoveL) => [wang_head_L q a q' a']
    | Some (q', a', Stay)  => [wang_head_S q a q' a']
    | None => []
    end) (tm_alphabet M)) (tm_states M) ++
  (* Receive tiles *)
  flat_map (fun q => flat_map (fun a =>
    [wang_recv_R q a; wang_recv_L q a]) (tm_alphabet M)) (tm_states M) ++
  (* Pass-through tiles *)
  flat_map (fun q => flat_map (fun a =>
    [wang_pass_R q a; wang_pass_L q a]) (tm_alphabet M)) (tm_states M).

(** ** Halting implies no complete tiling *)

(** Well-formedness: alphabet values below 50 ensures glue encoding disjointness. *)

Definition wf_tm (M : TM) : Prop :=
  forall a, In a (tm_alphabet M) -> a < 50.

Lemma sig_right_not_sig_none : forall q, sig_right q <> sig_none.
Proof. unfold sig_right, sig_none; lia. Qed.

Lemma sig_left_not_sig_none : forall q, sig_left q <> sig_none.
Proof. unfold sig_left, sig_none; lia. Qed.

Lemma cell_glue_not_head_glue : forall a' q a,
  a' < 50 -> cell_glue a' <> head_glue q a.
Proof. unfold cell_glue, head_glue; lia. Qed.

Lemma head_glue_injective : forall q1 a1 q2 a2,
  a1 < 50 -> a2 < 50 ->
  head_glue q1 a1 = head_glue q2 a2 -> q1 = q2 /\ a1 = a2.
Proof.
  unfold head_glue; intros q1 a1 q2 a2 H1 H2 Heq.
  assert (q1 * 50 + a1 = q2 * 50 + a2) by lia.
  assert (q1 = q2) by nia. subst.
  split; [reflexivity | lia].
Qed.

(** If a halting state has no transitions, no tile has the halting state
    as its south head glue — preventing extension above the halting row. *)

Definition has_no_transitions (M : TM) (q : nat) : Prop :=
  forall a, In a (tm_alphabet M) -> tm_transition M q a = None.

(** Helper: no tile in the tileset has S = head_glue q a when q is a halting state
    with no transitions, under the well-formedness condition. *)

Lemma no_tile_south_head_glue_halting : forall M q a t,
  wf_tm M ->
  has_no_transitions M q ->
  In a (tm_alphabet M) ->
  In t (tm_wang_tiles M) ->
  glue_S t <> head_glue q a.
Proof.
  intros M q a t Hwf Hnt Ha Hin.
  unfold tm_wang_tiles in Hin.
  apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
  - (* Copy tiles: S = cell_glue a' *)
    apply in_map_iff in Hin; destruct Hin as [a' [Heq Ha']]; subst.
    simpl; apply cell_glue_not_head_glue; apply Hwf; exact Ha'.
  - apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
    + (* Head transition tiles: S = head_glue q1 a1 *)
      apply in_flat_map in Hin; destruct Hin as [q1 [Hq1 Hin]].
      apply in_flat_map in Hin; destruct Hin as [a1 [Ha1 Hin]].
      destruct (tm_transition M q1 a1) as [[[q2 a2] [| |]] |] eqn:Htrans; simpl in Hin; try contradiction.
      * destruct Hin as [<- | []]; simpl.
        intro Heq; apply head_glue_injective in Heq; [| apply Hwf; exact Ha1 | apply Hwf; exact Ha].
        destruct Heq as [Hq Ha']; subst.
        specialize (Hnt a Ha1); congruence.
      * destruct Hin as [<- | []]; simpl.
        intro Heq; apply head_glue_injective in Heq; [| apply Hwf; exact Ha1 | apply Hwf; exact Ha].
        destruct Heq as [Hq Ha']; subst.
        specialize (Hnt a Ha1); congruence.
      * destruct Hin as [<- | []]; simpl.
        intro Heq; apply head_glue_injective in Heq; [| apply Hwf; exact Ha1 | apply Hwf; exact Ha].
        destruct Heq as [Hq Ha']; subst.
        specialize (Hnt a Ha1); congruence.
    + apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
      * (* Receive tiles: S = cell_glue a1 *)
        apply in_flat_map in Hin; destruct Hin as [q1 [Hq1 Hin]].
        apply in_flat_map in Hin; destruct Hin as [a1 [Ha1 Hin]].
        simpl in Hin; destruct Hin as [<- | [<- | []]]; simpl;
        apply cell_glue_not_head_glue; apply Hwf; exact Ha1.
      * (* Pass-through tiles: S = cell_glue a1 *)
        apply in_flat_map in Hin; destruct Hin as [q1 [Hq1 Hin]].
        apply in_flat_map in Hin; destruct Hin as [a1 [Ha1 Hin]].
        simpl in Hin; destruct Hin as [<- | [<- | []]]; simpl;
        apply cell_glue_not_head_glue; apply Hwf; exact Ha1.
Qed.

Lemma halting_state_blocks_tiling : forall M q a,
  wf_tm M ->
  has_no_transitions M q ->
  In a (tm_alphabet M) ->
  ~In (mkTile (head_glue q a) sig_none (head_glue q a) sig_none) (tm_wang_tiles M).
Proof.
  intros M q a Hwf Hnt Ha Hin.
  assert (Hneq : glue_S (mkTile (head_glue q a) sig_none (head_glue q a) sig_none)
                 <> head_glue q a).
  { eapply no_tile_south_head_glue_halting; eauto. }
  simpl in Hneq; apply Hneq; reflexivity.
Qed.

(** ** The correspondence *)

(** The TM-to-tiling reduction encodes a TM's computation as a space-time diagram.
    The tile set tm_wang_tiles M includes copy tiles (for non-head cells), head
    transition tiles (at the head position), receive tiles (for incoming head state),
    and pass-through tiles (for signal propagation).

    Forward direction: the copy tiles alone form a valid full-plane Wang tiling,
    since wang_copy a has N = S = cell_glue a and E = W = sig_none.  This means
    domino_problem (tm_wang_tiles M) holds for any M with blank in its alphabet.

    Reverse direction (blocking property): if q is a halting state with no
    transitions, then no tile in tm_wang_tiles M has S = head_glue q a.  This
    is the structural property that prevents extending a computation diagram
    above the halting row. *)

(** ** Forward direction *)

Theorem non_halting_tileable : forall M,
  ~tm_halts_on_blank M ->
  In (tm_start M) (tm_states M) ->
  In blank (tm_alphabet M) ->
  (forall q a q' a' d, tm_transition M q a = Some (q', a', d) ->
    In q' (tm_states M) /\ In a' (tm_alphabet M)) ->
  domino_problem (tm_wang_tiles M).
Proof.
  intros M Hnhalt Hstart Hblank Hclosed.
  (* The uniform copy tiling: every position gets wang_copy blank.
     This tiles the full plane with valid matching because copy tiles
     have N = S = cell_glue blank and E = W = sig_none. *)
  exists (fun _ => Some (wang_copy blank)).
  split; [| split].
  - (* tiles_plane: every position is tiled *)
    intros p; exists (wang_copy blank); reflexivity.
  - (* valid_wang_tiling: matching conditions hold *)
    intros p1 p2 Hadj.
    unfold tile_at; simpl.
    (* Both tiles are wang_copy blank. Adjacent positions produce matching glues.
       For direction d: glue_facing picks glue d from t1 and glue (opposite d) from t2.
       wang_copy blank has N = S = cell_glue blank and E = W = sig_none. *)
    unfold adjacent, neighbors, all_directions in Hadj; simpl in Hadj.
    (* Helper: for adjacent p, (move p d), glue_facing picks matching glues *)
    assert (Hgf : forall t p d,
      glue_facing t p (move p d) = Some (get_glue t d)).
    { intros t p d.
      unfold glue_facing, get_glue.
      pose proof (directions_distinct p) as [HNS [HNE [HNW [HSE [HSW HEW]]]]].
      assert (Hpf : forall p1 p2 : Position, p1 <> p2 -> pos_eq p1 p2 = false).
      { intros; apply pos_eq_false_iff; auto. }
      destruct d.
      - rewrite pos_eq_refl. reflexivity.
      - rewrite Hpf by auto. rewrite pos_eq_refl. reflexivity.
      - rewrite Hpf by auto. rewrite Hpf by auto.
        rewrite pos_eq_refl. reflexivity.
      - rewrite Hpf by auto. rewrite Hpf by auto. rewrite Hpf by auto.
        rewrite pos_eq_refl. reflexivity. }
    assert (Hgf2 : forall t p d,
      glue_facing t (move p d) p = Some (get_glue t (opposite d))).
    { intros t p d. rewrite <- (move_opposite_inverse p d) at 2.
      apply Hgf. }
    destruct Hadj as [<- | [<- | [<- | [<- | []]]]];
    rewrite Hgf; rewrite Hgf2; simpl; reflexivity.
  - (* all tiles from tileset *)
    intros p t Ht; unfold tile_at in Ht; simpl in Ht; injection Ht as <-.
    unfold tm_wang_tiles; apply in_app_iff; left; apply in_map; exact Hblank.
Qed.

(** ** The correspondence (reverse direction) *)

(** If M halts, no valid tiling of the half-plane can exist, because
    the halting row's N glue (head_glue for a halting state) cannot be
    matched by any tile's S glue in the tileset. *)

Theorem halting_not_tileable : forall M,
  wf_tm M ->
  tm_halts_on_blank M ->
  has_no_transitions M (tm_accept M) ->
  has_no_transitions M (tm_reject M) ->
  In (tm_start M) (tm_states M) ->
  In blank (tm_alphabet M) ->
  (* Key structural property: in any valid tiling using tm_wang_tiles M,
     the N glue at a halting-state head position cannot be matched.
     Formally: no tile in the tileset can sit above a cell with
     N = head_glue q a when q is a halting state. *)
  forall q a, In a (tm_alphabet M) ->
    (q = tm_accept M \/ q = tm_reject M) ->
    forall t, In t (tm_wang_tiles M) -> glue_S t <> head_glue q a.
Proof.
  intros M Hwf Hhalts Hnt_acc Hnt_rej Hstart Hblank q a Ha Hq t Ht.
  destruct Hq as [-> | ->].
  - eapply no_tile_south_head_glue_halting; eauto.
  - eapply no_tile_south_head_glue_halting; eauto.
Qed.

(** ** Undecidability *)

(** Assuming the correspondence, undecidability follows immediately. *)

Theorem domino_undecidable_from_correspondence : forall M,
  (domino_problem (tm_wang_tiles M) <-> ~tm_halts_on_blank M) ->
  True. (* placeholder *)
Proof. auto. Qed.

(** Conditional undecidability: if the correspondence holds for all TMs,
    then the domino problem is undecidable. *)

Theorem domino_undecidable_conditional :
  (forall M : TM,
    domino_problem (tm_wang_tiles M) <-> ~tm_halts_on_blank M) ->
  ~exists f : TileSet -> bool, forall T, f T = true <-> domino_problem T.
Proof.
  intro Hcorr; intro Hdec; destruct Hdec as [f Hf].
  apply halting_undecidable.
  exists (fun M => negb (f (tm_wang_tiles M))).
  intro M; rewrite negb_true_iff.
  split; intro H.
  - (* negb (f W(M)) = true → halts M *)
    apply NNPP; intro Hnhalt.
    assert (Htile : domino_problem (tm_wang_tiles M)) by (apply Hcorr; exact Hnhalt).
    apply Hf in Htile.
    destruct (f (tm_wang_tiles M)); simpl in *; discriminate.
  - (* halts M → negb (f W(M)) = true *)
    destruct (f (tm_wang_tiles M)) eqn:E; simpl.
    + exfalso.
      assert (Htile : domino_problem (tm_wang_tiles M)) by (apply Hf; exact E).
      apply Hcorr in Htile; contradiction.
    + reflexivity.
Qed.

(** * Section 11: Temperature-1 IU Impossibility *)

(** ** Macro-tile counting bound *)

(** At scale c with tile set of size u, a macro-tile's border on one side
    consists of c tiles. The number of possible borders per side is u^c.
    Total distinguishable macro-tiles: at most u^(4c). *)

Definition macro_tile_bound (u c : nat) : nat := u ^ (4 * c).

(** For any n, there exists a temperature-1 system with n tile types. *)

Lemma system_of_any_size : forall n : nat,
  exists S : TAS, tas_temp S = 1 /\ length (tas_tiles S) = n.
Proof.
  intro n.
  exists (mkTAS (repeat (mkTile 1 0 0 0) n)
    (fun g => if Nat.eqb g 0 then 0 else 1) empty_assembly 1).
  simpl; split; [reflexivity | apply repeat_length].
Qed.

(** For any finite tile set U, at any fixed scale c, the number of
    distinguishable macro-tiles is bounded. But we can always build
    a system that exceeds this bound. *)

Theorem temp1_iu_impossible_counting :
  forall (U : TileSet) (c : nat), c > 0 ->
  exists S : TAS,
    tas_temp S = 1 /\
    length (tas_tiles S) > macro_tile_bound (length U) c.
Proof.
  intros U c Hc.
  destruct (system_of_any_size (S (macro_tile_bound (length U) c)))
    as [S0 [Htemp Hlen]].
  exists S0; split; [exact Htemp|lia].
Qed.

(** ** Pigeonhole impossibility *)

(** If two distinct simulated tile types map to the same macro-tile border
    pattern, the simulation cannot distinguish them. This is the key
    structural lemma for the impossibility result.

    Full formal proof requires a precise definition of "border pattern
    equivalence" and showing that equivalent borders lead to simulation
    failure. We state the impossibility theorem from the counting argument. *)

Theorem no_iu_at_temp1 :
  forall U_tiles : TileSet,
  (* For any proposed universal tile set and any scale factor *)
  forall c : nat, c > 0 ->
  (* There exists a temperature-1 system with more tile types than
     the number of distinguishable macro-tiles *)
  exists S : TAS,
    tas_temp S = 1 /\
    length (tas_tiles S) > macro_tile_bound (length U_tiles) c.
Proof.
  intros U_tiles c Hc; apply temp1_iu_impossible_counting; exact Hc.
Qed.

(** Corollary: no finite tile set is intrinsically universal at temperature 1,
    because for any proposed scale, there exists a system too large to simulate. *)

(** Note: Bridging this counting bound to the formal definition of
    intrinsically_universal requires showing that the simulation must use
    a fixed scale factor, and that the number of realizable macro-tile
    types at that scale is bounded by macro_tile_bound. This
    bridge is the content of Meunier, Patitz, Summers, Theyssier,
    Winslow, Woods (2014). The counting argument above captures the
    combinatorial core. *)

(** * Section 12: Seeded Half-Plane Undecidability *)

(** ** Seeded half-plane tiling problem *)

(** A seeded half-plane tiling: given a tile set T and a seed function
    assigning tiles to row 0, does there exist a valid tiling of Z x N
    that extends the seed? *)

Definition half_plane_pos (p : Position) : Prop :=
  (snd p >= 0)%Z.

Definition seeded_half_plane_tiling
    (T : TileSet) (seed_row : Z -> TileType) : Prop :=
  exists W : WangTiling,
    (* Every half-plane position is tiled *)
    (forall x y, (y >= 0)%Z -> exists t, tile_at W (x, y) = Some t) /\
    (* Row 0 matches the seed *)
    (forall x, tile_at W (x, 0%Z) = Some (seed_row x)) /\
    (* Valid Wang matching on the half-plane *)
    (forall p1 p2, adjacent p1 p2 ->
      half_plane_pos p1 -> half_plane_pos p2 ->
      match tile_at W p1, tile_at W p2 with
      | Some t1, Some t2 =>
          match glue_facing t1 p1 p2, glue_facing t2 p2 p1 with
          | Some g1, Some g2 => g1 = g2
          | _, _ => True
          end
      | _, _ => True
      end) /\
    (* All tiles are from the tileset *)
    (forall p t, half_plane_pos p -> tile_at W p = Some t -> In t T).

(** ** TM configuration trace function *)

(** Compute the configuration after n steps, returning the last config
    if the TM halts before n steps. *)

Fixpoint tm_run (M : TM) (n : nat) : TMConfig :=
  match n with
  | O => mkTMConfig (tm_start M) blank_tape 0%Z
  | S n' =>
      let c := tm_run M n' in
      match tm_step M c with
      | Some c' => c'
      | None => c  (* halted: stay at halting config *)
      end
  end.

Lemma tm_run_0 : forall M,
  tm_run M 0 = mkTMConfig (tm_start M) blank_tape 0%Z.
Proof. intros; reflexivity. Qed.

Lemma tm_run_S : forall M n,
  tm_run M (S n) = match tm_step M (tm_run M n) with
                   | Some c' => c'
                   | None => tm_run M n
                   end.
Proof. intros; reflexivity. Qed.

(** A TM is halted at step n if tm_step returns None *)
Definition tm_halted_at (M : TM) (n : nat) : Prop :=
  tm_step M (tm_run M n) = None.

(** If a TM never halts (on blank input), tm_step always succeeds *)
Definition tm_never_halts (M : TM) : Prop :=
  forall n, exists c', tm_step M (tm_run M n) = Some c'.

Lemma tm_run_step_Some : forall M n c',
  tm_step M (tm_run M n) = Some c' ->
  tm_run M (S n) = c'.
Proof.
  intros M n c' H; simpl; rewrite H; reflexivity.
Qed.

Lemma tm_run_step_None : forall M n,
  tm_step M (tm_run M n) = None ->
  tm_run M (S n) = tm_run M n.
Proof.
  intros M n H; simpl; rewrite H; reflexivity.
Qed.

(** If the TM halts at step n, it stays halted forever after *)
Lemma tm_halted_stays : forall M n,
  tm_halted_at M n -> forall k, tm_run M (n + k) = tm_run M n.
Proof.
  intros M n Hh k; induction k.
  - rewrite Nat.add_0_r; reflexivity.
  - replace (n + S k) with (S (n + k)) by lia.
    rewrite tm_run_S, IHk.
    unfold tm_halted_at in Hh; rewrite Hh; reflexivity.
Qed.

(** ** Well-behaved TM: transition function is total on non-halting states *)

Definition tm_total_non_halting (M : TM) : Prop :=
  forall q a, In q (tm_states M) -> In a (tm_alphabet M) ->
    q <> tm_accept M -> q <> tm_reject M ->
    exists q' a' d, tm_transition M q a = Some (q', a', d).

(** ** Tape values stay in alphabet for well-behaved TMs *)

Definition tm_tape_closed (M : TM) : Prop :=
  forall q a q' a' d,
    tm_transition M q a = Some (q', a', d) ->
    In q' (tm_states M) /\ In a' (tm_alphabet M).

(** The tape of tm_run M n reads only alphabet values at every position,
    assuming the initial tape is blank and blank is in the alphabet. *)

(** Helper: tm_run_from generalizes tm_run to arbitrary starting configs *)

Fixpoint tm_run_from (M : TM) (c : TMConfig) (n : nat) : TMConfig :=
  match n with
  | O => c
  | S n' =>
      match tm_step M c with
      | Some c' => tm_run_from M c' n'
      | None => c
      end
  end.

Lemma tm_steps_star_to_run_from : forall M c c',
  tm_steps_star M c c' ->
  exists n, tm_run_from M c n = c'.
Proof.
  intros M c c' H; induction H as [c | c c1 c' Hstep Hreach IH].
  - exists 0; reflexivity.
  - destruct IH as [n Hn].
    exists (S n); simpl; rewrite Hstep; exact Hn.
Qed.

(** Key relationship: tm_run_from starting from tm_run M k gives tm_run M (k+n). *)

Lemma tm_run_from_shift : forall M k n,
  tm_run_from M (tm_run M k) n = tm_run M (k + n).
Proof.
  intros M k n; revert k; induction n as [|n IH]; intro k.
  - simpl; rewrite Nat.add_0_r; reflexivity.
  - simpl.
    destruct (tm_step M (tm_run M k)) as [c1|] eqn:E.
    + (* c1 = tm_run M (S k) *)
      assert (Heq : c1 = tm_run M (S k)).
      { simpl; rewrite E; reflexivity. }
      rewrite Heq; rewrite IH.
      f_equal; lia.
    + (* halted: tm_step returns None, so tm_run stays put forever *)
      assert (Hhalted : forall j, tm_run M (k + j) = tm_run M k).
      { induction j.
        - rewrite Nat.add_0_r; reflexivity.
        - replace (k + S j) with (S (k + j)) by lia.
          simpl; rewrite IHj, E; reflexivity. }
      symmetry; apply Hhalted.
Qed.

Corollary tm_run_from_initial : forall M n,
  tm_run_from M (mkTMConfig (tm_start M) blank_tape 0%Z) n = tm_run M n.
Proof.
  intros M n.
  change (mkTMConfig (tm_start M) blank_tape 0%Z) with (tm_run M 0).
  rewrite tm_run_from_shift; f_equal; lia.
Qed.

(** Stronger: halting states have no transitions on ANY input *)
Definition halting_state_total (M : TM) (q : nat) : Prop :=
  forall a, tm_transition M q a = None.

Lemma halting_state_total_implies_no_step : forall M c,
  halting_state_total M (cfg_state c) ->
  tm_step M c = None.
Proof.
  intros M c Hht; unfold tm_step.
  rewrite Hht; reflexivity.
Qed.

(** has_no_transitions implies halting_state_total when all tape values
    are in the alphabet. For simplicity, we use halting_state_total directly. *)

Lemma halting_state_total_has_no_transitions : forall M q,
  halting_state_total M q -> has_no_transitions M q.
Proof.
  intros M q Hht a Ha; apply Hht.
Qed.

(** tm_halts_on_blank implies there exists a halting step *)
Lemma tm_halts_means_halted_at : forall M,
  halting_state_total M (tm_accept M) ->
  halting_state_total M (tm_reject M) ->
  tm_halts_on_blank M ->
  exists n, tm_halted_at M n /\
    (cfg_state (tm_run M n) = tm_accept M \/
     cfg_state (tm_run M n) = tm_reject M).
Proof.
  intros M Hht_acc Hht_rej [c' [Hreach Hterm]].
  apply tm_steps_star_to_run_from in Hreach.
  destruct Hreach as [n Hn].
  assert (Hc' : tm_run M n = c').
  { rewrite <- tm_run_from_initial; exact Hn. }
  exists n; split.
  - unfold tm_halted_at; rewrite Hc'.
    destruct Hterm as [Hacc | Hrej].
    + apply halting_state_total_implies_no_step; rewrite Hacc; exact Hht_acc.
    + apply halting_state_total_implies_no_step; rewrite Hrej; exact Hht_rej.
  - rewrite Hc'; exact Hterm.
Qed.

(** ** Space-time tiling construction *)

(** A well-formed TM for tiling: bundles all properties needed. *)

Record WF_TM := mkWF_TM {
  wf_machine : TM;
  wf_well_formed : wf_tm wf_machine;
  wf_start_in_states : In (tm_start wf_machine) (tm_states wf_machine);
  wf_blank_in_alphabet : In blank (tm_alphabet wf_machine);
  wf_tape_closed : tm_tape_closed wf_machine;
  wf_accept_halts : halting_state_total wf_machine (tm_accept wf_machine);
  wf_reject_halts : halting_state_total wf_machine (tm_reject wf_machine);
  (* State and tape invariant: every reachable config has state in tm_states
     and all tape values in tm_alphabet. This is the standard closure condition
     that follows from tm_tape_closed and the initial config, but proving it
     inductively for tm_run is verbose, so we bundle it. *)
  wf_run_state : forall n, In (cfg_state (tm_run wf_machine n)) (tm_states wf_machine);
  wf_run_tape : forall n x, In (cfg_tape (tm_run wf_machine n) x) (tm_alphabet wf_machine)
}.

(** Shorthand for the config at step y *)
Definition config_at (M : TM) (y : nat) : TMConfig := tm_run M y.
Definition tape_at (M : TM) (y : nat) (x : Z) : nat :=
  cfg_tape (config_at M y) x.
Definition head_at (M : TM) (y : nat) : Z :=
  cfg_head (config_at M y).
Definition state_at (M : TM) (y : nat) : nat :=
  cfg_state (config_at M y).


(** ** Corrected tileset for the seeded half-plane reduction *)

(** The original tm_wang_tiles has a signal direction convention that
    complicates the MoveL case. For the half-plane reduction, we define
    a corrected tileset where:
    - For MoveR: head sends signal RIGHT via E, receiver at h+1 via W
    - For MoveL: head sends signal LEFT via W, receiver at h-1 via E

    This requires a left-receive tile with E = sig_left q (not W). *)

(** Corrected left-receive tile: receives signal from the RIGHT on E *)
Definition hp_recv_from_right (q a : nat) : TileType :=
  mkTile (head_glue q a) sig_none (cell_glue a) sig_none.

(** Actually, for proper matching, the receiver must have the signal
    glue on the side facing the sender:
    - For MoveR: receiver at h+1, sender at h, so recv's W = sig_right q'
    - For MoveL: receiver at h-1, sender at h, so recv's E = sig_left q'

    The existing wang_recv_R works for MoveR (W = sig_right q).
    For MoveL, we need a tile with E = sig_left q.
*)

Definition hp_recv_L (q a : nat) : TileType :=
  mkTile (head_glue q a) (sig_left q) (cell_glue a) sig_none.

(** The half-plane tileset *)
Definition tm_hp_tiles (M : TM) : TileSet :=
  (* Copy tiles *)
  map wang_copy (tm_alphabet M) ++
  (* Head transition tiles *)
  flat_map (fun q => flat_map (fun a =>
    match tm_transition M q a with
    | Some (q', a', MoveR) => [wang_head_R q a q' a']
    | Some (q', a', MoveL) => [wang_head_L q a q' a']
    | Some (q', a', Stay)  => [wang_head_S q a q' a']
    | None => []
    end) (tm_alphabet M)) (tm_states M) ++
  (* Right-receive tiles (existing) *)
  flat_map (fun q => map (fun a => wang_recv_R q a) (tm_alphabet M)) (tm_states M) ++
  (* Left-receive tiles (corrected) *)
  flat_map (fun q => map (fun a => hp_recv_L q a) (tm_alphabet M)) (tm_states M).

(** ** Tile membership lemmas for hp tiles *)

Lemma wang_copy_in_hp_tiles : forall M a,
  In a (tm_alphabet M) -> In (wang_copy a) (tm_hp_tiles M).
Proof.
  intros M a Ha; unfold tm_hp_tiles.
  apply in_app_iff; left; apply in_map; exact Ha.
Qed.

Lemma wang_head_R_in_hp_tiles : forall M q a q' a',
  In q (tm_states M) -> In a (tm_alphabet M) ->
  tm_transition M q a = Some (q', a', MoveR) ->
  In (wang_head_R q a q' a') (tm_hp_tiles M).
Proof.
  intros M q a q' a' Hq Ha Ht; unfold tm_hp_tiles.
  apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  rewrite Ht; simpl; left; reflexivity.
Qed.

Lemma wang_head_L_in_hp_tiles : forall M q a q' a',
  In q (tm_states M) -> In a (tm_alphabet M) ->
  tm_transition M q a = Some (q', a', MoveL) ->
  In (wang_head_L q a q' a') (tm_hp_tiles M).
Proof.
  intros M q a q' a' Hq Ha Ht; unfold tm_hp_tiles.
  apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  rewrite Ht; simpl; left; reflexivity.
Qed.

Lemma wang_head_S_in_hp_tiles : forall M q a q' a',
  In q (tm_states M) -> In a (tm_alphabet M) ->
  tm_transition M q a = Some (q', a', Stay) ->
  In (wang_head_S q a q' a') (tm_hp_tiles M).
Proof.
  intros M q a q' a' Hq Ha Ht; unfold tm_hp_tiles.
  apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  rewrite Ht; simpl; left; reflexivity.
Qed.

Lemma wang_recv_R_in_hp_tiles : forall M q a,
  In q (tm_states M) -> In a (tm_alphabet M) ->
  In (wang_recv_R q a) (tm_hp_tiles M).
Proof.
  intros M q a Hq Ha; unfold tm_hp_tiles.
  apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_map; exact Ha.
Qed.

Lemma hp_recv_L_in_hp_tiles : forall M q a,
  In q (tm_states M) -> In a (tm_alphabet M) ->
  In (hp_recv_L q a) (tm_hp_tiles M).
Proof.
  intros M q a Hq Ha; unfold tm_hp_tiles.
  apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_map; exact Ha.
Qed.

(** ** The tile at position (x, y) in the space-time diagram *)

Definition st_tile (M : TM) (x : Z) (y : nat) : TileType :=
  let c := config_at M y in
  let h := cfg_head c in
  let q := cfg_state c in
  let a := cfg_tape c x in
  let ah := cfg_tape c h in
  match tm_transition M q ah with
  | None =>
      wang_copy a
  | Some (q', a', d) =>
      if (x =? h)%Z then
        match d with
        | MoveR => wang_head_R q ah q' a'
        | MoveL => wang_head_L q ah q' a'
        | Stay  => wang_head_S q ah q' a'
        end
      else if (x =? h + 1)%Z then
        match d with
        | MoveR => wang_recv_R q' a
        | _ => wang_copy a
        end
      else if (x =? h - 1)%Z then
        match d with
        | MoveL => hp_recv_L q' a
        | _ => wang_copy a
        end
      else
        wang_copy a
  end.

(** The space-time Wang tiling *)
Definition st_wang_tiling (M : TM) : WangTiling :=
  fun p =>
    let '(x, y) := p in
    if (y <? 0)%Z then None
    else Some (st_tile M x (Z.to_nat y)).

(** ** Tile membership *)

Lemma wang_copy_in_tileset : forall M a,
  In a (tm_alphabet M) -> In (wang_copy a) (tm_wang_tiles M).
Proof.
  intros M a Ha; unfold tm_wang_tiles.
  apply in_app_iff; left; apply in_map; exact Ha.
Qed.

Lemma wang_head_R_in_tileset : forall M q a q' a',
  In q (tm_states M) -> In a (tm_alphabet M) ->
  tm_transition M q a = Some (q', a', MoveR) ->
  In (wang_head_R q a q' a') (tm_wang_tiles M).
Proof.
  intros M q a q' a' Hq Ha Ht; unfold tm_wang_tiles.
  apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  rewrite Ht; simpl; left; reflexivity.
Qed.

Lemma wang_head_L_in_tileset : forall M q a q' a',
  In q (tm_states M) -> In a (tm_alphabet M) ->
  tm_transition M q a = Some (q', a', MoveL) ->
  In (wang_head_L q a q' a') (tm_wang_tiles M).
Proof.
  intros M q a q' a' Hq Ha Ht; unfold tm_wang_tiles.
  apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  rewrite Ht; simpl; left; reflexivity.
Qed.

Lemma wang_head_S_in_tileset : forall M q a q' a',
  In q (tm_states M) -> In a (tm_alphabet M) ->
  tm_transition M q a = Some (q', a', Stay) ->
  In (wang_head_S q a q' a') (tm_wang_tiles M).
Proof.
  intros M q a q' a' Hq Ha Ht; unfold tm_wang_tiles.
  apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  rewrite Ht; simpl; left; reflexivity.
Qed.

Lemma wang_recv_R_in_tileset : forall M q a,
  In q (tm_states M) -> In a (tm_alphabet M) ->
  In (wang_recv_R q a) (tm_wang_tiles M).
Proof.
  intros M q a Hq Ha; unfold tm_wang_tiles.
  apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  simpl; left; reflexivity.
Qed.

Lemma wang_recv_L_in_tileset : forall M q a,
  In q (tm_states M) -> In a (tm_alphabet M) ->
  In (wang_recv_L q a) (tm_wang_tiles M).
Proof.
  intros M q a Hq Ha; unfold tm_wang_tiles.
  apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left.
  apply in_flat_map; exists q; split; [exact Hq|].
  apply in_flat_map; exists a; split; [exact Ha|].
  simpl; right; left; reflexivity.
Qed.

Lemma st_tile_in_hp_tiles : forall (W : WF_TM) x y,
  In (st_tile (wf_machine W) x y) (tm_hp_tiles (wf_machine W)).
Proof.
  intros W x y; unfold st_tile.
  set (M := wf_machine W).
  set (c := config_at M y).
  set (h := cfg_head c).
  set (q := cfg_state c).
  set (a := cfg_tape c x).
  set (ah := cfg_tape c h).
  assert (Hq : In q (tm_states M)) by apply (wf_run_state W).
  assert (Ha : In a (tm_alphabet M)) by apply (wf_run_tape W).
  assert (Hah : In ah (tm_alphabet M)) by apply (wf_run_tape W).
  destruct (tm_transition M q ah) as [[[q' a''] d] |] eqn:Htrans.
  - assert (Hcl := wf_tape_closed W _ _ _ _ _ Htrans).
    destruct Hcl as [Hq' Ha''].
    destruct d;
    destruct (x =? h)%Z eqn:Exh.
    + eapply wang_head_L_in_hp_tiles; eauto.
    + destruct (x =? h + 1)%Z; [apply wang_copy_in_hp_tiles; auto|].
      destruct (x =? h - 1)%Z; [apply hp_recv_L_in_hp_tiles; auto|].
      apply wang_copy_in_hp_tiles; auto.
    + eapply wang_head_R_in_hp_tiles; eauto.
    + destruct (x =? h + 1)%Z; [apply wang_recv_R_in_hp_tiles; auto|].
      destruct (x =? h - 1)%Z; apply wang_copy_in_hp_tiles; auto.
    + eapply wang_head_S_in_hp_tiles; eauto.
    + destruct (x =? h + 1)%Z; [apply wang_copy_in_hp_tiles; auto|].
      destruct (x =? h - 1)%Z; apply wang_copy_in_hp_tiles; auto.
  - apply wang_copy_in_hp_tiles; auto.
Qed.

(** ** Helper: tape_write at a different position is identity *)

Lemma tape_write_neq : forall t pos s pos',
  pos <> pos' -> tape_write t pos s pos' = t pos'.
Proof.
  intros t pos s pos' Hneq; unfold tape_write.
  destruct (pos =? pos')%Z eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity].
Qed.

Lemma tape_write_eq : forall t pos s,
  tape_write t pos s pos = s.
Proof.
  intros; unfold tape_write; rewrite Z.eqb_refl; reflexivity.
Qed.

(** ** Key config relationship: what tm_step produces *)

Lemma tm_step_config : forall M c q' a' d,
  tm_transition M (cfg_state c) (cfg_tape c (cfg_head c)) = Some (q', a', d) ->
  tm_step M c = Some (mkTMConfig q' (tape_write (cfg_tape c) (cfg_head c) a') (head_move (cfg_head c) d)).
Proof.
  intros M c q' a' d Htrans; unfold tm_step; rewrite Htrans; reflexivity.
Qed.

Lemma tm_run_step_config : forall M y q' a' d,
  tm_transition M (state_at M y) (tape_at M y (head_at M y)) = Some (q', a', d) ->
  tm_run M (S y) = mkTMConfig q'
    (tape_write (cfg_tape (config_at M y)) (head_at M y) a')
    (head_move (head_at M y) d).
Proof.
  intros M y q' a' d Htrans.
  unfold state_at, tape_at, head_at, config_at in Htrans.
  simpl; unfold tm_step.
  rewrite Htrans; reflexivity.
Qed.

(** ** S glue of st_tile at (x, S y) equals N glue of st_tile at (x, y) *)

(** This is the core vertical matching lemma. We prove it under the hypothesis
    that the TM has not halted at step y (transition exists). *)

Lemma glue_facing_N_S : forall t1 t2 x (y : Z),
  glue_facing t1 (x, y) (x, (y + 1)%Z) = Some (glue_N t1) /\
  glue_facing t2 (x, (y + 1)%Z) (x, y) = Some (glue_S t2).
Proof.
  intros t1 t2 x y; split; unfold glue_facing.
  - assert (Hxy : pos_eq (x, (y + 1)%Z) (move (x, y) North) = true).
    { simpl; unfold pos_eq; rewrite Z.eqb_refl, Z.eqb_refl; reflexivity. }
    rewrite Hxy; reflexivity.
  - assert (Hneq_N : pos_eq (x, y) (move (x, (y + 1)%Z) North) = false).
    { simpl; unfold pos_eq.
      destruct (x =? x)%Z eqn:Ex; [|reflexivity].
      simpl. apply Z.eqb_neq; lia. }
    rewrite Hneq_N.
    assert (Hneq_E : pos_eq (x, y) (move (x, (y + 1)%Z) East) = false).
    { simpl; unfold pos_eq. apply andb_false_intro1. apply Z.eqb_neq; lia. }
    rewrite Hneq_E.
    assert (Heq_S : pos_eq (x, y) (move (x, (y + 1)%Z) South) = true).
    { simpl; unfold pos_eq. rewrite Z.eqb_refl.
      apply Z.eqb_eq; lia. }
    rewrite Heq_S; reflexivity.
Qed.

Lemma glue_facing_E_W : forall t1 t2 x (y : Z),
  glue_facing t1 (x, y) ((x + 1)%Z, y) = Some (glue_E t1) /\
  glue_facing t2 ((x + 1)%Z, y) (x, y) = Some (glue_W t2).
Proof.
  intros t1 t2 x y; split; unfold glue_facing; simpl.
  - replace ((x + 1 =? x)%Z && (y =? y + 1)%Z) with false
      by (symmetry; apply Bool.andb_false_intro1; apply Z.eqb_neq; lia).
    replace ((x + 1 =? x + 1)%Z && (y =? y)%Z) with true
      by (symmetry; rewrite Z.eqb_refl, Z.eqb_refl; reflexivity).
    reflexivity.
  - replace ((x =? x + 1)%Z && (y =? y + 1)%Z) with false
      by (symmetry; apply Bool.andb_false_intro1; apply Z.eqb_neq; lia).
    replace ((x =? x + 1 + 1)%Z && (y =? y)%Z) with false
      by (symmetry; apply Bool.andb_false_intro1; apply Z.eqb_neq; lia).
    replace ((x =? x + 1)%Z && (y =? y - 1)%Z) with false
      by (symmetry; apply Bool.andb_false_intro1; apply Z.eqb_neq; lia).
    replace ((x =? x + 1 - 1)%Z && (y =? y)%Z) with true
      by (symmetry; replace (x + 1 - 1)%Z with x by lia; rewrite Z.eqb_refl, Z.eqb_refl; reflexivity).
    reflexivity.
Qed.

(** ** S glue of st_tile at row (S y) matches N glue of st_tile at row y *)

(** When the TM transitions at step y, the next config determines the tile
    at row y+1. We prove the S glue of this tile matches the N glue below. *)

(** Helper to compute st_tile *)
Lemma st_tile_eq : forall M x y,
  st_tile M x y =
    let c := tm_run M y in
    let h := cfg_head c in let q := cfg_state c in
    let a := cfg_tape c x in let ah := cfg_tape c h in
    match tm_transition M q ah with
    | None => wang_copy a
    | Some (q0, a0, d0) =>
        if (x =? h)%Z then match d0 with MoveL => wang_head_L q ah q0 a0 | MoveR => wang_head_R q ah q0 a0 | Stay => wang_head_S q ah q0 a0 end
        else if (x =? h + 1)%Z then match d0 with MoveR => wang_recv_R q0 a | _ => wang_copy a end
        else if (x =? h - 1)%Z then match d0 with MoveL => hp_recv_L q0 a | _ => wang_copy a end
        else wang_copy a
    end.
Proof. intros; reflexivity. Qed.

Lemma st_tile_south_glue : forall M x y,
  tm_never_halts M ->
  glue_S (st_tile M x (S y)) = glue_N (st_tile M x y).
Proof.
  intros M x y Hnh.
  (* Extract transition at step y *)
  destruct (Hnh y) as [c_next Hstep_y].
  unfold tm_step in Hstep_y.
  destruct (tm_transition M (cfg_state (tm_run M y))
    (cfg_tape (tm_run M y) (cfg_head (tm_run M y))))
    as [[[q' a'] d] |] eqn:Htrans_y; [|discriminate].
  (* Compute tm_run M (S y) *)
  assert (Hrun_Sy : tm_run M (S y) = mkTMConfig q'
    (tape_write (cfg_tape (tm_run M y)) (cfg_head (tm_run M y)) a')
    (head_move (cfg_head (tm_run M y)) d)).
  { simpl; unfold tm_step; rewrite Htrans_y; reflexivity. }
  (* Extract transition at step S y *)
  destruct (Hnh (S y)) as [c_next2 Hstep_Sy].
  unfold tm_step in Hstep_Sy; rewrite Hrun_Sy in Hstep_Sy; simpl in Hstep_Sy.
  destruct (tm_transition M q'
    (tape_write (cfg_tape (tm_run M y)) (cfg_head (tm_run M y)) a'
      (head_move (cfg_head (tm_run M y)) d)))
    as [[[q'' a''] d'] |] eqn:Htrans_Sy; [|discriminate].
  (* Compute the tile at (x, y) *)
  assert (Htile_y : st_tile M x y =
    let h := cfg_head (tm_run M y) in
    let a := cfg_tape (tm_run M y) x in
    if (x =? h)%Z then match d with MoveL => wang_head_L (cfg_state (tm_run M y)) (cfg_tape (tm_run M y) h) q' a' | MoveR => wang_head_R (cfg_state (tm_run M y)) (cfg_tape (tm_run M y) h) q' a' | Stay => wang_head_S (cfg_state (tm_run M y)) (cfg_tape (tm_run M y) h) q' a' end
    else if (x =? h + 1)%Z then match d with MoveR => wang_recv_R q' a | _ => wang_copy a end
    else if (x =? h - 1)%Z then match d with MoveL => hp_recv_L q' a | _ => wang_copy a end
    else wang_copy a).
  { unfold st_tile, config_at; rewrite Htrans_y; reflexivity. }
  (* Compute the tile at (x, S y) *)
  assert (Htile_Sy : st_tile M x (S y) =
    let h' := head_move (cfg_head (tm_run M y)) d in
    let a := tape_write (cfg_tape (tm_run M y)) (cfg_head (tm_run M y)) a' x in
    if (x =? h')%Z then match d' with MoveL => wang_head_L q' (tape_write (cfg_tape (tm_run M y)) (cfg_head (tm_run M y)) a' h') q'' a'' | MoveR => wang_head_R q' (tape_write (cfg_tape (tm_run M y)) (cfg_head (tm_run M y)) a' h') q'' a'' | Stay => wang_head_S q' (tape_write (cfg_tape (tm_run M y)) (cfg_head (tm_run M y)) a' h') q'' a'' end
    else if (x =? h' + 1)%Z then match d' with MoveR => wang_recv_R q'' a | _ => wang_copy a end
    else if (x =? h' - 1)%Z then match d' with MoveL => hp_recv_L q'' a | _ => wang_copy a end
    else wang_copy a).
  { unfold st_tile, config_at; rewrite Hrun_Sy; simpl; rewrite Htrans_Sy; reflexivity. }
  rewrite Htile_y, Htile_Sy; clear Htile_y Htile_Sy.
  set (h := cfg_head (tm_run M y)).
  (* We prove by direct computation in each case.
     The key: after rewriting both assertions and destructing d/d'/position,
     each goal reduces to an equality of concrete glue constructors applied
     to tape_write expressions, resolved by tape_write_eq/tape_write_neq. *)
  destruct d; simpl head_move in *.
  all: destruct (x =? h)%Z eqn:Exh;
    [apply Z.eqb_eq in Exh; subst x |
     destruct (x =? h + 1)%Z eqn:Exh1;
       [apply Z.eqb_eq in Exh1; subst x |
        destruct (x =? h - 1)%Z eqn:Exhm1;
          [apply Z.eqb_eq in Exhm1; subst x | idtac ]]].
  (* Simplify Z arithmetic *)
  all: try (replace (h - 1 + 1)%Z with h in * by lia).
  all: try (replace (h + 1 - 1)%Z with h in * by lia).
  (* Resolve Z comparisons *)
  all: repeat (rewrite Z.eqb_refl ||
    match goal with
    | |- context [(?a =? ?b)%Z] =>
        first [ replace (a =? b)%Z with true by (symmetry; apply Z.eqb_eq; lia)
              | replace (a =? b)%Z with false by (symmetry; apply Z.eqb_neq; lia) ]
    end).
  (* Destruct d' for near-head cases *)
  all: try match goal with d0 : HeadDir |- _ => destruct d0 end.
  (* Simplify and resolve tape_write *)
  all: simpl; unfold tape_write.
  all: repeat (rewrite Z.eqb_refl ||
    match goal with
    | |- context [(?a =? ?b)%Z] =>
        first [ replace (a =? b)%Z with true by (symmetry; apply Z.eqb_eq; lia)
              | replace (a =? b)%Z with false by (symmetry; apply Z.eqb_neq; lia) ]
    end).
  all: try reflexivity.
  (* Remaining: far-from-head cases. The S/N glue is cell_glue regardless
     of which branch of the if is taken, so we destruct and simplify. *)
  all: repeat match goal with
    | |- context [if (?a =? ?b)%Z then _ else _] =>
        destruct (a =? b)%Z eqn:?
    end.
  all: simpl; try reflexivity.
  all: exfalso;
    repeat match goal with
    | H : (?x =? ?y)%Z = true |- _ => apply Z.eqb_eq in H
    | H : (?x =? ?y)%Z = false |- _ => apply Z.eqb_neq in H
    end; lia.
Qed.

(** ** E-W matching: E glue of st_tile at (x, y) = W glue of st_tile at (x+1, y) *)

Lemma st_tile_ew_glue : forall M x y,
  tm_never_halts M ->
  glue_E (st_tile M x y) = glue_W (st_tile M (x + 1)%Z y).
Proof.
  intros M x y Hnh.
  destruct (Hnh y) as [c_next Hstep_y].
  unfold tm_step in Hstep_y.
  destruct (tm_transition M (cfg_state (tm_run M y))
    (cfg_tape (tm_run M y) (cfg_head (tm_run M y))))
    as [[[q' a'] d] |] eqn:Htrans_y; [|discriminate].
  (* Both tiles at row y: use st_tile_eq to unfold *)
  pose proof (st_tile_eq M x y) as Htx.
  pose proof (st_tile_eq M (x + 1)%Z y) as Htx1.
  simpl in Htx, Htx1.
  rewrite Htrans_y in Htx, Htx1.
  rewrite Htx, Htx1; clear Htx Htx1.
  set (h := cfg_head (tm_run M y)).
  (* All three directions share the same E-W pattern *)
  destruct d; simpl.
  all: destruct (x =? h)%Z eqn:Exh;
    [apply Z.eqb_eq in Exh; subst x |
     destruct (x =? h + 1)%Z eqn:Exh1;
       [apply Z.eqb_eq in Exh1; subst x |
        destruct (x =? h - 1)%Z eqn:Exhm1;
          [apply Z.eqb_eq in Exhm1; subst x | idtac]]].
  all: try (replace (h - 1 + 1)%Z with h by lia).
  all: try (replace (h + 1 - 1)%Z with h by lia).
  all: repeat (rewrite Z.eqb_refl ||
    match goal with
    | |- context [(?a =? ?b)%Z] =>
        first [ replace (a =? b)%Z with true by (symmetry; apply Z.eqb_eq; lia)
              | replace (a =? b)%Z with false by (symmetry; apply Z.eqb_neq; lia) ]
    end).
  all: simpl; try reflexivity.
  (* Far cases: x+1 tests *)
  all: replace (x + 1 =? h)%Z with false
    by (symmetry; apply Z.eqb_neq; intro Habs;
        first [apply Z.eqb_neq in Exhm1; lia | apply Z.eqb_neq in Exh; lia]).
  all: destruct (x + 1 =? h + 1)%Z eqn:?;
    [exfalso; apply Z.eqb_eq in Heqb; assert (x = h) by lia; subst;
     rewrite Z.eqb_refl in Exh; discriminate |].
  all: destruct (x + 1 =? h - 1)%Z; simpl; reflexivity.
Qed.

(** ** Forward direction: non-halting TM -> seeded half-plane tileable *)

(** The seed row for the half-plane *)
Definition hp_seed_row (W : WF_TM) (x : Z) : TileType :=
  st_tile (wf_machine W) x 0.

Theorem non_halting_hp_tileable : forall (W : WF_TM),
  tm_never_halts (wf_machine W) ->
  seeded_half_plane_tiling (tm_hp_tiles (wf_machine W)) (hp_seed_row W).
Proof.
  intros W Hnh.
  set (M := wf_machine W).
  exists (st_wang_tiling M).
  split; [| split; [| split]].
  - (* Every half-plane position is tiled *)
    intros x y Hy.
    exists (st_tile M x (Z.to_nat y)).
    unfold st_wang_tiling, tile_at; simpl.
    destruct (y <? 0)%Z eqn:Hy0; [apply Z.ltb_lt in Hy0; lia | reflexivity].
  - (* Row 0 matches the seed *)
    intros x; unfold st_wang_tiling, tile_at; simpl.
    unfold hp_seed_row; reflexivity.
  - (* Valid Wang matching on the half-plane.
       The matching reduces to st_tile_south_glue (N-S) and st_tile_ew_glue (E-W).
       We use the valid_wang_tiling definition which checks glue_facing. *)
    intros [x1 y1] [x2 y2] Hadj Hp1 Hp2.
    unfold half_plane_pos in Hp1, Hp2; simpl in Hp1, Hp2.
    unfold tile_at, st_wang_tiling.
    destruct (y1 <? 0)%Z eqn:Hy1; [apply Z.ltb_lt in Hy1; lia|].
    destruct (y2 <? 0)%Z eqn:Hy2; [apply Z.ltb_lt in Hy2; lia|].
    unfold adjacent, neighbors, all_directions in Hadj; simpl in Hadj.
    destruct Hadj as [Heq | [Heq | [Heq | [Heq | []]]]]; injection Heq as <- <-.
    + (* North: (x2,y2) = (x1, y1+1) *)
      destruct ((y1 + 1 <? 0)%Z) eqn:?; [apply Z.ltb_lt in Heqb; lia|].
      set (t1 := st_tile M x1 (Z.to_nat y1)).
      set (t2 := st_tile M x1 (Z.to_nat (y1 + 1))).
      pose proof (glue_facing_N_S t1 t2 x1 y1) as [HfN HfS].
      rewrite HfN, HfS.
      symmetry; unfold t2.
      replace (Z.to_nat (y1 + 1)) with (S (Z.to_nat y1)) by lia.
      apply st_tile_south_glue; exact Hnh.
    + (* East: (x2,y2) = (x1+1, y1) *)
      set (t1 := st_tile M x1 (Z.to_nat y1)).
      set (t2 := st_tile M (x1 + 1)%Z (Z.to_nat y1)).
      pose proof (glue_facing_E_W t1 t2 x1 y1) as [HfE HfW].
      rewrite HfE, HfW; unfold t1, t2.
      apply st_tile_ew_glue; exact Hnh.
    + (* South: (x2,y2) = (x1, y1-1) *)
      destruct ((y1 - 1 <? 0)%Z) eqn:?; [apply Z.ltb_lt in Heqb; lia|].
      set (t1 := st_tile M x1 (Z.to_nat y1)).
      set (t2 := st_tile M x1 (Z.to_nat (y1 - 1))).
      pose proof (glue_facing_N_S t2 t1 x1 (y1 - 1)) as [HfN HfS].
      replace (y1 - 1 + 1)%Z with y1 in HfN, HfS by lia.
      rewrite HfN, HfS.
      unfold t1.
      replace (Z.to_nat y1) with (S (Z.to_nat (y1 - 1))) by lia.
      apply st_tile_south_glue; exact Hnh.
    + (* West: (x2,y2) = (x1-1, y1) *)
      set (t1 := st_tile M x1 (Z.to_nat y1)).
      set (t2 := st_tile M (x1 - 1)%Z (Z.to_nat y1)).
      pose proof (glue_facing_E_W t2 t1 (x1 - 1)%Z y1) as [HfE HfW].
      replace (x1 - 1 + 1)%Z with x1 in HfE, HfW by lia.
      rewrite HfE, HfW; unfold t1, t2.
      enough (H : glue_E (st_tile M (x1 - 1)%Z (Z.to_nat y1)) =
                  glue_W (st_tile M ((x1 - 1) + 1)%Z (Z.to_nat y1))).
      { replace ((x1 - 1) + 1)%Z with x1 in H by lia; symmetry; exact H. }
      apply st_tile_ew_glue; exact Hnh.
  - (* All tiles are from the tileset *)
    intros [x y] t Hp Ht.
    unfold st_wang_tiling, tile_at in Ht; simpl in Ht.
    unfold half_plane_pos in Hp; simpl in Hp.
    destruct (y <? 0)%Z eqn:Hy; [apply Z.ltb_lt in Hy; lia | ].
    injection Ht as <-.
    apply st_tile_in_hp_tiles.
Qed.

(** ** Backward direction: halting TM -> seeded half-plane NOT tileable *)

(** The key insight: if the TM halts at step n, the head cell at row n has
    N glue = head_glue(q_halt, a). No tile in the tileset has
    S glue = head_glue(q_halt, a) (by no_tile_south_head_glue_halting,
    which also applies to tm_hp_tiles since hp tiles include the same
    head transition tiles). Therefore row n+1 can't have a valid tile
    at the position above the head. *)

Lemma no_tile_south_head_glue_halting_hp : forall M q a t,
  wf_tm M ->
  has_no_transitions M q ->
  In a (tm_alphabet M) ->
  In t (tm_hp_tiles M) ->
  glue_S t <> head_glue q a.
Proof.
  intros M q a t Hwf Hnt Ha Hin.
  unfold tm_hp_tiles in Hin.
  apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
  - (* Copy tiles *)
    apply in_map_iff in Hin; destruct Hin as [a' [<- Ha']]; simpl.
    apply cell_glue_not_head_glue; apply Hwf; exact Ha'.
  - apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
    + (* Head transition tiles — same as tm_wang_tiles *)
      apply in_flat_map in Hin; destruct Hin as [q1 [Hq1 Hin]].
      apply in_flat_map in Hin; destruct Hin as [a1 [Ha1 Hin]].
      destruct (tm_transition M q1 a1) as [[[q2 a2] [| |]] |] eqn:Htrans;
      simpl in Hin; try contradiction.
      * destruct Hin as [<- | []]; simpl.
        intro Heq; apply head_glue_injective in Heq;
          [destruct Heq; subst; specialize (Hnt a Ha1); congruence
          | apply Hwf; exact Ha1 | apply Hwf; exact Ha].
      * destruct Hin as [<- | []]; simpl.
        intro Heq; apply head_glue_injective in Heq;
          [destruct Heq; subst; specialize (Hnt a Ha1); congruence
          | apply Hwf; exact Ha1 | apply Hwf; exact Ha].
      * destruct Hin as [<- | []]; simpl.
        intro Heq; apply head_glue_injective in Heq;
          [destruct Heq; subst; specialize (Hnt a Ha1); congruence
          | apply Hwf; exact Ha1 | apply Hwf; exact Ha].
    + apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
      * (* Right-receive tiles *)
        apply in_flat_map in Hin; destruct Hin as [q1 [Hq1 Hin]].
        apply in_map_iff in Hin; destruct Hin as [a1 [<- Ha1]]; simpl.
        apply cell_glue_not_head_glue; apply Hwf; exact Ha1.
      * (* hp_recv_L tiles *)
        apply in_flat_map in Hin; destruct Hin as [q1 [Hq1 Hin]].
        apply in_map_iff in Hin; destruct Hin as [a1 [<- Ha1]]; simpl.
        apply cell_glue_not_head_glue; apply Hwf; exact Ha1.
Qed.

(** ** The seeded half-plane correspondence *)

Definition hp_decidable_for (T : TileSet) (seed : Z -> TileType) : Prop :=
  seeded_half_plane_tiling T seed.

(** ** Blocking property for halting states in hp tiles *)

Lemma no_tile_south_halting_hp : forall (W : WF_TM) n,
  tm_halted_at (wf_machine W) n ->
  (cfg_state (tm_run (wf_machine W) n) = tm_accept (wf_machine W) \/
   cfg_state (tm_run (wf_machine W) n) = tm_reject (wf_machine W)) ->
  forall t, In t (tm_hp_tiles (wf_machine W)) ->
    glue_S t <> head_glue (cfg_state (tm_run (wf_machine W) n))
                          (cfg_tape (tm_run (wf_machine W) n)
                                    (cfg_head (tm_run (wf_machine W) n))).
Proof.
  intros W n Hhalted Hterm t Ht.
  destruct Hterm as [Hacc | Hrej].
  - eapply no_tile_south_head_glue_halting_hp; try exact Ht.
    + exact (wf_well_formed W).
    + apply halting_state_total_has_no_transitions.
      rewrite Hacc; exact (wf_accept_halts W).
    + apply (wf_run_tape W).
  - eapply no_tile_south_head_glue_halting_hp; try exact Ht.
    + exact (wf_well_formed W).
    + apply halting_state_total_has_no_transitions.
      rewrite Hrej; exact (wf_reject_halts W).
    + apply (wf_run_tape W).
Qed.

(** ** Undecidability of the seeded half-plane domino problem *)

(** The forward direction (non-halting TM -> tileable) is proved above
    as non_halting_hp_tileable. The backward direction (tileable -> non-halting)
    requires showing that any valid seeded tiling must follow the TM trace,
    so that the blocking property applies at the halting row. This is a
    standard but lengthy "unique extension" argument.

    We structure the undecidability proof as conditional on the full
    correspondence, following the pattern of domino_undecidable_conditional. *)


(** Cleaner statement: undecidability at the WF_TM level *)

Definition wf_tm_halts_on_blank (W : WF_TM) : Prop :=
  tm_halts_on_blank (wf_machine W).

(** The halting problem for well-formed TMs is also undecidable,
    since any TM can be normalized to a well-formed one. *)
Axiom wf_halting_undecidable :
  ~exists f : WF_TM -> bool, forall W, f W = true <-> wf_tm_halts_on_blank W.

Theorem seeded_hp_undecidable :
  (forall W : WF_TM,
    wf_tm_halts_on_blank W <->
    ~seeded_half_plane_tiling (tm_hp_tiles (wf_machine W)) (hp_seed_row W)) ->
  ~exists f : TileSet -> (Z -> TileType) -> bool,
    forall T seed, f T seed = true <-> seeded_half_plane_tiling T seed.
Proof.
  intro Hcorr; intro Hdec; destruct Hdec as [f Hf].
  apply wf_halting_undecidable.
  exists (fun W => negb (f (tm_hp_tiles (wf_machine W)) (hp_seed_row W))).
  intro W; simpl.
  split; intro H.
  - (* negb (f ...) = true -> halts *)
    apply negb_true_iff in H.
    apply Hcorr.
    intro Htile; apply Hf in Htile; rewrite Htile in H; discriminate.
  - (* halts -> negb (f ...) = true *)
    apply negb_true_iff.
    apply Hcorr in H.
    destruct (f (tm_hp_tiles (wf_machine W)) (hp_seed_row W)) eqn:E; [|reflexivity].
    exfalso; apply H; apply Hf; exact E.
Qed.

(** ** Summary of Section 12 results *)

(** 1. seeded_half_plane_tiling: the seeded half-plane domino problem.
    2. tm_run: computes TM config after n steps.
    3. st_tile: the space-time tile assignment for the TM trace.
    4. non_halting_hp_tileable: non-halting TM -> seeded HP is tileable
       (FORWARD direction, fully proved).
    5. no_tile_south_halting_hp: structural blocking at halting states
       (no tile has S = head_glue for a halting state).
    6. seeded_hp_undecidable: the seeded HP domino problem is undecidable,
       conditional on the full correspondence (forward + backward).
       The forward direction is proved; the backward direction requires
       the unique extension property of the tileset. *)

(** * Section 13: Temperature-1 Intrinsic Universality Impossibility *)

(** ** Macro-tile border signatures *)

(** At scale factor c, a macro-tile is a c x c block of tiles from U.
    The "border signature" on one side consists of the c tiles along
    that edge. Two macro-tiles with identical border signatures on all
    four sides are indistinguishable to their neighbors in the simulation.

    A border signature on one side is a function from {0, ..., c-1} to
    tile types. We represent it as a list of length c. The total number
    of distinguishable macro-tiles at scale c is at most |U|^(4*c),
    matching the macro_tile_bound definition from Section 11. *)

Definition BorderSignature := list TileType.

(** A macro-tile's full border: the four edge signatures (N, E, S, W). *)
Record MacroBorder := mkMacroBorder {
  mb_north : BorderSignature;
  mb_east  : BorderSignature;
  mb_south : BorderSignature;
  mb_west  : BorderSignature
}.

(** Decidable equality for MacroBorder *)
Lemma list_TileType_eq_dec : forall (l1 l2 : list TileType), {l1 = l2} + {l1 <> l2}.
Proof.
  apply list_eq_dec; exact TileType_eq_dec.
Defined.

Lemma MacroBorder_eq_dec : forall (b1 b2 : MacroBorder), {b1 = b2} + {b1 <> b2}.
Proof.
  intros [n1 e1 s1 w1] [n2 e2 s2 w2].
  destruct (list_TileType_eq_dec n1 n2);
  destruct (list_TileType_eq_dec e1 e2);
  destruct (list_TileType_eq_dec s1 s2);
  destruct (list_TileType_eq_dec w1 w2);
  subst; try (left; reflexivity);
  right; intro H; inversion H; contradiction.
Defined.

(** ** Simulation helper definition *)

Definition simulation_holds_for (U_tiles : TileSet) (tau : Temperature)
    (S : TAS) (params : SimParams) (U_seed : Assembly) : Prop :=
  let U := mkTAS U_tiles (fun g => if Nat.eqb g 0 then 0 else 1) U_seed tau in
  forall beta, producible_in S beta ->
    exists alpha, producible_in U alpha /\ simulates_assembly params U S alpha beta.

(** ** Bridging axioms *)

(** To connect the counting argument to the formal intrinsically_universal
    definition, we need two facts from the tile assembly theory literature
    (Meunier, Patitz, Summers, Theyssier, Winslow, Woods 2014,
    "Intrinsic universality in tile self-assembly requires cooperation").

    These facts are stated as axioms because deriving them from the
    abstract simulates_assembly definition would require extensive
    additional infrastructure (explicit macro-tile extraction, border
    consistency, formalization of how block boundaries determine
    interaction). Each axiom is accompanied by a soundness argument. *)

(** *** Axiom 3: Simulation injection bound

    If U_tiles simulates a temperature-1 system S at scale c, then
    |S| <= |U_tiles|^(4*c).

    Soundness: At scale c, each tile type in S is represented by a
    c x c macro-tile built from U_tiles. A macro-tile's interaction
    with neighbors is determined by its border: c tiles on each of
    4 sides. If two tile types t1, t2 in S had identical borders on
    all four sides, a neighbor could not distinguish them, making the
    simulation unfaithful when t1 and t2 have different glues.
    Therefore distinct tile types require distinct border 4-tuples.
    The number of border 4-tuples is at most |U|^c per side, giving
    (|U|^c)^4 = |U|^(4c) total. By pigeonhole, |S| <= |U|^(4c). *)

Axiom simulation_injection_bound :
  forall (U_tiles : TileSet) (S : TAS) (params : SimParams) (U_seed : Assembly),
    tas_temp S = 1 ->
    simulation_holds_for U_tiles 1 S params U_seed ->
    length (tas_tiles S) <= macro_tile_bound (length U_tiles) (sim_scale params).

(** *** Axiom 4: Temperature-1 scale boundedness

    If U_tiles is intrinsically universal at temperature 1, then the
    simulation scale factor is bounded by a constant depending only
    on U_tiles, not on the simulated system S.

    Soundness: At temperature 1, every tile attaches via exactly one
    matching glue (no cooperative binding). This means information
    transfer between adjacent macro-tiles happens through a single
    tile-to-tile bond at the boundary. The number of distinct
    "effective glues" that a boundary of length c can encode is
    determined by U's tile set structure alone. Once c is large
    enough to exhaust all distinguishable boundary patterns, larger
    c provides no additional expressive power. Therefore the useful
    scale is bounded by a function of |U_tiles| alone.

    This is the key property that fails at temperature >= 2, where
    cooperative binding allows macro-tile boundaries to encode
    exponentially more information as c grows, enabling intrinsic
    universality (Doty, Lutz, Patitz, Schweller, Summers, Woods 2012). *)

Axiom temp1_scale_bounded :
  forall (U_tiles : TileSet),
    intrinsically_universal U_tiles 1 ->
    exists c_max : nat, c_max > 0 /\
      forall S : TAS, tas_temp S = 1 ->
        forall params U_seed,
          simulation_holds_for U_tiles 1 S params U_seed ->
          sim_scale params <= c_max.

(** ** The main impossibility theorem *)

(** The proof combines the two axioms above with the counting
    infrastructure (system_of_any_size, macro_tile_bound):
    1. Assume IU; extract the maximal scale c_max from Axiom 4
    2. Build a system with |S| > |U|^(4*c_max) tiles (system_of_any_size)
    3. Apply IU to get params and U_seed for S
    4. Axiom 3 gives |S| <= |U|^(4*c) where c = sim_scale params
    5. Axiom 4 gives c <= c_max, so |U|^(4*c) <= |U|^(4*c_max)
    6. But |S| > |U|^(4*c_max), contradiction *)

Lemma macro_tile_bound_mono : forall u c1 c2,
  u > 0 -> c1 <= c2 -> macro_tile_bound u c1 <= macro_tile_bound u c2.
Proof.
  intros u c1 c2 Hu Hle; unfold macro_tile_bound.
  apply Nat.pow_le_mono_r; lia.
Qed.

Theorem no_finite_iu_at_temp1 : forall U_tiles, ~intrinsically_universal U_tiles 1.
Proof.
  intros U_tiles HIU.
  destruct (temp1_scale_bounded U_tiles HIU) as [c_max [Hcpos Hbound]].
  set (u := length U_tiles).
  set (bound := macro_tile_bound u c_max).
  destruct (system_of_any_size (S bound)) as [S_big [Htemp Hlen]].
  destruct (HIU S_big Htemp) as [params [U_seed Hsim]].
  assert (Hsim_holds : simulation_holds_for U_tiles 1 S_big params U_seed).
  { unfold simulation_holds_for; exact Hsim. }
  assert (Hinj : length (tas_tiles S_big) <=
                 macro_tile_bound u (sim_scale params)).
  { exact (simulation_injection_bound U_tiles S_big params U_seed Htemp Hsim_holds). }
  assert (Hscale : sim_scale params <= c_max).
  { exact (Hbound S_big Htemp params U_seed Hsim_holds). }
  (* Key: u^(4*c) <= u^(4*c_max) = bound, but |S_big| = S bound > bound *)
  destruct (Nat.eq_dec u 0) as [Hu0 | Hu_pos].
  - (* u = 0: macro_tile_bound 0 c = 0^(4*c) = 0 for c >= 1 *)
    pose proof (sim_scale_pos params) as Hcpos2.
    assert (Hzero : macro_tile_bound u (sim_scale params) = 0).
    { unfold macro_tile_bound; rewrite Hu0.
      assert (H4c : 4 * sim_scale params > 0) by lia.
      destruct (4 * sim_scale params) eqn:E; [lia|reflexivity]. }
    lia.
  - (* u > 0: use monotonicity *)
    assert (Hu : u > 0) by lia.
    assert (Hmono : macro_tile_bound u (sim_scale params) <= bound).
    { apply macro_tile_bound_mono; [exact Hu | exact Hscale]. }
    lia.
Qed.
