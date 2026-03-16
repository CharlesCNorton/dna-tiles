# dna-tiles — Gaps and Weaknesses

31 issues identified by full-file audit (8195 lines, Rocq 9.0.0).
Arranged in logical completion order: each phase depends on the previous.

---

## Phase 1: Fix Foundational Definitions

Everything downstream depends on the mathematical objects being correct.

- [ ] **1. Enforce assembly finiteness.**
  `Assembly = Position -> option TileType` admits infinite assemblies.
  Standard aTAM requires finite assemblies. Add a finiteness predicate
  (e.g., `exists l, forall p, a p <> None -> In p l`) and thread it
  through `producible_in`, `multi_step`, and all simulation definitions.

- [ ] **2. Enforce assembly connectedness.**
  Standard aTAM requires assemblies to be connected subsets of Z^2.
  `multi_step` can currently place tiles at positions with no path to
  the seed. Add a connectedness invariant to the growth relation.

- [ ] **3. Constrain seed assemblies.**
  Standard aTAM starts from a single seed tile. The formalization allows
  arbitrary (possibly infinite, disconnected) seed assemblies. Either
  restrict seeds to single tiles or to finite connected assemblies, and
  document which theorems require which assumption.

- [ ] **4. Define terminal assemblies.**
  The aTAM notion of terminal assembly (no further tile can attach) is
  absent. This defines what a system "computes." Add `terminal : TAS ->
  Assembly -> Prop` and connect it to producibility.

- [ ] **5. Define local determinism.**
  Standard aTAM distinguishes locally deterministic TAS (at most one
  tile type can bind at each position given the current assembly state).
  This is critical for determinism/confluence to be meaningful. Define
  the predicate and add it as a precondition where needed.

- [ ] **6. Add uniqueness constraint to Block.**
  `Block = list (Position * TileType)` allows the same position to
  appear multiple times with different tiles. Add a functional
  constraint (no duplicate positions) or switch to a map type.

- [ ] **7. Fix the empty-block loophole in `simulates_assembly`.**
  The standard `simulates_assembly` accepts `nil` blocks (confirmed by
  the existence of `nontrivial_simulates_assembly` which adds `block <>
  nil`). With nil blocks, `intrinsically_universal` is trivially
  satisfiable by any tileset — choose alpha = seed, use nil blocks
  everywhere. **This potentially invalidates the entire standard IU
  framework.** Fix: require `block <> nil` in the base definition, or
  retire the base definition in favor of the nontrivial variant.

- [ ] **8. Derive `effective_behaviors` from the simulation framework.**
  Currently hardcoded as `2^(4 * |U|)`. This formula counts 4-glue
  assignments but the actual number of distinguishable behaviors depends
  on the simulation relation, scale, and strength function. Derive the
  bound from first principles or prove it is an upper bound on
  distinguishable macro-tile behaviors.

- [ ] **9. Verify `scale_position` injectivity and adjacency preservation.**
  The simulation maps positions by scaling. No proof that scaled
  positions don't collide or that adjacency structure is preserved.
  Prove both properties.

- [ ] **10. Verify `encode_tas_description` injectivity and decodability.**
  Used in the v2 UTM construction. Injectivity (distinct systems produce
  distinct encodings) is needed for the simulation to be faithful. Prove
  injectivity, or at minimum prove that the encoding is decodable.

---

## Phase 2: Computational Validation

Before proving hard theorems on corrected definitions, verify them
against known examples.

- [ ] **11. Add `Compute` checks and concrete TAS examples.**
  Define small TAS instances (e.g., a 2-tile temperature-1 system), run
  assembly steps via `Compute` or `Eval`, verify producibility claims
  concretely. A `Compute` check would have caught the east-glue
  mismatch that the formalization itself discovered.

- [ ] **12. Deduplicate witness machines.**
  `always_halting_tm` / `never_halting_tm` (used in classical
  discharges) and `halting_machine` / `nonhalting_machine` (Section 24,
  with full well-formedness proofs) serve the same purpose. Unify to one
  pair and verify well-formedness once.

---

## Phase 3: Transfer Existing Results to Corrected Definitions

Adapt proofs that currently target `strong_iu` or vacuous definitions
to the corrected framework.

- [ ] **13. Prove lower bound of 2 for corrected `intrinsically_universal`.**
  Currently proved only for `strong_iu` (which includes the behavior
  bound). Results.v:2237 acknowledges the gap. With the empty-block
  loophole fixed (#7), the standard definition becomes non-trivial and
  the lower bound should transfer.

- [ ] **14. Prove computational faithfulness of TM-to-tile encoding.**
  The forward Berger direction (non-halting → tileable) is proved, but
  the correspondence between tiling rows and TM configurations is only
  used implicitly. State and prove as a standalone theorem: row y of
  `fp_wang_tiling M` encodes `tm_run M (y-1)`.

- [ ] **15. Characterize simulation scale constraints.**
  The simulation relation parameterizes over scale but no results
  constrain achievable or necessary scales. The fixed-scale counting
  argument (Advanced.v:3526) shows 1 tile is insufficient at any fixed
  scale, but the standard IU definition allows variable scale per
  system. Resolve this gap or formally state it as an open problem.

- [ ] **16. Prove cooperative binding characterization.**
  The distinction between temperature 1 (non-cooperative) and
  temperature >= 2 (cooperative) is central to aTAM theory. Currently
  only the IU impossibility at temp 1 is proved. Formally characterize
  what cooperative binding enables beyond non-cooperative.

---

## Phase 4: Replace Classical Discharges with Genuine Proofs

Each of these "proofs" uses `excluded_middle_informative` to case-split
on an undecidable property, producing witnesses that carry zero
computational content. They are logically valid in classical Rocq but
mathematically vacuous.

- [ ] **17. Replace `cts_turing_complete_proof` with actual Cocke-Minsky
  encoding.**
  Current proof (Advanced.v:2453): case-splits on halting, returns a
  trivially halting or trivially looping CTS. Needed: construct a CTS
  and initial word that simulate the given TM step-by-step. This is the
  Cocke-Minsky (1964) / Matthew Cook encoding.

- [ ] **18. Replace `rule110_simulates_cts_proof` with actual Cook 2004
  encoding.**
  Current proof (Advanced.v:2664): witnesses are constant functions
  `(fun _ => sentinel_assembly)` and `(fun n => n)`. Needed: the actual
  170-page Cook encoding from CTS configurations to Rule 110 cell
  patterns, verified case-by-case. This is the hardest single item on
  the list.

- [ ] **19. Replace `utm_row_correspondence_proof` with actual row
  correspondence.**
  Current proof (Advanced.v:2624): tile assignment is `(fun _ =>
  control_tile_start)`. Every position gets the same tile. Needed: a
  tile assignment that reflects the actual TM computation at each row.

- [ ] **20. Replace `tm_normalizable_proof` with syntactic TM
  transformation.**
  Current proof (Advanced.v:2388): case-splits on halting, returns a
  hardcoded machine. Needed: a function that syntactically transforms
  any TM into a well-formed TM preserving halting behavior (e.g., by
  remapping states and adding missing transitions).

- [ ] **21. Replace `input_encoding_reducible_proof` with actual input
  encoding.**
  Current proof (Advanced.v:2474): returns `halting_machine`
  unconditionally; the hypothesis `Hacc` is unused in the witness.
  Needed: construct a TM M' that simulates M on the given input using
  blank tape (standard input-encoding reduction).

- [ ] **22. Replace `aperiodicity_hypothesis_proof` with actual Robinson
  1971 construction.**
  Current proof (Advanced.v:2713): case-splits on the origin-constrained
  domino problem, returns the tileset or `nil`. Needed: construct
  aperiodicity-enforcing tiles that embed computation, per Robinson 1971.

---

## Phase 5: Prove Conditional Hypotheses

These are the hard mathematical results that the formalization currently
assumes. Each is a substantial theorem in its own right.

- [ ] **23. Prove `fp_correspondence` backward direction.**
  (Results.v:2745) The unique extension argument: any valid full-plane
  tiling of `fp_tileset M` with `fp_start_tile M` at the origin must
  encode the TM computation of M. If M halts, the blocking property
  prevents tiling above the halting row, contradicting `tiles_plane`.
  This is a detailed inductive argument (Berger 1966, Robinson 1971).

- [ ] **24. Prove `berger_correspondence`.**
  (Results.v:3054) Construct a Berger-style tileset for each WF_TM such
  that the tileset tiles the plane iff the TM does not halt. Requires
  aperiodicity-enforcing tiles that prevent inert (copy-only) tilings.
  Depends on #22.

- [ ] **25. Prove `utm_row_correspondence_v2`.**
  (Advanced.v:3643) For every temp-2 system S and producible assembly
  beta, exhibit a producible assembly in the UTM system that simulates
  beta via the row correspondence. Depends on #18 and #19.

- [ ] **26. Prove `temp2_simulation_faithful_v2`.**
  (Advanced.v:3707) The full UTM simulation faithfulness theorem.
  Subsumes #25. This is the capstone of the IU construction.

---

## Phase 6: Infrastructure Improvements

- [ ] **27. Add Ltac/Ltac2 automation and hint databases.**
  Every proof is currently manual. Recurring patterns (glue matching,
  region case splits, Z arithmetic) should be automated. Add `Hint
  Resolve` databases for tile membership and `Ltac` tactics for the
  Wang tiling validity pattern.

- [ ] **28. Add abstract axiomatization.**
  Define typeclasses or module signatures for tile systems, assembly
  growth, and simulation relations. This separates the aTAM theory from
  the concrete representation and makes the framework reusable for
  variants (2HAM, kTAM, staged assembly).

---

## Phase 7: Mathematical Extensions

- [ ] **29. Formalize temperature programming theory.**
  Temperature is a parameter but the theory of how temperature affects
  computational power is unexplored beyond temp-1 impossibility and
  temp-2 IU. The sharp phase transition between temp 1 and temp 2 is a
  central result in the field.

- [ ] **30. Prove standard IU impossibility result.**
  `no_strong_iu_any_temp` proves impossibility for the behavior-bounded
  `strong_iu` definition. For the standard `intrinsically_universal`
  definition (after fixing #7), impossibility at temp 1 is proved, but
  the minimum tile set size at temp 2 remains open (2 <= n <= 248).
  Tighten the bounds.

- [ ] **31. Formalize cooperative binding geometry.**
  Improving the standard IU lower bound beyond 2 requires showing that
  no 2-tile system at temperature 2 can simulate all temp-2 TAS. This
  requires geometric arguments about cooperative binding that go beyond
  glue-counting. Currently acknowledged as open (Advanced.v:2836).

---

## Score Before Cures

| Dimension | Score |
|---|---|
| Compilation | 10/10 |
| Organization | 9/10 |
| Fully-proved substance | 6/10 |
| Classical discharges | 3/10 |
| Completeness vs. claims | 5/10 |
| Novelty | 7/10 |
| Proof engineering | 6/10 |
| **Overall** | **6/10** |
