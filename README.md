# DNA Tile Self-Assembly: Formal Verification

Machine-checked formalization of the abstract Tile Assembly Model (aTAM) in Rocq 9.0.0.

## Build

```
make
```

Requires [Rocq](https://rocq-prover.org/) 9.0.0 with OCaml 4.14.

## Structure

| File | Lines | Contents |
|------|-------|----------|
| `Core.v` | 1264 | aTAM definitions, assembly dynamics, determinism, confluence, diamond property, unique terminal assembly, Wang tilings, Turing machines, Rule 110, intrinsic universality definitions |
| `Results.v` | 3136 | Temperature-1 unique parent, domino problem undecidability, origin-constrained and full-plane Berger correspondence, IU impossibility at temperature 1, staged assembly model, IU construction framework, tile set size bounds |
| `Advanced.v` | 3795 | Assembly infrastructure (Manhattan distance, finite assemblies, union, restriction), cooperative binding theory, computation structure forcing, halting undecidability from Kleene, universality reductions, staged assembly hierarchy, corrected Kleene recursion theorem, corrected UTM encoding, IU lower bounds |

## Results

399 theorems. 0 axioms. 0 admitted proofs.

### Core theory (known results, machine-verified)

- Locally deterministic TAS have unique terminal assemblies
- The diamond property holds for all locally deterministic TAS
- Every producible assembly is a subassembly of every terminal assembly
- TM computation at temperature 2 via tile correspondence
- Rule 110 encodes all transitions with 8 tiles and cooperative binding
- Non-halting TMs produce valid full-plane Wang tilings
- Halting states block tiling extension
- 2-stage assembly strictly extends 1-stage assembly
- No finite tile set is strongly intrinsically universal at any temperature

### New results

- **Kleene ↔ halting undecidability.** The recursion theorem restricted to decidable-image functions is logically equivalent to the undecidability of the halting problem. Each implies the other with no additional assumptions. (`kleene_restricted_iff_halting_undecidable` in Advanced.v)

- **Unrestricted Kleene is false.** The standard informal statement "for all functions g, there exists a fixed point" is provably false when g ranges over all functions rather than computable ones. Counterexample: the halting-flip function, which maps halting TMs to a looping TM and vice versa. (`kleene_refuted` in Advanced.v)

- **UTM encoding glue mismatch.** The natural encoding of system descriptions as tiles produces tiles with east glue 0, but all tiles in the UTM tileset have non-zero east glue (1-4). This is a concrete bug in the tile construction that would cause assembly failure. Fixed with a corrected encoding and per-system extended tileset. (`all_encoding_tiles_in_utm_refuted`, `all_encoding_tiles_in_utm_v2_proof` in Advanced.v)

### Foundations

All theorems reduce to Rocq's type theory plus classical logic (`classic` from `Logic.Classical`) and constructive indefinite description (`ClassicalEpsilon`). Two propositions are stated as `Definition : Prop` and used as hypotheses where needed:

- `halting_undecidable` — the halting problem is undecidable (derived from `kleene_restricted`)
- `wf_halting_undecidable` — same for well-formed TMs (derived from `halting_undecidable` via normalization)

## References

- E. Winfree. *Algorithmic Self-Assembly of DNA.* PhD thesis, Caltech, 1998.
- D. Soloveichik, E. Winfree. *Complexity of Self-Assembled Shapes.* SIAM J. Comput., 2007.
- R. Berger. *The Undecidability of the Domino Problem.* Memoirs AMS, 1966.
- M. Cook. *Universality in Elementary Cellular Automata.* Complex Systems, 2004.
- D. Doty, J. Lutz, M. Patitz, R. Schweller, S. Summers, D. Woods. *The Tile Assembly Model is Intrinsically Universal.* FOCS, 2012.
- P. Meunier, M. Patitz, S. Summers, G. Theyssier, A. Winslow, D. Woods. *Intrinsic Universality in Tile Self-Assembly Requires Cooperation.* SODA, 2014.
