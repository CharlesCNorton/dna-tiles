# Remaining Work

| Order | Task |
|-------|------|
| 1 | Restrict `kleene_recursion_theorem` to computable functions by adding a computability predicate on g, then prove it. The current definition was refuted because it quantifies over all functions including non-computable ones like halting-flip. The fix is a new `computable` wrapper using Gödel indices, then the standard diagonal argument goes through. |
| 2 | Fix `encode_value_tile` east glue from 0 to a non-zero value matching the UTM tileset structure, then re-prove `all_encoding_tiles_in_utm`. The current encoding was refuted because all UTM tiles have non-zero east glue (1-4) while encoding tiles produce 0. Change the encoding to use east glue 3 or similar and verify membership. |
| 3 | Improve the IU lower bound beyond 4 for `strong_iu` by analyzing how many distinct border behaviors a k-tile set can produce and showing k=4 is still too few. The current bound comes from `effective_behaviors` counting; a structural argument about glue compatibility would tighten it. |
| 4 | Improve the IU lower bound beyond 2 for standard `intrinsically_universal` by showing that cooperative binding with only 2 tile types can't encode enough distinct macro-tile interfaces. This needs analysis of how temp-2 cooperation amplifies border expressiveness. |
| 5 | Construct the Doty et al. 248-tile IU set (or our 8-10 tile UTM variant) concretely, enumerate every tile, and prove it simulates any temp-2 TAS. The tile definitions are mechanical; the simulation proof is case analysis on how each simulated tile type maps to a macro-tile block. |
