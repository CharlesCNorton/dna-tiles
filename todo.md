# Remaining Work

| Order | Task |
|-------|------|
| 1 | Redefine `kleene_recursion_theorem` with a computability predicate on g and prove it. We refuted the old version by finding the halting-flip counterexample. The fix: Gödel indices for computable functions, then the diagonal argument closes. |
| 2 | Redesign `encode_value_tile` with non-zero east glue and prove UTM tile membership. We refuted the old encoding by showing the glue mismatch. The fix: switch east glue from 0 to 3, re-prove `In` for all cases. |
| 3 | Push the `strong_iu` lower bound past 4 by proving that small tile sets can't generate enough distinct border behaviors. The counting argument already got us to 4; a compatibility analysis on glue pairing will push higher. |
| 4 | Push the standard `intrinsically_universal` lower bound past 2 by proving that 2-tile cooperative systems can't encode enough macro-tile interfaces. Direct analysis of how temp-2 binding amplifies expressiveness. |
| 5 | Build the full IU tile set, enumerate every tile, and prove it simulates any temp-2 TAS. Tile definitions, then macro-tile block construction, then simulation proof by exhaustive case analysis. |
