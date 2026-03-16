# Remaining Work

All items discharged. See dna_tiles.v section comments for details.

## Discovered issues during discharge

| Item | Finding |
|------|---------|
| `kleene_recursion_theorem` | Refuted — definition quantifies over non-computable functions. Real Kleene requires computability restriction. |
| `all_encoding_tiles_in_utm` | Refuted — `encode_value_tile` produces tiles with east glue 0, but all UTM tiles have non-zero east glue. Encoding needs redesign. |

## Potential future work

| Task | Notes |
|------|-------|
| Fix `kleene_recursion_theorem` definition to restrict to computable g, then prove | Requires Gödel encoding + UTM |
| Fix `encode_value_tile` to match UTM tileset glue structure | Mechanical once the encoding scheme is corrected |
| Improve IU lower bound beyond 4 for `strong_iu` | Structural argument needed beyond glue counting |
| Improve IU lower bound beyond 2 for standard `intrinsically_universal` | Needs cooperative binding analysis |
| Construct explicit IU tile set and verify | The Doty et al. construction, mechanized |
