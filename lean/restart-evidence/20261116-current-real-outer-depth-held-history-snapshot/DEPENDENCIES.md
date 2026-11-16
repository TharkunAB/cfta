# Actual proof dependencies

Status: UNCOMPILED. Root must check every pending dependency first.

Append this code after the following owner components.

1. Existing scoped history components, including the exact global depth
   predicate and the checked `real_held_fragment_history_depth_zero` base.
2. Repaired original-budget prefix history module, raw SHA256 `5803fed477359f4129cded2294e58b0792c5081a3d08ff39184b0bee961ddb5f`.
   The owner needs its ordinary import at the file top.
3. Parked companion from `20261116-current-real-parked-restart-held-history-compose-repair`.
4. Right-prefix companion from `20261116-current-real-right-prefix-prepared-held-history-draft`.
   Its frozen header SHA256 is `ae97007874cf21235c5e8fe1c9c90512a02b62552b441517b4d063515c8b80b5`.
   It uses the actual successful preparation and opaque companions.
5. This `APPEND.lean.txt`, then its appendable probes.

The full-depth proof reuses the already checked resource-depth theorem. It does
not add a resource IH to its own header. It also reuses the checked zero-depth
history theorem instead of copying that proof.

The intermediate expand proof follows the literal seven runtime prefix branches.
Only the continuing parked and narrowed branches can produce outputs. Their
helpers retain every output before a later stop. The other five branches have
literal empty emitted lists. No native endpoint is treated as an enum-cache
history receipt.
