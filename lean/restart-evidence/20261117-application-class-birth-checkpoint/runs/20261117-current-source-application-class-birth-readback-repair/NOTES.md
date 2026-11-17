# Exact-header application birth repair

UNCOMPILED. The original candidate and failed check remain unchanged.

The FIRST public header09764d59 is byte-exact. All definitions, source inputs, operational conclusions, allocation order, ordered path lists and default limits are unchanged.

Two proof-local repairs address the actual diagnostics:

1. `pathReadback`: replace `rfl` by `cbv`. The actual trie constructor groups child keys in increasing order and reads each child in that order. The frozen path lists already use this order. `cbv` computes the existing trie construction and readback; it does not replace ordered equality by membership or permutation.
2. The final indexed-bucket proof: replace the ineffective `Nat.zero_add` simplification with `Function.comp_def`. The actual diagnostic retained a composed map function and its tuple projections. This reduction exposes the same literal inherited-plus-own bucket.

The appended probe file removes its import. Root appends these probes to the candidate source. An import after a theorem is invalid Lean syntax. No logical statement or proof changed for this harness repair.

The source-field propagation boundary remains as described in the original packet. This candidate proves only initial class birth from a genuine row certificate and actual own preparation. Later compatibility, TypeIn, all-history constraints and one finite accepted completion remain open.
