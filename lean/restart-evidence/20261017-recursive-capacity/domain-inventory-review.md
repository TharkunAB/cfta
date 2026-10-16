# Canonical original-domain inventory

Date: 2026-10-17 00:43 CEST. Source: `SourceRecursiveIntersectionDomainInventory.lean`, 175 lines, SHA256 `90ad6b5d91aa29fca22cf55cd1389c0ea8b18a781ac06967ab827f65d6fde431`.

The module constructs an explicit list of all supported canonical typed domain keys from two initial lists. The first list contains original binder identities. The second list contains original operand-identity pairs. There is no future-key list or completed execution premise.

`Supported` records canonical order, typed free entries, and membership in the two initial carriers. A typed free entry maps `name` to `NodeRef.mu name`. It cannot choose another binder or carry an arbitrary value. `canonical` sorts and removes repeated names and pairs. `inventory` reuses `SourceLeafRowProgress.subsets` for both initial lists. It maps the Cartesian product of those existing subset lists to canonical keys.

`mem_inventory_iff` proves both directions. Soundness follows from subset membership and canonicalization. Completeness filters the initial carrier lists by the actual domain's names and pairs. These filters are enumerated subsets. Typed free-entry reconstruction and canonical domain extensionality identify the resulting key with the actual key.

`inventory_length` gives exactly `2^(binders.length+pairs.length)` list entries. The inventory list can contain duplicate canonical keys when the initial carriers contain duplicates. This only enlarges the conservative bound. `supported_length_le` bounds any distinct supported key list by the same initial number. `Supported.mono` and `inventory_mono` permit larger initial carriers.

`supported_empty` and `empty_mem` cover the actual reserved empty key. `Supported.extend` and `extend_mem` follow literal `SourceRecursiveIntersectionDomain.extend`. Their only additional inputs state that the newly encountered binder names and operand pair belong to the initial carriers. No successful recursive request or future domain is an input. Repeated binder names and pairs are permitted. Canonicalization retains own-identity bindings and ordered distinct pair keys.

This is a pure finite-carrier foundation. It does not yet show that every prefix of a current recursive query remains in that carrier, or bound the physical domain cache after an arbitrary current prefix. The separate source-inventory and allocation modules can supply those steps. The domain wrapper shifts nonempty raw cache identities by one; this module bounds structural keys, so a later numeric range theorem must retain that shift and the signed first-key margin. The inventory is for one query's fixed original input heap. It is not a fixed carrier for all later outer reductions.

## Validation

The pinned Lean 4.34.1 direct source check passed with all linters, no warnings, and exit 0 in `domain-inventory-direct-3.log`. The shared canonical build then passed 380 jobs in `inventory-allocation-build.log`; this component was target 380. Root owns that canonical invocation. No Lake process was started by this component owner.

The imported public probe checks all 19 explicit public declarations and four Supported field accessors: 23 axiom/full-signature pairs. Five imported integration pairs passed:

- Two actual source extensions with repeated names retain exactly the two initial names and pairs, canonical order, and typed readback.
- A finite sequence of literal extensions stays inside the same initial inventory, with no bound on sequence length or repetitions.
- Any distinct supported key family satisfies the initial cardinality bound.
- A free entry that points to a different Mu identity is excluded.
- Duplicate and reordered initial carriers preserve key membership.

Both final probe sources use full explicit proof/universe/deep-term/name printing and one million print steps. Final logs contain no warning, error, `sorryAx`, omission, or truncation marker. Failed source attempts 1–2 and failed kernel attempts 1–2 remain in this directory with their exact sources and logs. The first kernel attempt stopped at an opaque computation in `decide`; the final kernel uses the exact proved name/pair membership laws instead. It still proves canonical ordering and exact source contents.

No old production source, Haskell source, Git state, Audit module, or older evidence was edited. No general recursive completion or host runtime correspondence is claimed here.
