# Independent source-inventory review

Date: 2026-10-17 00:45 CEST. Reviewed frozen source: `SourceRecursiveIntersectionSourceInventory.lean`, SHA256 `d8752c20dbb5ddb5f4571e66419b4e27d95f0ad2ae711aac4fb38795fa6a3338`.

No material defect was found. The module supplies static original-source carrier and key checks. It does not claim complete current `WordRanges` or native completion from those checks alone.

## Actual identity and binding origin

`names:22` is the full initial issued node range. `identity_mem:34` handles ordinary, Mu, and union entries through actual coherent entry issuance. It handles `.reference (.interned name)` through `IntersectionFlatMemoKeyPhysical.reference_bounded:26`. That theorem uses the reference's actual issued reservation. It does not require a complete ordinary node record at that identity. Empty and unsupported reference tags cannot satisfy the supplied source-identity equation.

`binding_mem:66` obtains the exact Mu entry and its availability from `Environment.bindings_available`. This covers both actual left and right Mu bindings, including duplicate names. `bound_names:76` transfers the complete actual binding list to the initial range. Neither theorem assumes that arbitrary source names are populated binders.

`pairs:26` uses the literal `Control.pair left right = (min left right, max left right)`, not an unsorted physical pair. `operand_pair_mem:57` derives both original identities from the same initial source heap. `extend_mem:84` then applies the actual canonical Typed domain-extension closure. It supplies no output-node carrier or future-key list.

## Exact allocated domain readback

`entered_mem:118` examines the literal `Environment.enter` result. It derives that result's full `.key` equality from `IntersectionEmptyDomain.make_correct`, under actual cache validity. It rewrites by that exact equality before applying extension membership. Thus it does not transfer a law to a different allocated domain or assume the requested result key.

The independent `actual_enter_body` kernel composes this endpoint with actual allocated key readback and `NodeScope.mu`. It obtains original source body scope, canonical Typed domain membership, and the current child request's static-source KeySafe check. The key check retains an explicit bound on the actual returned domain identity. The kernel does not derive that numeric bound from key membership alone.

## Cardinality and machine layout

`pairs_length:101` gives `N*N` list entries. Sorted pairs occur twice when their operands differ; the proof keeps those duplicates as a conservative bound. `domains_length:112` is exactly `2^(N+N*N)` by the proved DomainInventory list length. It is not a claim that all entries are different or reached.

`node_key_safe:133` uses only the initial source node supply and the original operand availability in `NodeScope`. It preserves the strict `source.nodes.next < 2^bits` margin. This is sufficient for the interned-reference sentinel condition `identity+1 < 2^bits`; weakening it to a non-strict supply bound would lose that case. It also requires the actual domain identity below `2^(bits+1)`. Memo-key absence remains a bypass: the theorem requires the literal present-key equation.

`edge_key_safe:150` obtains both actual raw edge identities from coherent initial residency and the initial edge supply. It preserves the non-strict `source.edges.next ≤ 2^(bits+2)` bound and the strict shifted-domain bound. Neither word theorem requires final constructor supplies or an output heap bound. Those output identities are not original operands of this one query.

The all-issued carrier is mathematically useful but very coarse. It includes unrelated earlier allocations and non-binder node identities. At `N=8`, its candidate inventory has `2^72` entries, already greater than the signed 64-bit domain-key range `2^63`. The imported `coarse_eight_inventory` kernel proves that arithmetic without enumerating the inventory. This is a limitation of a sufficient reservation theorem, not evidence of that many actual allocations or a Haskell defect. A practical bound should use a smaller reachable original carrier or a sharper canonical-domain analysis.

## Remaining boundary

The module does not connect every actual current finite prefix to these static scopes and domain memberships. It does not yet transport actual domain-cache allocation history through all current native instructions or derive a shifted identity bound at every reached demand. Root's separate DomainTrace work must establish those facts without a completed trace premise. This review does not certify that unfinished module.

The fixed carrier belongs to one native query over a fixed original source. The full outer reducer can use later constructor outputs as inputs to subsequent queries. No global fixed outer key carrier or general constrained recursive convergence result follows here. Host forcing, native containers, and Haskell runtime scheduling remain separate correspondence obligations.

## Validation

Canonical `source-allocation-build.log` completed 475 jobs, including this module as target 475. This owner ran no Lake build. Imported pinned Lean 4.34.1 checks passed on the first attempt: all 15 public axiom/full-signature pairs and three integration pairs (`actual_enter_body`, `actual_reference_name`, and `coarse_eight_inventory`). Both logs are terminal exit 0 with all linters and full explicit proof/universe/deep-term/name printing. They contain no warning, error, `sorryAx`, omission, or truncation marker. No production, older evidence, Git, or Haskell file was changed.
