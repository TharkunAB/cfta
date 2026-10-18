# Source-row anchors at actual captured native Mu writers

Reviewed and frozen at 2026-10-18 09:38 CEST.

Production: `lean/MicroCFTA/SourceCurrentNativeMuWriterSourceRows.lean`.
SHA-256: `36845b73f5e3bd85e959ef075d81c81032864b59b03c48b9d05cc9560b4b8c3a`.

The four public declarations are `Anchor`, `optional`, `MuRow`, and `returned_mu`.

Anchor retains an original StoredLiteralRowLineage.RowAt occurrence in the specified body. The selected row has the same symbol, full raw guard, and arity. It either equals the original row or has actual ordered stored Calls from that original row's children to the selected row's children under the lexical environment at that occurrence. No desired child equality or output relation is an input.

The generic optional producer consumes an actual maybeMu result, initial SemanticHeap and body availability, final-reader publication History, forward return-to-reader growth, and one direct physical selected row. When the optional pair name is absent, the actual equation gives literal unchanged body and unchanged heap. The selected row is directly an original node-row occurrence. When the pair is present, NativeConstructSourceRows.construct derives the anchor from actual reconstruction and the current raw ordinary call. No publication History before the optional entry is assumed or inferred.

MuRow retains exactly one captured writer. Its existential witnesses include the same before and after checked states, parent and child fuels, two identities, actual entered-domain value, checked parent Trace, exact child request Trace, actual generated bodyValue and availability, literal maybeMu equation, final checked-state update, retained evaluating owner, both captured heap growth links to the reader, and native memo Retained. The receipt also retains the prior OptionalOrigin and the new Anchor for THAT SAME bodyValue. The anchor is not attached to an unrelated writer or separately chosen body.

returned_mu starts with actual NativeEdgeWriterGrowth.History at the reader, reader publication History, the exact returned cell, an actual Mu decision, and a selected physical row. The existing QueryMuRowOrigins.returned_mu producer derives the captured writer and its actual child schedule. PublicationTrace.trace applied to that exact child Trace and the captured Good heap derives SemanticHeap at the optional entry. The theorem composes optional with the growth obtained by the exact final-state equality. It supplies no future invariant, body-origin law, or publication-history transfer backwards.

Trace is the existing CHECKED physical trace. Its contract includes per-step Inputs. This module does not derive that trace from a bare execute equation. The reader History is also an explicit causal-history input. It is not inferred from the presence of a returned cell alone.

The source anchor belongs to the captured writer's generated bodyValue. This is not a claim that it is an original row of either initial query operand. That further operand ancestry remains outside this module. The result does not prove native completion, outer completion, or arbitrary retained-Mu epsilon row congruence. It adds no BinderFree, NoDeep, finite Cap, or generic closed-body restriction. The specialized returned-cell theorem has the same native request domain as the prior Mu writer producer.

Selected receipts:

- `mu-writer-source-direct-1`: exit 0; actual raw strict log has 0 bytes; immutable executed snapshot equals production.
- `mu-writer-source-canonical-1`: exit 0; successful canonical build with 1493 jobs. It replays the unchanged existing unused-variable warning in InternedFreshOrdinaryClosedCompletion. No new source warning occurs.
- `mu-writer-source-public-1`: exit 0; four complete #check @, #print, and #print axioms pairs. All eight required options are explicit. Hardened validation reports no omissions, printer failures, errors, warnings, or sorryAx. Only propext, Classical.choice, and Quot.sound occur.

Each execution uses pinned Lean 4.34.1 and a five-minute heavy-management wrapper. Effective inner memory.max and memory.high are 4294967296, and memory.swap.max is 0. Direct and public runs execute immutable numbered sources with -Dlinter.all=true and the compiled LEAN_PATH.

There are no failed attempts in this component. Counts are four public pairs and zero constructed pairs. Root owns the request-level classification and integration. The manifest uses an explicit source and owned-evidence allowlist. It excludes mutable root working fixtures and shared component files.
