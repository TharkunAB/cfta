# Native callback histories and row readback

Proof checkpoint: `b9434f53`. Source main: `c0cc8a05`. Local merge: `896b0a1c`.
The preceding normalized source comparison remains unchanged.

## Established results

`SourceCurrentNativeMuHistory` transports the literal native callback,
constructor, and optional-binder executions to their causal publication
histories. It covers both successful and pending outcomes. The callback
requires availability of its supplied marker. The constructor supplies
its own probes and reservations.

`SourceCurrentNativePublicationTrace` proves that admitted ordinary Work
jobs introduce no completed Mu. Each checked native step preserves its
semantic heap and constructs a publication history to its actual stopping
heap. This includes failed and blocked outcomes. Trace induction uses each
physical instruction's actual heap inputs. Bounded execution retains its
explicit InputsThrough premise. Source-started traces derive the initial
semantic heap and publication history internally. Warm traces extend their
earlier history. The reached unused-Mu law follows from that history.
These results preserve the existing native tables and protected frames.
They do not construct general query completion.

`SourceCurrentNativeCallbackRowOrigins` proves exact Origin equivalence
through actual root filtering and bare-self erasure. The filter uses the
actual normal heap and available input. It needs no Closed, Cap, noDeep,
or global union-normality premise. Complete physical rows retain their
guards and ordered children. The view is an arbitrary fixed heap.

`SourceCurrentNativeConstructReadback.Readback` retains the actual native
Depth callback, ordinary callback, request, raw ordinary substitution,
filter pair, raw normalization and availability, selected complete Mu
payload, and causal final history. The payload's probes equal this call's
complete current probes. Its stored body can come from an earlier writer.
If usesLocal is false, the return equals eraseSelf applied to the current
ordinary callback. For every fixed view, its Origin rows are exactly those
of the current raw ordinary substitution.

`construct` derives that receipt from an actual successful native construct
and its initial SemanticHeap, Available body, and causal History.
`optional_complete` derives the successful return from initial Ready,
Available body, and causal History. It retains readiness, availability,
and history. It splits the exact absent-pair identity case from the used
construction case. It assumes neither a future completion nor a desired
stored comparison law. Bodies can contain nested Mu.

## Remaining boundary

The current raw ordinary substitution is not the original native body.
For a body row with child `reference old`, substitution changes that child
to `reference ordinary`. The complete physical edge changes. Its source
guard, symbol, and arity can remain equal. The next producer must retain
an occurrence relation with those exact fields and ordered child
substitution origins. Use the existing Required guard-origin field
relation where it applies. A Cap or GuardHeap bound does not supply this
occurrence relation.

The producer must follow actual stored execute and rebind through closed
leaf shortcuts, ordinary and union normalization, nested smart Mu, and
keep-first winners. The unused case now has exact current callback row
readback. A retained recursive binder still needs its actual writer and
unfolding relation. Do not replace either case with an assumed returned
row law. Compose this relation with the existing native row histories and
protected edge writers on the same actual trace.

General recursive outer-node progress, nonempty live walks, complete mutual
outer execution, and repeated-pass convergence remain open. The full
frontend, concrete runtime, and public Haskell pipeline adapters remain
open. The complete library target is unchanged; see notes-proof-status-20261017.md.

## Validation and Haskell handoff

The full pinned Audit passes 3084 jobs and 67897 dependency checks. Actual
limits are 4 GiB MemoryMax, 4 GiB MemoryHigh, zero swap, and 383 MiB peak.
All four final strict source checks are empty. Canonical builds pass.
Public probes inspect complete signatures, proof terms, and kernel axioms.
Constructed checks include a used pair with nested Mu, unused binding with
a live ordinary row, and exact warm replay. Read the evidence README and
checkpoint-validation.json for all final groups and counts.

Evidence: `restart-evidence/20261017-native-callback-history/`.
All older proofs and artifacts retain their bytes. No Haskell behavior
patch or new production defect is added. The field-pool repair b9219b9e
remains merged and validated. Root FINDINGS.md records that repair and
all earlier repair handoffs. The unchanged Haskell source reuses its strict
Nix all-component build, 798 examples plus golden, Fourmolu, and Cabal-gild.
