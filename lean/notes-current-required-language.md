# Current scan and exact required-path language

Source main `9a2f9bea` is merged at `d8beb7f5`. The equality worker is
unchanged from main `5c53de80`. These proofs extend the open-input domain
in [the completion note](notes-current-required-support.md).

## Exact required-worker language

`SourceCurrentRequiredLanguageEffects` derives semantic readiness,
constructor history, available returned children, and resident returned
rows from the actual `RequireChildren` and `RequireRows` graphs. Each
selected child uses its stored Needed requirement and original list index.

`SourceCurrentRequiredLanguage.node_exact` proves that the returned node
accepts exactly the original terms that match its Needed trie.
`requireAll_done` proves the corresponding independent `ForestRequired`
filter for the literal required worker. Child and row proofs retain the
original guards, symbols, arities, and order. Recursive heads supply their
actual exposed row domain. Strict Needed recursion discharges every child
language obligation.

`requireAll_paths` uses a checked root arity to state complete path
existence. `requireAll_keep` derives that arity from an accepted original
forest and actual path witnesses. The conditional forest filter alone does
not reject a missing root position. `primary_complete` derives finite exact
execution from an actual false primary class trace. Unselected siblings can
remain open. Neither a complete callback nor a later support law is supplied.

## One actual scan-final heap

`SourceCurrentPrimaryReplay` retains the primary endpoint condition and
actual unfolding results. Every completed primary trace has the same-answer
certificate above its returned heap. The target needs retained heap entries.
It needs no new target semantic or cost invariant.

`SourceCurrentClassScanSupport` follows the actual selected, skipped,
continued, and stopped scan branches. Each selected class retains its
original primary occurrence and growth to the actual scan-final heap.
Replay derives all selected primary certificates at that common heap.
Their canonical path union derives the required domain on the original
children. The proof retains the existing four completed memo invariants.
These certificates add no source predicate call or memo operation.

## Terminal tips and stage composition

`SourceCurrentSecondaryEndpointClosed` proves that a false current
empty-path secondary trace implies original endpoint closedness. It
includes the constrained-Mu endpoint. Open ordinary unfolding retains each
external free reference.

`SourceCurrentRequiredTipSupport` retains every maximal local tip, including
an empty suffix. Its empty requirement therefore implies terminal
closedness. Actual ordinary rows and recursive Head results transfer these
certificates to the selected original row children. This stronger domain
implies the earlier completion domain.

`SourceCurrentClassRequired.scan_required_complete` composes a successful
actual scan with finite exact required execution on its original children.
The required worker starts at the literal scan-final heap. The theorem
returns the exact canonical selected path union, constructor histories,
semantic readiness, original and returned value availability, a stable
finite execution, and exact independent filter language. Original accepted
forests with the original class paths are retained. The theorem also derives
the reconstructed forest domain and projection domains for every maximal
required tip. Read [the result-domain proof](notes-current-required-results.md).

## Remaining obligations

The scan memo, cost, and normalized-field invariants end at the scan heap.
This composition does not transfer them through the required worker. It
does not prove the later shared targets, class edits, fallback intersection,
or final reduction result. Original shorter paths that cease to be maximal
need their endpoint facts retained separately. Later class edits need a
preservation proof for the reconstructed domain.

Completed graph receipts do not prove GHC demand, physical containers,
machine bounds, allocation history, or memo publication. General constrained
completion and every broader library obligation remain active.
