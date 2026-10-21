# Source-only positional support plan

Written 2026-10-21 02:18 CEST. Every proposed producer below is unproved.
The checked counterexample is reported separately in positive-native-review.md.

## Exact observation

`SourceCurrentRequiredPositivePosition.PositiveAt` lines 25–40 uses natural
child indices. Its selected canonical row index is receipt data, not a path
component. Union alternatives preserve the path. Mu values and references have
no constructors. `not_plain` lines 42–58 excludes all such positions in an
`Annotated Plain` value. The actual Required theorem, lines 87–95, already
preserves the same path under its explicit `ExposureSafe` premise.

## Merge: the narrow next implementation

Proposed law, not proved in this package:

```
Support input output := ∀ p, PositiveAt output p → PositiveAt input p
SupportStored memo := ∀ key entry, memo key = some entry →
  Support entry.original entry.result
```

Use the actual `MemoMergeGraph.Call clear top input before memo output after
saved`, initial `SemanticReady`, `CostHeap`, `Available before input`, physical
`MemoMergeEffects.Stored`, `SupportStored memo`, and `plain top = true`.
The intended conclusion retains the actual `Effect`, physical stored table,
`SupportStored saved`, exact captured-original equality on hits, and
`Support input output`. The cold corollary starts with the empty Merge table.
A finite Plain cap is not needed for this Merge-only statement.

The proof should use `ConstrainedCapMemoMerge.run/call` (lines 93–181) as its
actual mutual Run/Call template. `hit_certificate` and `winner_certificate`
(lines 50–82) show the required complete-original alignment and first-winner
handling. Replace the cap certificate with the positional law; do not infer the
law from physical Stored or merely attach it to a historical outer writer.

Actual code branches in `MemoMergeGraph` lines 51–89 explain why this statement
is plausible. Small rows retain their original guard and ordered child calls.
Large rows introduce a plain Top guard and process the same numbered columns.
`SourceMergedSelectionLanguage.select_exact` supplies literal retained inputs.
`makeUnion` and `ordinaryUnion` require backward positional lemmas through their
actual row normalization. Mu values are not unfolded by Merge; a recursive
boundary keeps the actual union operands. The existing cap proof's unordered
`columns_member` fact is insufficient: the new proof must retain the column
number and derive a source row child lookup at that same number.

The already checked physical-cache countermodel in
`SourceCurrentPhysicalMergeSupportBoundary.empty_hit` explains why `SupportStored` is a
real semantic obligation. That countermodel is not an empty-table reachable
execution. A useful new Merge producer must derive the law on actual finishes
and propagate it from empty tables through later actual prefixes.

## Native: precise sufficient-law target and present gap

Proposed conditional node law, not proved here:

```
∀ depth, Bindings Plain source request.domain.key →
  Cap Plain depth request.left → Cap Plain depth request.right →
  ∀ p, PositiveAt result p →
    PositiveAt request.left p ∨ PositiveAt request.right p
```

A companion actual edge law must retain the full output guard disjunction and
the exact child index. It must cover a positive descendant even when its
parent row is plain. `NativeNodeRowLineage.ordinary` has the required actual
paired child calls without a positive-parent premise. `NativePositiveRowOrigins`
only adds a positive-root-side conclusion; its `positive_child` endpoint alone
cannot cover a plain parent with a positive descendant.

`Cap Plain depth` rules out the checked nonplain Mu example: a capped Mu must
be hereditary Plain (`ConstrainedCapNativeScope.mu_annotated`, lines 19–24).
The same module's `body_cap`, lines 73–79, derives the bound for actual Mu body
exposure. Positive positions in a body of such a Mu are impossible. A non-Mu
operand retains its own literal body, so this branch can preserve the position.

Plain bindings are separate from operand caps. Literal references have Cap zero
regardless of their resolved payload. `compileReference` (Compile lines 36–45)
reads the complete bound Mu. Existing `HereditaryNativeScope.Bindings`, or the
stronger `OriginalBindings`, ensures those bound Mu values are Plain.
`ConstrainedCapNativeScope.enter/read` (lines 38–71) preserves this invariant
through actual domain extension and later immutable source reads. Empty-domain
closed requests discharge the initial binding obligation; they do not remove
the obligation inside the proof.

Initial physical `Good`, actual admitted Trace, exact source availability and
semantic contexts remain required for an executable theorem. Guard conjunction
also needs actual ready cached fields: `UnconstrainedGuardClosure.conjoin_plain`
(lines 94–108) has explicit ActiveOption premises. `Good.fields` derives them,
as in `NativePositiveRowOrigins.positive_side`. Physical cache validity must
align a warm cell's complete captured request with the queried request.

A returned native cache needs this new conditional positional law in addition
to the existing cap/occurrence/scope laws. `ConstrainedCapCheckedJointCache`
(lines 23–28, 75–91, 135–184) gives the exact returned-cell storage, empty-table,
finish, and warm-read templates. `CheckedJointTrace.completed` gives the actual
strong-fuel induction. These are producer templates, not the desired theorem.

There is one additional constructor gap. A used optional construction may read
an older full Mu and smart-clean it to its stored body. Existing
`ConstrainedCapGuardHeap.Correct` retains only equality of scalar guard-depth
profiles. `GuardReadback.hit_cap` (lines 93–104) proves a scalar bound, not
position equality. Equal maximal depth does not distinguish positive siblings
at indices zero and one. Existing occurrence and scope laws do not repair this.

A full native positional proof must derive a body/probe positional invariant
from actual source callbacks or publication history, or prove the equivalent
warm optional-constructor support law from those causal receipts. It must not
assume a desired winning body or infer that law from Grows. No counterexample
to the complete existing heap invariants is claimed here; this is a precise
missing proof obligation. `NativeMuPublicationCallbacks.raw_callbacks` and
`StoredMuRetainedAlignment.RowCall` retain actual shared source syntax, full
fields and ordered children that can support such an induction.

For cap zero, the current returned cap law already gives `Annotated Plain`
output, so `PositiveAt` is impossible. The nontrivial positive-depth theorem
needs the positional constructor and returned-cache laws above. The finite-cap
premise is also not yet derived for every outer active owner. This package does
not close selected-copy support, owner renewal, or outer termination.

## Recommended next step

Implement actual Merge positional support first. It avoids Mu exposure and the
warm optional-constructor gap. For native support, isolate the actual warm
smart-cleanup positional lemma before copying the full checked trace induction.
Keep its initial publication/callback provenance explicit and derive it from
actual empty-table/source prefixes. Do not substitute a scalar signature law.
