# Actual pruning row filtering and strict row loss

Source: `52ca456d99bcef2dd6015543cce6636e87d4cbd9` on `formalize`.
Control source: `c6b104886e6e222756bdc084979d314dd2b23716`.
Main: `bd5a406a6a3f84b7e3ae0906082783911509df83`.
The full original-input objective remains incomplete. Work continues.

## Six checked laws

| Module and law | Result |
| --- | --- |
| SourcePruningNarrowControl: narrowAt_of_normal | Replay the same value and heap at every native reader fuel when the ordinary input is Normal and this key keeps every root row. |
| SourcePruningNarrowControl: narrowAt_complete_control | Derive an actual completed exposure/construction, Ready lineage, available closed ordinary Normal result, kept complete rows, sufficient-fuel stability and same-key replay. |
| SourcePruningNarrowControl: narrowAt_ordinary_rows | An actual successful filter of an available ordinary root retains only complete input root edges. |
| SourcePruningNarrowControl: prepare_of_normal | Retain the actual Empty rejection or nonempty pure action at the same value and heap, under Normal/kept/encode gates. |
| SourcePruningNarrowLineage: narrowAt_changed_loses_row | Unequal observed encoded handles force proper loss of a complete root edge from an ordinary Normal input. |
| SourcePruningNarrowLineage: narrowAt_constructed_changed_loses_row | Derive current Normal/Available/Ordinary from an actual earlier constructor and Keeps, then prove the same strict loss. |

Normal is the literal equation run(makeNode(nodeEdges value)) heap=(value,heap).
Ready and Available do not replace this premise. Ordinary here permits Empty
or an ordinary node at the root. It does not restrict every descendant to the
finite ordinary domain. Mu children can remain. The actual-success subset and
first strict-loss laws need no separate closedness or recursive NodeDomain.
They retain Ready, Available and their actual success observations.

The completion producer retains its Ready, Available and closed-input gates.
It constructs its finite native reader fuel and actual result internally.
Its result is Normal and all result rows pass the same key. It replays at
every reader fuel from that resulting heap. The original input is stable only
from the constructed sufficient reader fuel onward. This fuel differs from
the enumeration worker's recursive depth.

The strict-loss law consumes both actual encode observations and unequal
handles. It proves result-edge inclusion and one absent complete original
edge. Removing only a duplicate occurrence does not establish this conclusion.
If no original edge were lost, every original edge would be kept. Normal
replay would force the old literal value, contradicting the unequal handles.
The constructor companion uses an earlier literal makeNode equation and its
Keeps lineage. Existing makeNode_normal and normal_grows derive its current
Normal internally. It does not assume an arbitrary stored slot's history.
No numeric bound on a sequence is proved here.

The actual OuterNarrow/NativeView primitive filters complete root rows and
reconstructs their node. It performs no native recursive intersection.
Incoming/dispatch intersection and Prepared selected Mu/Union reconstruction
remain separate operations. They can replace the row source. Their bounds
do not follow from this filter's strict-loss law.

## Required proof repair and Haskell findings

The original uncompiled control draft claimed pure() for every retained
ordinary value. Empty is also ordinary. Its encode is some 0. Actual
Action.prepare selects some reject for Empty before inspecting that encode.
Root corrected the fourth conclusion to the literal Empty/nonempty match.
The Empty branch now returns EnumerationState.reject. The nonempty ordinary
node branch returns pure(). The first three theorem headers and bodies remain
exact. A second probe exposed an unqualified reject as an implicit parameter;
Root qualified EnumerationState.reject. The complete printed contract has no
reject parameter. The final repair replaces the unavailable by_contra tactic
in the strict-loss proof with explicit Classical.byContradiction. Both strict-
loss headers remain exact. Original drafts and complete failed logs remain.

These repairs change Lean proof statements or proof syntax. Actual Empty
rejection is the intended source behavior. No Haskell source changed. No
native command ran. No new Haskell defect, fix or repair candidate is
established. All earlier conditional Haskell findings remain in FINDINGS.

## Strongest whole-worker statement retained

The original-carrier worker laws remain exact. For each supplied finite
recursive depth satisfying their existing validity/resource gates, both actual
workers have a stable outcome, exact computed resources and paths within one
original finite carrier. Complete and smaller-depth path induction are
internal. The carrier is independent of recursive depth. Work bounds,
forecasts and Reserved can depend on depth. Recursive exhaustion remains
permitted. No common successful outcome across depths is established.
The successful recording and completed mixed-native cache laws remain exact.

## Remaining original-capacity gap

Sufficient ORIGINAL recursive depth for the intended finite ordered prefix
remains the largest gap. The proof must cover every earlier alternative and
staged child under the configured order and stops. It must compose actual
filter lineages, count source resets, and control incoming/dispatch
intersections, Prepared reconstruction, slot creation and raw SCS work.
The current result supplies a strict relation for one filter step. It does
not prove the whole worker's finite physical handle carrier or chain bound.
The checked fixed-handle boundary budget and finite path/key shapes remain
useful. Their real canonical/history gates must still reach each actual call.
Duplicate-erased shapes do not bound raw multiplicity or native allocation.

The completed native cache proof still needs whole-caller and EnabledEmpty
transport. Its generic unfinished-prefix extension is frozen but UNCOMPILED
in next-stored-prefix-review/NativeStoredPrefix-v3-UNCOMPILED.lean inside this
evidence. That draft has five laws. Its terminal match yields True for a
Yielded step; a yielded successor needs the extended actual Trace/Inputs.
Root has not run a prefix probe at this checkpoint.

A separate source-only review owns
/tmp/mcfta-native-normal-producer-review-20261030. It checks actual lookup or
successful filtering producers for Normal. It must distinguish coherent
cached depth/free fields from canonical row order and duplicate removal.
Its work is not a checked result of this checkpoint.

Keep the full public-input, output-soundness, ordered-prefix, both-worker,
optimized-interned-core, Prefix/table/count/checkpoint/public-adapter and
Haskell-correspondence objective. Keep constructor/equality, exact node-count
size classes, size order and both rank/unrank inverses. No percentage or
completion date is established.

## Verification and evidence

Default and strict Audit pass: 4,748 jobs and 82,993 dependency checks.
Fifteen serial compiler commands remain: twelve pass and three repaired
candidate probes fail. All 32 input snapshots remain. Both installed sources
match their strict snapshots and have empty strict logs. The final Audit
matches its strict snapshot. Lean4.34.1 uses warningAsError and linter.all.
Every command verifies 4 GiB maximum/high, zero swap and the five-minute cap.
No resource, heartbeat, queue or service setting changed. Default Lake
replays the existing unused-input warning.

Public verification passes 1,201 checks and unchanged 116 definition prints.
The complete old 4,848,753 bytes and intermediate 4,856,085 bytes remain exact
prefixes. Root and independent review read all six contracts and the complete
11,301-byte/151-line new tail. All six new axiom reports use standard axioms.
Full output: 4,860,054 bytes, SHA256
`266872f154e91e3e67c6dc08fe733a61c72685c25d6031affdce74939ecfc622`.
All 547 prior protected and 835 native inputs remain exact. There are now
549 protected inputs and 4,748 Lean files. Two Audit imports precede the
complete old body.

The preparation review retains 65 payloads and 67 regular files. The lineage
review retains 37 payloads and 39 files. The independent public review retains
42 payloads and 44 files. It read all 246 source lines and all 151 public lines.
It acquired zero old whole sources. The upcoming uncompiled prefix review
retains 40 payloads and 42 files. All owner manifests, pins, literal cuts,
source-only incidents, versions, false uncompiled candidates and failed logs
remain. All historical manifest dependencies are copied into this snapshot.

Evidence: /tmp/mcfta-narrowing-control-20261030.
Archive: lean/restart-evidence/20261030-narrowing-control.
Use safe extraction into a fresh destination. Remove restored write bits
before ownership checks. Give metadata verifiers a writable output directory.
All prior root documents remain complete exact suffixes.
Public adapters and Haskell Word64, interner, container, laziness and warm-CAF
correspondence remain open. The backend goal marker still says blocked despite
resumed instructions and verified progress. Work continues. No pause or
completion is claimed.
