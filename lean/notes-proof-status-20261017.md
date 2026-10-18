# Proof status at 2026-10-18

Checked at proof checkpoint `e66b49b7`. Source main is `c0cc8a05`,
merged into `formalize` at `896b0a1c`. This note reports the current theorem
boundaries. It adds no theorem and no Haskell behavior change.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. The target is
a family of theorems, with this schematic form for each operation P:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

The support predicate must describe initial inputs and resource limits.
It must not assume successful completion. The specification must include
the documented errors and validation order where the API returns errors.
There is no completed single whole-library theorem. The largest mathematical
gap is general recursive outer progress and repeated-pass convergence.
Concrete public Haskell correspondence is a separate remaining obligation.
Excluding active memo-key collisions is one part of progress. A complete
termination proof must also bound fresh recursive requests or give a
well-founded measure. Parent reduction can construct new values.

Actual successful lower, Parent and outer workers now retain the causal
Mu body/probe guard heap for any predicate. Actual unfinished prefixes and
node-busy dispatches retain it from initial physical facts. This is separate
from an annotation law over every raw edge. Positional ordinary Required and
Edit survivors retain the exact unselected child and an indexed full source
row. The earlier Edit law needs explicit semantic reads. A separate note
corrects the older mixed-heap interpretation. These supporting results do not
produce general recursive completion or enlarge the complete outer domain.
Read [the earlier checkpoint](notes-current-outer-guard-transport.md).

Actual Required preparation and the subsequent class right fold now
compose same-index full-row origins and exact unselected children from
initial physical facts. The ordinary Edit origin no longer requires
supplied semantic row reads. Accepted recursive Head yields empty-own rows.
Actual false primary selection supplies the selected original Root premise;
public smart Mu does not supply it for arbitrary values. The tracked Root
condition then survives the literal class fold. Compiler footprints and
successful worker equations remain explicit. These are immediate input
origins. Proper initial-source descent, all-owner separation and fresh-call
bounds remain open. Read
[the earlier checkpoint](notes-current-actual-positional-lineage.md).

Actual full local row origins now follow the initial raw guard, its field
lookup and precheck, literal Scan, Required preparation and class passes.
Actual selection supplies Root. Source paths supply compiled absence.
Untouched constrained recursive values need no Root assumption. A positive
retained continuation has smaller structural mass than its explicit immediate
source node. That node can be reconstructed. General initial-source descent
and a global recursive rank remain open. The successful worker equations
and initial raw footprint stay explicit. Read
[the earlier checkpoint](notes-current-selected-local-lineage.md).

Actual Parent construction now retains the local indexed row relation or
returns the Empty sentinel. A fixed positive continuation chain is
well-founded even when intermediate containing nodes are reconstructed.
Its next anchor must be the exact retained child. The full outer worker
still needs a producer for those exact consecutive steps and footprints.
A source-built closed example proves that guard footprints are not
hereditary over nested rows. No general recursive domain is enlarged.
Read [the earlier checkpoint](notes-current-parent-native-lineage.md).

Actual cold and warm outer edge calls now retain indexed Parent origins
for their exact captured request. Empty initial tables, completed node calls
and unfinished prefixes produce that memo invariant. Literal walks identify
the exact dispatched value, inherited descent, earlier siblings and suffix.
A positive row of that input supplies a strict source-anchor continuation
step under the original raw footprint. A general consecutive execution
producer and global progress remain open. The checked raw conjunction
counterexample has a rejected first input. No accepted-input closure claim
or Haskell defect follows. Read
[the earlier checkpoint](notes-current-outer-positional-dispatch.md).

Actual coherent active classes now derive every present slot's exact
input and prefix/call/suffix schedule. Whole-slot callbacks retain complete
original paths. Literal leaves derive their target force, native request,
full intermediate state and raw steps without a future semantic read law.
Initial physical facts derive midpoint and final validity and residency.
Semantic traces and historical writer origins remain open at this boundary.
An accepted source-built operation also refutes ordinary height and positive
count measures that treat unions as opaque. General recursive completion
and the complete ordinary outer domain are unchanged. Read
[the earlier checkpoint](notes-current-selected-edit-events.md).

Actual selected edits now recover the literal earlier target writers of
warm class slots. Their target-table histories fix the class, captured
forest, target path and complete worker states. They assert no physical
or semantic transport to those historical entries. Initial exact native
key validity, closed resident operands and numeric headroom now produce
checked traces from raw execution. An initial causal native history then
produces the exact returned node cell and earlier complete request writer.
Historical semantic target receipts and the stronger initial key invariant
still need transport through the full class schedule. General recursive
completion and the complete ordinary outer domain are unchanged. Read
[the earlier checkpoint](notes-current-selected-read-producers.md).

Initial numeric completion now produces target/class/fold semantic Reads
at literal successful worker endpoints. Complete value, Checked and Merge
uniqueness aligns all states without a forecast lower-bound premise on the
observed fuels. Historical semantic SlotReceipt and actual class-selected
reads/histories then follow from initial supported contexts. Selected path
closure permits open untouched roots; no finite input Cap is added. Frame,
semantic caches, valid globals and numeric reservations remain explicit.
The next general bridge is that context at the actual outer class entry.
General recursive completion and the complete ordinary outer domain are
unchanged. Read [the earlier checkpoint](notes-current-actual-semantic-reads.md).

Initial numeric Parent support now derives semantic receipts at literal
successful Parent and outer edge-body returns. All four Parent components
align. An actual outer edge success also derives its complete receipt,
Frame/Fits and Post without a notBusy or fuel lower-bound premise. The
existing Parent producer derives its internal class contexts and domains.
This supplies the endpoint for an actual rows_edge summary from supported
initial entry facts. General rows_tail/walk_tail semantic transport and
initial recursive resource schedules remain open. Mu cleanup is already
unchanged. No finite ordinary domain or finite Cap is added. General
recursive completion and the strongest complete outer domain are unchanged.
Read [the earlier checkpoint](notes-current-parent-semantic-reads.md).

The finite physical guard alphabet now derives initial flat raw bounds and
actual precheck class/path/step bounds. Initial native queries construct
their own receipts and returned guard bounds. Exact finite own-record and
ambient-word reservations retain index-sensitive compiler syntax and derive
the actual Parent reservation from current initial Context/Fits. No inherited
size, hereditary domain, finite Cap or future-entry capacity callback is
added. Single-Parent initial scheduling is checked. The general fixed-fuel
outer resource/guard composition and semantic rows_tail/walk_tail summaries
remain open. General recursive completion and the strongest complete outer
domain are unchanged. Read
[the earlier checkpoint](notes-current-native-guard-envelopes.md).

Initial exact finite cases now bound the complete Parent output profile
and all nine lower fuels. One joined Room test derives UniformReserved;
a computed mathematical width supplies that test. This asserts no host64
capacity. Actual Target completion constructs a finite returned guard
carrier. A separate literal outer replay bounds entered Parent calls from
supplied outer fuel on every outcome. Other outer allocations remain outside
that count. Full Parent carrier, outer resource scheduling and semantic
rows_tail/walk_tail composition remain open. General recursive completion
and the strongest complete outer domain are unchanged. Read
[the earlier checkpoint](notes-current-parent-uniform-envelope.md).

Finite raw guard carriers now accompany actual complete node edits and
class folds and passes, including supported recursive Head exposure.
Preparation returns its own carrier. FullClasses, Local and Parent still
need their carrier composition. Non-Parent constructor bounds now retain
the same carrier and physical profile at each local entry. Their whole
outer schedule and equality-cache bounds remain open. General recursive
completion and the strongest complete outer domain are unchanged. Read
[the earlier checkpoint](notes-current-parent-guard-composition.md).

Finite raw guard carriers now compose through complete Classes, Local and
Parent. Exact initial own-record and count cases determine a common Parent
carrier at the same full receipt, output profile and nine-fuel replay.
No future entry or guard-range callback is supplied. The remaining outer
bridge must derive semantic Context, Frame, scheduled Fits and carriers
through rows_tail and walk_tail. Equality-operation resources need a
separate account from the physical Profile. General recursive completion
and the strongest complete outer domain are unchanged. Read
[the earlier checkpoint](notes-current-parent-full-guard-carrier.md).

The complete mutual outer traversal now derives semantic Reads, Post,
Frame, scheduled physical Fits and a finite raw guard carrier at every
supported successful return. One initial final-profile Room condition
covers reached Parent reservations. Each row and child suffix receives
the actual returned context. No future-result or reached-check oracle is
supplied. Initial semantic and physical facts and literal bounded success
remain explicit. General recursive completion stays open. Read
[the earlier checkpoint](notes-current-outer-initial-schedule.md).

Literal unfinished outer phase prefixes now derive semantic Post, current
Context, Frame, scheduled physical bounds, guard carriers and ready inputs
from their initial facts. Exact seed traces bound the remaining lower-fuel
ceiling without forecast monotonicity. Actual node-busy failures construct
their own dispatch prefix and derive those same facts at the fault caller.
This identifies the complete colliding request. It does not exclude the
collision or cover arbitrary interior lower-worker fault states. The whole
call need not succeed. General recursive completion remains open. Read
[the current checkpoint](notes-current-outer-prefix-schedule.md).

Initial scheduled capacity and nine lower-fuel bounds now exclude every
Parent fault from all six outer phases. A literal failure constructs its
own reached row entry. Initial prefix semantics and its exact seed derive
the current Parent reservation and fuel bounds. Completion uses the actual
captured edge owner. No successful enclosing call is assumed. Outer memo
faults, outer exhaustion and general completion remain open. Read
[the current checkpoint](notes-current-outer-parent-failure.md).

An initially idle edge table now remains idle at every literal reached
outer phase entry. Initial prefix semantics supply current valid links at
the exact row that emits an edge memo fault. Valid links exclude absence;
idle excludes busy. All edge memo diagnostics are therefore excluded from
the stated initial semantic and scheduled resource facts. No lower-fuel
ceiling or successful enclosing call is needed. A terminal Parent fault
can still retain an evaluating edge owner. General node-owner exclusion
and fresh-call bounds remain open. Read
[the current checkpoint](notes-current-outer-edge-idle.md).

Closed native query rows now have an explicit terminal classification.
Actual swap/reset forwarding preserves both operand closures and excludes
bare-reference terminal branches. Union rows have an actual selected
ordered member call with the same full row. Mu branches have their actual
entered body trace and literal binder schedule. This last result does not
establish row occurrence in an original source body. General used-writer
alignment and source-anchor composition remain open. Read
[the current checkpoint](notes-current-native-terminal-origins.md).

## Strongest current claim in plain technical English

For a validated finite graph, the checked exact-size model lists exactly
the distinct accepted terms of each requested node-count size. It counts
those terms correctly. Rank and unrank follow the specified order and are
inverses. Cyclic graphs are included. Correct finite yes/no guard replies
give these successful query results. Finite replies that include unknown
can instead stop with an error. The declared ordering laws remain explicit.
`SourceSizedFiniteKeysPublic.decided_complete_exact` states finite execution
and exact query laws on successful output under these solver contracts.

The checked recursive native intersection has exact intersection semantics
for closed resident Original operands. Initial resource bounds construct
supported physical executions. The complete finite ordinary constrained
outer pass preserves the full guarded language. That outer-pass domain
excludes Mu, references, and explicit unions in every descendant.

For the general supported recursive outer traversal, successful runs now
derive language preservation from initial semantic and physical facts.
An internal result accepts no new terms and preserves membership for
terms that satisfy its inherited constraints. With empty inherited
constraints, the returned and input languages are exactly equal. The
proof also derives the semantic state invariant and scheduled physical
allocation bounds at that same return. It does not assume a future callee
result or semantic trace. It still assumes that this bounded run succeeds.

Every literal unfinished outer phase prefix also retains the required
semantic state and the initial scheduled allocation bounds. Its exact
phase history bounds the remaining lower-worker fuel ceiling. A reported
node-busy fault derives its own such prefix and complete colliding request.
These facts do not require success of the enclosing call.

With enough initial scheduled capacity and lower fuel, no outer phase can
report a Parent fault. This excludes errors in the lower reduction and
constructor as well as lower fuel exhaustion. It does not exclude outer
memo collisions, outer exhaustion, domain errors or binder outcomes.

For an initially idle edge table, initial semantic facts and scheduled
capacity also exclude every edge memo diagnostic, at any lower fuels.
Reached outer phase entries retain edge idle. A terminal lower failure
can retain an active edge owner. Node memo collisions remain open.

These are separate checked results for the implementation model. They do
not establish that every valid public Haskell call terminates and satisfies
its contract. General outer progress, repeated-pass convergence, retained-Mu
callback alignment, and the remaining concrete adapters are still open.

The latest supporting results construct both raw source calls and both
stored reconstructions from initial Ready inputs. They cover every
BinderFree source: Empty, indexed variables, nodes, and unions. Captured
values can contain arbitrary recursive Mu records. One theorem uses paired
lexical inputs. Another requires replacement agreement only on live source
support. Dead rows need no agreement for their unused children. Results
agree on physical Empty and observations at every finite depth and fixed
view. Full guards and ordered child relations remain explicit.

Every actual binder publication with a static BinderFree body now supplies
both filtered body and ordinary-probe reconstructions. Union roots are
included. Exact literal root parts pass through reconstruction. Actual
repaired callbacks derive the same bare-self case. An actual outer node-busy
failure also constructs its own exact dispatch prefix and the enclosing
activation of every active node owner. No caller supplies completed-call
graphs or the desired prefix. The busy request has its owner's physical key.
This identifies the possible collision; it does not exclude it.

A selected own equality class with distinct paths below one child index
derives a nonempty actual child payload. That child key differs from every
initially Ready Top owner key. A crossing-class example loses its immediate
constraints at both children, so this local case is not general progress.
Actual source construction now recovers the first writer of each selected
Mu record. It produces that writer's callback histories, physical growth,
and issued-reference transport into the reader. Later warm requests retain
the same selected record. A BinderFree condition on that recovered writer
constructs both filtered reconstructions. Other source publications and
captured values can contain binders. Writer metadata alone does not assert
installed membership; the public producers retain that evidence separately.

Literal lower and outer workers now derive operation growth on every
outcome. Actual busy-failure ancestry includes growth from each activation
into the busy reader. Initial Ready values, exact field loads, and structural
constraint-cache validity reach that reader. Full operation-memo validity is
not inferred from growth. Actual native row writers also derive coverage of
both raw stored class fields through the full joined guard. A retained
same-index split then separates its computed child obligation from Top keys.

These results do not extend the completed outer-pass domain. General key
exclusion, fresh recursive-call bounds, nested writer bodies, full smart
cleanup composition, and complete Haskell correspondence remain open. Read
[the current growth and lineage results](notes-current-active-growth-lineage.md).

Actual completed native node and edge requests now derive full operation-memo
validity, allocated fields and result residency from initial physical facts.
They do not require future reached checks or word ranges. Their native memo
invariant is physical; semantic key correspondence remains separate. Indexed
descent after that actual return constructs new payload Ready. Completed lower
and Parent workers now derive physical invariants from initial inputs.
Actual successful outer calls and unfinished execution prefixes now derive
full physical invariants and input readiness from their entry facts.

A separate nested-source branch now constructs full smart binder execution
when the own lexical argument is absent from static live support. Arbitrary
nested bodies and recursive captures are included under that condition. Actual
publication callbacks are literally equal and construct the same stored
reconstruction schedules. The general branch that uses its own argument stays
open. Positive guard syntax also supplies raw-class coverage through each
actual staged normalization and local separation from Top owner keys. Actual
checked query traces derive terminal forwarding and ordinary joined-row origins.
Those traces include per-step Inputs checks. Initial closed inputs now construct
actual recursive Head exposure with stored-body descriptors. General Mu and
union chains now derive chronological terminal ordinary rows. Actual indexed
edits and class right folds derive individual full-row survival chains with
ordered child reads and exact initial/final memo bundles. Mu-body and native
compileMu lineage do not yet reduce every selected row to original operands.
These results do not enlarge the complete outer-pass domain.

Completed native/lower/Parent workers now produce full operation validity,
heap readiness, allocated fields, probe and cost heaps, growth and available
results from initial facts. Literal successful worker equations remain inputs.
Actual unfinished outer prefixes now derive full physical invariants from
entry facts. The result does not produce completion, numeric headroom,
semantic native key correspondence or global memo language laws.

A separate RootMatch relation preserves immediate atoms and complete ordinary
rows through actual union construction and self filtering. It permits union
permutation and duplicate removal. References use an explicit lexical relation.
Mu atoms and ordered row children use an explicit value relation. The result
does not derive those relations for arbitrary retained source writers. General
used-local source induction remains open. An unrestricted capture-alias example
refutes a stronger structural relation, not actual fresh publication.
Read [the current exact boundaries](notes-current-parent-invariants-head-origins.md).

The current recursive execution proofs derive physical probe preservation
from initial weak native Good and stored filtered probes. They compose through
completed lower and Parent calls and actual outer execution prefixes. An
actual busy failure gives exact full request equality with its active owner,
plus readiness and activation growth for every active owner. Collision
exclusion and a finite bound on fresh calls remain open.

Resident Mu nodeBody reconstruction now constructs exact smart cleanup and
retains the complete caller at every bound, including zero. This uses actual
cached probes. It does not prove general source body/probe congruence. Literal
node bodies now construct original Head row indices and full warm child calls
at the final reader. Actual used publication inputs derive alias and filtered
free-name transport. Full used-binder output RootMatch remains open. Read
[the current exact boundaries](notes-current-outer-prefix-invariants.md).

Actual completed class execution now derives individual full-row chains
through each compiled edit and the literal right fold. Each ordinary rebuild
retains its full RowsReads, explicit initial and final memos, source index,
ordered child calls, and exact constructor result. General recursive Head
exposure derives chronological terminal ordinary rows through Mu and union
roots. These are not general original-operand lineage or completion results.

For a nonempty inherited active owner, an equal nested full request requires
an actual intervening own-field height gain. The source accessor contains
nonempty effective equality classes. A checked local example increases height
and then returns the same inherited identity at a proper child node. Thus
inherited descent alone does not supply a global termination measure.

Arbitrary nested used-source builds now derive bare-reference and Empty-tag
correspondence under their lexical relations. A strict body induction
hypothesis constructs both actual filtered callbacks and their RootMatch.
This proves an induction step. It does not close the general induction or
identify every earlier retained writer body. Read
[the current exact boundaries](notes-current-class-row-chain.md).

Actual cold and warm outer edge calls now retain the captured request's
complete symbol and guard, with Top as the only rejection alternative.
The field law persists through all completed outer workers and actual
unfinished prefixes. Initially empty tables derive it from physical facts.
The actual nonempty-owner busy classification now recovers the earlier
row and completed edge call for its gain event. This is an immediate reached
row. Proper initial-source descent remains unproved.

Actual combination and inherited-prefix producers now derive finite path
domains and height bounds from initial operands. Saturation can increase
height beyond both operand heights: a checked actual example has fixed
input heights 2 and 1 and output height 3. The computed bound applies to
one call. It does not control an unbounded sequence of fresh row additions.

Closed Mu Head exposure through a union body now derives earlier source-row
indices and ordered child calls for literal node alternatives. Arbitrary
other member shapes retain their actual indexed origins. General body-root
Mu fusion and earlier selected-writer alignment remain open. The used-source
review also requires a recursive value lift that permits unordered root
alternatives and retains ordered children, lexical Mu bodies, and exact
closed captures. A source-size induction alone cannot cover an older writer.
Read [the current exact boundaries](notes-current-parent-row-trace.md).

Actual successful native node and edge calls now preserve causal Mu
guard profiles from initial physical Good and ready operands. They do not
need a supplied checked Trace or future result law. Successful return is
still a premise. A separate actual-prefix theorem retains a fixed finite
alphabet of original derived edge constraints without an instruction-count
ceiling. That theorem retains its checked Trace and initial code checks.
These are distinct invariants. Neither bounds inherited payload growth,
fresh recursive calls or source-row movement. The complete outer-pass
domain and strongest complete claim are unchanged. Read
[the current boundaries](notes-current-global-guard-progress.md).

## Observable contracts

The main observable contracts are:

- Exact listing returns all distinct accepted terms at a node-count size.
  It returns no duplicates. Counting gives the cardinality of that class.
- Rank and unrank follow the specified order and satisfy both inverse laws.
- Each transformation has its own language relation. Exact transformations
  preserve language. Over-approximations prove inclusion. Representative
  selection has a separate restriction contract.
- Generation covers the specified members. Sampling has the specified
  weights and probabilities. Members, accepting runs, and distinct accepted
  terms require separate statements.
- Current Haskell execution agrees with the specified algorithm and errors.
  This includes memo effects, machine bounds, and representation limits.

Exact queries use the explicit graph, including cyclic graphs. The optimized
interned core remains the construction and transformation path. Read
[ADR 0004](../docs/adr/0004-explicit-graph-boundary.md).

## Established results and their limits

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact accepted size classes, finite class evaluation, counts, size-major enumeration, retained row order, and both distinct-term rank/unrank inverses. The finite carrier comes from validated raw graph keys. | Concrete host and solver adapters and complete public pipeline composition. See [Sized contracts](notes-sized-finite-keys.md). |
| Interned construction | Repaired closed syntax has a finite constructor execution. Syntax includes binders and unions. Actual construction and field histories derive physical and semantic entry facts. | Concrete lazy Haskell publication, interning, and runtime correspondence. The word Ordinary in older module names does not by itself exclude binders. |
| Normalized source callbacks | Actual source publication histories derive the unused stored-Mu body-to-ordinary law, including earlier warm winners. Nested raw source calls have equal ordered stripped alternatives under the stated finite coverage, freshness, noDeep, and actual cache-history premises. Actual native steps and traces now produce the causal publication history. Unused native returns preserve the current raw ordinary callback rows. | Recursive row occurrence transport through retained Mu and concrete runtime correspondence. The common heap of closed_compared comes from actual closed source construction. This is not raw record equality or general termination. |
| Stored substitution | Recursive node-row matching constructs both plans with one exact Value. Initial Ready and available data construct both union-normalization/substitution orders with physical empty agreement, equal observations at every depth and fixed view, and exact literal root parts. Actual self filtering preserves those parts from the derived final heap. Initial Ready data now constructs filtered reconstruction and the retained-member schedule with exact literal parts, including the bare-self exception. Actual parent construction preserves this relation, including row survival, full guards, and ordered children. Source-indexed ordinary-node Mu publication callbacks now retain both exact schedules, common-reader growth, and equal ordered child Empty and row-drop tests. Closed and open roots and nested Mu values remain included. | Derive the literal relation for the actual retained-Mu body and ordinary-probe writers, then compose smart cleanup and warm winners. General root self-filter congruence is proved for normal available roots with the same literal atoms and exact rows. See [literal provenance](notes-current-literal-union-provenance.md). |
| Recursive native intersection | Checked execution has exact intersection semantics for closed Original resident operands. Initial numeric bounds construct a physical query, its checked instruction schedule, and allocation bounds. Mu and union operands are included. Persistent native histories now derive actual earlier edge writers, exact captured handles, writer-to-reader heap growth, and indexed full guard origins. Initial numeric query inputs produce completion and the same history with all resource bounds. Actual surviving compileRows rows now retain source row/child indices, full joined guards, and historical child calls at growing heaps. Returned node cells retain their captured compiled body and protected finish. Ready-cell retention allows final-reader history to recover earlier row writers without internal active-owner history. Actual captured ordinary node bodies now derive their row compiler and indexed historical children, including ready node hits. | Compose contextual semantics and generated result-fed callers on the same actual trace. Complete concrete runtime and total memory bounds. |
| Finite ordinary constrained reduction | Initial profiles and constructor headroom derive the original universal raw Reach numeric Plan. The complete modeled outer pass has stable execution, exact full guarded-language preservation, retained stores, and constructor request bounds. | The domain excludes Mu, references, and explicit unions in every descendant. The theorem does not bound total Haskell runtime or memory. |
| General reduction components | Initial resources construct supported readers, Merge, Target, Force, Leaf, editors, class passes, local reduction, parent edges, and edge memo calls. Actual primary certificates now construct complete Required returns with exact language and structural row origins. Initial Ready data and field availability derive exact normalization fixedness through the actual inherited prefix and indexed descent. Actual completed Parent reads now retain native writer history through Scan, Required, class passes, local reduction, and construction, with the existing explicit Parent range plan. Actual edited normalized rows retain indexed source prefixes, full fields, and derived writer histories at the same captured row states. Selected child calls now retain exact prefixes and suffixes with captured histories. Actual class right folds retain source-indexed tail, class, and head execution phases. Their selected leaf calls derive original-input closedness, historical target receipts, and exact native returned cells and writers. Actual suffixes now retain those exact cells and strong writers at the full class reader, and derive its native history. Captured ordinary writers supply conditional full row and ordered-child lineage at that reader. | General recursive outer-node progress and repeated-pass convergence remain open. Component support domains do not establish their composition for every recursive caller. |
| Outer memo owners | Equal physical request keys identify complete ready request arguments. Bounded workers retain evaluating owners on busy faults. Initial edge-idle tables exclude outer edge-busy faults. A constructed copied-child case reaches a ready hit while ancestor node owners remain active. Actual descent of a Ready live nonempty inherited payload strictly lowers path height and changes its identity, including warm hits. An actual empty-own prefix retains normalized inherited values. Actual normalization and combination produce fixed payloads, and indexed descent preserves fixedness. Strict class dependencies remain exact among retained classes of one normalized payload. Initial fields and Ready operands now produce original-constituent containment and dependency preservation through actual accessor, combination, normalization, and retained indexed descent. A mirrored copied-child case reaches a fresh demand before its original sibling, then completes. Another source reaches the exact original node under a different inherited key while its root owner evaluates; the local precheck and both completed calls produce Empty. | General node-busy exclusion still needs a causal progress or owner-disjointness argument for nonempty local classes and all active ancestors. The constructed prefix and descent cases do not prove a general outer parent-and-child execution. See [actual row progress](notes-current-active-row-progress.md). |
| Source input reconstruction | Initial Ready data constructs raw and stored schedules for every BinderFree source, including union roots and recursive captures. Actual source construction recovers each selected Mu record's first writer, callback histories, physical growth and issued-reference transport. Later warm requests keep that record. BinderFree of the recovered writer constructs both filtered reconstruction calls. | The condition applies to the recovered writer. Arbitrary nested writer bodies and full smart cleanup composition remain open. Writer metadata alone is not installed-record evidence. The complete outer-pass domain is unchanged. See [current lineage](notes-current-active-growth-lineage.md). |
| Active owner ancestry | Actual node-busy failure constructs its dispatch, every active owner's exact enclosing activation, and actual operation growth into the reader. Literal lower and outer workers prove growth on every outcome without a graph, range, Ready or future-completion premise. Initial Ready values, full field loads and structural constraint-cache validity persist. Actual native writers derive raw stored-class coverage through full joined guards. Same-index splits separate computed child obligations from Top owner keys. | Full physical operation invariants now reach actual unfinished outer prefixes. The complete captured busy request equals its active owner. General all-ancestor collision exclusion and fresh-call bounds remain open. Crossing classes can disappear at both children. Positive raw guards and complete field occurrences through class edits are covered. Individual class row chains now retain ordered child reads. Complete retained-Mu/source lineage remains open. A repeated full request under a nonempty inherited owner requires an actual own-field height gain. Its exact earlier reached row and completed edge call are now derived. This does not make that row a proper initial-source occurrence. No general termination theorem follows. |
| Completed lower and Parent physical invariants | Actual successful Target, Force, Leaf, editors, class folds, Scan, Required, local reduction and Parent construction derive full operation Valid, heap Ready, allocated fields, probe/cost heaps, growth and available results from initial facts. No Ranges, InputsThrough, Cap or future state invariant is supplied. | Completion is a premise. Physical filtered probes now compose through actual unfinished outer prefixes. Global memo language laws, numeric headroom and progress remain open. |
| Recursive Head and class fields | Initial closed inputs construct actual Head and stored-body descriptors. Literal-node stored bodies derive indexed original rows and ordered warm child calls at the exact final reader. Nested Mu children are included. Actual indexed edits and class right folds classify complete field occurrences, including final empty propagation. | Checked native Trace Inputs remain explicit. Individual full-row chains now retain ordered child reads. Union-body source-node alternatives now derive earlier indexed rows and ordered calls. General retained-Mu body alignment and native compileMu original-operand lineage remain open. |
| Used binder root alternatives | Actual union normalization and self filtering preserve bidirectional root alternatives, complete ordinary fields and ordered child relations. The relation permits permutation and duplicates. | Actual fresh publication inputs now derive alias and raw/filtered free-name transport, including the actual earlier retained writer. Complete output reference, Mu-atom and ordered child relations still need general used-local source induction. This alone is not language equivalence. |
| Other library components | Checked language, equality, enumeration, arithmetic, union-find, memo, ranking, generation, and sampling results exist. Some source drivers and restricted adapters are complete. | Their remaining adapters and recursive callers do not yet form a complete current-library implementation theorem. See [API coverage](API-COVERAGE.md). |

The finite ordinary result is in
`SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryRoot.finite`,
`constructed_root`, and `prepared_root`. The caller no longer supplies the
reached numeric Plan. Read [the resource result](notes-current-raw-reach-capacity.md).

The earlier recursive native result is
`SourceCurrentAllocatedNativeColdClosedExact.cold_complete`.
`SourceRecursiveIntersectionRequestProgress.initial_complete` already derives
semantic completion for closed Original inputs. These semantic results
do not require the caller to supply semantic Completes.
`SourceCurrentAllocatedNativeConstructedHistory.query_complete` also derives
entry facts from actual generic construction and a covered field history.
It retains the actual build and WordRanges premises.

`SourceCurrentAllocatedNativeComputedBudget.initial` now constructs the
complete physical query and its resources from initial counters, causal
stored mass, closed Original operands, semantic readiness, idle native
tables, and numeric headroom. It does not require a future Trace,
WordRanges, instruction count, or returned-result law. Read
[computed query budgets](notes-current-computable-query-rank.md).
This receipt still needs contextual language composition on the same trace.
It does not bound all internal constructor work, solver work, or total memory.

The latest Required entry is
`SourceCurrentRequiredPrimaryOrigins.constructed`. Actual construction
derives its readiness, cost, guard, and union-normality facts. An earlier
false primary class and initial operand availability construct a complete
Required return with exact guarded language and indexed original row
origins. It assumes no future Required result. Read
[Required origins](notes-current-required-origins.md).

## Remaining work

1. Derive retained-Mu row and ordered-child provenance from actual causal
   writers. Recursive normalized plan and stored congruence construct both
   calls with one exact result from initial Ready and available captures.
   Their structural relation is not yet derived for arbitrary retained-Mu
   histories. Union normalization already has physical Empty agreement,
   all-depth observations, and exact literal atoms and complete rows.
   Ordinary parents preserve observations. Root self filtering preserves
   exact literal parts for normal available roots. The initial theorem
   derives these parts for the two union orders, but not for arbitrary
   selected body and ordinary-probe writers.
   Actual ordinary-node callback publications retain source row schedules,
   child Empty tests, and row-drop agreement. Every BinderFree source now
   derives all-depth observations and physical Empty agreement. Structural
   induction retains strict source-size witnesses for node children and
   union members. Initial Ready data constructs both raw source calls and
   both sequential stored calls with their local histories. Captured values
   can contain Mu records. Support compatibility replaces whole-list Paired
   when only live source captures need replacement agreement.
   Actual reserved binder bodies now have paired lexical inputs with unequal
   outer-reference tails. Their reserved names are fresh by actual cache
   misses, cut contexts, and issued-reference facts. The paired reference
   base gives exact repaired execution equality. The ordinary induction step now accepts these unequal paired tails.
   Actual ordinary probes derive compatible replacement maps on live source
   support. General arbitrary captures can alias a probe name. Actual paired
   publication inputs now derive the required freshness and live aliases,
   including captured Depth aliases. Actual filtered free names correspond
   under the fresh local-name pair, also at the recovered earlier writer.
   Every publication with a BinderFree source body now derives filtered body/probe reconstruction
   agreement. The root-erasure proof handles union roots with exact literal
   parts. Actual repaired callback profiles derive bare-self parity. Derive
   the nested source binder case. Actual first-writer chronology and reader
   transport are now produced by source execution. A BinderFree recovered
   writer supplies both current calls. Derive the result for arbitrary
   nested writer bodies.
   Then compose smart cleanup, fixed captures, and root filtering. Retain
   full guards, ordered children, literal Mu atoms, bare references, and
   epsilon origins. Derive freshness and issued-reference transport from
   actual execution; four-table Grows does not supply the latter. Compose
   native callbacks and protected edge histories on the same trace. Read
   [literal provenance](notes-current-literal-union-provenance.md) and
   [the new induction cases](notes-current-selected-child-lineage.md).
2. Derive progress for actual outer-node children after parent returns and
   inherited combine/descent. The measure must respect physical memo keys,
   or prove that a fresh request differs from every active owner. Actual
   node-busy failure now produces its own exact dispatch and every active
   owner's enclosing activation. No caller supplies the prefix or past
   completed-call graphs. Actual lower and outer workers now attach
   operation growth to those phases. Native row writers derive raw stored
   class coverage through their full joined guards. Positive syntax gives local
   raw-class origins. Actual class phases now compose full guard occurrences.
   Individual full-row survival chains are now derived for actual completed
   class Reads. Complete retained-Mu body and original-operand lineage.
   Physical completed Parent invariants now compose through actual unfinished
   outer prefixes without future state premises.
   Selected same-index own paths already
   give a nonempty child payload and key separation from Ready Top owners.
   A normalized crossing class can disappear at both immediate children.
   Cover those classes and non-Top active owners without assuming the
   desired global separation law. Also derive a finite fresh-call bound or
   a well-founded measure. Key exclusion alone does not give that bound.
   Actual
   normalization and combination now produce exact fixed payloads. Actual
   trie descent preserves fixedness. The full accessor/prefix/descent path
   derives it from initial Ready data and field availability. Empty-own
   prefixes retain normalized inherited values; nonempty descent then
   strictly lowers path height and changes its canonical identity. The
   retained class dependencies now remain exact within each normalized
   payload. A copied child can still require fresh work before its original
   sibling is visited. The remaining argument must control nonempty local
   classes and all active ancestors. Persistent native histories supply
   actual earlier full guard writers, exact owner handles, and growth into
   the reader heap, but not a global occurrence rank. Exact selected-child
   prefixes and class-fold phases now retain their actual captured histories.
   Actual class leaves derive historical target receipts and exact native
   returned cells, with closedness from the original selected domains.
   Captured ordinary writers derive full row and child lineage at the leaf
   return. Actual child and class suffixes now retain the same returned cell
   and strong writer at the full-fold reader, and derive its native history.
   Historical target slots remain at the leaf return.
   Actual returned native node cells retain their compiled body and finish.
   Ready cells at a past body return persist into the final reader, whose
   history recovers earlier edge writers without internal active-owner
   history. A warm writer's child call can precede the current body. These
   results still need a compatible causal rank for all active outer owners.
   A checked source now repeats the exact original value under a different inherited key; its
   local precheck and both complete calls produce Empty. This rejects whole
   physical-value descent, not proper row-origin measures. Ordinary height
   and maximum constrained depth do not suffice.
   Then complete nonempty live child walks, ordered rows, ordinary node
   bodies, and the full mutual outer pass. Mu and union roots can be terminal
   while selected paths still enter their contents. Read
   [actual row progress](notes-current-active-row-progress.md).
3. Prove convergence for repeated reduction passes and complete the remaining
   recursive pruning and compilation callers. One exact completed pass does
   not establish a fixed point. Semantic narrowing alone does not bound
   intermediate structural growth.
4. Complete current frontend correspondence. This includes typing and
   refinement derivation, drawn fields, symbolic measures, new errors,
   validation order, and generator-specific order.
5. Complete concrete runtime and external adapters. These include maps and
   arrays, signed indexes and counters, lazy memo publication and forcing,
   process-global state, interning, codecs, solver answers, IO, and random
   draws. Keep explicit primitive and user-code assumptions visible.
6. Compose generated result-fed native queries and complete public pipelines
   through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Abstract
   composition does not discharge a missing implementation adapter.

The older PlainRegion theorem permits opaque Mu and union leaves. It requires
empty physical equality payloads on traversed ordinary edges. It does not
prove general recursive selected narrowing.

## Haskell repairs and evidence

The recursive field-pool defect is repaired by `b9219b9e`, merged in PR 65.
The current derivation rejects a pool for a field of the datatype itself.
The retained Chain example returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone holds still treats supplied pools as opaque. The repair rejects
the invalid derivation input; it does not change that standalone evaluator.
Root [FINDINGS](../FINDINGS.md) keeps the repair handoff first. It records
the failure, reproducer, affected paths, commit, validation, and merge status.
It also records the earlier negative-bound and named-measure repairs.
The historical failure reports retain their original bytes and source dates.

The last completed full pinned Audit passes 3162 jobs and 69585 dependency
checks. Only propext, Classical.choice, and Quot.sound occur. All four new
strict source logs are empty. Complete public proof prints and constructed
integrations pass. The Audit replays one unchanged old unused-variable
warning. The unchanged Haskell source retains its strict Nix all-component
build, 798 examples plus golden, Fourmolu, and Cabal-gild validation. These
checks are component evidence. They do not measure whole-library completion.

The latest completed evidence is in
`restart-evidence/20261018-paired-source-induction/`. It includes strict
source checks, public signatures, complete public proof output, axiom checks,
constructed executions, independent review, and preservation checks. Failed
printer and earlier warned attempts remain preserved. A large constructed
proof is checked privately and exposed by a theorem with the same statement.
Its complete public proof print names that checked private witness.
No new Haskell defect was established. General recursive progress and full
correspondence remain open.
