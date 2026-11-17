# Next full warm query: NoNewMu dependency audit

Status: OPEN design. No theorem or compiler credit.

The full target is the execute endpoint AND every bounded actual Trace prefix
of the next query, starting at the SAME retained oldSnapshot. The old state is
an actual cold prefix at arbitrary oldControl. It need not be a completed cold
query. The target retains the accepted original source, stored full U, both
original request operands, actual plans, physical operations and supplied fuels.
It assumes source inventory only at the PAST machine before that cold prefix.
It assumes no NoNewMu, Profile, result law or qualification at a future warm cut.

This is a native-query component. It does not change the original worker's
source/root/noStop scope or discard outputs before stops. The execute conclusion
keeps its actual heap, including pending and blocked outcomes. It does not
assert that the native query completes or that an emitted partial term has a
finite accepted completion.

## Three exact open contracts

FULL-FIRST-HEADER.lean.txt declares
NativeAllocation.original_universe_next_warm_query_no_new_mu.
It concludes NoNewMu from oldSnapshot.heap to the actual execute heap and to
EVERY bounded actual prefix heap. No newControl, successful-result or completed
warm-output restriction is imposed. No warm table is replaced by initial tables.

ADMISSION-FIRST-HEADER.lean.txt declares
NativeAllocation.original_universe_next_warm_mu_query_prefix_admission.
It classifies the actual selected Mu request into the existing warm Qualified
predicate or the same TWO auxiliary Mu-owner shapes as the cold theorem. Each
auxiliary clause retains ONE full-pattern/base-domain/AuthenticEntryAt bundle.
Its fixed wholeCount, query prefix and actual reader all start at oldSnapshot.
This is a requested producer conclusion, not a supplied classification premise.

OPTIONAL-FIRST-HEADER.lean.txt declares
NativeAllocation.original_universe_next_warm_optional_prefix_no_new_mu.
It retains the literal optionalBinder, its actual child body and current heap.
It concludes NoNewMu for the actual maybeMu outcome, including pending effects.
It supplies the only missing writer case in the final execute/Trace induction.

All three headers were frozen before this audit body. They are OPEN. The
prospective preamble is not a proof file and has not been compiled.

## What the current dependencies do

SourceSynthesisCurrentUniverseColdNoNewMu:31-76 proves the heap-step decomposition.
Only optionalBinder needs a source result argument. Work jobs use
SourceCurrentNativePublicationTrace.work_noNewMu:22. Other native/memo controls
retain the heap. ColdNoNewMu:78-176 proves the exact execute and Trace induction,
including terminal blocked/pending effects. These private helpers cannot be
called from another module. Their proof text can be reused with a warm anchor;
there is no need for another runtime engine or a modified execution function.

NativeAllocation:1844-1954 is the checked cold Mu-call admission producer.
NativeAllocation:2197-2589 is the checked cold optional writer proof. Its
original source entry, actual queried owner, child Trace and current reader
come from ONE ConsistentOptionalOwner.request invocation. That public theorem
accepts an arbitrary physical start (ConsistentOptionalOwner:35-110). It is
already applicable at oldSnapshot after deriving Physical from oldActual.
It does not itself classify the queried request into a source family.

WarmCMDefinitions:21-49 defines the prospective Qualified and result laws.
NodeResult is an implication from ClosedQualified or MixedQualifiedAt to a
Profile. EdgeResult is also conditional on qualification of all zipped inputs.
These predicates do not assert that every actual query is qualified.

The prospective source Gamma theorem is WarmCMHistory:38-76. It derives BOTH
Returned tables at its reader AND every prefix of ONE fixed full warm H. Its
public premises include the actual old cold prefix, the actual warm H and the
physical plans. It does not take semantic finish callbacks as public premises.
Its initial law calls are at94-106 and actual warm induction at115-117.
Its prospective C/M/edge dependencies must pass before this theorem has credit.

The prospective af8 component, WarmActualChild:164-213, constructs the literal
U/P enter's AuthenticEntryAt and B/P MixedQualifiedAt at ONE actual horizon.
It then applies Gamma and the actual warm reader law to the SAME child result.
It covers fresh evaluation and memo hits for THAT child, not every Mu owner.
Its header also asks that the chosen P is Available at oldSnapshot and that the
old cold root completed. The more general Gamma has neither restriction on
that intermediate pattern nor the oldControl. Do not silently add either
restriction to the new full-query target merely to call af8.

SourceCurrentNativeWarmAuxiliaryPrefixes: its FIRST header derives all FOUR
auxiliary Returned laws at every actual warm prefix from the genuine source
and traces. The implication takes the actual AuthenticEntryAt at fixed H.
It is already a source-derived law, not a future semantic supplier.
The reader export SamePrefixKeyedChildResult:298 observes a SAME actual child
and reader under those laws. It does not fabricate another cache or entry.

## The remaining source admission gap

NativeAllocation's NodeAdmission, EdgeAdmission, CodeAdmission and
ControlAdmission are defined at40,72,83,124. Their types embed the cold anchor
initial(width,machine) and cold AuthenticEntry. CodeAdmission's enter/read
obligations at98-120 refer to literal prefixes at that same anchor. The
same-owner source compile helpers at1533, step_admission at1551 and
trace_admission at1666 therefore do not typecheck as warm-start facts merely
by changing a final theorem argument. The public projection at1844 and the
full cold prefix exports at2700/2763 retain that restriction.

The step proof has no semantic cache-result assumption. For a ready memo hit,
work result, or successful optional result, its continuation admission is
universal in the returned payload. For an evaluate observation, Physical and
the actual inputs identify the captured request (1611-1664). Empty memo tables
are not needed for those transition arguments. The problem is the embedded
history anchor and source family types, not a need to assume a warm result law.
The sibling carrier audit records the detailed port. This audit does not copy
its helper declarations or claim that changing only a public wrapper
will repair those types.

Replacing oldSnapshot by initial(width,oldSnapshot.machine) discards retained
tables and changes the run. Extending an old cold Trace through a new independent
request does not work either: its literal pure continuation stops. Neither
operation is allowed. The source call proof must retain oldSnapshot itself and
warm AuthenticEntryAt(newRoot,oldSnapshot,H) throughout the existing carrier.

Gamma alone cannot discharge this gap. A Returned implication says nothing
about a request outside its qualifier. That logical non-implication is not an
actual reachable-source counterexample. No Haskell defect is claimed.

## Concrete proof sequence after the semantic candidates pass

1. Derive Physical, growth, operation validity and source NoNewMu at oldSnapshot
   from the SAME oldActual. Derive both new-root Profiles from their actual
   Available/closed fields and StartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu:214.
   This uses only the earlier cold inventory, never the desired warm endpoint.

2. Produce warm Mu-call admission at the actual query prefix. Reuse the current
   source compile/step/Trace argument with an honest warm anchor and the existing
   AuthenticEntryAt. Do not supply Gamma, qualification or a future cache law.
   The three genuine physical initialization helpers needing warm variants are
   physical_at_root_prefix:287, authentic_domain_key:317 and the literal entry
   constructor original_entry_from_literal_enter:360. Existing WarmEntry:21-73,
   checked_trace_extension:28 and OrderedOriginalEntry:30 provide their actual
   physical entry interfaces. The fixed-H source projection must keep ALL
   auxiliary alternatives; a symbol-only or closed-only result is insufficient.

3. At ONE optional prefix use ConsistentOptionalOwner.request ONCE. Set H to
   that actual prefix's used count. The owner equation supplies the exact child
   prefix, enter, child result and final reader. Call the newly derived source
   Gamma and auxiliary-prefix theorems on THAT H. Their initial laws are then
   derived for that H internally. Do not splice laws produced for a different H.
   If a caller has already fixed H, retain that H and its same literal trace.

   The optional cases are C plus four mixed/auxiliary variants:

   | Queried owner | Actual child law | Optional action |
   | --- | --- | --- |
   | C: U/P at empty domain, either operand order | actual B/P MixedQualifiedAt and Gamma Profile | free=[] makes its binder unused |
   | M: B/U at authentic K | BodyFirst BB product at K+e, cutoff e | same-cutoff stored-U reclosure |
   | M: U/R at authentic K | Coherent BR product at K+d, cutoff d | same-cutoff stored-U reclosure |
   | Aux: U/R at K+e | repeated e result at K+e+d | outer binder d is unused because e differs from d |
   | Aux: B/U at K+d | Coherent BB product at K+d+e, cutoff d | outer binder e is unused; do NOT reclose at e |

   Here U is the original full Mu, B its open body, R its interned reference,
   e=pair(bodyId,U.id), and d=pair(U.id,U.id). Body identity separation at the
   authentic coherent heap gives e≠d. The current cold optional proof already
   implements each row, so port those proof steps and the warm reader calls.
   For the first row, use Gamma directly with the actual entry qualification if
   the stricter af8 header cannot be instantiated. Do not add an earlier P lookup
   or a completed old-root premise just to match af8.

4. Reuse the cold_step_no_new_mu, traceOld and executeOld proof structure with
   oldSnapshot as literal start and the new optional producer as an internally
   proved dependency. The step cases still use the original physical inputs.
   The execute induction must retain the actual heap of every terminal outcome.
   Compose the resulting receipt with the already derived source→oldSnapshot
   receipt to recover source inventory at every new prefix and execute endpoint.

All branch data must be retained from the same owner/entry/child observation.
Use the chosen AuthenticEntryAt bundle for its auxiliary key and payload law.
An equal Prop index does not identify independently hidden constructor fields.

## Claim boundary and later iteration

The first strict Work52 chain failed in Mixed notation. Defs, C and edge passed;
Gamma and af8 were blocked. This audit gives the blocked semantic components
no proof credit. It does not depend on an unfinished or independently chosen
future trace. It records a route that becomes usable only after strict passes.

Even a proved FULL header closes ONE next warm query after a genuine cold
prefix. It does not prove an arbitrary sequence of independent warm queries.
For later worker calls, the predecessor tables may contain cells first returned
by a previous warm query. Reuse at that boundary must derive the next query's
initial six laws from the actual previous history and the new full qualifier.
It must not reuse the cold-only initial law as if the predecessor were cold.
This remains distinct from the original worker's source/root/noStop attachment.

NoNewMu constrains completed Mu records in nodeRecords. It permits ordinary
heap growth and does not state that reservation counters or pending records
remain unchanged.

No finite accepted completion, native language inhabitance, Type/Marker class
compatibility, guard truth or Haskell correspondence follows from NoNewMu.
The original goal still requires ONE assignment for EVERY historical branch
obligation of the SAME accepted source/root, with all original fuels and outputs.
No source mutation, compiler, test, Git, board or temporary object action ran.
