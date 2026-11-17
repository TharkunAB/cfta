# Original accepted source and public partial-output boundary

Status: READ-ONLY AUDIT. No proof or counterexample is claimed.
The original full completion target remains unchanged.

## Result

A bounded internal stop is not a fresh public source output.
The checked eager output-control theorem already excludes that interpretation.
At every supplied work and recursive fuel, stop=none forces each actual emitted
output to have metadata=none and pure selection next=.done.
A stopped result can retain outputs that were emitted before a later stop.
Those retained outputs still satisfy the same no-stop control theorem.

This does not prove that every source no-stop output has a finite native model.
A completed selection may retain recursive boundaries.
No accepted-source execution with an uninhabited query and a public output was
constructed or checked in this audit. Generic truncation examples do not supply
such an execution.

## Exact Lean boundary

- SourceSynthesisCurrentConstruction.lean:16-23 defines firstOrderRaw.
  It constructs rows and applies the query-type filter.
  The theorem firstOrderRaw_ok_iff_nonnegative at54-63 says that construction
  succeeds exactly for nonnegative signed sizes. This is not an inhabitation test.
- SourceSynthesisCurrentNoStopSourceEntry.lean:67-99 retains the actual original
  build, stored U, initialized caller and startup root. The accepted_no_stop_eager_entry
  theorem derives the literal no-stop decision expand0. It does not replace the root.
- SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.lean:39-75 defines
  the actual resumeWithNarrow operation. A done decision emits one output.
  A stuck decision emits none. An expand decision at recursive depth zero returns
  stopped [] exhausted. Selected and preparation failures add no fresh output.
  The metadata-bearing output at decision none is the optional stop-rule branch.
- SourceSynthesisSharedEagerOutputControl.lean:456-473 proves runEager_output_control
  for every original workFuel and recursiveFuel. For actual output membership,
  stop=none implies metadata=none, which implies next(defaultOrder,cache)=done.
  The conclusion applies even when the enclosing result later stops.
- SourcePruningEnumerationSharedPreparedRecursive.lean:62-71 preserves the existing
  output list through finish of a stopped fold. It does not convert the stopped
  observation or candidate cache into an output.
- SourcePruningEnumerationSharedRecursive.lean:54-62 defines the actual Output.
  It has metadata, cache, caller and saved queries. It has no optional fragment
  field. No normal Source declaration named stoppedOutput was found. A notation
  such as stoppedOutput(fragmentnone) must therefore be tied to a specific API
  before it is used as a public-emission witness.
- SourcePruningEnumerationSharedPreparedSelectedDriver.lean:71-90 starts only
  after an actual native done value and successful encodeNode. A failed native
  root or unencoded value is a separate result, not a started enumeration output.

## Partial observation is not semantic acceptance

SourcePruningEnumerationPartialOutput.rootPartial at39-48 is a root observer.
It reads the stored root fragment, or its hole, then calls expandPartial.
The hole equation at50-79 renders an unexpanded slot as a hole, except an actual
empty-bucket decoded recursive boundary, which renders as truncated recursion.
It does not search for a finite accepted completion.

rootPartial_stored_equations at159-211 guarantees a finite observation and says
that EVERY assignment satisfying the stored equations completes that observation.
rootPartial_complete_pending_choices at236-265 extends compatible pending choices
structurally. Neither theorem derives actual native-domain or guard satisfaction.
OutputResources.root_partial_complete in SharedPreparedPartialOutput.lean:33-74
first requires genuine OutputResources. Its semantic completion clause at57-61
still assumes Satisfies for the same output state.
Thus rootPartial success from an arbitrary current cache, including a diagnostic
observation before the worker finishes, is not the source output predicate.

## Actual Haskell public paths

Data/CFTA/Enumeration.hs:968-1014 defines enumerateUntil'.
With no stop rule it returns only at ExpansionDone. ExpansionStuck rejects the
branch. There is no explicit Lean-style runtime fuel or budget-stop output here.
With an explicit stop rule it can return a partial state before completion.

- termsPruneWith at1171-1174 runs enumerateFully' before expandUVarWith.
- truncatedTerms at1094-1100 runs enumerateFully before partial rendering.
- runsFrom at1285-1294 runs enumerateFully, renders the root and retains residual
  obligations. It does not apply a separate accepts(root,term) filter.
- expandUVarWith at1076-1082 rejects a nonrecursive unexpanded root. It permits a
  recursive boundary marker. expandTermFragWith at1057-1067 renders recursive
  holes with the configured marker; it is not an inhabitation check.
- termsPruneUntil at1188-1201 uses an explicit stop rule and partial rendering.
  Its documentation at1176-1186 explicitly allows a partial term without a
  completion. This API is broader than the original noStop source target.
- expandPartialTermFrag at1046-1054 is also public for diagnostics. Direct use
  during progress does not imply a completed no-stop source emission.

Specftacular/Pruning.hs:95-106 uses termsPruneUntil with the atTypes stop rule.
This is not noStop. Its typing callback can reject a fragment without a typing;
openTypes at182-194 rejects unresolved program holes but keeps type placeholders.
These checks must not be silently identified with the original noStop contract.

Data/CFTA/Gen/Synthesis.hs:949-970 converts listed runs to Programs. programRuns
removes duplicate Programs; programsIn removes duplicate typed terms. Neither
adds a final semantic accepts check. The query filter belongs to rawSearchSpace
at778-779 and its construction, not to a post-enumeration inhabitance filter.

## Required theorem and remaining input boundary

For the original target, retain actual accepted firstOrderRaw, the SAME original
native build and startup root, stop=none, ALL supplied fuels, and actual membership
output in emitted(runEager ... originalStartup). That membership is the necessary
operational boundary. Do not replace it with arbitrary partial-read success,
internal stopped candidate membership, or a generic truncated term.

Finishedness is already source-independent and checked by runEager_output_control.
The remaining theorem must derive ONE finite assignment for THAT actual output,
with native domains, stored equations, UF aliases, current guards and ALL removed
historical obligations. It must then complete the SAME original partial root.
No existing public filter automatically supplies this joint model.

The closest checked semantic consumer is
SourceSynthesisCurrentRealDoneRendering.accepted_real_rendered_assignment:26.
It keeps original source, noStop, supplied work/depth and actual output. At69-72
it still requires every actual pending native handle's boundary atoms to come
from the original U. At75-79 it requires actual rendering and truth of its
returned residual obligations. Those are explicit conditional premises, not
filters already enforced by fragment/readback acceptance. The whole source lift
must derive the needed native/guard/history facts internally. Adding a future
assignment, a satisfiability filter, or sufficient-budget premise to the original
public target would change the requested theorem.

## Audit limits

Read-only source inspection only. No Lean or Haskell execution was run.
No theorem, resource bound, runtime fuel, Haskell code or public target changed.
No reachable source bug or counterexample is claimed.
