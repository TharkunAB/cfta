# Automatic ancestry from actual outer busy failures

Date: 2026-10-18 01:09 CEST.
Production: SourceCurrentOuterExecutionAncestry.lean.
SHA256: 32ec52112a2159e98d64670c35de7f6d93bb3e165cf10ee92c5393626f833234.

## Completed result

initial takes an ACTUAL literal nodeCall failure of the form
`failed (nodeMemo handle busy) after`. Its input caller is the literal outer
initialization with the supplied checked state, Merge memo, and fourth memo.
It derives its own finite reached dispatch prefix. The dispatch caller is
EXACTLY the supplied full failure state `after`. Actual beginNode returns
busy at the same handle and leaves that caller unchanged.

The theorem then derives the complete captured owner and its key equality
with the reached candidate. Ancestor retains the exact earlier beginNode
activation, captured request, owner, caller before demand, selected handle,
evaluating body-entry cell, node-table validity, and unfinished body prefix.
The conclusion also covers EVERY evaluating node handle at the failure
caller. No activation-stack invariant is an input.

No Ready, availability, Cap, range, completed graph, successful future call,
desired prefix, or desired owner relation is a producer premise. Initial
empty outer tables derive the required node-table validity and idle fact.
The lower supplied states can contain warm cells and memos.

This result does not prove that a cold source call can encounter busy. It
does not exclude a collision or prove termination. The remaining progress
obligation is to exclude key equality between a reached candidate and every
derived enclosing activation. The statement retains physical keys, not an
assumed source-size or whole-value descent measure.

## How the prefix is produced

The old OuterActiveAncestry prefix requires both successful earlier worker
equations and completed graph witnesses for suffix steps. Its graph extractor
needs reached range evidence. This module leaves that source unchanged.

The new Step uses only literal branch equations and ACTUAL completed earlier
worker equations. A direct induction on the bounded mutual worker derives
node-table validity and forward/reverse evaluating-cell preservation for
every successful earlier call. It does not use semantic graph extraction.
The private finish proof excludes the selected handle from previously
evaluating cells using actual lookup/demand and node-table validity.

A second mutual induction follows the ACTUAL failed worker. Each successful
earlier prefix supplies its derived node-table facts. Each failed recursive
branch supplies the next reached phase. The proof constructs its own prefix
instead of accepting one. failed exposes this result for all six recursive
phase forms. The two edge functions cannot directly report outer nodeMemo
busy; their literal faults have different constructors.

Empty and union bodies return literally. Reference, exhausted, Mu-rebuild,
and parent failures retain their distinct faults. An underlying native busy
fault inside a parent remains a parent fault; this theorem does not classify
it as an outer node-owner collision. Thus Mu and union inputs have no added
closure restriction, but their unrelated failure kinds are outside this
nodeMemo-busy conclusion.

Step.failed and Reached.failed tie the constructed prefix to the literal
phase interpreter with the same fault and full caller. Reached.running
protects an enclosing evaluating owner throughout its unfinished prefix.
These facts concern the logical serial worker, not host demand or concurrency.
NodeValid checks key links and cell bounds. It does not supply heap semantics
or prove full request equality from a malformed physical key alias. Both
complete requests and their exact keys remain explicit.

## Constructed validation

warm_busy_dispatch builds its own physical ordinary source and derives its
availability. Actual beginNode activates its root in initially empty outer
tables. A SEPARATE indexed walk then requests that same key while the owner
is active. The literal walk really fails busy after its actual inherited
descent changes the operation state. failed derives its nonempty walk-to-node
prefix at that exact full fault caller. The cell retains the original owner.

This is a warm protocol invocation. It is not a claim that the cold root's
own recursive body reaches that invocation. It is not a termination
counterexample and does not instantiate the cold initial theorem's failure
premise with an invented nested execution.

actual_prefixes builds the same physical source. An actual rejected Parent
call returns a sentinel before field or child work. Its literal descendants
activate the Empty child. The test derives ancestry for every evaluating
handle with two protected owners. The actual completed Empty-child suffix
then leaves the root evaluating and the child returned. The new prefix
uses no supplied completed graph. These tests derive their actual equations
from the fixture; no future Trace, successful output, or stack law is input.

The printed integration theorems have the exact standalone checked types.
Private witnesses keep the printed proof aliases small. The verifier compares
both public statements to the standalone successful kernel source.

## Verification

Selected strict: outer-execution-direct-7; exit 0 and actual log 0 bytes.
Selected canonical: outer-execution-canonical-1; exit 0 and 1777 jobs.
The canonical log replays the unchanged old ClosedCompletion warning.
Selected public: outer-execution-public-1; 23 full triples.
These comprise 13 handwritten heads and 10 constructors.
Selected constructed strict: outer-execution-kernels-4; exit 0, log 0 bytes.
Selected constructed print: outer-execution-kernels-public-1; 2 full triples.
All eight explicit printer options are present. Only standard axioms occur.
Some declarations use no axioms. No printer omission or diagnostic remains.

Every Lean command executes a numbered immutable snapshot. All runs retain
their exact source, raw log, metadata, and effective cgroup readback. The
limits are 4294967296 bytes maximum, 4294967296 bytes high, and zero swap.
Direct attempts 1 through 6 preserve proof and linter diagnostics. Partial
direct attempt 3 is clean, but it is not selected as the final proof.
Kernel attempts 1 through 3 preserve namespace and exact-state rewrite
failures. No attempt was deleted or overwritten. No run was terminated.

All older sources and evidence remain unchanged. No Audit, documentation
authority, Haskell source, or Git state was edited. The new manifest and
verifier record this component's exact selected and failed artifacts.
