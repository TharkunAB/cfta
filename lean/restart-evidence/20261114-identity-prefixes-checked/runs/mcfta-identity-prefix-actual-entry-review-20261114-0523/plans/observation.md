# Exact observation proposal

Status: proposed pure projections and theorem. No bodies or compiler check.
Both sides observe the same native backend with identity narrowing. The theorem does
not compare the configured pruning worker with the identity specialization.

1. eraseMetadata : Metadata Typing → Metadata Unit sends every input to
   ⟨[],[],[],()⟩. The literal Haskell state is unit. Preserve the entire original
   result separately. This projection does not change an operational Core or heap.
2. erasePrefix : SelectedStep.Result width Typing → SelectedStep.Result width Unit.
   stopped: keep the read and checked raw observations exact.
   parked: keep checked Core/candidate; map ONLY Metadata in each successful raw
   ((metadata,next),Core). Keep None, [], raw errors, list order and Next exact.
   narrowed: keep checked/prepared/caller/full Queries/action/candidate/ordinary exact;
   map ONLY Metadata in successful Right raw ((Bool,metadata),Core).
3. eraseFailure : PreparedRecursive.Failure width Typing → Failure width Unit.
   exhausted: keep uv and Cached exact; replace metadata with eraseMetadata metadata.
   selected: keep uv and use erasePrefix on the actual observation.
   callback: keep uv, raw list/errors/Bool/Core/order; map successful metadata only.
   preparation: keep uv and the entire actual Preparation exact, including fault heap.
   alternatives: keep uv and processed receipts exact. Keep edge stops and endpoints
   exact. In continuation stops retain the receipt/optional endpoint and recurse on
   the contained Failure. This is a pure map over the existing recursive datatype.
4. eraseResult : HookResult (Output width Typing) (Failure width Typing) width →
   HookResult (Output width Unit) (Failure width Unit) width.
   Map every output's Option metadata; retain the Option constructor and SAME cache,
   full Caller and full Queries. Retain output order and duplicate occurrences.
   Keep complete versus stopped, all final/optional endpoints and erased stop reason.
   Do not turn failure into success or identify exhausted work with empty language.
5. Default observation relation for two results is equality after this exact map.
   For literal Haskell unit oracle, derive the concrete callback equation in this
   quotient: recordTypes_empty gives false, SAME Core and updated metadata; the
   concrete lower-depth metadata-erasure IH removes that update. The recursive
   decision is SOME next(no preference) on the SAME cache. There is no public
   arbitrary continuation/provider assumption and no second operational worker.
6. The theorem in erasure-header proves initial-metadata independence. It also
   permits the Unit representative. It does not, alone, assert correspondence to
   Haskell or provide an operational semantics for host laziness or global interning.
   To use the quotient as the literal control trace, verify each existing actual
   selected/parked/callback/preparation equation after this map. The callback reduces
   to pure(false,unit), and native narrowing reduces to SAME value/heap by definition.
   Existing generic eager children then supply the SAME checked expansion operation;
   source/Haskell primitive representation and processed-root/order links remain.
7. A callback hook is unnecessary for this exact observable claim. It is required
   only if exact un-erased Metadata values or literal raw callback identity are the
   target. Those are deliberately absent from the Haskell default API. No assertion
   is made for metadata-dependent order, metadata-dependent stop, nonempty templates
   or the old configured narrow. Stopped prefixes at every finite fuel are retained.
