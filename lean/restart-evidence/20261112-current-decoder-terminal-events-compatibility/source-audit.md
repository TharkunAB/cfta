# Terminal query events and Program completion shape
Generated 2026-11-12T19:45:08.095785+01:00.

Base: `6d2844a668d29ad4795d7e34816d28790e984eb7`. Current integrated main: `e53852064d3ef5a2eafec47d754c27504b11de5f`.

Five strict-checked modules. All previous proof and Audit content remains.

## SourceSynthesisPartialProgramDecoder
Source SHA256: `f3d4aabeee4f2e1810ae6fc01c67082b3dc6b434c3bb5898a3c3f4a5565b6b2c`. Lines: 114.
Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisPartialProgramDecoder.completion_decoder_of_projection": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem completion_decoder_of_projection [DecidableEq Symbol]
    (partialTerm : SourcePruningTemplates.PartialTerm)
    (program : SourceSynthesisProgramTermSize.Program)
    (projected : SourceSynthesisProgramTermSize.Projection literal Prod.fst
      (SourcePruningPositions.openProgram true partialTerm) program) :
    ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
      SourcePruningPartialMatch.Completes assignment partialTerm full →
      SourceSynthesisProgramTermSize.Projection literal Prod.fst full program ∧
      SourceSynthesisProgramTermSize.toProgram literal Prod.fst full =
        SourceSynthesisProgramTermSize.toProgram literal Prod.fst
          (SourcePruningPositions.openProgram true partialTerm) := by
```

## SourceSynthesisProgramChildSlots
Source SHA256: `ab2d1b82f73d772c0cfd09afb681a55628d66338a8c6d00a091f298aeb9dc059`. Lines: 66.
Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramChildSlots.program_child_slot": [
    "propext",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem program_child_slot
    (incoming : Node) (scs : List Suspended)
    (fields : ValueFields valid literal incoming)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (before after : Core) (action : EnumerateM Symbol Constraint (Fragment Symbol))
    (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    ∃ handle, encodeNode incoming = some handle ∧ fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values := (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)} := by
```

## SourcePruningEnumerationSharedIncomingQueryEvents
Source SHA256: `4adbdd92705ba2b5f003593dd3da3b299ce5164f916a501fd9619d7a115d8119`. Lines: 146.
Public names and checked axioms:

```json
{
  "MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents.observe_exact": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem observe_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := observe checkEmpty representativeFuel nativeFuel p h beforeCaller before uv incoming incomingScs queries
    observed.1 = SourcePruningEnumerationSharedIncomingNode.run
      checkEmpty representativeFuel nativeFuel p h beforeCaller before uv incoming incomingScs queries ∧
    observed.2.length ≤ 1 ∧
    (observed.2.length = 1 ↔ ∃ found oldHandle oldScs old,
      UnionFind.findRoot representativeFuel before.representatives uv = some found ∧
      before.values[found.representative]? = some (.unenumerated (some oldHandle) oldScs) ∧
      lookupNode beforeCaller.checked.native.machine.heap oldHandle = some old) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      start = beforeCaller ∧ saved = queries ∧ left = incoming ∧
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by
```

## SourcePruningEnumerationSharedTerminalFoldQueryEvents
Source SHA256: `a84aa92503c88ee0b320d70a41cb31419e43ed81917bc9c0e1eb5065bb0b4290`. Lines: 251.
Public names and checked axioms:

```json
{
  "MicroCFTA.SourcePruningEnumerationSharedTerminalFoldQueryEvents.fold_observe_exact": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem fold_observe_exact
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries) :
    let observed := foldObserved checkEmpty nativeFuel p h sources caller before target queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.fold checkEmpty nativeFuel p h sources caller before target queries ∧
    observed.2.length ≤ sources.length ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by
```

## SourcePruningEnumerationSharedTerminalQueryEvents
Source SHA256: `c7277b08d9b99752a30bc464eed19e502e111eb8bee623c8224a3a08533096ee`. Lines: 263.
Public names and checked axioms:

```json
{
  "MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents.run_observe_exact": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem run_observe_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := runObserved checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.run
      checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries ∧
    observed.1.1 = SourcePruningEnumerationSharedCachedTerminal.raw
      checkEmpty representativeFuel nativeFuel p h first rest before.waiting caller before.core incoming incomingScs queries ∧
    observed.2.length ≤ (match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      representativeFuel first rest before.waiting before.core) with
      | [.ok ((recorded, _, _), _)] => recorded.length + 1
      | _ => 1) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by
```

## partial-program-decoder-note.md
SHA256 `d5ce5419e3b4790b3692ae8ff92d6f6cba9e1d989bb69623d49cfc5ea1c79e75`.

# Decoder preservation for projected partial Programs

Frozen runtime candidate, 2026-11-12 19:17 CET. ROOT owns strict verification.
SourceSynthesisPartialProgramDecoder.lean: 114 lines.
One public completion_decoder_of_projection at line 99.
SHA256: f3d4aabeee4f2e1810ae6fc01c67082b3dc6b434c3bb5898a3c3f4a5565b6b2c.
The public header is alpha-equivalent to the 91-line audit proposal.
Public-header SHA256: 130f22ddc7ce57d236491dbd917d6563929df6470177601eebddef80a8eadf6c.

The current input is the existing Projection of openProgram true partial to one Program.
The result quantifies every assignment, full term, and actual Completes relation.
It returns the same Program Projection and equality of the full and current concrete decoders.
It does not assert that any completion exists or provide a model or typing certificate.

The private proof follows the existing Projection constructors.
A projected Program node has one, four, or two children. An opaque hole/truncation renders
with zero children, so it cannot replace that Program node.
A concrete completion retains the same full symbol, exact arity, and ordered children.
Component annotations are unrestricted. Application recurses only through slots 2 and 3.
Filter recurses only through slot 1. Type and marker completions remain unrestricted.
The final decoder equality follows from Projection.toProgram_eq on both terms.

The proof permits component names that equal app/filter/Mu and keeps their exact arities.
It requires no name freshness, all-Mu discharge, native admission, Room, or new typing hierarchy.
Small private concrete/map-list inversions support the proof. There is one public observer.

This lemma does not derive the current Projection from Packet, native ValueFields, selected
row readback, callback type classification, or an actual enumeration cache.
That operational role preservation remains the separate seam in current-partial-decoder-next.md.
The generic whole-Program truncation counterexample remains outside this lemma's Projection input.

No compilation, repository edits, Git, Haskell, root documentation, or evidence changes.

The first strict check found only missing-import and reserved-keyword parser failures.
The R251 repair adds SourceSynthesisLabelProgramBuildRoles explicitly and renames every
Lean binder/reference partial to partialTerm. Comments retain their original prose.
Old source SHA: d9eaa841ff334056aa2e4324fe0203ff06571e06a303242169a17dd9cf702bc2.
Old header SHA: 29532d65b179e0bae1c3468985a59e80cd06763959f5150aee2231b6548a352b.
New source/header hashes appear above. Mechanical reverse alpha-renaming reproduces the
exact old header. No premise, output, quantifier, decoder, or proof operation changes.
The initial113 source/note, owner snapshot, and 191327 failure log remain preserved.
No quotation precheck or linter is disabled. ROOT will run the focused strict rerun.


## program-child-slots-note.md
SHA256 `35182b2c01b131224d7d35af24e8c574f395f9e307828859c2d763cb917f62bc`.

# Program child slot receipt

Frozen source: SourceSynthesisProgramChildSlots.lean, 66 lines.
SHA256: ab2d1b82f73d772c0cfd09afb681a55628d66338a8c6d00a091f298aeb9dc059.
Status: ROOT strict PASS, one public law, 2026-11-12.

One public law: SourceSynthesisProgramChildSlots.program_child_slot, line 22.
Its public header is the small audit header, with the bound name pathScope and
explicit Fragment Symbol. This is only an alpha rename of the audit binder.
Guard validity and literal names remain arbitrary. The input state is arbitrary.
The inputs retain actual SAME prepareChild identity and SAME action Success.
The result identifies encodeNode, hole before.counter and the complete raw state.
The state includes allocation ancestry and the exact suspended bucket write.
No heap availability, model, Room, class-freshness or final projection is assumed.

Proof: annotation-only trie paths exclude the empty path. Trie.nil_mem therefore
excludes terminal tries. ValueFields then leaves only empty and ordinary cases.
Empty prepares reject, which has no successful action. The ordinary case inverts
the actual action with success_bind, allocate_exact, modify_success and success_pure.
These are the checked raw equations used by prepareChild_complete's node branch.
The full prepareChild_complete theorem also requires a coherent heap, availability,
closedness, realization and slot alignment. Those premises are absent here, so
the proof uses its underlying raw equations instead of adding those hypotheses.

The law does not derive alignment or a valid stored slot from malformed raw states.
It does not add a cached ChildDispatch observer or a ProgramSlots datatype.
The actual guard-to-annotation-scope producer and complete role history remain open.
Later composition must retain existing Safe/realized/indexed execution receipts.
No compilation, repository edit, Haskell change or runtime defect claim was made.

Parser repair, 2026-11-12 19:23 CET:
ROOT's first strict check rejected the reserved binder scoped. Its focused log is
program-child-slots-192212-failure.txt. Only scoped -> pathScope changed, twice.
Preserved original: SourceSynthesisProgramChildSlots-f10702b0.lean, 66 lines,
SHA256 f10702b00b1becfb8a4fae4836773310e0aa20cb9d4e35706a2bcbea12a455d5.
Old header SHA256: dd83cb70997b06d57d31138d9d8e0c11ed6ff7c5046f0b8eac7da2f991cf1d50.
New header SHA256: a48d961c01d7bc0e6b97380f650f003d1730ebf4c208149d77001dc9205c4378.
Mechanical byte checks passed: reverse alpha rename equals the entire original
file exactly, and the same reverse rename equals the original header exactly.
All premises, operations, public meaning and the line count remain unchanged.

Record layout repair, 2026-11-12 19:27 CET:
ROOT's second check rejected the header update's continuation indentation at33:66.
Log: program-child-slots-192444-failure.txt. The same complete update is now one line.
Preserved original: SourceSynthesisProgramChildSlots-407be81f.lean, 66 lines,
SHA256 407be81f81f1f005e354f93b1ea8a68e0366a5c1216988da953d546cf4bb1fc2.
New header SHA256: 10bcd07dcf71af21d814fd89b797e9dbd65a75322f0fa0bdb00b0130a1f47080.
Mechanical byte checks passed: the entire files and headers each match exactly
after whitespace removal. All premises, operations and outputs remain unchanged.
The revised line count is 64. The proof body is byte-identical to the prior draft.

Trie proof repair, 2026-11-12 19:30 CET:
ROOT's third check parsed the header. It found two errors in elimination of tagged:
the unnamed cases operation did not rewrite the projected sc.trie in that premise.
Log: program-child-slots-192854-failure.txt. The proof now retains trieRead and
rewrites tagged explicitly in the empty and branch cases. The terminal case uses
trieRead. No other proof step changed. The frozen public header is byte-identical.
Preserved original: SourceSynthesisProgramChildSlots-c7528efd.lean, 64 lines,
SHA256 c7528efdeef0ad2ae38247add84be3dfdacd4c74ed8c7c4c1d48f877a2208cf0.
The revised line count is 66. Strict checking remains ROOT's next operation.

Final strict result, reported by ROOT at R252 start:
ROOT replaced only terminal => exact trieRead with terminal => rfl. The named
cases operation had already rewritten the terminal goal. All other source bytes,
the public header and operations remain unchanged. The final 66-line file passed
the strict check with one public law. Runtime and repository hashes match above.
This note records ROOT's check. No source was edited during the follow-up audit.


## shared-incoming-query-events-note.md
SHA256 `b2331a0b5f92e3c8d1559899cd23349ce4030d9057c4d923d03348d98f0a0282`.

# Actual incoming intersection events

The observer copies the literal incoming operation. It retains the complete
Except result, compressed Core read state, full Caller and endpoint query memos.
Every native execute outcome records one event at its actual start endpoint.
The native call and the returned Core action each execute once.
The event count is at most one. The exact branch requires a successful root
lookup, an unenumerated slot with an old handle, and a successful native lookup.
No old handle and all earlier failures produce no query event.

The operations and complete public statement match the initial frozen source.
Only the proof changed. The done branch now splits its actual completed phase
and replacement encoding. Two unused simp arguments were removed for strict
checking. No linter or quotation check was disabled.

This count covers the explicit demand.execute intersection site. The optional
enabled worker remains unchanged. Its internal calls and arbitrary consumer
work are outside this count. No whole eager-run resource bound is claimed.


## shared-terminal-fold-query-events-note.md
SHA256 `91035eafa00ecfaad55a009a4d7c1f1d907b67b6f4285ca0342e9924e245fae2`.

# R251 terminal fold query events

Status: ROOT strict PASS, one public law, exact repaired 251-line source.

Source: SourcePruningEnumerationSharedTerminalFoldQueryEvents.lean, 251 lines.
SHA256: a84aa92503c88ee0b320d70a41cb31419e43ed81917bc9c0e1eb5065bb0b4290
Header and operational definitions: shared-terminal-fold-query-events-header.txt.
Header SHA256: 336d54ddfe0fabf5813b805e8cf1cd08adad48da7524f41dce4b8ab37da97571

Namespace: MicroCFTA.SourcePruningEnumerationSharedTerminalFoldQueryEvents.
Public operations: rawFoldObserved, cachedAdapterObserved, foldObserved.
Public law: fold_observe_exact.

The observer calls checked SharedDispatchQueryEvents.observe once at each
reached source slot. Private rawHeadObserved executes the returned Core
action once. It keeps the full original dispatcher fault and native endpoint.
The cached adapter uses the existing pure adapt function on that same raw result.

The public law retains equality of the entire old cached fold result.
This includes every raw error, raw success, native and worker fault, Caller,
Queries, Core and optional Cached value. No projection field is omitted.
The event list contains at most sources.length native execute calls.
Each event keeps the exact current Caller, Queries, operands and native Outcome.
The law identifies its actual execute call at that event's caller.

Both fold paths append head events before tail events. Only a singleton
successful Core action continues. A raw nil, error or multiple result stops.
A missing cache after singleton success invokes the actual rawFold tail.
Its events remain in the returned list. A native or worker fault and an
unhandled dispatch stop before the remaining source slots.

Private proofs derive the head event facts from checked observe_exact.
They derive raw tail facts by induction on the literal source list.
The cached proof uses that same induction and includes the raw-tail case.
No future completion, model, heap, event or work supplier is assumed.

Scope: the terminal fold component. The separate incoming-node native query
site and complete terminal run remain open here. ROOT owns the incoming site.
Events count native execute invocations, including native failures and fuel-zero
attempts. They do not count native steps, allocations, time or consumer work.
The event type carries actual Queries. It does not fabricate the proof-only
EndpointMemoGateTrace.Memos.unfolding field. No eager C/Q or whole default
completion claim follows. No Haskell changes or defect claims were made.

The original 250-line source is preserved as the -8b3b6266 snapshot.
The first strict log is shared-terminal-fold-query-events-192210-failure.txt.
The repair supplies True.intro after simp reduces reflexive equalities.
It generalizes the private prepend helper over both result universes.
It also renames two proof binders that resemble the Unit constructor.
The public statement and every operational definition remain byte-identical.


## shared-terminal-query-events-note.md
SHA256 `1ffe6f16fcca967ce5c4ffee64b8e5ddd0a703d08eede2bf5f0e657ee958663c`.

# R251 full terminal explicit query events

Status: local proof repair frozen after the first ROOT strict check.
The repaired source has not been compiled.

Source: SourcePruningEnumerationSharedTerminalQueryEvents.lean, 263 lines.
SHA256: c7277b08d9b99752a30bc464eed19e502e111eb8bee623c8224a3a08533096ee
Header and operations: shared-terminal-query-events-header.txt, 99 lines.
Header SHA256: 29ba31695c703da36f628e7fc8adddd5db3d0ae200c9cfc6a8588c56b74e6511

Namespace: MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents.
Public operation: runObserved.
Public law: run_observe_exact.

The observer executes the actual terminal prefix once. It invokes checked
SharedTerminalFoldQueryEvents.foldObserved once at the actual reached fold.
Only a singleton successful fold invokes the private incomingObserved helper.
That helper calls checked SharedIncomingQueryEvents.observe once. It uses
that same full incoming observation for both raw and cached adapter branches.
It attaches the existing pure cache adapter only when a cache is present.

The list order is fold events followed by incoming events. This is the
literal order in SharedCachedTerminal.raw and run. No incoming call occurs
after a stopped fold. The rawFold tail events remain present when an inner
cache adapter returns none. The final cache may remain absent after the
actual incoming operation. The observer retains all branches and endpoints.

The public law retains equality of the entire original cached run result.
It also retains equality of its entire raw projection to the actual raw
operation. The second equality uses checked SharedCachedTerminal.erase.
No independent raw operation is executed by runObserved.

The event bound is the actual successful prefix's recorded.length + 1.
The theorem selects that length through a proof-only match on the same
literal prefix expression. If the prefix result is not a singleton success,
the bound is 1. The actual event list is empty in that case. Empty incoming
also returns an empty event list before the prefix. No count premise is
public. This draft does not identify recorded.length with an original
suspension-list length under arbitrary current states.

Each event retains its actual complete Caller, Queries, operand pair and
native Outcome. The theorem identifies the exact execute call at that
caller's checked state. Raw Core errors, optional none, all native faults,
representative-compressed read Core, waiting state and cache are retained.

Scope: explicit SourceEqualityNativeDemand.execute intersection sites.
Calls inside SharedEnabledEmpty are unchanged and are not counted. This is
not a bound on all native calls, native steps, allocations or arbitrary
consumer work. No full eager C/Q, whole-source completion or lazy default
correspondence claim follows. No Haskell change or defect claim was made.

The original 252-line draft is preserved as the -66a7e50e snapshot.
The first strict failure leaves only the three final incoming result branches.
The repair applies congrArg to the entire incoming result equality before
its final branch match. A local proof-only finalize function preserves the
complete final cached result. The operation and public header are unchanged.

The 263-line -152b9c86 draft and the second failure log are preserved.
The second repair changes only the proof-local finalize function. It now
matches merged.1.1 and uses the exact original projected endpoint fields.
This aligns the congrArg result with the original run match definitionally.
No whole-tuple match remains in that proof-local function.


## shared-incoming-query-events-operations-and-header.txt
SHA256 `1a9e704fd79e20a9ea543deeab7c2a5e0e06c0c4a57bdab97f43cde2eb8d5195`.

import MicroCFTA.SourcePruningEnumerationSharedIncomingNode
import MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents

/-!
# Actual incoming intersection query events

The observer retains every original native, Core and memo endpoint.
It records only the explicit intersection execute site.
The optional enabled worker remains unchanged. Its internal calls are not counted.
The returned Core action executes once on its actual read state.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationIncomingNode (finish)
open SourcePruningEnumerationSharedDispatchQueryEvents (Event)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome
local notation "Observed" => SourcePruningEnumerationSharedEnabledEmpty.Outcome

/-- The full incoming result includes the actual compressed read state. -/
abbrev IncomingResult (EnumGuard : Type) (width : Nat) :=
  (Except (NativeOutcome width Node ⊕ Observed width)
    (Option (List (Except Error (Unit × EnumerationState.State Symbol EnumGuard))))) ×
    Caller width × Queries × EnumerationState.State Symbol EnumGuard

variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

local instance incomingEventsMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Record the actual single query site and retain the full incoming operation. -/
noncomputable def observe
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    IncomingResult EnumGuard width × List (Event width) :=
  match UnionFind.findRoot representativeFuel before.representatives uv with
  | none => ((.ok (some [.error .representativeFuel]), beforeCaller, queries, before), [])
  | some found =>
      let readState : EnumerationState.State Symbol EnumGuard := {before with representatives := found.forest}
      match before.values[found.representative]? with
      | none => ((.ok (some [.error .invalidSlot]), beforeCaller, queries, readState), [])
      | some (.unenumerated oldNode oldScs) =>
          match oldNode with
          | none =>
              match encodeNode incoming with
              | none => ((.ok none, beforeCaller, queries, readState), [])
              | some handle =>
                  ((.ok (some (ExceptT.run (finish found.representative handle incomingScs oldScs incoming readState))),
                    beforeCaller, queries, readState), [])
          | some oldHandle =>
              match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
              | none => ((.ok none, beforeCaller, queries, readState), [])
              | some old =>
                  let actual : NativeOutcome width Node := SourceEqualityNativeDemand.execute nativeFuel
                    (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
                    beforeCaller.checked
                  let event : Event width := (beforeCaller, queries, incoming, old, actual)
                  match actual with
                  | .done query queried =>
                      let phase : Observed width × Queries :=
                        if checkEmpty then
                          SourcePruningEnumerationSharedEnabledEmpty.check p h query queried beforeCaller.fourth queries
                        else (.skipped queried beforeCaller.fourth, queries)
                      let afterCaller : Caller width := SourceCurrentAllocatedPartialState.advance
                        beforeCaller phase.1.state phase.1.memo beforeCaller.merge
                      match phase.1.completed with
                      | some answer =>
                          let replacement : Node := if answer then .empty else query
                          match encodeNode replacement with
                          | none => ((.ok none, afterCaller, phase.2, readState), [event])
                          | some handle =>
                              ((.ok (some (ExceptT.run (finish found.representative handle incomingScs oldScs replacement readState))),
                                afterCaller, phase.2, readState), [event])
                      | none => ((.error (.inr phase.1), afterCaller, phase.2, readState), [event])
                  | other =>
                      ((.error (.inl other), SourceCurrentAllocatedPartialState.advance
                        beforeCaller other.state beforeCaller.fourth beforeCaller.merge, queries, readState), [event])
      | some _ => ((.ok (some [.error .invalidIntersection]), beforeCaller, queries, readState), [])

/-- Exact events preserve the full result and identify the actual incoming query branch. -/
theorem observe_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (uv : Nat) (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := observe checkEmpty representativeFuel nativeFuel p h beforeCaller before uv incoming incomingScs queries
    observed.1 = SourcePruningEnumerationSharedIncomingNode.run
      checkEmpty representativeFuel nativeFuel p h beforeCaller before uv incoming incomingScs queries ∧
    observed.2.length ≤ 1 ∧
    (observed.2.length = 1 ↔ ∃ found oldHandle oldScs old,
      UnionFind.findRoot representativeFuel before.representatives uv = some found ∧
      before.values[found.representative]? = some (.unenumerated (some oldHandle) oldScs) ∧
      lookupNode beforeCaller.checked.native.machine.heap oldHandle = some old) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      start = beforeCaller ∧ saved = queries ∧ left = incoming ∧
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by


## shared-terminal-fold-query-events-header.txt
SHA256 `336d54ddfe0fabf5813b805e8cf1cd08adad48da7524f41dce4b8ab37da97571`.

import MicroCFTA.SourcePruningEnumerationSharedDispatchQueryEvents
import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal

/-!
# Query events through actual terminal folds

The fold keeps the complete original observation and its optional cache.
Events from a raw tail remain present when the cache is unavailable.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedTerminalFoldQueryEvents
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedDispatchQueryEvents (Event)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error (Unit × Core))
variable {width : Nat}
local notation "Fault" => SourceEqualityNativeDemand.Outcome width Node ⊕ SourcePruningEnumerationSharedEnabledEmpty.Outcome width
local notation "Head" => Except Fault (Option Raw) × Caller width × Queries
local notation "RawResult" => Except Fault (Option Raw) × Caller width × Queries × Core
local notation "Adapter" => Except Fault (Option Raw) × Caller width × Queries × Option Cached
local notation "FoldResult" => RawResult × Option Cached
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private noncomputable def rawHeadObserved
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Core)
    (source target : Nat) (queries : Queries) : Head × List (Event width) :=
  let observed := SourcePruningEnumerationSharedDispatchQueryEvents.observe checkEmpty nativeFuel p h caller before source target queries
  (match observed.1 with
    | (.error fault, reached, saved) => (.error fault, reached, saved)
    | (.ok none, reached, saved) => (.ok none, reached, saved)
    | (.ok (some action), reached, saved) => (.ok (some (ExceptT.run (action before))), reached, saved), observed.2)

/-- Retain the actual raw fold and all query events in execution order. -/
noncomputable def rawFoldObserved
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Core) (target : Nat) (queries : Queries) : RawResult × List (Event width) :=
  match sources with
  | [] => ((.ok (some [.ok ((), before)]), caller, queries, before), [])
  | source :: rest =>
      let head := rawHeadObserved checkEmpty nativeFuel p h caller before source target queries
      match head.1 with
      | (.error fault, reached, saved) => ((.error fault, reached, saved, before), head.2)
      | (.ok none, reached, saved) => ((.ok none, reached, saved, before), head.2)
      | (.ok (some raw), reached, saved) =>
          match raw with
          | [.ok ((), after)] =>
              let tail := rawFoldObserved checkEmpty nativeFuel p h rest reached after target saved
              (tail.1, head.2 ++ tail.2)
          | other => ((.ok (some other), reached, saved, before), head.2)

/-- Attach the existing cache adapter to the same executed raw head. -/
noncomputable def cachedAdapterObserved
    (checkEmpty : Bool) (nativeFuel p h : Nat) (caller : Caller width) (before : Cached)
    (source target : Nat) (queries : Queries) : Adapter × List (Event width) :=
  let head := rawHeadObserved checkEmpty nativeFuel p h caller before.core source target queries
  (match head.1 with
    | (.error fault, reached, saved) => (.error fault, reached, saved, none)
    | (.ok none, reached, saved) => (.ok none, reached, saved, none)
    | (.ok (some raw), reached, saved) => (.ok (some raw), reached, saved,
        SourcePruningEnumerationCachedAdapter.adapt reached.checked.native.machine.heap before source target raw), head.2)

/-- Retain cached and raw continuation events at their actual reached endpoints. -/
noncomputable def foldObserved
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries) : FoldResult × List (Event width) :=
  match sources with
  | [] => (((.ok (some [.ok ((), before.core)]), caller, queries, before.core), some before), [])
  | source :: rest =>
      let head := cachedAdapterObserved checkEmpty nativeFuel p h caller before source target queries
      match head.1 with
      | (.error fault, reached, saved, _) => (((.error fault, reached, saved, before.core), none), head.2)
      | (.ok none, reached, saved, _) => (((.ok none, reached, saved, before.core), none), head.2)
      | (.ok (some raw), reached, saved, cache) =>
          match raw with
          | [.ok ((), core)] =>
              match cache with
              | none =>
                  let tail := rawFoldObserved checkEmpty nativeFuel p h rest reached core target saved
                  ((tail.1, none), head.2 ++ tail.2)
              | some recovered =>
                  let tail := foldObserved checkEmpty nativeFuel p h rest reached
                    (EnumerationExpandableIndex.frame core recovered) target saved
                  (tail.1, head.2 ++ tail.2)
          | other => (((.ok (some other), reached, saved, before.core), cache), head.2)

/-- The complete old fold and its ordered actual query events share one execution. -/
theorem fold_observe_exact
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (caller : Caller width) (before : Cached) (target : Nat) (queries : Queries) :
    let observed := foldObserved checkEmpty nativeFuel p h sources caller before target queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.fold checkEmpty nativeFuel p h sources caller before target queries ∧
    observed.2.length ≤ sources.length ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by


## shared-terminal-query-events-header.txt
SHA256 `29ba31695c703da36f628e7fc8adddd5db3d0ae200c9cfc6a8588c56b74e6511`.

import MicroCFTA.SourcePruningEnumerationSharedTerminalFoldQueryEvents
import MicroCFTA.SourcePruningEnumerationSharedIncomingQueryEvents

/-!
# Ordered explicit query events in the actual shared terminal operation

The fold executes before the incoming merge. The observer retains both
complete cached and raw observations. It counts explicit intersection calls.
It does not count internal calls in the enabled empty worker.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedDispatchQueryEvents (Event)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Waiting" => EnumerationWaitingIndex.Waiting
local notation "Raw" => List (Except Error (Unit × Core))
local notation "PrefixRaw" => List (Except Error ((List Nat × Nat × Waiting) × Core))
local notation "TerminalRaw" => List (Except Error (Fragments.Fragment Symbol × Core))
variable {width : Nat}
local notation "Fault" => SourceEqualityNativeDemand.Outcome width Node ⊕ SourcePruningEnumerationSharedEnabledEmpty.Outcome width
local notation "Incoming" => Except Fault (Option Raw) × Caller width × Queries × Core
local notation "Terminal" => Except (PrefixRaw ⊕ (Fault ⊕ Raw)) (Option TerminalRaw) × Caller width × Queries × Core × Waiting
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private noncomputable def incomingObserved
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (cache : Option Cached) (caller : Caller width) (before : Core) (target : Nat)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    (Incoming × Option Cached) × List (Event width) :=
  let observed := SourcePruningEnumerationSharedIncomingQueryEvents.observe
    checkEmpty representativeFuel nativeFuel p h caller before target incoming incomingScs queries
  ((observed.1, match cache with
    | none => none
    | some recovered =>
        match observed.1 with
        | (.ok (some raw), reached, _, read) =>
            SourcePruningEnumerationIncomingCacheAdapter.adapt reached.checked.native.machine.heap
              indexFuel target incomingScs (EnumerationExpandableIndex.frame before recovered) read raw
        | _ => none), observed.2)

/-- Retain every original terminal result and its ordered explicit query events. -/
noncomputable def runObserved
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    (Terminal × Option Cached) × List (Event width) :=
  if incoming = .empty then
    (((.ok (some []), caller, queries, before.core, before.waiting), some before), [])
  else
    match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run representativeFuel first rest before.waiting before.core) with
    | [.ok ((recorded, winner, moved), joined)] =>
        let fold := SourcePruningEnumerationSharedTerminalFoldQueryEvents.foldObserved
          checkEmpty nativeFuel p h recorded caller ⟨joined, before.expandable, moved⟩ winner queries
        match fold.1 with
        | ((.error fault, reached, saved, outer), _) =>
            (((.error (.inr (.inl fault)), reached, saved, outer, moved), none), fold.2)
        | ((.ok none, reached, saved, outer), _) =>
            (((.ok none, reached, saved, outer, moved), none), fold.2)
        | ((.ok (some raw), reached, saved, outer), cache) =>
            match raw with
            | [] => (((.ok (some []), reached, saved, outer, moved), cache), fold.2)
            | [.ok ((), folded)] =>
                let merged := incomingObserved checkEmpty representativeFuel nativeFuel p h indexFuel
                  cache reached folded winner incoming incomingScs saved
                match merged.1 with
                | ((.error fault, last, finalQueries, read), _) =>
                    (((.error (.inr (.inl fault)), last, finalQueries, read, moved), none), fold.2 ++ merged.2)
                | ((.ok none, last, finalQueries, read), _) =>
                    (((.ok none, last, finalQueries, read, moved), none), fold.2 ++ merged.2)
                | ((.ok (some rows), last, finalQueries, read), finalCache) =>
                    (((.ok (some (rows.map fun row => match row with
                      | .error fault => .error fault
                      | .ok result => .ok (.hole winner, result.2))), last, finalQueries, read, moved), finalCache), fold.2 ++ merged.2)
            | stopped => (((.error (.inr (.inr stopped)), reached, saved, outer, moved), none), fold.2)
    | stopped => (((.error (.inl stopped), caller, queries, before.core, before.waiting), none), [])

/-- The complete cached and raw results retain the same ordered actual calls. -/
theorem run_observe_exact
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    let observed := runObserved checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries
    observed.1 = SourcePruningEnumerationSharedCachedTerminal.run
      checkEmpty representativeFuel nativeFuel p h indexFuel first rest caller before incoming incomingScs queries ∧
    observed.1.1 = SourcePruningEnumerationSharedCachedTerminal.raw
      checkEmpty representativeFuel nativeFuel p h first rest before.waiting caller before.core incoming incomingScs queries ∧
    observed.2.length ≤ (match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      representativeFuel first rest before.waiting before.core) with
      | [.ok ((recorded, _, _), _)] => recorded.length + 1
      | _ => 1) ∧
    ∀ start saved left right actual, (start, saved, left, right, actual) ∈ observed.2 →
      actual = SourceEqualityNativeDemand.execute nativeFuel
        (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain left right)) start.checked := by


## actual-program-guard-scope-next.md
SHA256 `08aa977db1d35736097cea6a3762909b743292be7ab7c8cd5e0d066746b4f639`.

# Actual Program-child suspended guard scope

Frozen read-only audit, 2026-11-12 19:33 CET. No new semantic reader is needed.
The missing cut is an indexed composition of existing guard/normalizer/trie observers.
Use fixed current Symbol and literal, with the explicit LabelProgramBuildRoles import.
Program-child roles are row OCCURRENCES, not a global classification of native values.

Proposed ONE public observer, using existing aliases and no new role judgment:
```lean
theorem program_child_scope
    (valid : Constraint → Prop) (edge : EdgeValue Symbol Constraint)
    (fields : SourceSynthesisHereditaryProgramFields.EdgeFields valid literal edge)
    (scs : List EnumerationState.Suspended) (start : Nat)
    (inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (index : Nat) (incoming : Node) (bucket : List EnumerationState.Suspended)
    (selected : (SourcePruningEnumerationEdgeInputs.children edge scs start tries)[index]? =
      some (incoming, bucket))
    (programIndex :
      (edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
      (edge.entry.key.symbol = literal "filter" ∧ index = 1)) :
    SourceSynthesisHereditaryProgramFields.ValueFields valid literal incoming ∧
      EnumerationState.descendScs index scs = [] ∧
      bucket = EnumerationState.descendScs index (EnumerationCorrectness.suspendedVars start tries) ∧
      ∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail
```
The inherited condition is the CURRENT Program-slot invariant. It does not constrain future slots.
projected and selected observe the SAME actual prefix receipt and its indexed EdgeInputs list.
They do not supply future projection, readback, scope, model, or worker success.
Instantiate valid with the current source Origin predicate and start with the actual pre-prefix counter.
The result feeds ProgramChildSlots.program_child_slot at the actual child bucket.

Exact decomposition of the proof:
1. EdgeInputs.children:15 is zipIdx followed by a map. getElem?_map/getElem?_zipIdx identify
   the same native child and bucket = descend(index,inherited) ++ descend(index,suspendedVars).
   EdgeChildLanguage:78-89 already uses this exact indexed inversion.
2. Case on FULL EdgeFields, retaining the actual fixed guard and complete child list.
   An annotated row has length one and cannot supply a selected Program index.
   Application permits indices 2/3; filter permits index 1. Full current literal labels distinguish
   app/filter. Component names may collide with either string; exact arity handles that case.
   The same case supplies ValueFields for the ACTUAL selected child.
3. Derive cached own equalities: top_cached for the annotated case; for eqGuard rewrite
   eqGuard_eq_source and use SourceEqualityGuardReadback.normalize_cached on its literal classes.
   Do not call CurrentGuardPreparation's private eqGuard_cached by a mangled name.
4. Constraint.project_complete:21, reduced at its actual sourceEqualities result, identifies
   tries=readClasses classes, validity, and each classTrie's EXACT represented paths.
   List.mem_map then transports every own trie path to members of the actual source classes.
   No satisfying term or independent readback catalog enters this step.
5. For fixed app/filter guards, use GuardRegions.application_guard_endpoints:133 and
   filter_guard_endpoints:144. These already include normalization/right-extension preservation.
   Rewrite the SAME EdgeFields guard. These public constant-layout laws need no old root equality.
6. Descend actual own scopes with application_descend_function:75 / argument:80 /
   filter_descend_program:85. Their result is annotationRegion, equivalently 0::tail.
   EqualityTrie.descendScs_exact:628 retains each actual sc.var and its original path provenance.
7. Every Program index is nonzero. An inherited path already starts with zero, so it has no path
   starting at that selected index. descend_valid plus empty_exact/valid_has_path establishes
   that every descended inherited trie is structurally empty and filtered out by descendScs.
   Hence the actual Program-child bucket contains ONLY fresh own-class descents, as returned above.
8. Validity needs no new proof: OrdinarySemanticGates.children_valid:104 combines inherited
   validity with projected trie validity; EnumerationSemantics.descend_valid:369 also suffices.

Existing model-free PathTransport.descended_path_original:32 can replace the forward direction
of Trie.descend_exact without a validity premise. Keep validity separately for canonicality.
Do NOT instantiate PathTransport.prepare_paths with annotationRegion for all child indices:
annotationRegion is NOT closed under arbitrary leading-index deletion. Deleting zero can reach
an arbitrary Type path. Its generic BucketPaths.descend requires exactly that false closure.
The new indexed observer uses distinct parent/child predicates, and only actual Program indices.

Do not weaken FULL EdgeFields to ProgramEdge.guard_regions' untagged three-way disjunction.
That result forgets which region belongs to the selected row. At app child1, applicationRegion
allows the marker root; it cannot be treated as a filter Program child's annotation region.
Use the case, full literal label, child lookup, and exact arity together.
App's raw own paths enter Program children as 2::0::tail or 3::0::tail; filter uses 1::0::tail.
Inherited Program-slot paths are instead 0::tail at the PARENT. Their selected descents are empty.
Do not require the Program child's whole bucket to be empty: fresh own equalities can remain.

Remaining ProgramSlots obligations are separate from this pure scope cut:
- Derive current EdgeFields from the SAME native selected row/readback, not meaning alone.
- Keep the strict ValueFields root and source layouts through actual preparation/dispatch/storage.
- Relate fresh own equality IDs and later Program-child allocation IDs by actual counter bounds.
- Preserve IncomingAvoid for every marked Program root through Type-terminal UF unions.
- Preserve fragment occurrence roles and raw-UVar class membership through callback/compression.
The theorem creates no global role history, completion, decoder Projection, or termination result.

Other reused references: HereditaryProgramFields:24/31/51; GuardRegions.annotationRegion:19;
EnumerationEquality.classTrie/readClasses:17/21; EqualityTrie.nil_mem:93 and descend_valid:432;
EqualityTrie.empty_exact:421; EnumerationCorrectness.suspendedVars:412;
EnumerationCPSDescent.suspendedVars_valid:249; CachedOwn.prepare_inputs in OwnInputShape:32.
Guard preparation and trie readback are reused; no second guard engine or native producer is needed.
No compiler, repository edits, Git, Haskell, root documentation, or evidence changes.


## current-enumerated-role-invariant-next.md
SHA256 `fc761fc2a3a178a442f0bda38516d3ade54bceab501bbf806f1c95b544cd0b5e`.

# Current enumerated Program roles

Read-only audit, 2026-11-12 19:11 CET. No implementation or defect claim.
The target is noStop rendering. Future atTypes stopping is a separate extension.

Existing source-derived starting facts:
CurrentComputedWidthSharedCompletion.accepted returns SAME result/readback and
ValueFields (Origin (encodedLibrary lib)) literal result at the completed heap.
HereditaryProgramFields.ValueFields:24 is empty or ordinary, recursively at all
Program children. EdgeFields:32 records the complete guard and ordered 1/4/2 layout.
ValueFields.roles:51 and fields:90 derive ProgramValue and annotation fields.
ProgramBuildRolesGeneric.ProgramValue:99 permits unions; strict ValueFields does not.
Use the stronger returned ValueFields, not an assumed generic ProgramValue closure.

SelectedPreparation.complete:55 retains the raw slot/store, lookup and full context.
It does not attach a Program role to that UVar. Its language equivalence alone does
not imply structural fields. SelectedValue.run:20, however, is the IDENTITY on
empty/ordinary values. Thus actual selected preparation of a ValueFields value
returns that SAME value and heap. This is a direct case proof, not a new supplier.

RecursivePacket.Packet:21 retains context/safety/references/indexes/order/template bounds.
GraphReferences.ReferencesCarry:39 gives graph carriers, not occurrence roles.
Carriers.CarriesGraph:23 permits either restricted pending or completed slots.
RecordTypes.recordTypes_metadata:89 proves the raw metadata update, not its role
correctness. recordTypes_frame:106 does retain the complete compression frame.
None of these results alone excludes a Program-position Mu or raw hole.

One necessary new proof predicate: ProgramSlots valid literal heap core P.
P : Nat -> Prop marks actual Program UVar OCCURRENCES. It is a proof-only set.
Do not classify native values globally and do not add a typing judgment.
For each P u, require u<counter, IsRoot core.representatives u, and:
- IncomingAvoid u core. No stored suspended reference targets u's class.
- Its stored value is either an enumerated Program fragment or a restricted
  pending slot with the ACTUAL native lookup and ValueFields certificate.
- For a pending Program slot, every suspended trie is Valid and every represented
  path has shape 0::tail. Do not require its bucket=[]: function/argument slots
  can carry constraints descending into their first Type child.
An enumerated Program fragment uses existing Fragment syntax: a hole must name P;
an annotated leaf has one arbitrary Type child; app has four children with its
two Program children certified recursively; filter has its candidate certified.
Retain full literal layouts. A component can itself be named app or filter.
No complete term, Projection, model or source acceptance is a predicate premise.

Initialization derives P={0} from SAME returned root lookup and bucket=[].
The existing initial_packet result supplies the exact store and slot indexes.
ProgramSlots is NOT the existing metadata.types or a set of native handles.
It must be extended at actual fresh Program-child allocations.

Smallest operational cut: add the Program-child receipt at the existing shallow
child boundary, then use it in actual ChildDispatch, not a replacement evaluator.
Here is a precise minimal raw-action lemma; symbols/guards use the current aliases:

```lean
theorem program_child_slot
    (incoming : Node) (scs : List Suspended)
    (fields : ValueFields valid literal incoming)
    (scoped : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (before after : Core) (action : EnumerateM Symbol Constraint (Fragment Symbol))
    (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    ∃ handle, encodeNode incoming = some handle ∧ fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter
          (.unenumerated (some handle) scs)}
```

Empty input has no success. Ordinary input gives the exact fresh raw slot.
Trie.nil_mem:93 derives nonterminal from scoped. No terminal union runs at this
Program-child route. ShallowChild.prepareChild_complete:38 already records this
exact node-branch state. ChildDispatch.nonterminal_complete:167 retains all actual
cached indexes and uses the same raw action, so add the receipt to that result.
This cut does not yet prove the whole ProgramSlots history invariant.

To derive scoped at each actual Program child, use actual EdgeInputs.children:15,
the EdgeFields fixed guard, Constraint.project_complete:21 and Trie.descend_exact:133.
For app, source classes reach children2/3 only below their annotation child0.
For filter, candidate child1 is reached only below child0. Inherited Program-slot
paths begin0 and cannot descend to its own app/filter Program children at2/3/1.
Annotated rows have no Program children. Type-field children remain unrestricted.
Existing ActualSharedSelectedProgramFootprints proves analogous native class-edit
facts, but is not already a proof for enumeration suspended tries and UVar updates.

The UF boundary is TYPE-child terminal dispatch, not selected-value normalization.
Maintain IncomingAvoid for every marked Program slot and avoidance for transient
child buckets. TraversalCompletion.complete_with_fragments:32 supplies protected
old roots when incoming buckets avoid them; References.descend_allowed:25,
fresh_separate:324 and incoming_read:372 provide existing transport components.
TerminalPrefix.run_complete:46 identifies the merged winners from sc.var roots.
These references must avoid every P slot. Then terminal unions cannot absorb a
Program slot, and its stored fields and class remain unchanged.
The callback preserves this invariant through recordTypes_frame, independently
of the classification accuracy of the updated metadata.types.

At noStop finished, NativeIndex.candidate:17 makes every pending marked ordinary
value expandable. Actual next(fun _=>none)=done plus index validity excludes them.
The stored fragment invariant and dependency order then give a concrete Program
skeleton through the actual partial renderer. Gamma owns the pure decoder step.
This proves Program projection, not a ground Type completion or ordinary typing.
Native Value identity/handle and UVar identity are different namespaces, both Nat.
The same native value can occur at distinct Type and Program slots. Equal numeric
IDs, shared native readback, or metadata membership alone prove no role collision.
Before atTypes soundness, separately prove its raw metadata classification survives
UF representative changes. Do not infer that result from the noStop invariant.


## program-fragment-readback-next.md
SHA256 `d4e2054aca778ba4b364ea07a5530dce32cb8b887d6b7976fa61e13bccb2cbee`.

# Program projection of the actual default readback

Read-only audit, 2026-11-12 19:39 CET. No new source or runtime claim.
The remaining structural gap is slot-role preservation, not an absent rank theorem.

Existing actual readback:
SharedPreparedMarkerOutput.OutputResources.default_finished_render_partial_models:136
runs agreement once on the SAME output, keeps literal Mu rendering, tagged root,
ordered residuals and their separate complete compression endpoints. It returns
term = openProgram true partialRoot and the actual rootPartial success at rootAfter.
It retains Packet/Stratified at all endpoints. Its model observer is conditional;
do not use that observer to assume an assignment, completion or Projection.
DefaultPartialAgreement.default_finished_render_partial:296 already gives agreement.
PartialOutput.rootPartial_complete:159 gives the actual finite readback from Safe,
Stratified and root allocation. No ground Type completion is required.

Minimal independent new cut: exclude an actual pending Program slot at noStop done.
Use current standard aliases Symbol/Constraint/Core/Node and implicit parameters
formulas/solver/inventory/caller/memos/metadata/before/valid/literal below.
All heap occurrences denote caller.checked.native.machine.heap. This is one actual
lookup identity, not an assumed future source acceptance or final projection.

```lean
theorem no_pending_program_slot
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (uv handle : Nat) (scs : List EnumerationState.Suspended) (value : Node)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : SourcePruningEnumerationNodes.lookupNode
      caller.checked.native.machine.heap handle = some value)
    (fields : SourceSynthesisHereditaryProgramFields.ValueFields valid literal value) :
    False
```

Proof requires no new datatype. Reuse the small flags_false argument, currently
private at DefaultFinishedRendering:40 and DefaultPartialAgreement:245. Derive
uv<counter from packet.safe.1.aligned and stored. packet.valid supplies the actual
NativeIndex.candidate correspondence; finished makes its slot flag false.
ValueFields:24 has only empty/node, so recursiveBoundary value=false. NativeIndex
candidate:17 is therefore some true for this actual pending handle and ANY bucket.
This contradicts the actual false flag. No metadata.types premise is involved.
This cut does not show that all later Program slots still have ValueFields.

The required history invariant has separate, inspectable parts:
1. Mark RAW Program UVar occurrences P, including0, not native handles. Retain live
   roots and their actual native readbacks with ValueFields while pending.
2. Pending Program buckets have Valid annotation-only paths. IncomingAvoid and
   transient bucket avoidance keep Type-child UF unions away from marked roots.
   SelectedProgramChildRetention.input_fields:63 and prepared_fields:91 retain
   complete fields and SAME selected value. ProgramChildSlots.program_child_slot:22
   records the exact actual raw allocation/write. Gamma owns guard-to-bucket scope.
3. Stored enumerated Program fragments have literal annotated-leaf/app/filter
   arities1/4/2. At each app/function/argument or filter/candidate position, holes
   refer only to P, and nested concrete fragments obey these same layouts.
   Type subtrees remain unrestricted. Do not classify by symbol name alone.
4. Retain the existing allocation bounds, Safe, ReferencesCarry and indexed flags.
   A raw hole whose class was eliminated or replaced is not covered by fields alone.
   UF protection must connect the mark to its actual live representative/store.

Once those history facts are derived, the new exclusion law makes every marked
slot enumerated at finished. GetValue/rootFragment read their SAME stored fragments.
EnumerationCompressionFrame.Frame:20 keeps values, counter and exact root paths.
EnumerationObservations.rootPartial_frame:22 / expandPartial_frame:20 retain those
facts across annotation reads and all ordered child reads. Program roles therefore
transport through compression without a new model argument.

The next structural observer can then induct on the ACTUAL successful renderer's
fuel, mutually over fragment/list syntax. Zero fuel has no success. A Program hole
reads an enumerated marked fragment; a concrete node preserves its exact arity.
Application's first two Type children need no Projection; use the actual ordered
mapM readback for its last two Program children. Filter needs only its candidate.
This derives exists program, Projection literal Prod.fst
(openProgram true partialRoot) program. Projection.toProgram_eq:61 gives the SAME
decoder. Transfer through the returned term=openProgram equality, not a second run.
PartialProgramDecoder.completion_decoder_of_projection:99 can subsequently reuse
that SAME Program for every completion; it supplies no completion existence.

Rank and cycles:
EnumerationOrder.Stratified:18 already makes levels constant on UF classes and
strictly increase along EVERY hole of every stored enumerated fragment. The pending
frontier bounds those levels. Packet.ordered retains this for the actual state.
EnumerationPartialCompletion.expandPartial_complete:60 and the native wrapper use
this rank to construct finite readback fuel. A cycle of enumerated Program slots
would contradict strict level increase, independently of native Type Mu boundaries.
A conditional observer of an already successful readback needs only fuel induction;
it does not need another native-height or acyclicity premise.

MergedOrdinaryHeight.child_lt:50 bounds actual ordinary native child values. It does
not yet attach those heights to every later UVar or enumerated fragment dependency.
Likewise the fresh raw before.counter returned by ProgramChildSlots does not alone
prove that later UF representatives retain parent<child order. Alignment, mark
extension and UF protection are still necessary. With those additional receipts,
counter order or native height could give another Program-only rank, but neither
bridge is already the complete role-history theorem. Reuse existing Stratified.

noStop done alone permits opaque pending Type Mu/union values and arbitrary cyclic
malformed fragment stores. Actual Packet/Stratified rules out the latter; the new
role-history facts must exclude the former at Program positions. This structural
projection claim is separate from ordinary typing, residual guard truth, default
pipeline correspondence and any termination, weighted Room or graph-work bound.


## Current strongest claim and remaining scope

The previously checked SourceSynthesisCurrentComputedWidthExactProgramLanguage
accepted_exact theorem retains the entire same computed-width initializer and
pruning run. With no avoid rules, its returned native node accepts exactly
eligible Programs with original query coverage and the requested component count.
The width is a mathematical input-derived value. It is not a fixed host bound.

The new decoder lemma does not derive the Program shape of an actual final
partial readback. Marked raw Program slots must retain native fields, valid
annotation-only suspended paths and literal fragment layouts through all actual
child, callback and UF updates. Type-slot metadata is not a native node ID.
Existing Stratified facts handle the readback rank. No new rank gate is needed.

Complete eager query counts, original-input total work, default Mu rendering,
reduce/refold, projected output order and duplicate handling, both rank/unrank
inverse laws and native Haskell/FFI correspondence remain separate obligations.
No production Haskell repair is made here. The existing external Liquid duplicate
name/refinement defect remains recorded in root FINDINGS.md. Main and the board
were refreshed at 19:30 CET; no newer repair was present then.
