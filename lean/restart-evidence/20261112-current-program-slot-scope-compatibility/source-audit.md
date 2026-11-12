# Actual Program slot roles and state preservation
Generated 2026-11-12T20:18:00.956975+01:00.

Base `19a6bca9f2cb903b6810900d0746586924fb760e`. Current main `e53852064d3ef5a2eafec47d754c27504b11de5f`.

Nine strict-checked modules. All previous proof content remains.

## SourceSynthesisProgramEnumerationRoles
SHA256 `e31274ac2cb247cb8d20267c4253ecaf1de8520886ed8f003b267d59bd3f5c84`. Lines 87.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramEnumerationRoles.initial_program_slots": [
    "propext",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem initial_program_slots
    (heap : NativeHeap) (handle : Nat) (value : Node)
    (decoded : lookupNode heap handle = some value)
    (fields : ValueFields valid literal value) :
    ProgramSlots valid literal heap (EnumerationState.initial handle) (fun uv => uv = 0) := by
```

Full role definitions and frozen initial header:

```lean
import MicroCFTA.SourceSynthesisHereditaryProgramFields
import MicroCFTA.SourceSynthesisGuardRegions
import MicroCFTA.SourcePruningEnumerationPathTransport
import MicroCFTA.EnumerationReferences

/-!
# Program roles in raw enumeration slots

The predicates refer to the existing Fragment syntax and raw UVar slots.
Type children remain unrestricted. Native handles do not determine Program roles.
Safety and fragment dependency levels remain in the existing execution Packet.
-/
namespace MicroCFTA.SourceSynthesisProgramEnumerationRoles
open Fragments EnumerationState EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceSynthesisHereditaryProgramFields (ValueFields)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint

/-- Program positions retain their literal layouts or a marked raw occurrence. -/
inductive FragmentRoles (literal : String → Symbol) (marked : Nat → Prop) : Fragment Symbol → Prop where
  | hole (uv : Nat) (known : marked uv) : FragmentRoles literal marked (.hole uv)
  | component (symbol : Symbol) (annotation : Fragment Symbol) :
      FragmentRoles literal marked (.node symbol [annotation])
  | application (annotation marker function argument : Fragment Symbol)
      (first : FragmentRoles literal marked function)
      (second : FragmentRoles literal marked argument) :
      FragmentRoles literal marked (.node (literal "app") [annotation, marker, function, argument])
  | filter (goal candidates : Fragment Symbol) (body : FragmentRoles literal marked candidates) :
      FragmentRoles literal marked (.node (literal "filter") [goal, candidates])

/-- A stored Program payload has actual native fields or an enumerated Program fragment. -/
inductive SlotRole (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (marked : Nat → Prop) : UVarValue Symbol → Prop where
  | pending (handle : Nat) (scs : List Suspended) (value : Node)
      (decoded : lookupNode heap handle = some value) (fields : ValueFields valid literal value)
      (validTries : EnumerationSemantics.ValidSuspended scs)
      (annotationPaths : SourcePruningEnumerationPathTransport.BucketPaths
        SourceSynthesisGuardRegions.annotationRegion scs) :
      SlotRole valid literal heap marked (.unenumerated (some handle) scs)
  | enumerated (fragment : Fragment Symbol) (roles : FragmentRoles literal marked fragment) :
      SlotRole valid literal heap marked (.enumerated fragment)

/-- Marked raw occurrences remain live roots with protected references and actual payloads. -/
structure ProgramSlots (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (state : Core) (marked : Nat → Prop) : Prop where
  /-- Each marked raw occurrence belongs to the allocated slot domain. -/
  bounded : ∀ uv, marked uv → uv < state.counter
  /-- Each marked raw occurrence remains its own representative. -/
  roots : ∀ uv, marked uv → IsRoot state.representatives uv
  /-- Stored equality references avoid every marked Program class. -/
  incoming : ∀ uv, marked uv → EnumerationReferences.IncomingAvoid uv state
  /-- The exact raw slot contains a permitted Program payload. -/
  stored : ∀ uv, marked uv → ∃ payload,
    state.values[uv]? = some payload ∧ SlotRole valid literal heap marked payload

variable {valid : Constraint → Prop} {literal : String → Symbol}

/-- Literal raw initialization marks slot zero with its same native Program readback. -/
theorem initial_program_slots
    (heap : NativeHeap) (handle : Nat) (value : Node)
    (decoded : lookupNode heap handle = some value)
    (fields : ValueFields valid literal value) :
    ProgramSlots valid literal heap (EnumerationState.initial handle) (fun uv => uv = 0) := by
```

## SourceSynthesisProgramChildScope
SHA256 `fc1b69e72d00934808a25f7c60c90e1b4b0de576266a0285f906c450a924268d`. Lines 199.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramChildScope.program_child_scope": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

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
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
```

## SourceSynthesisProgramChildSources
SHA256 `4f15b84d6d39d7107485fe80cd365db649e05c563acfae882dec8729ef0b390a`. Lines 52.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramChildSources.program_child_sources": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem program_child_sources
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
    (SourceSynthesisHereditaryProgramFields.ValueFields valid literal incoming ∧
      EnumerationState.descendScs index scs = [] ∧
      bucket = EnumerationState.descendScs index (EnumerationCorrectness.suspendedVars start tries) ∧
      ∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) ∧
      ∀ sc ∈ bucket, start ≤ sc.var ∧ sc.var < start + tries.length := by
```

## SourceSynthesisNoPendingProgramSlot
SHA256 `e0c74dad6d2247822a90042c069c2ee46e60e2f2bb6bee19e42396a6a4325846`. Lines 74.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisNoPendingProgramSlot.no_pending_program_slot": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

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
    False := by
```

## SourcePruningEnumerationSharedTerminalQueryCount
SHA256 `b40af81ae3ed583748f73cf798ee9c29507f178cba4b7b5d732b6f6612af0fd6`. Lines 109.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourcePruningEnumerationSharedTerminalQueryCount.run_query_count": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem run_query_count
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    (SourcePruningEnumerationSharedTerminalQueryEvents.runObserved checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest caller before incoming incomingScs queries).2.length ≤ rest.length + 2 := by
```

## SourceSynthesisProgramChildRoleStep
SHA256 `18d26263fedb27276db68bef70f086086a88b035493f25accb42ba18178d3afd`. Lines 128.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramChildRoleStep.program_child_role_step": [
    "propext",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem program_child_role_step
    (heap : NativeHeap) (incoming : Node) (scs : List Suspended)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap incoming) (closed : incoming.free = [])
    (fields : ValueFields valid literal incoming)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (before after : Core) (marked : Nat → Prop)
    (safe : Safe before) (roles : ProgramSlots valid literal heap before marked)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv scs)
    (action : EnumerateM Symbol Constraint (Fragment Symbol)) (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    ∃ handle, encodeNode incoming = some handle ∧ lookupNode heap handle = some incoming ∧
      fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)} ∧
      Safe after ∧ ProgramSlots valid literal heap after (fun uv => marked uv ∨ uv = before.counter) := by
```

## SourceSynthesisProgramFragmentWrite
SHA256 `2966bc452ff7c67d284ce8a16ffe2c54d4fb3f6e82565b3475fd4fadf72992a0`. Lines 54.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramFragmentWrite.setValue_program_slots": [
    "propext",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem setValue_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (uv : Nat) (selected : marked uv) (fragment : Fragment Symbol)
    (roles : FragmentRoles literal marked fragment)
    (written : Success (EnumerationState.setValue uv (.enumerated fragment)) before () after) :
    after = {before with values := before.values.set uv (.enumerated fragment)} ∧
      ProgramSlots valid literal heap after marked := by
```

## SourceSynthesisProgramRolesCompression
SHA256 `79fc01254535c7d81404f2c23a770bb87d85661bba11d9509ad86e25c2e02f76`. Lines 39.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramRolesCompression.compression_frame_program_slots": [
    "propext",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem compression_frame_program_slots
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (frame : EnumerationCompressionFrame.Frame before after)
    (roles : ProgramSlots valid literal heap before marked) :
    ProgramSlots valid literal heap after marked := by
```

## SourceSynthesisProgramRolesNativeHeap
SHA256 `8c000af36968107b4d31ead1a747110a9a0e757fe03918de82371e24e814527e`. Lines 37.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramRolesNativeHeap.keeps_program_slots": [
    "propext",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem keeps_program_slots
    (beforeHeap afterHeap : NativeHeap) (state : Core) (marked : Nat → Prop)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap)
    (roles : ProgramSlots valid literal beforeHeap state marked) :
    ProgramSlots valid literal afterHeap state marked := by
```

## no-pending-program-slot-note.md
SHA256 `e730849d15a384f9410c0a106aa80f0c59aec47be301f6968bc615c015dc64ea`.

# No pending Program slot at noStop completion

Header frozen before proof, 2026-11-12 19:44 CET.
The public law uses the exact header from the 101-line readback audit.
Current standard aliases and implicit Packet parameters apply.

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

No additional nonempty, scope, metadata.types, model, rank or Projection premise.
The Packet and native lookup refer to the SAME caller heap and cached state.
This law is a single-slot exclusion. It does not derive roles for every later slot.
Frozen source: SourceSynthesisNoPendingProgramSlot.lean, 74 lines.
SHA256: e0c74dad6d2247822a90042c069c2ee46e60e2f2bb6bee19e42396a6a4325846.
Status: runtime draft. ROOT must run the strict check.
One public law: no_pending_program_slot, line 52. Imports are RecursivePacket
and HereditaryProgramFields. A mechanical byte check confirms that the entire
public header equals the header frozen above before proof construction.

No public flags_false observer was found in the existing selection/index modules.
The local private flags_false proof follows the checked DefaultFinishedRendering
proof. It retains the actual noStop next call and maintained candidate flags.
The public proof derives uv<counter from actual store membership and Safe alignment.
Packet.valid supplies candidate coherence at that SAME slot and caller heap.
ValueFields makes recursiveBoundary false in both possible cases, including Empty.
The actual pending candidate is therefore true for any bucket, contradicting done.

The module does not construct a model, rank, completion or Program-slot history.
It does not classify metadata.types, force a nonempty Program, or restrict names.
No compiler, repository, Git, Haskell or evidence operation was performed.


## program-child-role-step-note.md
SHA256 `98ee3c31b69b8230f13865752e2c8d5b74e692b55fa1c204c6c842e9a20fe271`.

# R252 Program child role step

Status: one local proof repair frozen after ROOT first strict check.
The repaired source has not been compiled.

Source: SourceSynthesisProgramChildRoleStep.lean, 128 lines.
SHA256: 18d26263fedb27276db68bef70f086086a88b035493f25accb42ba18178d3afd
Public header: program-child-role-step-header.txt, 44 lines.
Header SHA256: 471bd445d26338ed3639ab7afc9f566ba03fc81e257286bb4a4bbcdba9ca4f34

Namespace: MicroCFTA.SourceSynthesisProgramChildRoleStep.
Public law: program_child_role_step.
No operation, observer or public invariant type is added.

Current inputs: coherent native heap; available closed incoming native value;
ValueFields for that value; valid annotation-only child bucket; Safe before;
ProgramSlots for the old marked roots; current bucket reference bounds; bucket
Avoids for every old marked root; the actual prepareChild result and Success.
These inputs describe the current allocation event. No post-state role,
completion, model, projection, rank or future heap property is supplied.

The theorem retains the same encoded and decoded native handle, actual
fresh-hole fragment, exact complete written Core state and Safe after.
It proves ProgramSlots after for exactly marked uv or uv = before.counter.
The action is the existing prepareChild action from the same actual Success.
No second producer is used. The native heap does not change in this Core action.

The proof reuses checked program_child_slot for the exact raw slot update.
It uses ChildEffects.child for safety and protection of every old live root.
The existing allocation_allowed and setValue_allowed laws preserve each old
IncomingAvoid predicate. allocated_isolated derives fresh-root isolation from
current storage bounds. outside_class and current bucket bounds exclude that
fresh root from the written bucket. No fresh-root avoidance input is added.

Private fragment and slot monotonicity proofs extend old role certificates
to the larger mark predicate. The fresh payload uses the same incoming native
readback and the actual valid annotation-only bucket. Native identity alone
does not classify a Program role. Unrestricted Type fields remain unrestricted.

Scope: one successful shallow Program-child allocation event. Empty incoming
has no successful action and is excluded by the checked event law. This does
not establish terminal merge, Program root expansion, Type-child events or
global role history. It does not add a Packet wrapper or a cache role theorem.
No Haskell change or defect claim was made.

The original 127-line source is preserved as the -95bc4e3e snapshot.
The first strict check has one error in representative projection elaboration.
The repair first infers congrArg from the full actual state equality. It then
checks that inferred projected equality against the forest preservation goal.
The public header and all conclusions remain byte-identical.


## program-child-scope-note.md
SHA256 `ef12d7e190a6c98640be2b4f3d43fe49db1faeec0f720f63505a13c0c684864c`.

# Actual Program-child guard scope

Frozen source: SourceSynthesisProgramChildScope.lean, 199 lines.
SHA256: fc1b69e72d00934808a25f7c60c90e1b4b0de576266a0285f906c450a924268d
Public law: program_child_scope.
Header SHA256: e4ed95f9e3e667270f5f70cece0c758c7962dae44fc491b1476290d51ab82fc0.
The header is byte-identical to the 93-line R251 audit's proposed header.
The literal map and Symbol are fixed to the current source alphabet.
The explicit LabelProgramBuildRoles import supplies the literal map.

The law observes the same actual Constraint.project and indexed EdgeInputs result.
It retains full source EdgeFields, exact child ValueFields, inherited descent=[],
the exact fresh-only bucket equation, validity, and annotation-only represented paths.
The complete source row and child arity handle component names app/filter safely.

Four private helpers extract annotation tails, remove inherited nonzero descents,
read the same projected source classes, and transport paths through trie descent.
The proof reuses project_complete, normalized GuardRegions endpoints,
descend_exact/descend_valid/empty_exact, and actual children_valid.
No generic annotation tail-closure or new semantic reader is assumed.
Existing SourceSynthesisInheritedRegions handles another physical-payload representation;
this law instead observes the actual enumeration trie buckets and original SC variables.

Unverified draft. ROOT performs all strict compilation and publication.
No compiler, Git, repository source, Haskell, root docs, or evidence changes.
No global ProgramSlots history, UF protection, callback preservation, Projection,
completion existence, all-Mu discharge, or whole enumeration termination is claimed.

First strict check: three local proof errors, no new premises or missing primitive.
The inherited-empty branch now simplifies the final false=true contradiction.
The filter branch keeps index and explicitly uses its proved position=1.
This avoids subst selecting the earlier indexed.snd=index equality.
The initial 200-line source f5a2d24a2753 is preserved unchanged as a snapshot.
The frozen public header and all operations are unchanged. No compiler was run here.


## program-child-sources-note.md
SHA256 `3047dafd68fc0ee4a3be1f8b57b5caa0b15245cdfaa78d65eac9595935e22fa3`.

# Program-child raw variable sources

Frozen SourceSynthesisProgramChildSources.lean: 52 lines, one public law.
SHA256: a49eed37ba6f9577753a160b5e52e1d42a316d8ed5fa6b14a678216a4f2e34b3
Public header SHA256: ed55f5c5f24dae51c271f663719386451eaa739c0ccb889c518afbd8f885e32c
Public law: program_child_sources.
The complete inputs equal the checked program_child_scope inputs.
The complete prior conclusion remains grouped unchanged. One exact interval is appended.
Header/input/conclusion preservation was checked by literal text comparison.

The proof calls program_child_scope once and retains its complete result.
It rewrites the same actual bucket with that result's own-descent equality.
The literal map/filter inversion retains the SAME original suspended variable.
Existing suspendedVars_variables and List.mem_range' yield both exact bounds.
There is no new observer, semantic producer, freshness gate, or count premise.

Dependency ChildScope199 fc1b69e7 passed ROOT strict checking with one public law.
This new source is an unverified draft for ROOT's strict check.
Raw numerical bounds do not establish UnionFind representative separation.
Later IncomingAvoid still needs the actual marked-root bounds and UF forest facts.
No compiler, Git, repository source, Haskell, root docs, or evidence changes.


## program-enumeration-roles-note.md
SHA256 `b4bc2a4daa7ca403f8d2f41da1dffe26945a6e41acb0133efd87ffd661d6df3c`.

# Program roles at literal raw initialization

Definitions and header frozen before proof, 2026-11-12 19:59 CET.
The source defines three proof predicates over existing Fragment/UVarValue/Core.
FragmentRoles admits marked raw holes, arbitrary-symbol one-child components,
literal app with four children, and literal filter with two children. Type children
are unrestricted. Only Program children recurse. Component-name collisions remain.
SlotRole retains an actual pending handle/lookup/ValueFields or an enumerated
FragmentRoles payload. It reuses ValidSuspended, BucketPaths and annotationRegion.
ProgramSlots retains actual raw bounds, root identity, IncomingAvoid and the exact
stored SlotRole. It does not duplicate Safe, Packet, model or rank predicates.
Binary Protected is a transition receipt. It is not an extra one-state field.
Transient input avoidance remains an actual event obligation for later proofs.

```lean
theorem initial_program_slots
    (heap : NativeHeap) (handle : Nat) (value : Node)
    (decoded : lookupNode heap handle = some value)
    (fields : ValueFields valid literal value) :
    ProgramSlots valid literal heap (EnumerationState.initial handle) (fun uv => uv = 0)
```

The theorem must use the literal EnumerationState.initial handle. It takes the
SAME actual heap readback and complete fields. It takes no initialized-state
predicate, future Projection, completion, model or whole-history supplier.
Raw slot0 is the only mark. Native handles do not serve as UVar marks.
The UF/live-root choice is resolved: bound+IsRoot+IncomingAvoid are the existing
single-state facts required by protected-step lemmas. No global native role map
or closure of marks under nonroot aliases is required.

Frozen source: SourceSynthesisProgramEnumerationRoles.lean, 87 lines.
SHA256: e31274ac2cb247cb8d20267c4253ecaf1de8520886ed8f003b267d59bd3f5c84.
Status: runtime draft. ROOT must run the strict check.
One public law: initial_program_slots, line 63. No instances are introduced.
The definitions-only source had SHA256
94a349468e090bfcb34b44f1b7a3fe8c92d117e1060b2dad1d29eda6449c863f.
Mechanical byte checks confirm that those definitions and the frozen header are
unchanged after proof construction. The proof uses literal initial store values,
the existing initialized singleton UF read, and the absence of suspended references.
The actual decoded/fields receipt supplies the pending payload at raw slot0.

IncomingAvoid concerns suspended equality references, as defined by the existing
EnumerationReferences predicate. It does not forbid Program-fragment holes that
point to marked Program slots. Those holes are retained by FragmentRoles.
The module proves neither transition preservation nor actual finished projection.
It assumes no ordinary typing, model, completion, future role receipt or rank.
No compilation, repository, Git, Haskell or evidence operation was performed.


## program-fragment-write-note.md
SHA256 `148abfdefeb6ed42ab1cc7fab933eb9395ce4d2908adf39b6b59713f4f33b68a`.

# Actual enumerated Program-fragment write

Frozen SourceSynthesisProgramFragmentWrite.lean: 54 lines, one public law.
SHA256: 2966bc452ff7c67d284ce8a16ffe2c54d4fb3f6e82565b3475fd4fadf72992a0
Public law: setValue_program_slots.
Frozen header SHA256: 43327b5cad55f3d8566bdf8e5d166e418fb7e1a373f33af53d66c47e86399a22
The header is unchanged after proof construction.

Inputs are current ProgramSlots, marked uv, FragmentRoles, and the SAME successful
actual EnumerationState.setValue uv (.enumerated fragment) action.
The result retains the complete Core value-update equality and derives ProgramSlots after.
It does not accept a supplied after-role predicate or new storage/counter-alignment gate.

EnumerationDriver.modify_success supplies the exact state update once.
The unchanged counter/representatives retain all marked bounds and root identities.
EnumerationReferences.setValue_allowed retains IncomingAvoid for each marked root:
the new enumerated payload contains no suspended references.
ProgramSlots.stored supplies a real pre-write value at the selected marked slot.
That actual readback supplies the list bound for getElem?_set_self, without Safe.
The new role is exactly SlotRole.enumerated fragment roles.
Other marked raw slots retain their original payloads by getElem?_set_ne.
The proof introduces no new role predicates, instances, or helper observers.

Unverified runtime draft; ROOT runs the strict check and publication.
FragmentRoles alone permits cycles. This law proves neither Safe after nor rank.
Packet.ordered and actual later callback/finalization composition remain separate.
No model, completion, native rewrite, or whole enumeration result is claimed.
No compiler, Git, repository, Haskell, root documentation, or evidence changes.


## program-roles-compression-note.md
SHA256 `ad8285a2d0e915f08f3a91a6b16019a9fedbbc772bcee32aae585e9eb8c19453`.

# Program roles across the existing compression frame

Header frozen before proof, 2026-11-12 20:09 CET.
The theorem uses the actual existing EnumerationCompressionFrame.Frame.
The native heap, literal labels, validity predicate and raw marks stay the same.

```lean
theorem compression_frame_program_slots
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (frame : EnumerationCompressionFrame.Frame before after)
    (roles : ProgramSlots valid literal heap before marked) :
    ProgramSlots valid literal heap after marked
```

Use Frame.counter and Frame.values for the exact allocation domain and payloads.
Use Frame.reaches for each marked raw root. Existing frame_incoming transports
IncomingAvoid through the SAME frame and its exact class equivalence. It needs
no Safe, totality, rank, native model, Projection or after-role supplier.
The law covers actual compression reads when their existing read law returns
this Frame. It does not claim role preservation through allocation or slot writes.

Frozen source: SourceSynthesisProgramRolesCompression.lean, 39 lines.
SHA256: 79fc01254535c7d81404f2c23a770bb87d85661bba11d9509ad86e25c2e02f76.
Status: runtime draft. ROOT must run the strict check.
One public law: compression_frame_program_slots, line 19.
The entire public header matches the pre-proof frozen header byte-for-byte.
Imports: checked ProgramEnumerationRoles and existing EnumerationPendingReplacement.
The proof calls frame_incoming on the SAME supplied frame. Its class transport
uses SameClass as common finite root paths and rewrites each via Frame.reaches.
No new predicates, instances, native operations or relation were introduced.
No compiler, repository, Git, Haskell or evidence operation was performed.


## program-roles-native-heap-note.md
SHA256 `e02442275c10de066b558a4ca90e5276b68bdd3349be12bb56f34907d0f1f2a1`.

# Program roles across native heap growth

One public keeps_program_slots law uses the existing native Keeps relation.
The actual caller Post.effects.keeps supplies this relation. No functional
lookup oracle, new bridge relation, native model or future role predicate enters.
The full enumeration Core and marked raw occurrences remain fixed. The pending
case uses checked lookupNode_keeps. All fields and annotation paths remain.
The stored fragment case retains its exact FragmentRoles certificate.
This lemma does not derive a caller Post or compose the complete loop.


## shared-terminal-query-count-note.md
SHA256 `c943d53db9894112b0d99bf2e3eacc99f63dae7827b5b76ea7401da966d39b33`.

# R252 terminal count from the actual source-list length

Status: ROOT strict PASS, one public law, exact 109-line b40af81a source.

Source: SourcePruningEnumerationSharedTerminalQueryCount.lean, 109 lines.
SHA256: b40af81ae3ed583748f73cf798ee9c29507f178cba4b7b5d732b6f6612af0fd6
Public header: shared-terminal-query-count-header.txt, 48 lines.
Header SHA256: d6f1d755cf33e29b534757473cae44d2d4fd3c96a93bd11ed2dec8679f717ca1

Namespace: MicroCFTA.SourcePruningEnumerationSharedTerminalQueryCount.
Public law: run_query_count.
No public operation is introduced.

The law bounds the same checked TerminalQueryEvents.runObserved event list
by rest.length + 2. The input first :: rest has rest.length + 1 suspensions.
The existing fold contributes at most one explicit query per recorded source.
The actual incoming merge contributes at most one more explicit query.

The private representative traversal proof uses Success and List.mapM_cons.
Each successful traversal returns exactly one result per input suspension.
The private prefix proof decomposes the actual binds and final pure result.
The final prefix result retains the complete recorded list. The filtered
canonicalIds list changes the waiting transfer only. It does not change
the recorded list returned to the actual fold.

The public proof calls checked run_observe_exact once. It inspects the
literal prefix result in that same count receipt. A singleton success
supplies the private traversal proof. Other prefix shapes have no terminal
query events and satisfy the existing fallback bound. No Ready, Safe,
completion, prefix-success or count premise is added to the public law.

The law uses the exact old observer. Its full cached/raw result equality
and exact event semantics remain available through checked run_observe_exact.
There is no new observer, second worker, replay or native operation.

Scope: explicit intersection execute sites in the dispatch fold and the
incoming merge. EnabledEmpty internal calls are not counted. The law does
not bound all native calls, native steps, allocations or consumer work.
It gives no whole eager/default completion or lazy Haskell claim.
No Haskell change or defect claim was made.

The original 108-line source is preserved as the -666abd8c snapshot.
The first strict log is shared-terminal-query-count-195427-failure.txt.
The repair follows the actual success_pure equalities in the forward direction.
It also reduces the returned triple projections before rewriting recorded.
The private local LawfulMonad proof gains the existing List.map_const' step.
That step is inside the original header snapshot prelude. The public theorem
statement remains byte-identical. No operational definition is changed.


## program-child-role-step-header.txt
SHA256 `471bd445d26338ed3639ab7afc9f566ba03fc81e257286bb4a4bbcdba9ca4f34`.

import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourceSynthesisProgramChildSlots
import MicroCFTA.SourcePruningEnumerationChildEffects
import MicroCFTA.SourcePruningEnumerationIsolatedPending

/-!
# Program roles after one actual child allocation

The event keeps every old marked root and marks the actual fresh child.
Current storage bounds exclude references to the new root.
The transient child bucket must avoid the old marked root classes.
-/
namespace MicroCFTA.SourceSynthesisProgramChildRoleStep
open Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationReferences InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourceSynthesisProgramEnumerationRoles
open SourceSynthesisHereditaryProgramFields (ValueFields)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {valid : Constraint → Prop} {literal : String → Symbol}

/-- The same successful child action retains old Program roles and adds its fresh root. -/
theorem program_child_role_step
    (heap : NativeHeap) (incoming : Node) (scs : List Suspended)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap incoming) (closed : incoming.free = [])
    (fields : ValueFields valid literal incoming)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (before after : Core) (marked : Nat → Prop)
    (safe : Safe before) (roles : ProgramSlots valid literal heap before marked)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv scs)
    (action : EnumerateM Symbol Constraint (Fragment Symbol)) (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    ∃ handle, encodeNode incoming = some handle ∧ lookupNode heap handle = some incoming ∧
      fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)} ∧
      Safe after ∧ ProgramSlots valid literal heap after (fun uv => marked uv ∨ uv = before.counter) := by


## program-child-scope-header.txt
SHA256 `e4ed95f9e3e667270f5f70cece0c758c7962dae44fc491b1476290d51ab82fc0`.

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


## program-child-sources-header.txt
SHA256 `ed55f5c5f24dae51c271f663719386451eaa739c0ccb889c518afbd8f885e32c`.

theorem program_child_sources
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
    (SourceSynthesisHereditaryProgramFields.ValueFields valid literal incoming ∧
      EnumerationState.descendScs index scs = [] ∧
      bucket = EnumerationState.descendScs index (EnumerationCorrectness.suspendedVars start tries) ∧
      ∀ sc ∈ bucket, EqualityTrie.Valid sc.trie ∧
        ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail) ∧
      ∀ sc ∈ bucket, start ≤ sc.var ∧ sc.var < start + tries.length


## program-fragment-write-header.txt
SHA256 `43327b5cad55f3d8566bdf8e5d166e418fb7e1a373f33af53d66c47e86399a22`.

theorem setValue_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (uv : Nat) (selected : marked uv) (fragment : Fragment Symbol)
    (roles : FragmentRoles literal marked fragment)
    (written : Success (EnumerationState.setValue uv (.enumerated fragment)) before () after) :
    after = {before with values := before.values.set uv (.enumerated fragment)} ∧
      ProgramSlots valid literal heap after marked


## program-roles-native-heap-header.txt
SHA256 `b6539c30735454c7a57ee14ed2652e95b55807a364ab0132004dd826efacc8d5`.

import MicroCFTA.SourceSynthesisProgramEnumerationRoles

/-!
# Program slot roles across actual native heap growth

The existing native Keeps relation retains each successful node lookup.
The enumeration Core and its marked raw occurrences stay fixed.
Actual caller Post.effects.keeps supplies this native relation.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesNativeHeap
open EnumerationState InternedConstructorTemplates
open SourceSynthesisProgramEnumerationRoles
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {valid : Constraint → Prop} {literal : String → Symbol}

/-- Actual native growth retains every marked slot and its complete payload role. -/
theorem keeps_program_slots
    (beforeHeap afterHeap : NativeHeap) (state : Core) (marked : Nat → Prop)
    (kept : SourceEqualityRequiredCache.Keeps beforeHeap afterHeap)
    (roles : ProgramSlots valid literal beforeHeap state marked) :
    ProgramSlots valid literal afterHeap state marked := by


## shared-terminal-query-count-header.txt
SHA256 `d6f1d755cf33e29b534757473cae44d2d4fd3c96a93bd11ed2dec8679f717ca1`.

import MicroCFTA.SourcePruningEnumerationSharedTerminalQueryEvents

/-!
# Query count from the literal terminal input

A successful prefix records one representative for each suspension.
The bound counts explicit intersection calls in the checked observer.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedTerminalQueryCount
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Waiting" => EnumerationWaitingIndex.Waiting
variable {width : Nat}

local instance queryCountMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance queryCountLawfulMonadList : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- Count the same checked observation without a prefix or count premise. -/
theorem run_query_count
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended) (caller : Caller width) (before : Cached)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    (SourcePruningEnumerationSharedTerminalQueryEvents.runObserved checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest caller before incoming incomingScs queries).2.length ≤ rest.length + 2 := by


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


## Remaining proof boundary

The strongest construction/pruning theorem remains accepted_exact from the
previous checkpoint. Its same input-derived-width initializer and pruning run
preserve exactly eligible Programs at the requested count and original query
coverage when no avoid rules are present. Full current typed observables remain.
This is not a fixed host-capacity guarantee or full default enumeration theorem.

The new laws derive actual operational cases of Program role preservation.
They do not yet compose terminal UF merging, every callback or the full driver.
A fresh child step uses current Safe, actual native availability/readback, valid
annotation paths, existing bucket reference bounds and transient old-root
avoidance. These are current event inputs. The after-role conclusion is derived.
Fragment writes do not claim Safe or rank from FragmentRoles alone. Existing
Packet.ordered/Stratified facts supply rank separately. IncomingAvoid covers
suspended equality references; it does not prohibit legal Program-fragment holes.

Actual finished partial readback still needs the composed role history. The
conditional completion decoder is checked, but it does not supply this history.
Full eager native query totals, all original-input resource bounds, default Mu
rendering, reduce/refold, output order/multiplicity, rank/unrank inverse laws and
Haskell/FFI correspondence remain separate. Existing counterexamples and source
pins remain intact. No production Haskell repair or new behavior is asserted.
