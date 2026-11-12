# Terminal protection, parent callback and actual Program readback
Generated 2026-11-12T20:46:52.427259+01:00.

Base `c81730fe7ab5bdca9e958e511c1064be24eba076`. Integrated main `e53852064d3ef5a2eafec47d754c27504b11de5f`.

Six strict-checked modules. All previous proof content remains.

## SourceSynthesisProgramRolesTerminalPrefix
SHA256 `d6e52bb130638582ea6b7e802f55763357c917cc2f37ce4f4ea48b5b2f2df63f`. Lines 154.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramRolesTerminalPrefix.terminal_prefix_program_slots": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem terminal_prefix_program_slots
    (heap : NativeHeap) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting moved : Waiting) (before after : Core) (recorded : List Nat) (winner : Nat)
    (marked : Nat → Prop) (safe : Safe before)
    (roles : ProgramSlots valid literal heap before marked)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv (first :: rest))
    (actual : Success (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting)
      before (recorded, winner, moved) after) :
    after = {before with representatives := after.representatives} ∧
      ProgramSlots valid literal heap after marked ∧
      ∀ uv, marked uv → EnumerationDriver.Protected uv before after ∧
        ¬UnionFind.SameClass after.representatives uv winner ∧ uv ∉ recorded := by
```

## SourceSynthesisProgramRolesAssimilation
SHA256 `5961c7d3f83d323d0dd4fafec7a99f13543b98b64347a57ed18fa50e5856254e`. Lines 162.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramRolesAssimilation.finish_program_slots": [
    "propext",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem finish_program_slots
    (heap : NativeHeap) (before : Core) (marked : Nat → Prop)
    (roles : ProgramSlots valid literal heap before marked)
    (target handle : Nat) (leftScs rightScs : List Suspended) (result : Node)
    (unmarkedTarget : ¬marked target)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv (leftScs ++ rightScs)) :
    (∀ source after, ¬marked source →
      Success (SourcePruningEnumerationAssimilation.finish source target handle leftScs rightScs result) before () after →
      after = assimilated before target source (.unenumerated (some handle) (leftScs ++ rightScs)) ∧
        ProgramSlots valid literal heap after marked ∧
        ∀ uv, marked uv → EnumerationDriver.Protected uv before after) ∧
    (∀ after,
      Success (SourcePruningEnumerationIncomingNode.finish target handle leftScs rightScs result) before () after →
      after = {before with
        values := before.values.set target (.unenumerated (some handle) (leftScs ++ rightScs))
        recursionAncestry := fun other => if other = target then
          (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
          else before.recursionAncestry other} ∧
        ProgramSlots valid literal heap after marked ∧
        ∀ uv, marked uv → EnumerationDriver.Protected uv before after) := by
```

## SourceSynthesisProgramParentCallbackRoles
SHA256 `ebd3ad2cfdfa37119e861851a8ec4948673f8b26e40e0b98ae9a19454328a1c6`. Lines 247.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramParentCallbackRoles.parent_callback_roles": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem parent_callback_roles
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (target : Nat) (selected : marked target)
    (node : Option Nat) (targetScs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (checkEmpty : Bool) (r n p h k start : Nat) (scs : List Suspended)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (initialCaller caller : Caller width) (initial childrenAfter : Cached)
    (initialQueries : Queries) (memos : Memos) (fragments : List Fragment)
    (traversed : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Trace checkEmpty r n p h k
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries)
      initialCaller initial initialQueries fragments caller childrenAfter memos.query)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap childrenAfter.core marked)
    (stored : childrenAfter.core.values[target]? = some (.unenumerated node targetScs))
    (history : ∀ child ∈ fragments, PendingFragment childrenAfter.core child ∧
      FragmentAvoid childrenAfter.core.representatives target child)
    (seed : Seed) (packet : Packet formulas solver inventory caller memos metadata childrenAfter)
    (allocated : FragmentBound childrenAfter.core.counter (.node edge.entry.key.symbol fragments))
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (roots : Nat → Nat) (finalizeFuel : Nat) (before : Cached)
      (fuel : Nat) (result : Bool × Metadata Typing) (after : Core),
      ((∀ extra, SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
        (finalizeFuel + extra) target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter) = some before) ∧
      ExceptT.run (SourcePruningEnumerationFinalize.finish target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core) =
        [.ok ((.node edge.entry.key.symbol fragments), before.core)] ∧
      before.core = {(SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core with
        values := childrenAfter.core.values.set target (.enumerated (.node edge.entry.key.symbol fragments)),
        expansionAncestry := []} ∧
      before.core.values[target]? = some (.enumerated (.node edge.entry.key.symbol fragments)) ∧
      before.expandable = (fun slot => if slot = target then false else childrenAfter.expandable slot) ∧
      before.waiting = EnumerationCanonicalWaiting.count roots (-1) (EnumerationSchedule.references
        (.unenumerated node targetScs : EnumerationState.UVarValue Symbol)) childrenAfter.waiting ∧
      Roots before.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) ∧
      StorageValid before.core ∧ SourcePruningEnumerationObservation.PendingRealized caller.checked.native.machine.heap before.core ∧
      (Safe (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core →
        IsRoot childrenAfter.core.representatives target → Safe before.core)) ∧
      Packet formulas solver inventory caller memos metadata before ∧
      (Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata target (.inl (.node edge.entry.key.symbol fragments)) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments))) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments)) before.core) = [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → HookResult)
            stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (fuel + extra) metadata target (.node edge.entry.key.symbol fragments) caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      FragmentRoles literal marked (.node edge.entry.key.symbol fragments) ∧
      ProgramSlots valid literal caller.checked.native.machine.heap before.core marked ∧
      ProgramSlots valid literal caller.checked.native.machine.heap after marked := by
```

## SourceSynthesisProgramRoleReadback
SHA256 `9719c009e08ac4df8b22a87d4af70d060c08bb49c67237753393d63f6d525af4`. Lines 207.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramRoleReadback.root_partial_program": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem root_partial_program
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) (fuel : Nat) (actualPartial : PartialTerm) (after : Core)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial
      caller.checked.native.machine.heap fuel) before.core actualPartial after) :
    ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
      EnumerationCompressionFrame.Frame before.core after := by
```

## SourceSynthesisProgramRoleCompletions
SHA256 `f300f0109e022a147cdb92b659f6ba693d04fbdbc0ce915eb8a5645047cbe6ec`. Lines 53.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramRoleCompletions.root_partial_completions_program": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem root_partial_completions_program
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) (fuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm) (after : Core)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial
      caller.checked.native.machine.heap fuel) before.core actualPartial after) :
    ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
      EnumerationCompressionFrame.Frame before.core after ∧
      ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
        SourcePruningPartialMatch.Completes assignment actualPartial full →
        Projection literal Prod.fst full program := by
```

## SourceSynthesisProgramRolesPartialCompletion
SHA256 `45b9fe33ad95d2b277e0d7a68471baba3d6795a0556d4a7e9c6b85b47aa0dd14`. Lines 73.

Public names and checked axioms:

```json
{
  "MicroCFTA.SourceSynthesisProgramRolesPartialCompletion.complete_program_root": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ]
}
```

Full public statement:

```lean
theorem complete_program_root
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) :
    ∃ (level : Nat → Nat) (frontier : Nat),
      EnumerationOrder.Stratified before.core level frontier ∧
      ∃ (bound : Nat) (actualPartial : PartialTerm) (after : Core),
        (∀ extra,
          Success (SourcePruningEnumerationPartialOutput.rootPartial
            caller.checked.native.machine.heap (bound + extra)) before.core actualPartial after ∧
          ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
            caller.checked.native.machine.heap (bound + extra) before.core) = [.ok (actualPartial, after)]) ∧
        EnumerationDriver.RenderStable before.core after ∧
        EnumerationCompressionFrame.Frame before.core after ∧
        EnumerationOrder.Stratified after level frontier ∧
        (∀ (language : NodeLanguage Symbol) (meaning : Constraint → Language.Term Symbol → Prop)
          (assignment : Nat → Language.Term Symbol),
          Satisfies language meaning assignment before.core →
            Satisfies language meaning assignment after ∧
            SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
        ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
          ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
            SourcePruningPartialMatch.Completes assignment actualPartial full →
              Projection literal Prod.fst full program := by
```

## program-parent-callback-note.md
SHA256 `46ec3771bccd4b2112ba32f8dca83941e9a9679458a3f8fe0317f8767b3916b4`.

# Program-parent assembly and actual callback roles

Frozen source: SourceSynthesisProgramParentCallbackRoles.lean, 247 lines.
SHA256: ebd3ad2cfdfa37119e861851a8ec4948673f8b26e40e0b98ae9a19454328a1c6
One public law: parent_callback_roles.
Frozen header SHA256: b5ecee9c1fbafff6d0ee9410857d2fb604a4227e7aeb1d9375c6955814e95809.
Header text was frozen before proof construction; the first strict check required the syntax-only corrections below.

The input Packet is CURRENT childrenAfter, before residual recording/finalization.
No after-Packet is supplied. Current child roles, pending/avoid histories and the
pending-parent readback are component receipts from the completed child stage.
The original trace retains every actual native caller/cache/query endpoint in order.
Its length supplies the exact child count; FULL EdgeFields selects the parent layout.
Component names app/filter remain legal and use the one-child component constructor.

SelectedEdge.finish records the residual. Its allocated parent bound supplies safety.
The same counter, representatives and values retain the current role/order fields.
One Finalize.complete produces the actual stable finalizer cache and ENTIRE receipt.
Its same raw write feeds checked FragmentWrite. The current pending/avoid history
feeds write_stratified; no rank conclusion comes from FragmentRoles alone.
The finalized Packet is derived internally with unchanged full native caller/Memos.
One callback_complete_resources returns its ENTIRE original callback tuple.
That same Frame transports marked bounds/roots/IncomingAvoid/stored SlotRole.
Both verdicts and the arbitrary recur/restart equation retain the same result/core.
No second finalizer, callback, native worker/build, or semantic witness is produced.

Unverified runtime draft; ROOT alone runs strict checking/publication.
The initial proposal incorrectly supplied a finalized Packet; the initial header/note
are preserved as -initial-a68d332e snapshots. The corrected header removes that gate.
Current child-history/roles/slots must still be derived by the full driver induction.
No all-branch completion, callback falsehood, decoder Projection, or whole termination.
No compiler, repository, Git, Haskell, root docs, or evidence changes.

First strict check: three namespace/parser diagnostics before full proof checking.
The 240-line ffbe51375622 source and original 196dca4460ae header are preserved.
ChildTraversal is a namespace, not a declaration accepted by selective open (...).
The import is unchanged; plain parent-namespace open and the fully qualified actual
SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Trace replace it.
The intended unenumerated Symbol argument now uses the explicit ascription
(.unenumerated node targetScs : EnumerationState.UVarValue Symbol).
A mechanical text check confirms these are the ONLY public-header changes.
Both corrections name the same intended old types/constructor. No receipt,
operation, premise, conclusion, or role condition is added or removed.
No compiler was run here. ROOT must check the corrected source.

Second strict check: actual PendingRealized namespace and two local bound transports.
The d8346a86f885 source and b00e7da43e6f header are preserved as snapshots.
The only header change fully qualifies SourcePruningEnumerationObservation.PendingRealized.
No free-variable placeholder is intended; this is exactly the original finalizer's predicate.
The proof explicitly derives preparedCounter from the residual update, then beforeCounter
from that equality and the SAME finalizer core receipt. Original packet.bounded and allocated
transfer along this equality. The parent fragment let is unfolded explicitly for allocated.
No new bound premise, Packet input, state, or producer is introduced. No compiler was run here.


## program-role-completions-note.md
SHA256 `eaac457e366e310766c46fd5cd1c993a20ec1a495d4d5ef872b42dafc6d22840`.

# Same Program across actual readback completions

One public root_partial_completions_program calls the actual readback observer
once. It retains its entire Program projection and Core frame, then applies
the checked completion decoder. Every completion has that same Program.
Projection.toProgram_eq gives the corresponding decoder equality. No public
decider, model, completion witness or desired Projection premise was added.
The classical decider used inside the proof does not appear in the projection
statement. The current Packet/ProgramSlots/readback success are the existing
readback observer inputs. The complete driver still needs to derive its roles.


## program-role-readback-note.md
SHA256 `0487ea1dca26dc1d561f2db76a33882df8d46982f06254787cd86970f77041a2`.

# Program projection of the actual partial root

Header frozen before proof, 2026-11-12 20:19 CET.
The actual expandPartial has no visited-marker state. Its bound decreases at each
hole expansion and concrete node. Only pending slots can produce holes/truncation.
Opaque Type reads can return either form, which the Program projection ignores.
Repeated marked holes are expanded at their actual ordered compression states.
Thus the implication remains true for the current predicates and actual renderer.

```lean
theorem root_partial_program
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) (fuel : Nat) (actualPartial : PartialTerm) (after : Core)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial
      caller.checked.native.machine.heap fuel) before.core actualPartial after) :
    ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
      EnumerationCompressionFrame.Frame before.core after
```

All aliases and existing implicit Packet parameters use the current definitions.
No canonical-cache, rank, model, completion, residual truth or future Projection
gate is added. The actual SAME after endpoint is retained. Projection.toProgram_eq
gives its decoder equality with the SAME Program, for any supplied symbol decider.
The public output needs no extra decoder typeclass premise.

Plan: derive all marked stores enumerated with no_pending_program_slot. Preserve
their full ProgramSlots through SAME compression frames. Induct on actual rendering
fuel; use mapM_sound for exact ordered children and opaque annotation prefixes.
Apply this to the actual rootFragment read and the SAME actual partial root render.
This observer does not yet derive the role invariant from the complete driver.

Frozen source: SourceSynthesisProgramRoleReadback.lean, 207 lines.
SHA256: 9719c009e08ac4df8b22a87d4af70d060c08bb49c67237753393d63f6d525af4.
Status: runtime draft. ROOT must run the strict check.
One public law: root_partial_program. Mechanical byte comparison confirms that
the entire public header matches the header frozen before proof construction.
Private EnumeratedSlots only abbreviates actual completed marked stores and the
existing ProgramSlots receipt. The public proof derives it from actual noStop.
Its transport calls checked compression_frame_program_slots on the SAME frame.

The private native-independent readback proof uses the existing expandPartial for
an arbitrary Graph. The public native adapter unfolds only its public expandPartial
wrapper; it does not name or copy the private native boundary view. mapM_sound
retains exact child order and compression states before annotation/function/argument
reads. Each child receipt is conditional on its existing FragmentRoles; opaque Type
children need no role proof. Repeated marked holes use their actual raw root reads.
Renderer fuel decreases at every recursive read. No extra rank premise is added.

No compilation, repository, Git, Haskell or evidence operation was performed.

First strict repair:
ROOT's log is program-role-readback-202932-failure.txt. Preserved original212L as
SourceSynthesisProgramRoleReadback-dfba47d5.lean, SHA256
dfba47d5f7a7cf81d559eb7603ce67204283ebc593bb00324b20d0b2c6641c63.
The private reserved binder prefix is now earlierFrame. The node helper retains
its actual middle state instead of eliminating it through the final pure equality.
The hole case rewrites the actual existing expandPartial equation directly instead
of using a manually spelled match as a change target. No boundary-view supplier
was added. The entire public header remains byte-identical. Only private proof
steps changed; the new source has207 lines. ROOT must run the focused strict check.


## program-roles-assimilation-note.md
SHA256 `600a8c943ee70f32f88cedc431f9f5197eafbf4216c40e83e9a7f0c31170b48f`.

# R253 Program roles through both actual finish actions

Status: ROOT kernel PASS. One private linter repair is frozen for strict recheck.

Source: SourceSynthesisProgramRolesAssimilation.lean, 162 lines.
SHA256: 5961c7d3f83d323d0dd4fafec7a99f13543b98b64347a57ed18fa50e5856254e
Public header: program-roles-assimilation-header.txt, 43 lines.
Header SHA256: 94e80cfd8787e8f9a849e8f7493bb877ce303cb65e2608677fb07cccc1df1439

Namespace: MicroCFTA.SourceSynthesisProgramRolesAssimilation.
Public law: finish_program_slots.
No operation, observer or public invariant type is added.

The one public conjunction covers actual Assimilation.finish and
IncomingNode.finish successful actions. Current inputs are the fixed native
heap, existing ProgramSlots, an unmarked raw target, and the actual combined
bucket Avoids property for every marked Program root. Only the assimilation
arm requires its source to be unmarked. The two arms use their own actual
Success receipts and exact reached Core state.

Both arms return the complete literal final Core formula, ProgramSlots on
the same mark predicate and Protected for every marked root. Those Protected
receipts retain the exact raw payload, root identity and complete class.
No Safe input or Safe-after claim is made. No native value role/readback is
needed for payloads written to unmarked slots. The native heap stays fixed.

The private write proof uses setValue_allowed. It reads the exact current
write equation through modify_success. Unmarked-slot indexing preserves all
marked raw payloads. Current bucket Avoids retains incoming-reference exclusion.

The two private shape observers use the literal actual finish operations.
Empty assimilation rejects before writing. Empty incoming writes and updates
ancestry before rejecting. Neither branch has a successful raw action.
Each nonempty branch has the exact written state used by the public proof.
The proof uses explicit write-state formulas and their modify equations.
It executes no second worker and chooses no independent endpoint.

A private transport lemma uses only equal counters, forests and stores.
It handles the actual ancestry update. It does not claim a CompressionFrame,
which would require recursion ancestry to remain equal. No future roles,
heap, completion, projection, model or rank supplier is used.

Scope: unmarked-slot raw finish actions. Native query allocation and heap
transport, the preceding representative read, cache metadata, Type events,
marked-root fragment writes and the full parent/driver role invariant remain
separate. No Haskell change or defect claim was made.

The original 162-line source is preserved as the -3165856c snapshot.
The first check passed the kernel and reported only unnecessarySimpa at line 59.
The repair changes that private proof step from simpa only to simp only.
The public header and operations remain unchanged.


## program-roles-partial-completion-note.md
SHA256 `ec36e75994bf19bc076cbec23426b3e802b1380f1385841c3b395f154048c945`.

# One actual partial-root producer and one Program

Header frozen before proof, 2026-11-12 20:36 CET.
The literal labels are the checked SourceSynthesisLabelProgramBuildRoles.literal.
Only existing implicit Packet parameters and the arbitrary validity predicate apply.

```lean
theorem complete_program_root
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) :
    ∃ (level : Nat → Nat) (frontier : Nat),
      EnumerationOrder.Stratified before.core level frontier ∧
      ∃ (bound : Nat) (actualPartial : PartialTerm) (after : Core),
        (∀ extra,
          Success (SourcePruningEnumerationPartialOutput.rootPartial
            caller.checked.native.machine.heap (bound + extra)) before.core actualPartial after ∧
          ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
            caller.checked.native.machine.heap (bound + extra) before.core) = [.ok (actualPartial, after)]) ∧
        EnumerationDriver.RenderStable before.core after ∧
        EnumerationCompressionFrame.Frame before.core after ∧
        EnumerationOrder.Stratified after level frontier ∧
        (∀ (language : NodeLanguage Symbol) (meaning : Constraint → Language.Term Symbol → Prop)
          (assignment : Nat → Language.Term Symbol),
          Satisfies language meaning assignment before.core →
            Satisfies language meaning assignment after ∧
            SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
        ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
          ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
            SourcePruningPartialMatch.Completes assignment actualPartial full →
              Projection literal Prod.fst full program
```

The full original producer receipt precedes the appended Program receipt.
The SAME Program is outside the universal original-model observer. The header
supplies neither fuel/readback success nor a rank, model, completion or capacity.
The original observer remains conditional on Satisfies. It does not prove that
any satisfying Type assignment or any completion exists.
The actual shared driver must still derive the ProgramSlots history.

Frozen source: SourceSynthesisProgramRolesPartialCompletion.lean, 73 lines.
SHA256: 45b9fe33ad95d2b277e0d7a68471baba3d6795a0556d4a7e9c6b85b47aa0dd14.
Status: runtime draft. ROOT must run the strict check.
One public law: complete_program_root, line 32.
The entire public header matches the pre-proof frozen header byte-for-byte.
The sole import is checked SourceSynthesisProgramRoleCompletions.

The proof extracts its existing level/frontier from packet.ordered and its initial
root bound from roles.bounded0. It calls rootPartial_complete exactly once. It calls
root_partial_completions_program exactly once on that producer's actual extra0 run.
The original chosen bound, partial term and complete endpoint appear unchanged
in every receipt field. The universal original-model observer is retained intact.
The appended Program and all-completions projection are outside that observer.
Mechanical source checks confirm both call counts and the frozen header.
No compiler, repository, Git, Haskell or evidence operation was performed.


## program-roles-terminal-prefix-note.md
SHA256 `bb2d8feb0c3d37120d9cf7809b6d3909615511f34119bcba69f212dc064924ef`.

# R253 Program roles through the actual terminal prefix

Status: ROOT strict PASS, one public law, exact 154-line d6e52bb1 source.

Source: SourceSynthesisProgramRolesTerminalPrefix.lean, 154 lines.
SHA256: d6e52bb130638582ea6b7e802f55763357c917cc2f37ce4f4ea48b5b2f2df63f
Public header: program-roles-terminal-prefix-header.txt, 56 lines.
Header SHA256: 5fa5f8aef9c7b6defb8fd9b3ddebb159d83e8d6381431017acf4112e8212b793

Namespace: MicroCFTA.SourceSynthesisProgramRolesTerminalPrefix.
Public law: terminal_prefix_program_slots.
No operation, observer or public invariant type is added.

Inputs are the current fixed native heap, Safe before, existing ProgramSlots,
a current first :: rest bucket that avoids every marked Program root, and
the same actual successful TerminalPrefix.run receipt. The law preserves
ProgramSlots on exactly the original mark predicate. It retains the complete
Core shape after = before with only the representative forest changed.
Every marked root retains its complete Protected receipt, stays separate
from the actual winner class, and is absent from the actual recorded list.

The private proof decomposes the actual representative scan, union loop,
final representative read and returned tuple. It reuses representatives_scan,
terminal_unions, merging_representative and joined_root_set. The same root-map
argument already proves mergeTerminal_protected in EnumerationSchedule.
The proof observes the actual prefix before the later assimilation loop.
It does not execute or assume that later loop.

The bucket avoids each marked class, so its recorded representatives cannot
contain a marked root. The union loop preserves each omitted class. Exact
store preservation and that class equivalence retain IncomingAvoid for all
old marked roots. Their SlotRole certificates use the same native heap and
unchanged raw payloads. No native heap transport or native query is needed.

This intermediate endpoint does not generally satisfy Safe. Union can leave
an unassimilated source payload in a raw slot that is no longer a root.
The theorem therefore preserves marked Program roots without a Safe-after
claim. It does not add source bounds solely to prove global storage safety.

Scope: one actual successful terminal prefix. Payload assimilation, incoming
native merge, Type events, cache role history and the full parent/driver role
invariant remain separate. No future roles, model, projection, rank, worker,
completion or native effect supplier is used. No Haskell change or defect
claim was made.


## program-parent-callback-header.txt
SHA256 `b5ecee9c1fbafff6d0ee9410857d2fb604a4227e7aeb1d9375c6955814e95809`.

theorem parent_callback_roles
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (target : Nat) (selected : marked target)
    (node : Option Nat) (targetScs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (checkEmpty : Bool) (r n p h k start : Nat) (scs : List Suspended)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (initialCaller caller : Caller width) (initial childrenAfter : Cached)
    (initialQueries : Queries) (memos : Memos) (fragments : List Fragment)
    (traversed : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Trace checkEmpty r n p h k
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries)
      initialCaller initial initialQueries fragments caller childrenAfter memos.query)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap childrenAfter.core marked)
    (stored : childrenAfter.core.values[target]? = some (.unenumerated node targetScs))
    (history : ∀ child ∈ fragments, PendingFragment childrenAfter.core child ∧
      FragmentAvoid childrenAfter.core.representatives target child)
    (seed : Seed) (packet : Packet formulas solver inventory caller memos metadata childrenAfter)
    (allocated : FragmentBound childrenAfter.core.counter (.node edge.entry.key.symbol fragments))
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (roots : Nat → Nat) (finalizeFuel : Nat) (before : Cached)
      (fuel : Nat) (result : Bool × Metadata Typing) (after : Core),
      ((∀ extra, SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
        (finalizeFuel + extra) target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter) = some before) ∧
      ExceptT.run (SourcePruningEnumerationFinalize.finish target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core) =
        [.ok ((.node edge.entry.key.symbol fragments), before.core)] ∧
      before.core = {(SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core with
        values := childrenAfter.core.values.set target (.enumerated (.node edge.entry.key.symbol fragments)),
        expansionAncestry := []} ∧
      before.core.values[target]? = some (.enumerated (.node edge.entry.key.symbol fragments)) ∧
      before.expandable = (fun slot => if slot = target then false else childrenAfter.expandable slot) ∧
      before.waiting = EnumerationCanonicalWaiting.count roots (-1) (EnumerationSchedule.references
        (.unenumerated node targetScs : EnumerationState.UVarValue Symbol)) childrenAfter.waiting ∧
      Roots before.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) ∧
      StorageValid before.core ∧ SourcePruningEnumerationObservation.PendingRealized caller.checked.native.machine.heap before.core ∧
      (Safe (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core →
        IsRoot childrenAfter.core.representatives target → Safe before.core)) ∧
      Packet formulas solver inventory caller memos metadata before ∧
      (Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata target (.inl (.node edge.entry.key.symbol fragments)) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments))) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments)) before.core) = [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → HookResult)
            stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (fuel + extra) metadata target (.node edge.entry.key.symbol fragments) caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      FragmentRoles literal marked (.node edge.entry.key.symbol fragments) ∧
      ProgramSlots valid literal caller.checked.native.machine.heap before.core marked ∧
      ProgramSlots valid literal caller.checked.native.machine.heap after marked


## program-role-completions-header.txt
SHA256 `a7a26751cb5484ce5f1d9459348bed4910aa43f0def69b9fe712c8fa9ed7a1a7`.

import MicroCFTA.SourceSynthesisProgramRoleReadback
import MicroCFTA.SourceSynthesisPartialProgramDecoder

/-!
# One Program across completions of the actual finished readback

The current packet and Program slots determine the actual readback projection.
Every completion retains that same Program. The full Core frame remains.
The complete driver must still derive its Program-slot history.
-/
namespace MicroCFTA.SourceSynthesisProgramRoleCompletions
open EnumerationState EnumerationCorrectness
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
open SourceSynthesisProgramTermSize (Projection)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {caller : SourceCurrentAllocatedPartialState.State width}
    {memos : EndpointMemoGateTrace.Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : EnumerationExpandableIndex.Cached Symbol Constraint}
    {valid : Constraint → Prop}

/-- The same actual readback and every completion project to one Program. -/
theorem root_partial_completions_program
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) (fuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm) (after : Core)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial
      caller.checked.native.machine.heap fuel) before.core actualPartial after) :
    ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
      EnumerationCompressionFrame.Frame before.core after ∧
      ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
        SourcePruningPartialMatch.Completes assignment actualPartial full →
        Projection literal Prod.fst full program := by


## program-roles-assimilation-header.txt
SHA256 `94e80cfd8787e8f9a849e8f7493bb877ce303cb65e2608677fb07cccc1df1439`.

import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourcePruningEnumerationAssimilation
import MicroCFTA.SourcePruningEnumerationIncomingNode
import MicroCFTA.EnumerationReferences

/-!
# Program roles through actual unmarked-slot finish actions

The finish actions write unmarked raw slots and update ancestry.
The supplied buckets avoid all marked Program classes.
No safety claim is made for the intermediate unassimilated state.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesAssimilation
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationReferences
open InternedConstructorTemplates SourceSynthesisProgramEnumerationRoles
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {valid : Constraint → Prop} {literal : String → Symbol}

/-- Both actual finish sites retain every marked Program root and its exact stored payload. -/
theorem finish_program_slots
    (heap : NativeHeap) (before : Core) (marked : Nat → Prop)
    (roles : ProgramSlots valid literal heap before marked)
    (target handle : Nat) (leftScs rightScs : List Suspended) (result : Node)
    (unmarkedTarget : ¬marked target)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv (leftScs ++ rightScs)) :
    (∀ source after, ¬marked source →
      Success (SourcePruningEnumerationAssimilation.finish source target handle leftScs rightScs result) before () after →
      after = assimilated before target source (.unenumerated (some handle) (leftScs ++ rightScs)) ∧
        ProgramSlots valid literal heap after marked ∧
        ∀ uv, marked uv → EnumerationDriver.Protected uv before after) ∧
    (∀ after,
      Success (SourcePruningEnumerationIncomingNode.finish target handle leftScs rightScs result) before () after →
      after = {before with
        values := before.values.set target (.unenumerated (some handle) (leftScs ++ rightScs))
        recursionAncestry := fun other => if other = target then
          (before.expansionAncestry ++ before.recursionAncestry target).eraseDups
          else before.recursionAncestry other} ∧
        ProgramSlots valid literal heap after marked ∧
        ∀ uv, marked uv → EnumerationDriver.Protected uv before after) := by


## program-roles-terminal-prefix-header.txt
SHA256 `5fa5f8aef9c7b6defb8fd9b3ddebb159d83e8d6381431017acf4112e8212b793`.

import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.EnumerationDriver

/-!
# Program roles at the actual terminal prefix endpoint

The prefix changes only the representative forest. Its bucket avoids each
marked Program class. Those roots retain their raw payloads and classes.
Payload assimilation follows this intermediate endpoint.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationReferences InternedConstructorTemplates
open SourceSynthesisProgramEnumerationRoles
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Waiting" => EnumerationWaitingIndex.Waiting
variable {valid : Constraint → Prop} {literal : String → Symbol}

local instance prefixRolesMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance prefixRolesLawfulMonadList : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- The same terminal prefix retains every marked Program root and its complete class. -/
theorem terminal_prefix_program_slots
    (heap : NativeHeap) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting moved : Waiting) (before after : Core) (recorded : List Nat) (winner : Nat)
    (marked : Nat → Prop) (safe : Safe before)
    (roles : ProgramSlots valid literal heap before marked)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv (first :: rest))
    (actual : Success (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting)
      before (recorded, winner, moved) after) :
    after = {before with representatives := after.representatives} ∧
      ProgramSlots valid literal heap after marked ∧
      ∀ uv, marked uv → EnumerationDriver.Protected uv before after ∧
        ¬UnionFind.SameClass after.representatives uv winner ∧ uv ∉ recorded := by


## actual-program-parent-callback-next.md
SHA256 `b97ee80bc214f543e1dd01fafa13acad880638bc962e56c9f4adda0e08858c41`.

# Actual parent assembly, finalization, and Left callback

Frozen corrected header, 2026-11-12 20:33 CET. Fixed current Symbol/literal.
Packet is at CURRENT childrenAfter, before residual recording and finalization.
The new stored/history inputs are CURRENT pending-root and returned-child receipts.
They are exposed by SharedTraversalResources.complete_with_fragments_resources:78-84.
FragmentRoles alone supplies neither pending targets nor acyclic fragment dependencies.

```lean
theorem parent_callback_roles
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (target : Nat) (selected : marked target)
    (node : Option Nat) (targetScs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (checkEmpty : Bool) (r n p h k start : Nat) (scs : List Suspended)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (initialCaller caller : Caller width) (initial childrenAfter : Cached)
    (initialQueries : Queries) (memos : Memos) (fragments : List Fragment)
    (traversed : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Trace checkEmpty r n p h k
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries)
      initialCaller initial initialQueries fragments caller childrenAfter memos.query)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap childrenAfter.core marked)
    (stored : childrenAfter.core.values[target]? = some (.unenumerated node targetScs))
    (history : ∀ child ∈ fragments, PendingFragment childrenAfter.core child ∧
      FragmentAvoid childrenAfter.core.representatives target child)
    (seed : Seed) (packet : Packet formulas solver inventory caller memos metadata childrenAfter)
    (allocated : FragmentBound childrenAfter.core.counter (.node edge.entry.key.symbol fragments))
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (roots : Nat → Nat) (finalizeFuel : Nat) (before : Cached)
      (fuel : Nat) (result : Bool × Metadata Typing) (after : Core),
      ((∀ extra, SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
        (finalizeFuel + extra) target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter) = some before) ∧
      ExceptT.run (SourcePruningEnumerationFinalize.finish target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core) =
        [.ok ((.node edge.entry.key.symbol fragments), before.core)] ∧
      before.core = {(SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core with
        values := childrenAfter.core.values.set target (.enumerated (.node edge.entry.key.symbol fragments)),
        expansionAncestry := []} ∧
      before.core.values[target]? = some (.enumerated (.node edge.entry.key.symbol fragments)) ∧
      before.expandable = (fun slot => if slot = target then false else childrenAfter.expandable slot) ∧
      before.waiting = EnumerationCanonicalWaiting.count roots (-1) (EnumerationSchedule.references
        (.unenumerated node targetScs : EnumerationState.UVarValue Symbol)) childrenAfter.waiting ∧
      Roots before.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) ∧
      StorageValid before.core ∧ SourcePruningEnumerationObservation.PendingRealized caller.checked.native.machine.heap before.core ∧
      (Safe (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core →
        IsRoot childrenAfter.core.representatives target → Safe before.core)) ∧
      Packet formulas solver inventory caller memos metadata before ∧
      (Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata target (.inl (.node edge.entry.key.symbol fragments)) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments))) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments)) before.core) = [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → HookResult)
            stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (fuel + extra) metadata target (.node edge.entry.key.symbol fragments) caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      FragmentRoles literal marked (.node edge.entry.key.symbol fragments) ∧
      ProgramSlots valid literal caller.checked.native.machine.heap before.core marked ∧
      ProgramSlots valid literal caller.checked.native.machine.heap after marked
```

Derive layout by FULL EdgeFields and actual ordered Trace length. Component names may collide.
SelectedEdge.finish changes only obligations. Derive its Packet internally from allocated.
Call Finalize.complete ONCE. Keep its ENTIRE packet, then derive the SAME finalized Packet:
setValue_pending preserves history; write_stratified uses CURRENT history/stored, not FragmentRoles.
Checked FragmentWrite proves the same actual raw write's ProgramSlots; Frame retains them.
Call callback_complete_resources ONCE with its ORIGINAL prerequisites; retain its ENTIRE tuple.
No supplied after-Packet, model, Projection, future completion, or second callback is used.
The actual child-history induction for current slots/history/roles remains open.
Routes: ChildTraversal.Trace:227; SelectedEdge.finish:427; CapturedEdge.run:523;
SharedPreparedRecursive.continueWith:74; SharedPreparedCallbackResources:37; EnumerationOrder:83.
No compiler, repository, Git, Haskell, root documentation, or evidence changes.


## Remaining proof boundary

The strongest exact construction/pruning theorem remains accepted_exact: the
same successful current first-order initializer and completed pruning run
retain exactly eligible Programs at the requested count and original query
coverage with avoid=[]. Width is mathematical input-derived, not a fixed host
capacity guarantee. All prior native and typing observations remain.

The new complete_program_root theorem is conditional on the actual finished
Packet and ProgramSlots. It derives its finite readback, stable result, Program
projection and all-completions projection without a supplied readback or model.
It preserves the original model observers under their original forall/implication;
it does not turn them into existence of a satisfying type assignment.

TerminalPrefix performs union operations before payload assimilation. Its
intermediate result retains marked Program roots but does not claim Safe after.
Both actual finish actions preserve Program roles without that invalid gate.
The parent callback uses CURRENT child-endpoint Packet and history receipts.
It derives the finalized Packet rather than assuming one after finalization.

Full shared-terminal native resource composition, nonmarked/type transitions,
class allocation and the actual driver role induction remain open. Full default
semantic output still needs satisfying/residual facts. Eager total native work,
original-input capacities/work, reduce/refold, Mu output, order/multiplicity,
rank/unrank inverses and Haskell/FFI correspondence remain separate. Existing
source-pinned counterexamples and all prior proofs remain. No Haskell repair
or new runtime behavior is asserted.
