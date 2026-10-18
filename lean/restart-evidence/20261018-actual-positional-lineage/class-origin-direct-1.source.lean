import MicroCFTA.SourceCurrentActualRequiredRowOrigins
import MicroCFTA.SourceCurrentActualEditRowOrigins
import MicroCFTA.SourceCurrentActualPlainHeadOrigins
import MicroCFTA.SourceCurrentClassPositionalFootprints
import MicroCFTA.SourceCurrentLowerGuardHeapReturns

/-!
# Actual class-fold positional row origins

Literal class paths determine the untouched continuation. Physical entry
facts and actual earlier returns supply each selected call. An ordinary
rebuild retains full rows. Accepted recursive exposure supplies only empty
own fields. These origins compose through the actual right fold.
-/
namespace MicroCFTA.SourceCurrentActualClassRowOrigins
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceCurrentLowerOperationInvariants (Effect SharedGood)
open SourceCurrentActualRequiredRowOrigins (Root Link)
open SourceCurrentClassPositionalFootprints (Unselected)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Good" => SourceCurrentNativeOperationHeap.Good
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "Worker" => SourceCurrentAllocatedSharedEditWorker.edit
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "GuardHeap" => SourceCurrentConstrainedCapGuardHeap.Heap Plain
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem bind_done {A B : Type} (first : SourceCurrentAllocatedSharedEditWorker.Outcome width A)
    (next : A → Shared width → SourceCurrentAllocatedSharedEditWorker.Outcome width B)
    {value : B} {after : Shared width} (actual : first.bind next = .done value after) :
    ∃ result middle, first = .done result middle ∧ next result middle = .done value after := by
  cases first with
  | done result middle => exact ⟨result,middle,rfl,actual⟩
  | failed => cases actual

private theorem shared_advance {before : Shared width} (good : SharedGood before) {checked : Checked width}
    (effect : Effect before.checked checked) : SharedGood (SourceCurrentAllocatedSharedTargetState.advance before checked) :=
  ⟨effect.good,good.stored.grows effect.keeps,
    fun path value present => effect.keeps.available value (good.slots path value present)⟩

private theorem head_effect {fuel value before result after}
    (actual : SourceCurrentAllocatedSharedEditWorker.head fuel value before = .done result after)
    (good : SharedGood (width := width) before) (available : Available before.checked.native.machine.heap value) :
    Effect before.checked after.checked ∧ SharedGood after ∧ Available after.checked.native.machine.heap result := by
  cases returned : SourceEqualityRequiredWorker.head fuel value before.checked.native.machine.heap with
  | pending | unresolved | exhausted =>
    simp only [SourceCurrentAllocatedSharedEditWorker.head,returned] at actual
    cases actual
  | done output heap =>
    simp only [SourceCurrentAllocatedSharedEditWorker.head,returned] at actual
    cases actual
    have graph := SourceEqualityRequiredWorkerSound.head_graph fuel value _ _ heap returned
    obtain ⟨keeps,semantic,costs,fields,known⟩ := SourceCurrentRequiredHeapEffects.head
      (SourceCurrentConjunctionEquality.FieldAvailable before.checked.operations) graph
      good.checked.semantic good.checked.costs good.checked.fields available
    have effects : SourceCurrentConjunctionRowsAllocation.Effects
        (SourceCurrentAllocatedNativeEffects.physical before.checked) ⟨heap,before.checked.operations⟩ :=
      ⟨keeps,⟨semantic,costs,good.checked.operations,fields⟩,SourceEqualityConstraintMemoAllocation.grows_refl _⟩
    have effect : Effect before.checked
        (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked ⟨heap,before.checked.operations⟩) :=
      ⟨good.checked.advance _ effects,keeps,effects.grows⟩
    exact ⟨effect,shared_advance good effect,known⟩

private theorem ordinary_root {value : Node} (ordinary : SourceEqualityRequiredCache.Ordinary value) : Root value := by
  cases value <;> trivial

private theorem ordinary_below {record originals e p h m s n entries value before result after}
    (actual : Worker record originals e p h m s n (.editBelow entries) value before = .done result after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap value) (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (childIndex : Nat) (absent : SourceEqualityNeededMap.lookup (childIndex : Int) entries = none) :
    Root result ∧ Link childIndex value result := by
  cases value with
  | empty =>
    cases e with
    | zero => cases actual
    | succ e => cases actual; exact ⟨by trivial,fun row impossible => by cases impossible⟩
  | node entry rows depth free =>
    exact ⟨ordinary_root (SourceCurrentActualEditRowOrigins.edit_node_ordinary actual good originalsAvailable available),
      fun row member => .inr (SourceCurrentActualEditRowOrigins.edit_node actual good originalsAvailable available childIndex absent member)⟩
  | reference | mu | union => cases ordinary

/-- An actual below edit retains positional origins, including its own accepted recursive Head. -/
theorem below {record originals e p h m s n entries value before result after}
    (actual : Worker record originals e p h m s n (.editBelow entries) value before = .done result after)
    (good : SharedGood (width := width) before) (originalsAvailable : Values before.checked.native.machine.heap originals)
    (available : Available before.checked.native.machine.heap value) (guards : GuardHeap before.checked.native.machine.heap)
    (root : Root value) (childIndex : Nat) (absent : SourceEqualityNeededMap.lookup (childIndex : Int) entries = none) :
    Root result ∧ Link childIndex value result := by
  have recursiveCase (recursive : SourceEqualityRequiredGraph.Recursive value)
      (accepted : SourceMemoGate.unconstrained value = true)
      (run : ∃ exposed middle, SourceCurrentAllocatedSharedEditWorker.head h value before = .done exposed middle ∧
        Worker record originals (e-1) p h m s n (.editBelow entries) exposed middle = .done result after) :
      Root result ∧ Link childIndex value result := by
    obtain ⟨exposed,middle,first,last⟩ := run
    have verified := SourceCurrentActualPlainHeadOrigins.shared_head first good.checked guards available accepted
    obtain ⟨effect,current,known⟩ := head_effect first good available
    have retained := ordinary_below last current
      (fun value member => effect.keeps.available value (originalsAvailable value member)) known verified.2.2.1 childIndex absent
    exact ⟨retained.1,Link.trans (fun row member => .inl (verified.2.2.2 row member)) retained.2⟩
  cases value with
  | empty | node => exact ordinary_below actual good originalsAvailable available trivial childIndex absent
  | reference name => cases e <;> cases actual
  | mu entry body depth ordinary =>
    cases e with
    | zero => cases actual
    | succ e =>
      exact recursiveCase trivial root (by
        obtain ⟨exposed,middle,first,last⟩ := bind_done _ _ actual
        exact ⟨exposed,middle,first,last⟩)
  | union entry values depth free =>
    cases e with
    | zero => cases actual
    | succ e =>
      exact recursiveCase trivial root (by
        obtain ⟨exposed,middle,first,last⟩ := bind_done _ _ actual
        exact ⟨exposed,middle,first,last⟩)

/-- A successful literal class retains the indexed input continuation from its entry facts. -/
theorem run_class {e p h m s n record values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.runClass e p h m s n record values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (guards : GuardHeap before.native.machine.heap)
    (coherent : SourceEqualityClassOrder.Coherent record) (index childIndex : Nat)
    (unselected : Unselected record index childIndex) {source result : Node}
    (input : values[index]? = some source) (output : results[index]? = some result) (root : Root source) :
    Root result ∧ Link childIndex source result := by
  obtain ⟨entries,shared,start,finish,original,built,sameState,sameMemo,found,earlier,later,dispatch⟩ :=
    SourceCurrentClassPositionalFootprints.class_dispatch actual coherent index childIndex unselected output
  have same := Option.some.inj (found.symm.trans input)
  subst original
  rcases dispatch with ⟨absent,rfl,same⟩ | ⟨children,selected,absent,call⟩
  · exact ⟨root,Link.refl _ _⟩
  · have prefix : SourceCurrentAllocatedSharedEditWorker.editList (Worker record values e p h m s n)
        (.editBelow entries) (values.take index) (SourceCurrentAllocatedSharedTargetState.initial before memo) =
        .done (results.take index) start := earlier
    have prefixAvailable : Values before.native.machine.heap (values.take index) :=
      fun value member => available value (List.mem_of_mem_take member)
    have initial := SharedGood.initial good stored
    obtain ⟨effect,current,known⟩ := SourceCurrentLowerOperationInvariants.edit_list prefix initial available prefixAvailable
    have currentGuards := SourceCurrentLowerGuardHeapReturns.edit_list Plain prefix initial available prefixAvailable guards
    exact below call current (fun value member => effect.keeps.available value (available value member))
      (effect.keeps.available source (available source (List.mem_of_getElem? input))) currentGuards root childIndex
      (by simpa using absent)

private theorem class_bind_done (first : SourceCurrentAllocatedClassWorker.Outcome width)
    (next : List Node → Checked width → Memo → SourceCurrentAllocatedClassWorker.Outcome width)
    {results after saved} (actual : first.bind next = .done results after saved) :
    ∃ values middle memo, first = .done values middle memo ∧ next values middle memo = .done results after saved := by
  cases first with
  | done values middle memo => exact ⟨values,middle,memo,rfl,actual⟩
  | failed => cases actual

/-- The actual right fold composes exact positional row origins at the same forest index. -/
theorem fold {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (guards : GuardHeap before.native.machine.heap)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record) (index childIndex : Nat)
    (unselected : ∀ record ∈ records, Unselected record index childIndex) {source result : Node}
    (input : values[index]? = some source) (output : results[index]? = some result) (root : Root source) :
    Root result ∧ Link childIndex source result := by
  induction records generalizing values before memo results after saved source result with
  | nil =>
    cases actual
    cases Option.some.inj (input.symm.trans output)
    exact ⟨root,Link.refl _ _⟩
  | cons record records ih =>
    obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
    obtain ⟨entries,shared,start,finish,original,built,sameState,sameMemo,found,earlier,later,dispatch⟩ :=
      SourceCurrentClassPositionalFootprints.class_dispatch last (coherent record List.mem_cons_self) index childIndex
        (unselected record List.mem_cons_self) output
    have tail := ih first good stored available guards
      (fun record member => coherent record (List.mem_cons_of_mem _ member))
      (fun record member => unselected record (List.mem_cons_of_mem _ member)) input found root
    obtain ⟨effect,retained,known⟩ := SourceCurrentLowerOperationInvariants.class_fold first good stored available
    have currentGuards := SourceCurrentLowerGuardHeapReturns.class_fold Plain first good stored available guards
    have head := run_class last effect.good retained known currentGuards (coherent record List.mem_cons_self)
      index childIndex (unselected record List.mem_cons_self) found output tail.1
    exact ⟨head.1,tail.2.trans head.2⟩

/-- Final Empty propagation retains the row relation from the complete actual class pass. -/
theorem pass {e p h m s n records values before memo results after saved}
    (actual : SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo = .done results after saved)
    (good : Good (width := width) before) (stored : Stored before.native.machine.heap memo)
    (available : Values before.native.machine.heap values) (guards : GuardHeap before.native.machine.heap)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record) (index childIndex : Nat)
    (unselected : ∀ record ∈ records, Unselected record index childIndex) {source result : Node}
    (input : values[index]? = some source) (output : results[index]? = some result) (root : Root source) :
    Root result ∧ Link childIndex source result := by
  obtain ⟨middle,checked,current,first,last⟩ := class_bind_done _ _ actual
  cases last
  by_cases erased : middle.any (fun value => value.referenceOf == .empty) = true
  · have member : result ∈ middle.map (fun _ => (Value.empty : Node)) := by
      simpa only [EqualityLeafProjectionRuntimeEmpty.propagate,erased,ite_true,EqualityLeafProjectionRuntimeEmpty.erase]
        using List.mem_of_getElem? output
    obtain ⟨original,included,same⟩ := List.mem_map.mp member
    cases same
    exact ⟨by trivial,fun row impossible => by cases impossible⟩
  · have same : EqualityLeafProjectionRuntimeEmpty.propagate middle = middle := by
      simp [EqualityLeafProjectionRuntimeEmpty.propagate,erased]
    exact fold first good stored available guards coherent index childIndex unselected input (by simpa only [same] using output) root

end MicroCFTA.SourceCurrentActualClassRowOrigins
