import MicroCFTA.SourceCurrentAllocatedPartialInitialization

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.emptyValue
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.operations
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.checked
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.caller
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.globals
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.inventory
#print axioms MicroCFTA.SourceCurrentAllocatedPartialInitialization.emptyValue_live
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.emptyValue_live
#print axioms MicroCFTA.SourceCurrentAllocatedPartialInitialization.operations_correct
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.operations_correct
#print axioms MicroCFTA.SourceCurrentAllocatedPartialInitialization.inventory_source
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.inventory_source
#print axioms MicroCFTA.SourceCurrentAllocatedPartialInitialization.inventory_roots
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.inventory_roots
#print axioms MicroCFTA.SourceCurrentAllocatedPartialInitialization.globals_valid
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.globals_valid
#print axioms MicroCFTA.SourceCurrentAllocatedPartialInitialization.constructed
#check @MicroCFTA.SourceCurrentAllocatedPartialInitialization.constructed

namespace InitializationChecks
open MicroCFTA
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedPartialInitialization
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

theorem constructed_loaded_field (width : Nat)
    {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (key : EdgeKey Symbol Guard) (edge : EdgeValue Symbol Guard)
    (present : heap.edgeRecords key = some edge) :
    ∃ loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula,
      SourceEqualityConstraintFieldLookup.load key.constraint (operations final).constraints = .ok (some loaded) ∧
      EqReady (operations final).constraints loaded.stored ∧
      SourceEqualityConjoinAllocation.readback loaded = key.constraint ∧
      SourceEqualityPhysicalPayload.read key.constraint.equalities = .ok loaded.stored.payload := by
  have initial := (constructed width history valid expression covered value heap built formulas solver).1
  exact (initial.ready.good.fields key edge present).receipts initial.ready.good.operations

theorem constructed_published_root (width : Nat)
    {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ identity,
      let request : SourceCurrentAllocatedPartialState.NodeRequest := ⟨.live identity [], value⟩
      let started := SourceCurrentAllocatedPartialState.beginNode request (caller width final heap)
      started.1 = 0 ∧ started.2.1 = .evaluate request ∧
      started.2.2.nodeResults.cells 0 = some ⟨request, .evaluating⟩ ∧
      SourceCurrentAllocatedPartialMemoSound.Sound formulas solver started.2.2 := by
  obtain ⟨context, identity, _, inherited, available, _, _⟩ :=
    constructed width history valid expression covered value heap built formulas solver
  let request : SourceCurrentAllocatedPartialState.NodeRequest := ⟨.live identity [], value⟩
  have fresh := SourceCurrentAllocatedPartialMemoSound.beginNode_fresh request (caller width final heap) rfl
  have sound := SourceCurrentAllocatedPartialMemoSound.beginNode_sound formulas solver request
    (caller width final heap) context.sound inherited available
  refine ⟨identity, ?_, ?_, ?_, sound⟩
  · exact congrArg Prod.fst fresh.1
  · exact congrArg (fun result => result.2.1) fresh.1
  · exact fresh.2

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
theorem complete_canonical_history
    {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial) :
    Cache.Extends initial.table (operations final).constraints.table ∧
      Cache.Extends initial.issued (operations final).constraints.issued ∧
      (operations final).combinations = (SourceEqualityConstraintMemoAllocation.initial final).combinations ∧
      (operations final).descents = (SourceEqualityConstraintMemoAllocation.initial final).descents := by
  have earlier := history.verified valid
  have allocated := operations_correct final earlier.1
  have steps := SourceEqualityConstraintAllocation.steps_trans earlier.2.1 allocated.2.1.constraints
  exact ⟨Cache.steps_table_extends steps, Cache.steps_issued_extends valid steps, rfl, rfl⟩

def beforeWarm : Cache.State Key := ⟨37, fun _ => none, fun _ => none⟩
def warm : Cache.State Key := (Cache.intern beforeWarm []).2

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
theorem nonzero_warm_hit :
    Cache.Valid warm ∧ emptyValue warm = .live 37 [] ∧
      operations warm = SourceEqualityConstraintMemoAllocation.initial warm ∧
      EqReady (operations warm).constraints (.live 37 []) := by
  have initial : Cache.Valid beforeWarm := by
    constructor <;> intro first second absent <;> cases absent
  have valid := (Cache.intern_correct beforeWarm [] initial).1
  refine ⟨valid, rfl, rfl, ?_⟩
  exact (operations_correct warm valid).2.2

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
theorem exact_warm_cache (cache : Cache.State Key) (entry : Cache.Interned Key)
    (present : cache.table [] = some entry) :
    emptyValue cache = .live entry.identity [] ∧
      operations cache = SourceEqualityConstraintMemoAllocation.initial cache := by
  simp only [emptyValue, operations, SourceEqualityMkEdgeAllocation.emptyField,
    SourceEqualityConstraintAllocation.intern, SourceEqualityConstraintMemoAllocation.initial,
    SourceEqualityPartialConstraintKey.key, List.map_nil, Cache.intern, present]
  exact ⟨trivial, trivial⟩

omit [DecidableEq Symbol] in
theorem computed_root_model (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (holds : Guard → Language.Term Symbol → Bool) :
    ((inventory expression value heap built).inputs holds).valid
      (SourceRecursiveIntersectionInputView.inputOf value) := by
  let actual := inventory expression value heap built
  exact SourceCurrentAllocatedNativeInputInventoryModels.root_valid actual.source actual.facts holds
    actual.roots actual.originals actual.available actual.closed value List.mem_cons_self

end InitializationChecks

#print axioms InitializationChecks.constructed_loaded_field
#check @InitializationChecks.constructed_loaded_field
#print axioms InitializationChecks.constructed_published_root
#check @InitializationChecks.constructed_published_root
#print axioms InitializationChecks.complete_canonical_history
#check @InitializationChecks.complete_canonical_history
#print axioms InitializationChecks.nonzero_warm_hit
#check @InitializationChecks.nonzero_warm_hit
#print axioms InitializationChecks.exact_warm_cache
#check @InitializationChecks.exact_warm_cache
#print axioms InitializationChecks.computed_root_model
#check @InitializationChecks.computed_root_model
