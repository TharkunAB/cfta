import MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry

#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry.prefixState
#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry.operations_ready
#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry.entry
#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry.finite
#check MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry.prefixState
#check MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry.operations_ready
#check MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry.entry
#check MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry.finite

namespace MicroCFTA.SourceCurrentConjunctionAllocatedClassEntryProbes
open Cache InternedConstructorTemplates SourceRecursiveIntersectionThunks
open SourceCurrentConjunctionAllocatedClassEntry
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
variable (width : Nat) (heap : State Symbol Guard) (loaded : Allocated) (inherited : Stored) (cache : Cache.State Key)

-- The state retains the complete actual returned operation cache.
example : (prefixState width heap loaded inherited cache).operations =
    (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited
      (SourceEqualityConstraintMemoAllocation.initial cache)).2 := rfl

-- The physical constructor heap is unchanged by equality allocation.
example : (prefixState width heap loaded inherited cache).native.machine.heap = heap := rfl

-- The native state is the same cold state throughout this precheck.
example : (prefixState width heap loaded inherited cache).native = initial width ⟨heap, Cache.emptyState⟩ := rfl

-- The returned interner is the actual prefix result, including positive empty allocations.
example : (prefixState width heap loaded inherited cache).operations.constraints =
    (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited
      (SourceEqualityConstraintMemoAllocation.initial cache)).2.constraints := rfl

-- Completed combination cells come from the actual prefix, without a reset.
example : (prefixState width heap loaded inherited cache).operations.combinations =
    (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited
      (SourceEqualityConstraintMemoAllocation.initial cache)).2.combinations := rfl

-- Completed descent cells come from the same actual prefix.
example : (prefixState width heap loaded inherited cache).operations.descents =
    (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited
      (SourceEqualityConstraintMemoAllocation.initial cache)).2.descents := rfl

-- Current physical fields derive their retained loads from actual operation growth.
example (before : Checked width) (after : Operations) (ready : Ready before)
    (valid : SourceEqualityConstraintMemoAllocation.Valid after)
    (growth : SourceEqualityConstraintMemoAllocation.Grows before.operations after) :
    SourceCurrentConjunctionEquality.Fields after before.native.machine.heap :=
  (operations_ready before after ready valid growth).good.fields

-- The same growth retains the scoped native cells without a semantic model premise.
example (before : Checked width) (after : Operations) (ready : Ready before)
    (valid : SourceEqualityConstraintMemoAllocation.Valid after)
    (growth : SourceEqualityConstraintMemoAllocation.Grows before.operations after) :
    SourceCurrentAllocatedNativeScopeCache.Scoped (⟨before.native, after⟩ : Checked width).native :=
  (operations_ready before after ready valid growth).scopedCache
end MicroCFTA.SourceCurrentConjunctionAllocatedClassEntryProbes
