import MicroCFTA.SourcePruningEnumerationNativeOpaqueCountermodel
import MicroCFTA.SourcePruningEnumerationPartialOutput

namespace MicroCFTA.SourcePruningEnumerationNativeOpaquePartial
open Language Fragments EnumerationState EnumerationCorrectness
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "before" => SourcePruningEnumerationNativeOpaqueCountermodel.before
local notation "caller" => SourcePruningEnumerationNativeOpaqueCountermodel.caller
local notation "guard" => SourcePruningEnumerationNativeOpaqueCountermodel.guard
local notation "fresh" => SourcePruningEnumerationSharedOpaqueBucketBoundary.after 6 before
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

/-- Reading the fresh slot publishes its singleton representative in the same state. -/
def observed : Core :=
  {(fresh).core with representatives := UnionFind.put (fresh).core.representatives 2 (.root 1)}

omit [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] in
private theorem read_exact (fuel : Nat) :
    getValue (fuel + 1) 2 (fresh).core =
      [.ok (.unenumerated (some 6) [], observed)] := by
  rfl

/-- The same native opaque allocation renders a truncation at every positive fuel. -/
theorem fresh_partial_exact (width : Nat) (symbol : Symbol) (fuel : Nat) :
    ExceptT.run (SourcePruningEnumerationPartialOutput.expandPartial
      (caller width symbol).checked.native.machine.heap (fuel + 1) (.hole 2) (fresh).core) =
      [.ok (.node .truncated [], observed)] := by
  obtain ⟨handle, encoded, decoded⟩ := SourcePruningEnumerationNodes.available_readback
    (InternedOpaqueUnionWitness.heap symbol guard)
    (InternedOpaqueUnionWitness.value symbol guard)
    (InternedOpaqueUnionWitness.coherent symbol guard)
    (InternedOpaqueUnionWitness.available symbol guard)
    (InternedOpaqueUnionWitness.closed symbol guard)
  have literal : SourcePruningEnumerationNodes.encodeNode
      (InternedOpaqueUnionWitness.value symbol guard) = some 6 := rfl
  have same : handle = 6 := Option.some.inj (encoded.symm.trans literal)
  subst handle
  rw [SourcePruningEnumerationPartialOutput.expandPartial_hole]
  rw [bind_single _ _ _ _ _ (read_exact fuel)]
  change SourcePruningEnumerationNodes.lookupNode
      (caller width symbol).checked.native.machine.heap 6 =
      some (InternedOpaqueUnionWitness.value symbol guard) at decoded
  dsimp only
  rw [decoded]
  rfl

end MicroCFTA.SourcePruningEnumerationNativeOpaquePartial
