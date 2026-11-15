import MicroCFTA.SourcePruningEnumerationSharedProperPathWitness
import MicroCFTA.EnumerationPendingAssignment
import MicroCFTA.EnumerationPendingAgreement

/-!
# One removed arrow-child bucket and every stored fragment equation

One actual parked bucket supplies one finite UF-compatible pending choice.
The stratified evaluator extends those choices through all stored fragments.
Agreement at pending roots retains the full removed bucket at its raw targets.
The same assignment retains source Type witnesses at every direct pending slot.
Other native domains, residuals, and historical buckets remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedArrowBucketFragmentWitness
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates
open SourceSynthesisFiniteTypeWitnesses (TypeIn)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

set_option autoImplicit false
variable {Typing Key : Type} {width : Nat}

/-- One assignment satisfies the removed arrow-child bucket, all old UF aliases, and every stored fragment equation. -/
theorem selected_parked_arrow_bucket_fragment_assignment
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel depth uv handle : Nat)
    (metadata updated : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before parked : Cached) (checked core : Core) (next : Option Next)
    (safe : Safe before.core)
    (level : Nat → Nat) (frontier : Nat)
    (stratified : EnumerationOrder.Stratified before.core level frontier)
    (pending : EnumerationReferences.PendingReferences before.core)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (selected : SourcePruningEnumerationRestart.decision stop order metadata before =
      some (.expand uv))
    (bucket : List Suspended)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) bucket))
    (arrowPaths : ∀ sc ∈ bucket, ∀ path ∈ EqualityTrie.fromPathTrie sc.trie,
      path = [1] ∨ path = [2])
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parked) (some [.ok ((updated, next), core)]))
    (catalog : List (String × Nat)) :
    ∃ (resolved : Core) (rho : Nat → Term Symbol),
      resolved.values[uv]? = some (.unenumerated (some handle) bucket) ∧
      Success (setValue uv (.unenumerated (some handle) [])) resolved () checked ∧
      parked.core = checked ∧ core = checked ∧
      UnionFind.Satisfies before.core.representatives rho ∧
      (∀ slot fragment, before.core.values[slot]? = some (.enumerated fragment) →
        rho slot = fill rho fragment) ∧
      (∀ sc ∈ bucket, Suspended.Holds rho (rho uv) sc) ∧
      (∀ (occurrence : Nat) (sc : Suspended), bucket[occurrence]? = some sc →
        Suspended.Holds rho (rho uv) sc) ∧
      ∀ slot node scs, before.core.values[slot]? = some (.unenumerated node scs) →
        TypeIn catalog (rho slot) := by
  obtain ⟨resolved, base, resolvedSlot, cleared, parkedSame, coreSame, baseAliases,
      _checkedAliases, _parkedAliases, _coreAliases, baseHeld, _baseIndexed,
      baseMembers, _sourceMembers⟩ :=
    SourcePruningEnumerationSharedProperPathWitness.selected_parked_arrow_bucket_assignment
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth uv handle
      metadata updated caller queries before parked checked core next safe valid selected
      bucket stored arrowPaths actual catalog
  obtain ⟨rho, aliases, equations, agreement⟩ :=
    EnumerationPendingAssignment.stratified_extend_pending before.core safe level frontier
      stratified base baseAliases
  have held := EnumerationPendingAgreement.stored_bucket_holds_transfer before.core safe pending
    base rho baseAliases aliases
    (fun slot node scs atSlot => (agreement slot node scs atSlot).symm)
    uv (some handle) bucket stored baseHeld
  refine ⟨resolved, rho, resolvedSlot, cleared, parkedSame, coreSame,
    aliases, equations, held, ?_, ?_⟩
  · intro occurrence sc indexed
    exact held sc (List.mem_iff_getElem?.mpr ⟨occurrence, indexed⟩)
  · intro slot node scs atSlot
    rw [agreement slot node scs atSlot]
    exact baseMembers slot

end MicroCFTA.SourcePruningEnumerationSharedArrowBucketFragmentWitness

#print axioms MicroCFTA.SourcePruningEnumerationSharedArrowBucketFragmentWitness.selected_parked_arrow_bucket_fragment_assignment
