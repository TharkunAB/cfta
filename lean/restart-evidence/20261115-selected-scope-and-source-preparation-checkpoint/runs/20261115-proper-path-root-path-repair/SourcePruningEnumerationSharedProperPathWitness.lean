import MicroCFTA.SourcePruningEnumerationSharedParkedRawBucketReceipt
import MicroCFTA.SourcePruningEnumerationSelection
import MicroCFTA.SourceSynthesisFiniteTypeWitnesses

/-!
# One finite assignment for an actual removed arrow-child path

Actual selection separates the selected class from every stored reference.
One finite assignment satisfies all UF aliases and one indexed removed path.
Every value of this assignment belongs to the source Type universe syntax.
This result does not satisfy all native domains, fragments, residuals, or history.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedProperPathWitness
open Language EnumerationState EnumerationCorrectness EnumerationSchedule
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
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

set_option autoImplicit false
variable {Typing Key : Type} {width : Nat}

/-- Actual selected parking admits one finite UF assignment for one indexed arrow-child path. -/
theorem selected_parked_one_arrow_path_assignment
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel depth uv handle : Nat)
    (metadata updated : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before parked : Cached) (checked core : Core) (next : Option Next)
    (safe : Safe before.core)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (selected : SourcePruningEnumerationRestart.decision stop order metadata before =
      some (.expand uv))
    (bucket : List Suspended)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) bucket))
    (occurrence : Nat) (sc : Suspended) (indexed : bucket[occurrence]? = some sc)
    (path : EqualityTrie.Path)
    (_represented : path ∈ EqualityTrie.fromPathTrie sc.trie)
    (arrowChild : path = [1] ∨ path = [2])
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parked) (some [.ok ((updated, next), core)]))
    (catalog : List (String × Nat)) :
    ∃ (resolved : Core) (rho : Nat → Term Symbol),
      resolved.values[uv]? = some (.unenumerated (some handle) bucket) ∧
      Success (setValue uv (.unenumerated (some handle) [])) resolved () checked ∧
      parked.core = checked ∧ core = checked ∧
      UnionFind.Satisfies before.core.representatives rho ∧
      UnionFind.Satisfies checked.representatives rho ∧
      UnionFind.Satisfies parked.core.representatives rho ∧
      UnionFind.Satisfies core.representatives rho ∧
      (rho uv).atPath path = some (rho sc.var) ∧
      (∀ slot, TypeIn catalog (rho slot)) ∧
      ∀ (holds : SourceSynthesisGeneralizeSyntax.Guard → Term Symbol → Bool),
        (∀ term, holds SourceSynthesisGeneralizeSyntax.top term = true) →
        ∀ slot, InternedGuardedSyntax.evaluate holds []
          (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal
            (SourceSynthesisTypeSyntax.allTypes SourceSynthesisGeneralizeSyntax.top catalog))
          (rho slot) := by
  classical
  obtain ⟨ready, incoming, _realized⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before uv valid safe selected
  obtain ⟨clearHandle, removed, readAfter, _value, root, size, resolved,
      _rawRead, clearSlot, rawPath, readFrame, _lookup, _boundary, _repeated,
      _representative, resolvedFrame, _keyMember, resolvedSlot, cleared, checkedSame,
      parkedSame, _adapted, _restart, _metadataSame, coreSame, _nextSame, _notStuck,
      _rawAliases, _resume⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.parked_singleton_removed_bucket_receipt
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth uv
      metadata updated caller queries before parked checked core next safe.1.total actual
  obtain ⟨rootSize, rootRead⟩ := ready.root
  have rootSame : root = uv :=
    (UnionFind.reaches_unique rawPath rootRead).1
  subst root
  have samePayload := UVarValue.unenumerated.inj (Option.some.inj (stored.symm.trans clearSlot))
  have handleSame : handle = clearHandle := Option.some.inj samePayload.1
  have bucketSame : bucket = removed := samePayload.2
  subst clearHandle
  subst removed
  have scMember : sc ∈ bucket := List.mem_iff_getElem?.mpr ⟨occurrence, indexed⟩
  have separated : ¬UnionFind.SameClass before.core.representatives uv sc.var :=
    incoming (.unenumerated (some handle) bucket)
      (List.mem_iff_getElem?.mpr ⟨uv, stored⟩) sc scMember
  let base : Term Symbol := .node (literal "var1") []
  let branch : Term Symbol := .node (literal "->")
    [.node (literal "(->)") [], base, base]
  have baseMember : TypeIn catalog base := .leaf "var1" (by simp)
  have branchMember : TypeIn catalog branch := .arrow base base baseMember baseMember
  let rho : Nat → Term Symbol := fun slot =>
    if UnionFind.SameClass before.core.representatives uv slot then branch else base
  have selfClass : UnionFind.SameClass before.core.representatives uv uv :=
    ⟨uv, rootSize, rootRead, rootRead⟩
  have targetValue : rho uv = branch := by simp only [rho, if_pos selfClass]
  have rawValue : rho sc.var = base := by simp only [rho, if_neg separated]
  have beforeAliases : UnionFind.Satisfies before.core.representatives rho := by
    intro left right same
    by_cases first : UnionFind.SameClass before.core.representatives uv left
    · have second := UnionFind.sameClass_trans first same
      simp only [rho, if_pos first, if_pos second]
    · have second : ¬UnionFind.SameClass before.core.representatives uv right := by
        intro joined
        exact first (UnionFind.sameClass_trans joined (UnionFind.sameClass_symm same))
      simp only [rho, if_neg first, if_neg second]
  have frames := readFrame.trans resolvedFrame
  have keptClasses : ∀ left right,
      UnionFind.SameClass checked.representatives left right ↔
        UnionFind.SameClass before.core.representatives left right := by
    intro left right
    rw [checkedSame]
    change UnionFind.SameClass resolved.representatives left right ↔ _
    simp only [UnionFind.SameClass, frames.reaches]
  have checkedAliases : UnionFind.Satisfies checked.representatives rho := by
    intro left right same
    exact beforeAliases left right ((keptClasses left right).mp same)
  have located : (rho uv).atPath path = some (rho sc.var) := by
    rcases arrowChild with first | second
    · rw [first, targetValue, rawValue]
      rfl
    · rw [second, targetValue, rawValue]
      rfl
  have members : ∀ slot, TypeIn catalog (rho slot) := by
    intro slot
    dsimp only [rho]
    split
    · exact branchMember
    · exact baseMember
  refine ⟨resolved, rho, resolvedSlot, cleared, parkedSame, coreSame,
    beforeAliases, checkedAliases, ?_, ?_, located, members, ?_⟩
  · simpa only [parkedSame] using checkedAliases
  · simpa only [coreSame] using checkedAliases
  · intro holds topHeld slot
    exact (members slot).member holds topHeld

end MicroCFTA.SourcePruningEnumerationSharedProperPathWitness
