import MicroCFTA.SourceEqualityOpenOrdinaryHead
import MicroCFTA.SourceEqualityProjectionPathDomain
import MicroCFTA.SourceEqualityProjectionPathComplete

/-!
# Selected projection through an open ordinary Mu unfolding

The source exposes a Mu head and projects the same path through its rebuilt
ordinary node. The path domain belongs to that actual rebuilt value. Free
references in unvisited siblings need not disappear. The domain derives
finite projection and its actual effects. It is not derived from a gate.
-/
namespace MicroCFTA.SourceEqualityProjectionOpenOrdinary
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceEqualityProjectionPathDomain
open InternedGuardedLanguage (meaning)

/-- Every actual selected projection through an open ordinary unfolding retains closed resident output. -/
theorem effects [DecidableEq (EdgeKey Symbol Guard)]
    {index : Int} {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project (index :: path) value before result after)
    (semantic : SemanticReady before) (available : Available before value)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (recursive : ∃ own body probe ordinary, value = .mu own body probe ordinary)
    (unfolded : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done (.node entry edges depth free) middle)
    (domain : NodeClosed (index :: path) (run (makeNode edges) middle).1) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨own, originalBody, probe, ordinary, rfl⟩ := recursive
  have actual := SourceEqualityOpenOrdinaryHead.ordinary (.mu own originalBody probe ordinary) before middle
    entry edges depth free semantic available ⟨own, originalBody, probe, ordinary, rfl⟩ unfolded
  cases trace with
  | recursive _ head body =>
      obtain ⟨sameValue, sameState⟩ := actual.1.unique head
      cases sameValue
      cases sameState
      have projected := node_effects body actual.2.2.1 actual.2.2.2.1 domain
      exact ⟨actual.2.1.trans projected.1, projected.2⟩

/-- An accepted subtree survives the actual open Mu exposure and selected projection. -/
theorem included [DecidableEq (EdgeKey Symbol Guard)]
    {index : Int} {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project (index :: path) value before result after)
    (semantic : SemanticReady before) (available : Available before value)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (recursive : ∃ own body probe ordinary, value = .mu own body probe ordinary)
    (unfolded : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done (.node entry edges depth free) middle)
    (domain : NodeClosed (index :: path) (run (makeNode edges) middle).1)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term part : Term Symbol) (accepted : meaning holds ambient value term)
    (selected : SymbolicSignedPaths.lookup term (index :: path) = some part) :
    meaning holds ambient result part := by
  obtain ⟨own, originalBody, probe, ordinary, rfl⟩ := recursive
  have actual := SourceEqualityOpenOrdinaryHead.ordinary (.mu own originalBody probe ordinary) before middle
    entry edges depth free semantic available ⟨own, originalBody, probe, ordinary, rfl⟩ unfolded
  cases trace with
  | recursive _ head body =>
      obtain ⟨sameValue, sameState⟩ := actual.1.unique head
      cases sameValue
      cases sameState
      exact node_included body actual.2.2.1 actual.2.2.2.1 domain holds ambient term part
        ((actual.2.2.2.2.2 holds ambient term).mpr accepted) selected

/-- Selected projection through the actual open ordinary head preserves physical edge annotations. -/
theorem heap (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)]
    {index : Int} {path : List Int} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : Project (index :: path) value before result after)
    (semantic : SemanticReady before) (available : Available before value)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (recursive : ∃ own body probe ordinary, value = .mu own body probe ordinary)
    (unfolded : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done (.node entry edges depth free) middle)
    (domain : NodeClosed (index :: path) (run (makeNode edges) middle).1)
    (fields : SourceEqualityAnnotationHeap.Heap annotation before) : SourceEqualityAnnotationHeap.Heap annotation after := by
  obtain ⟨own, originalBody, probe, ordinary, rfl⟩ := recursive
  have actual := SourceEqualityOpenOrdinaryHead.ordinary (.mu own originalBody probe ordinary) before middle
    entry edges depth free semantic available ⟨own, originalBody, probe, ordinary, rfl⟩ unfolded
  have headHeap := SourceEqualityOpenOrdinaryHead.ordinary_heap annotation (.mu own originalBody probe ordinary)
    before middle entry edges depth free semantic available fields unfolded
  cases trace with
  | recursive _ head body =>
      obtain ⟨sameValue, sameState⟩ := actual.1.unique head
      cases sameValue
      cases sameState
      exact node_heap annotation body actual.2.2.1 actual.2.2.2.1 domain headHeap

/-- The selected domain after an actual open ordinary unfolding derives finite source projection. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (index : Int) (path : List Int) (value : Value Symbol Guard) (before middle : State Symbol Guard)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (semantic : SemanticReady before) (available : Available before value)
    (recursive : ∃ own body probe ordinary, value = .mu own body probe ordinary)
    (unfolded : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done (.node entry edges depth free) middle)
    (domain : NodeClosed (index :: path) (run (makeNode edges) middle).1) :
    ∃ result after, Project (index :: path) value before result after ∧ Keeps before after ∧
      SemanticReady after ∧ Available after result ∧ result.free = [] := by
  have actual := SourceEqualityOpenOrdinaryHead.ordinary value before middle entry edges depth free
    semantic available recursive unfolded
  obtain ⟨result, after, body, kept, finalSemantic, resultAvailable, closed⟩ :=
    SourceEqualityProjectionPathComplete.node_complete (index :: path) (run (makeNode edges) middle).1
      (run (makeNode edges) middle).2 actual.2.2.1 actual.2.2.2.1 domain
  have recursiveHead : SourceEqualityRequiredGraph.Recursive value := by
    obtain ⟨own, originalBody, probe, ordinary, rfl⟩ := recursive
    trivial
  exact ⟨result, after, .recursive recursiveHead actual.1 body, actual.2.1.trans kept,
    finalSemantic, resultAvailable, closed⟩

end MicroCFTA.SourceEqualityProjectionOpenOrdinary
