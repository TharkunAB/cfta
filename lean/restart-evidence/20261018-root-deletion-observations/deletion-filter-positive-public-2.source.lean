import MicroCFTA.SourceCurrentStoredMuRootContract
import MicroCFTA.SourceCurrentNativeBinderProfile
import MicroCFTA.SourceEqualityRequiredCache
set_option linter.all true
namespace MicroCFTA.RootContractActualPublications
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedFreshOrdinaryDepthHeap (usesLocal)
open InternedBinderProtocol (Reference NodeKey)
open InternedRootProfile (Profile profile Equivalent)
open InternedStoredSubstitution (leaves)
open SourceCurrentStoredProfileFunction (denote)
open SourceCurrentStoredMuProfileContract (shadow)
open SourceCurrentStoredMuRootContract (Correct)
open SourceCurrentStoredMuTrackedProfile (erase)
open SourceCurrentPublicationHeapInduction (Heap)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceEqualityRequiredCache (Ready Keeps)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

private def expression (used : Option Bool) : Syntax Nat Bool :=
  match used with | none => .var 0 | some false => .node [.mk 7 false [.var 0]] | some true => .var 1
private def captures : List (Value Nat Bool) := [.reference (.uninterned 10)]
private def source (smart : Bool) (used : Option Bool) : Syntax Nat Bool := .binder smart (expression used)
private def actual (smart : Bool) (used : Option Bool) := build (source smart used) captures empty
private def result (smart : Bool) (used : Option Bool) : Value Nat Bool :=
  match actual smart used with | .done value _ => value | .pending .. => .empty
private def reader (smart : Bool) (used : Option Bool) := (actual smart used).state
private def depthCall (used : Option Bool) := callback (expression used) captures .depth (empty : State Nat Bool)
private def depthValue (used : Option Bool) := match depthCall used with | .done value _ => value | .pending .. => .empty
private def ordinaryCall (used : Option Bool) := callback (expression used) captures (.uninterned (ordinaryLevel (depthValue used))) (depthCall used).state
private def ordinaryValue (used : Option Bool) := match ordinaryCall used with | .done value _ => value | .pending .. => .empty
private def key (used : Option Bool) := muKey (depthValue used) (ordinaryValue used)
private def stored (smart : Bool) (used : Option Bool) := ((reader smart used).nodeRecords (key used)).getD .empty
private def entry (smart : Bool) (used : Option Bool) : Interned NodeKey := match stored smart used with | .mu entry _ _ _ => entry | _ => ⟨0,.node []⟩
private def body (smart : Bool) (used : Option Bool) := match stored smart used with | .mu _ body _ _ => body | _ => .empty
private def entryHeap (smart : Bool) (used : Option Bool) (warm : Bool) := if warm then reader smart used else empty
private theorem done (smart : Bool) (used : Option Bool) (warm : Bool) :
    build (source smart used) captures (entryHeap smart used warm) = .done (result smart used) (reader smart used) := by
  cases smart <;> cases used with
  | none => cases warm <;> cbv
  | some mode => cases mode <;> cases warm <;> cbv
private theorem captures_available (state : State Nat Bool) : InternedNestedProvenance.Values state captures := by
  intro value member
  have equal : value = .reference (.uninterned 10) := by simpa only [captures,List.mem_singleton] using member
  cases equal
  exact InternedNestedProvenance.ordinary_available state _
private theorem initial_ready : Ready (empty : State Nat Bool) :=
  SourceEqualityRequiredCache.constructed .empty .empty empty (by rw [build])
private theorem source_keeps (expression : Syntax Nat Bool) (inputs : List (Value Nat Bool))
    (before : State Nat Bool) (initial : Ready before) (available : InternedNestedProvenance.Values before inputs)
    (result : Value Nat Bool) (after : State Nat Bool) (actual : build expression inputs before = .done result after) : Keeps before after := by
  have checked := InternedFreshOrdinaryFacts.build_verified expression inputs before initial.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before initial.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before initial.semantic.1.normal.facts.coherent.valid initial.covered result after actual
  · simpa only [actual,Outcome.state] using (InternedOpenDepthExecution.build_depth expression inputs before
      (SourceRecursiveIntersectionSemanticHeap.context before initial.semantic inputs available) initial.semantic.2 initial.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history
private theorem ready (smart : Bool) (used : Option Bool) : Ready (reader smart used) := by
  exact (source_keeps (source smart used) captures empty initial_ready (captures_available empty)
    (result smart used) (reader smart used) (done smart used false)).ready
private theorem context (smart : Bool) (used : Option Bool) : Context (reader smart used) captures :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context _ (ready smart used).semantic _ (captures_available _),
    (ready smart used).semantic.2⟩
private theorem present (smart : Bool) (used : Option Bool) :
    (reader smart used).nodeRecords (key used) =
      some (.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) := by
  cases smart <;> cases used with
  | none => cbv
  | some mode => cases mode <;> cbv
private theorem available (smart : Bool) (used : Option Bool) :
    Available (reader smart used) (.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) :=
  (ready smart used).semantic.1.normal.facts.cached.nodes _ _ (present smart used)
private theorem returned (smart : Bool) (used : Option Bool) :
    finish smart (.mu (entry smart used) (body smart used) (depthValue used) (ordinaryValue used)) = result smart used := by
  cases smart <;> cases used with
  | none => cbv
  | some mode => cases mode <;> cbv
private theorem heap (smart : Bool) (used : Option Bool) : Heap Correct (reader smart used) := by
  intro other actualEntry actualBody actualDepth actualOrdinary installed
  cases smart <;> cases used
  all_goals try (rename_i mode; cases mode)
  all_goals cbv at installed
  all_goals try simp only [Cache.put] at installed
  all_goals repeat' first | split at installed | cases installed
  all_goals
    constructor
    · intro assignment replacement cuts
      cbv
      exact ⟨Iff.rfl,fun _ => Iff.rfl⟩
    · cbv
private theorem checked (smart : Bool) (kind : Option Bool) :
    ∃ (expression : Syntax Nat Bool) (captures : List (Value Nat Bool))
      (result : Value Nat Bool) (reader : State Nat Bool)
      (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
      expression = (match kind with | none => .var 0 | some false => .node [.mk 7 false [.var 0]] | some true => .var 1) ∧
      captures = [.reference (.uninterned 10)] ∧
      build (.binder smart expression) captures empty = .done result reader ∧
      build (.binder smart expression) captures reader = .done result reader ∧
      Ready reader ∧ Context reader captures ∧
      reader.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      Available reader (.mu entry body depth ordinary) ∧
      Correct entry body depth ordinary ∧ Heap Correct reader ∧
      result = finish smart (.mu entry body depth ordinary) := by
  exact ⟨expression kind,captures,result smart kind,reader smart kind,entry smart kind,body smart kind,
    depthValue kind,ordinaryValue kind,rfl,rfl,done smart kind false,done smart kind true,
    ready smart kind,context smart kind,present smart kind,available smart kind,
    heap smart kind _ _ _ _ _ (present smart kind),heap smart kind,(returned smart kind).symm⟩

/-- Actual raw and smart publications satisfy tagged deletion for local, used, and external bodies. -/
theorem actual_publications (smart : Bool) (kind : Option Bool) :
    ∃ (expression : Syntax Nat Bool) (captures : List (Value Nat Bool))
      (result : Value Nat Bool) (reader : State Nat Bool)
      (entry : Interned NodeKey) (body depth ordinary : Value Nat Bool),
      expression = (match kind with | none => .var 0 | some false => .node [.mk 7 false [.var 0]] | some true => .var 1) ∧
      captures = [.reference (.uninterned 10)] ∧
      build (.binder smart expression) captures empty = .done result reader ∧
      build (.binder smart expression) captures reader = .done result reader ∧
      Ready reader ∧ Context reader captures ∧
      reader.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      Available reader (.mu entry body depth ordinary) ∧
      Correct entry body depth ordinary ∧ Heap Correct reader ∧
      result = finish smart (.mu entry body depth ordinary) := checked smart kind

end MicroCFTA.RootContractActualPublications

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.RootContractActualPublications.actual_publications
#print MicroCFTA.RootContractActualPublications.actual_publications
#print axioms MicroCFTA.RootContractActualPublications.actual_publications
