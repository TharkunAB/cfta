import MicroCFTA.EqualityLeafProjectionRequireParent
import MicroCFTA.EqualityRawLeafCompiler

/-!
# Complete source-first occurrence correspondence for required paths

Structural recursion composes exact leaf requirements, source row filtering,
canonical parent reconstruction, and closed child occurrence transport.
The actual worker runs first. Finite later preparation represents its exact
returned record. No whole-worker or whole-pass correspondence is assumed.
-/
namespace MicroCFTA.EqualityLeafProjectionRequireExact
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionSyntax (Tree Edge Path fits)
open EqualityLeafProjectionCompile (Tag)
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionCompileOrdinary
open EqualityLeafProjectionRepresentation EqualityLeafProjectionWorkers
open EqualityLeafProjectionRequireCorrespondence EqualityLeafProjectionRequireTransport

/-- Local source leaf behavior and actual cache construction derive complete
recursive requirement correspondence on every finite original occurrence. -/
theorem require_transport [DecidableEq (EdgeKey Symbol Guard)]
    (leaf : Leaf → Work Symbol Guard (Value Symbol Guard))
    (leafAvailable : LeafAvailable leaf) (leafOrdinary : LeafOrdinary leaf) (leafRequires : LeafRequires leaf)
    (tree : Tree (Tag Symbol Guard) Leaf) : Transport leaf tree := by
  intro paths state facts value represented
  by_cases root : fits paths 0 = true
  · have checked := root_only leaf tree paths root state value represented
    refine ⟨state, value, facts, ?_, ?_, checked.2⟩
    · rw [checked.1]
      exact grows_refl state
    · exact congrArg (fun result : Option (Value Symbol Guard) × State Symbol Guard => result.1) checked.1
  · have proper : fits paths 0 = false := Bool.eq_false_iff.mpr root
    cases tree with
    | empty =>
        have same : value = .empty := (congrArg (fun result : Value Symbol Guard × State Symbol Guard => result.1) represented).symm
        subst value
        exact ⟨state, .empty, facts, by simpa only [require_empty, run] using grows_refl state, by simp [require_empty, run], rfl⟩
    | leaf input =>
        have checked := leaf_proper leaf leafRequires input paths proper state facts value represented
        refine ⟨state, .empty, facts, ?_, ?_, checked.2⟩
        · rw [checked.1]
          exact grows_refl state
        · exact congrArg (fun result : Option (Value Symbol Guard) × State Symbol Guard => result.1) checked.1
    | node edges =>
        apply EqualityLeafProjectionRequireParent.node leaf leafAvailable leafOrdinary edges ?_ paths proper state facts value represented
        intro edge member child present
        exact require_transport leaf leafAvailable leafOrdinary leafRequires child
termination_by sizeOf tree
decreasing_by
  have edgeSmall := List.sizeOf_lt_of_mem member
  cases edge with
  | mk tag children =>
      have childSmall := List.sizeOf_lt_of_mem present
      simp only [EqualityLeafProjectionSyntax.Edge.children] at childSmall
      simp_wf
      simp only [EqualityLeafProjectionSyntax.Edge.mk.sizeOf_spec] at edgeSmall
      subst tree
      simp only [EqualityLeafProjectionSyntax.Tree.node.sizeOf_spec]
      omega

noncomputable local instance : DecidableEq EqualityLeafProjectionLeafCache.ConstraintKey := by classical exact inferInstance

/-- Arbitrary admitted initial raw guards instantiate the complete recursive theorem. -/
theorem raw_transport
    (tree : Tree (Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityRawLeafInventory.Leaf initial symbols)) : Transport EqualityRawLeafCompiler.build tree :=
  require_transport EqualityRawLeafCompiler.build EqualityRawLeafCompiler.leaves_available
    EqualityRawLeafCompiler.leaves_ordinary (fun input paths state facts => EqualityRawLeafCompiler.require_exact input paths state facts) tree

/-- Compile original raw occurrences, run the actual source requirement, and
construct a finite exact representation of its already returned physical result. -/
theorem compiled_raw_require
    (tree : Tree (Tag (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey)
      (EqualityRawLeafInventory.Leaf initial symbols)) (paths : List Path)
    (state : State (Fin symbols) EqualityLeafProjectionLeafCache.ConstraintKey) (facts : Facts state) :
    let compiled := run (EqualityLeafProjectionCompile.compile EqualityRawLeafCompiler.build tree) state
    let actual := run (require paths compiled.1) compiled.2
    ∃ after result, Facts after ∧ Grows actual.2 after ∧ actual.1 = some result ∧
      Represents EqualityRawLeafCompiler.build (EqualityLeafProjectionSyntax.require paths tree) after result := by
  let compiled := run (EqualityLeafProjectionCompile.compile EqualityRawLeafCompiler.build tree) state
  have compiledFacts := compile_available EqualityRawLeafCompiler.build EqualityRawLeafCompiler.leaves_available tree state facts
  exact raw_transport tree paths compiled.2 compiledFacts.1 compiled.1
    (completed EqualityRawLeafCompiler.build tree state facts.coherent.valid)

end MicroCFTA.EqualityLeafProjectionRequireExact
