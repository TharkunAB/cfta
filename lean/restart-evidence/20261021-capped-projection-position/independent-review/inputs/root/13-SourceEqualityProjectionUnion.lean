import MicroCFTA.SourceEqualityProjectionRead

/-!
# The closed-operand source union used by getPath

Operations.union reads nodeEdges for each closed operand, concatenates the
rows, and makes one node. The graph keeps each row read and the final cache.
It does not replace these reads with stored ordinary edges or createUnion.
-/
namespace MicroCFTA.SourceEqualityProjectionUnion
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionRead
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

/-- Read every operand in source list order and concatenate its exposed rows. -/
inductive ReadAll [DecidableEq (EdgeKey Symbol Guard)] :
    List (Value Symbol Guard) → State Symbol Guard → List (EdgeValue Symbol Guard) → State Symbol Guard → Prop where
  | nil : ReadAll [] state [] state
  | cons (first : Read value before rows middle) (rest : ReadAll values middle more after) :
      ReadAll (value :: values) before (rows ++ more) after

/-- A closed source union constructs one ordinary node after all row reads. -/
inductive Union [DecidableEq (EdgeKey Symbol Guard)] :
    List (Value Symbol Guard) → State Symbol Guard → Value Symbol Guard → State Symbol Guard → Prop where
  | node (read : ReadAll values before edges middle)
      (built : run (makeNode edges) middle = (result, after)) : Union values before result after

/-- Closed source union retains complete operand language and every cache invariant. -/
theorem ReadAll.verified [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (trace : ReadAll values before edges after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    Keeps before after ∧ SemanticReady after ∧ Edges after edges ∧ ClosedEdges edges ∧
      ∀ holds ambient term, (∃ edge ∈ edges, EdgeMeaning (meaning holds ambient) holds edge term) ↔
        ∃ value ∈ values, meaning holds ambient value term := by
  induction trace with
  | nil =>
      exact ⟨pure_keeps _ semantic.ready, semantic, (by simp [Edges]), (by simp [ClosedEdges]), by simp⟩
  | @cons value before rows middle values more after first rest ih =>
      have firstFacts := first.verified semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have tailAvailable : Values middle values := fun child member =>
        firstFacts.1.available child (available child (List.mem_cons_of_mem _ member))
      have tailClosed : ClosedValues values := fun child member => closed child (List.mem_cons_of_mem _ member)
      have restFacts := ih firstFacts.2.1 tailAvailable tailClosed
      refine ⟨firstFacts.1.trans restFacts.1, restFacts.2.1, ?_, ?_, ?_⟩
      · intro edge member
        rcases List.mem_append.mp member with left | right
        · exact InternedEdgeResidency.edge_grows middle after restFacts.1.growth edge (firstFacts.2.2.1 edge left)
        · exact restFacts.2.2.1 edge right
      · intro edge member
        rcases List.mem_append.mp member with left | right
        · exact firstFacts.2.2.2 edge left
        · exact restFacts.2.2.2.1 edge right
      · intro holds ambient term
        have firstExact := first.exact semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self) holds ambient term
        have restExact := restFacts.2.2.2.2 holds ambient term
        simpa only [List.mem_append, or_and_right, exists_or, List.mem_cons, exists_eq_or_imp, exists_eq_left] using or_congr firstExact restExact

/-- Finite operand lists have finite complete row-read graphs. -/
theorem readAll_complete [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ edges after, ReadAll values before edges after ∧ Keeps before after ∧ SemanticReady after ∧
      Edges after edges ∧ ClosedEdges edges := by
  induction values generalizing before with
  | nil => exact ⟨[], before, .nil, pure_keeps before semantic.ready, semantic, by simp [Edges], by simp [ClosedEdges]⟩
  | cons value values ih =>
      obtain ⟨rows, middle, first, kept, ready, _, _⟩ :=
        SourceEqualityProjectionRead.complete value before semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      obtain ⟨more, after, rest, _, _, _, _⟩ := ih middle ready
        (fun child member => kept.available child (available child (List.mem_cons_of_mem _ member)))
        (fun child member => closed child (List.mem_cons_of_mem _ member))
      have trace := ReadAll.cons first rest
      have checked := trace.verified semantic available closed
      exact ⟨_, _, trace, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩

/-- Any completed closed union has the exact independent union language in its actual cache. -/
theorem Union.verified [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard} {result : Value Symbol Guard}
    (trace : Union values before result after) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    Keeps before after ∧ SemanticReady after ∧ Available after result ∧ result.free = [] ∧
      ∀ holds ambient term, meaning holds ambient result term ↔ ∃ value ∈ values, meaning holds ambient value term := by
  cases trace with
  | node read built =>
      have rows := read.verified semantic available closed
      have finished := SourceEqualityRequiredCache.node _ _ rows.2.1.ready rows.2.2.1 rows.2.2.2.1
      have finalSemantic := SourceEqualityRequiredSemanticCache.node _ _ rows.2.1 rows.2.2.1 rows.2.2.2.1
      have sameResult := congrArg Prod.fst built
      have sameState := congrArg Prod.snd built
      dsimp only at sameResult sameState
      subst result
      subst after
      refine ⟨rows.1.trans finished.1, finalSemantic, finished.2.1, finished.2.2.1, ?_⟩
      intro holds ambient term
      exact (MergedColdInterpretation.makeNode_exact _ rows.2.1.ready.semantic.1.normal.facts
        (meaning holds ambient) _ rows.2.2.1 holds (InternedGuardedLanguage.laws holds ambient) term).trans
          (rows.2.2.2.2 holds ambient term)

/-- Every finite closed forest has a finite complete physical source union. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ result after, Union values before result after ∧ Keeps before after ∧ SemanticReady after ∧
      Available after result ∧ result.free = [] := by
  obtain ⟨rows, middle, read, _, _, _, _⟩ := readAll_complete values before semantic available closed
  have trace := Union.node read rfl
  have checked := trace.verified semantic available closed
  exact ⟨_, _, trace, checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1⟩

end MicroCFTA.SourceEqualityProjectionUnion
