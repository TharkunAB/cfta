import MicroCFTA.SourceRecursiveIntersectionKernelVerified
import MicroCFTA.MergedPhysicalGroupEdges
import MicroCFTA.EqualityLeafProjectionPhysical

/-!
# Actual guarded product-row requests and physical readback

Successful ordered walks derive their complete request traces. Edge
readback retains the actual symbol, conjoined guard, and child results.
Node readback derives the canonical surviving rows from the actual calls.
No product-language or equivalent product-row contract is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain

/-- Actual ordered source requests retain each returned value and intermediate cache. -/
inductive WalkTrace (call : A → Machine Symbol Guard → Result Symbol Guard B) :
    List A → Machine Symbol Guard → List B → Machine Symbol Guard → Prop where
  | nil (state) : WalkTrace call [] state [] state
  | cons (request requests before value middle values after)
      (returned : call request before = .done value middle)
      (rest : WalkTrace call requests middle values after) :
      WalkTrace call (request :: requests) before (value :: values) after

/-- Every successful actual walk has exactly its ordered complete request trace. -/
theorem walk_done_iff (call : A → Machine Symbol Guard → Result Symbol Guard B)
    (requests : List A) (state : Machine Symbol Guard) (values : List B) (final : Machine Symbol Guard) :
    walk call requests state = .done values final ↔ WalkTrace call requests state values final := by
  induction requests generalizing state values final with
  | nil =>
      constructor
      · intro done
        simp only [walk] at done
        cases done
        exact .nil state
      · intro trace
        cases trace
        simp only [walk]
  | cons head tail ih =>
      constructor
      · intro done
        cases first : call head state with
        | failed failure after => simp only [walk, first, Result.bind] at done; cases done
        | done value middle =>
            cases rest : walk call tail middle with
            | failed failure after => simp only [walk, first, Result.bind, rest] at done; cases done
            | done results after =>
                simp only [walk, first, Result.bind, rest] at done
                cases done
                exact .cons head tail state value middle results final first ((ih middle results final).mp rest)
      · intro trace
        cases trace with
        | cons request requests before value middle values after returned rest =>
            simp only [walk, returned, Result.bind, (ih middle values final).mpr rest]

/-- Ordered source requests return one complete value at each original position. -/
theorem WalkTrace.length (trace : WalkTrace call requests before values after) : values.length = requests.length := by
  induction trace with
  | nil => rfl
  | cons request requests before value middle values after returned rest ih => simp only [List.length_cons, ih]

/-- Successful ordinary constructor work retains the exact physical result and current domain cache. -/
theorem work_done [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A) (state : Machine Symbol Guard)
    (value : A) (final : Machine Symbol Guard) (done : work request state = .done value final) :
    value = (run request state.heap).1 ∧ final = {state with heap := (run request state.heap).2} := by
  obtain ⟨sameValue, sameState⟩ := Result.done.inj done
  exact ⟨sameValue.symm, sameState.symm⟩

/-- Equal-arity source edge readback derives actual child traces, literal fields, and final cache effects. -/
theorem edge_readback [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard)
    (valid : Valid state) (known : Domain state domain) (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (sameArity : left.children.length = right.children.length) (value : EdgeValue Symbol Guard) (final : Machine Symbol Guard)
    (done : edge emptyGuard conjoin (call domain) left right state = .done value final) :
    ∃ children after,
      WalkTrace (fun pair => call domain pair.1 pair.2) (left.children.zip right.children) state children after ∧
      work (makeEdge left.entry.key.symbol (conjoin left.entry.key.constraint right.entry.key.constraint) children) after = .done value final ∧
      value.entry.key.symbol = left.entry.key.symbol ∧
      value.entry.key.constraint = conjoin left.entry.key.constraint right.entry.key.constraint ∧ value.children = children := by
  have checked := children_checked call calls domain (left.children.zip right.children) state valid known (by
    intro pair member
    have contained := List.of_mem_zip member
    exact ⟨valid.1.cached.edges left.entry.key left leftResident pair.1 contained.1,
      valid.1.cached.edges right.entry.key right rightResident pair.2 contained.2⟩)
  simp only [edge, sameArity, ite_true] at done
  cases walked : walk (fun pair => call domain pair.1 pair.2) (left.children.zip right.children) state with
  | failed failure after => simp only [walked, Result.bind] at done; cases done
  | done children after =>
      have afterValid : Valid after := by simpa only [walked, Result.state] using checked.valid
      have available := checked.result children after walked
      simp only [walked, Result.bind] at done
      have literal := MergedPhysicalGroupEdges.makeEdge_fields after.heap afterValid.1 left.entry.key.symbol
        (conjoin left.entry.key.constraint right.entry.key.constraint) children available
      have same := (work_done _ after value final done).1
      exact ⟨children, after, (walk_done_iff _ _ _ _ _).mp walked, done, by simpa only [same] using literal⟩

/-- Unequal source arities derive the literal empty edge without any child call. -/
theorem edge_mismatch_readback [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : Valid state)
    (different : left.children.length ≠ right.children.length) (value : EdgeValue Symbol Guard) (final : Machine Symbol Guard)
    (done : edge emptyGuard conjoin call left right state = .done value final) :
    value.entry.key.symbol = left.entry.key.symbol ∧ value.entry.key.constraint = emptyGuard ∧ value.children = [.empty] ∧
      final.domains = state.domains := by
  simp only [edge, different, ite_false] at done
  have actual := work_done _ state value final done
  have literal := MergedPhysicalGroupEdges.makeEdge_fields state.heap valid.1 left.entry.key.symbol emptyGuard [.empty]
    (by intro value member; simp only [List.mem_singleton] at member; subst value; exact empty_available state.heap)
  rw [actual.1, actual.2]
  exact ⟨literal.1, literal.2.1, literal.2.2, rfl⟩

/-- Actual matched row requests derive precisely the parent's canonical surviving physical rows. -/
theorem node_readback [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : node emptyGuard conjoin (call domain) left right state = .done value final) :
    ∃ rows after,
      WalkTrace (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) state rows after ∧
      work (makeNode rows) after = .done value final ∧ nodeEdges value = canonicalEdges (surviving rows) := by
  have checked := rows_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  simp only [node] at done
  cases walked : walk (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) state with
  | failed failure after => simp only [walked, Result.bind] at done; cases done
  | done rows after =>
      have afterValid : Valid after := by simpa only [walked, Result.state] using checked.valid
      have resident := checked.result rows after walked
      simp only [walked, Result.bind] at done
      have same := (work_done _ after value final done).1
      exact ⟨rows, after, (walk_done_iff _ _ _ _ _).mp walked, done,
        by rw [same]; exact EqualityLeafProjectionPhysical.makeNode_edges rows after.heap afterValid.1.coherent afterValid.1.linked resident⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
