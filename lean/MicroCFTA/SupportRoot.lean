import MicroCFTA.SupportJoin

/-!
# Closing support roots without changing descendant constraints

An n-way join retains its child list and its equality constraint. All emitted
paths are nonempty. Replacing only the root symbol preserves those reads.
-/
namespace MicroCFTA.SupportRoot
open Language GeneratorCombinators BinderLanguage SupportGraph

/-- Replace one root symbol and retain its complete child list. -/
def replaceRoot (label : Label Symbol) : Term (Label Symbol) → Term (Label Symbol)
  | .node _ children => .node label children

/-- A nonempty path does not read the root symbol. -/
theorem path_root (label old : Label Symbol) (children : List (Term (Label Symbol)))
    (path : List Nat) (nonempty : path ≠ []) :
    (Term.node label children).atPath path = (Term.node old children).atPath path := by
  cases path with
  | nil => contradiction
  | cons first rest => rfl

/-- Equalities between descendant positions survive a root replacement. -/
theorem equality_root (label old : Label Symbol) (children : List (Term (Label Symbol)))
    (left right : List Nat) (leftNonempty : left ≠ []) (rightNonempty : right ≠ []) :
    PathsEqual (.node label children) left right ↔ PathsEqual (.node old children) left right := by
  simp only [PathsEqual, path_root label old children left leftNonempty,
    path_root label old children right rightNonempty]

/-- Replace the edge's root label and retain every original constraint. -/
def closeEdge (label : Label Symbol) (payload : Payload (Label Symbol))
    (children : List (Support Symbol)) : Support Symbol :=
  .branch ⟨label, payload.guard⟩ children

/-- Root relabelling is exact when the retained guard does not depend on that symbol. -/
theorem closeEdge_exact (environment : Env (Label Symbol)) (label : Label Symbol)
    (payload : Payload (Label Symbol)) (children : List (Support Symbol))
    (independent : ∀ terms, payload.guard (.node label terms) ↔ payload.guard (.node payload.label terms))
    (term : Term (Label Symbol)) :
    meaning environment (closeEdge label payload children) term ↔
      ∃ original, meaning environment (.branch payload children) original ∧ term = replaceRoot label original := by
  simp only [closeEdge, meaning]
  constructor
  · rintro ⟨terms, rfl, accepted, guard⟩
    exact ⟨.node payload.label terms, ⟨terms, rfl, accepted, (independent terms).mp guard⟩, rfl⟩
  · rintro ⟨original, ⟨terms, rfl, accepted, guard⟩, rfl⟩
    exact ⟨terms, rfl, accepted, (independent terms).mpr guard⟩

/-- The source retains its join guard when a user node closes the joined layer. -/
def closeJoin (symbol : Symbol) (component : Nat) (operation : Support Symbol)
    (supports : List (Support Symbol)) : Support Symbol :=
  closeEdge (.user symbol)
    ⟨.joinN, fun term => ∀ index < supports.length, PathsEqual term [0, index + 1] [index + 1, 0]⟩
    (edge .centerKeyed (operation :: (SupportJoin.keys component 0 supports.length).map singleton) ::
      SupportJoin.argumentNodes component 0 supports)

/-- Closing a join retains its exact graph language under the actual term callback. -/
theorem closeJoin_exact (environment : Env (Label Symbol)) (symbol : Symbol) (component : Nat)
    (operation : Support Symbol) (supports : List (Support Symbol)) (term : Term (Label Symbol)) :
    meaning environment (closeJoin symbol component operation supports) term ↔
      ∃ original, meaning environment (SupportJoin.joinNode component operation supports) original ∧
        term = SupportTerms.labelTerm symbol original := by
  have copied := closeEdge_exact environment (.user symbol)
    ⟨.joinN, fun term => ∀ index < supports.length, PathsEqual term [0, index + 1] [index + 1, 0]⟩
    (edge .centerKeyed (operation :: (SupportJoin.keys component 0 supports.length).map singleton) ::
      SupportJoin.argumentNodes component 0 supports)
    (fun terms => by
      constructor <;> intro valid index inside
      · exact (equality_root (.user symbol) .joinN terms [0, index + 1] [index + 1, 0] (by simp) (by simp)).mp (valid index inside)
      · exact (equality_root (.user symbol) .joinN terms [0, index + 1] [index + 1, 0] (by simp) (by simp)).mpr (valid index inside)) term
  change meaning environment (closeJoin symbol component operation supports) term ↔
    ∃ original, meaning environment (SupportJoin.joinNode component operation supports) original ∧
      term = replaceRoot (.user symbol) original at copied
  rw [copied]
  constructor <;> rintro ⟨original, accepted, same⟩
  all_goals
    obtain ⟨operationTerm, terms, _, _, shape⟩ := (SupportJoin.join_exact environment component operation supports original).mp accepted
    refine ⟨original, accepted, ?_⟩
    simpa [shape, SupportJoin.joinTerm, replaceRoot, SupportTerms.labelTerm] using same

end MicroCFTA.SupportRoot
