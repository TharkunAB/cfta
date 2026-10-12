import MicroCFTA.IntersectDomain

/-!
# Progress between closed-environment resets

The source remembers each newly encountered binder pair. A recursive
reference unfolds to its own binder. Ordinary constructor and union descent
uses a finite structural weight. These three facts prove that all recursive
calls between closed-environment resets form a well-founded relation.
The reset branch is separate: it clears the remembered pairs and requires
a decrease between closed subproblems.
-/
namespace MicroCFTA.IntersectSchedule
open Language SymbolicGraphView

/-- Pairs that have not yet introduced a binder in this domain. -/
def unseen (pairs : List Pair) (domain : Domain) : List Pair :=
  pairs.filter fun key => decide (key ∉ domain.seen)

/-- Adding a remembered pair removes it from the remaining pair list. -/
theorem unseen_extend (pairs : List Pair) (domain : Domain) (bindings : List (Nat × Input)) (key : Pair) :
    unseen pairs (extend domain bindings key) = (unseen pairs domain).filter (fun found => decide (found ≠ key)) := by
  simp only [unseen, extend, List.filter_filter, List.mem_cons, not_or, Bool.decide_and]

/-- A newly introduced source pair strictly decreases the finite remaining-pair count. -/
theorem unseen_decreases (pairs : List Pair) (domain : Domain) (bindings : List (Nat × Input)) (key : Pair)
    (possible : key ∈ pairs) (fresh : key ∉ domain.seen) :
    (unseen pairs (extend domain bindings key)).length < (unseen pairs domain).length := by
  rw [unseen_extend]
  have member : key ∈ unseen pairs domain := by simp [unseen, possible, fresh]
  have bounded := List.length_filter_le (fun found : Pair => decide (found ≠ key)) (unseen pairs domain)
  apply Nat.lt_of_le_of_ne bounded
  intro same
  have kept := List.length_filter_eq_length_iff.mp same key member
  simp at kept

/-- Structural weights stop at binders; their bodies decrease the separate pair measure. -/
structure LocalWeight (view : View Symbol) where
  value : Input → Nat
  binder : ∀ name, value (.mu name) = 0
  reference : ∀ name, value (.ref name) = 1
  positive : ∀ node, 0 < value (.node node)
  child : ∀ node row, row ∈ view.rows node → ∀ child ∈ row.children, value child < value (.node node)
  member : ∀ node child, child ∈ view.members node → value child < value (.union node)

/-- An edge worker has one phase above every paired child call. -/
def edgeWeight (weight : Input → Nat) (left right : Row Symbol) : Nat :=
  1 + largest ((left.children.zip right.children).map fun children => weight children.1 + weight children.2)

/-- Source node and edge calls carry their current recursive domain. -/
inductive Call (Symbol : Type) where
  | node (domain : Domain) (left right : Input)
  | edge (domain : Domain) (left right : Row Symbol)

/-- Remaining binder pairs, constructor descent, and one canonical-order swap give the measure. -/
def measure (pairs : List Pair) (weight : Input → Nat) : Call Symbol → Nat × (Nat × Nat)
  | .node domain left right => ((unseen pairs domain).length,
      (weight left + weight right, if greater left right then 1 else 0))
  | .edge domain left right => ((unseen pairs domain).length, (edgeWeight weight left right, 0))

/-- Recursive control edges excluding the separately handled closed-environment reset. -/
inductive LocalStep (view : View Symbol) (pairs : List Pair) : Call Symbol → Call Symbol → Prop where
  | swap domain left right (larger : greater left right = true) :
      LocalStep view pairs (.node domain right left) (.node domain left right)
  | both domain first second (possible : pair (.mu first) (.mu second) ∈ pairs)
      (fresh : pair (.mu first) (.mu second) ∉ domain.seen) :
      LocalStep view pairs
        (.node (extend domain [(first, .mu first), (second, .mu second)] (pair (.mu first) (.mu second)))
          (view.body first) (view.body second))
        (.node domain (.mu first) (.mu second))
  | leftMu domain name right (possible : pair (.mu name) right ∈ pairs) (fresh : pair (.mu name) right ∉ domain.seen) :
      LocalStep view pairs (.node (extend domain [(name, .mu name)] (pair (.mu name) right)) (view.body name) right)
        (.node domain (.mu name) right)
  | rightMu domain left name (possible : pair left (.mu name) ∈ pairs) (fresh : pair left (.mu name) ∉ domain.seen) :
      LocalStep view pairs (.node (extend domain [(name, .mu name)] (pair left (.mu name))) left (view.body name))
        (.node domain left (.mu name))
  | leftUnion domain name right child (member : child ∈ view.members name) :
      LocalStep view pairs (.node domain child right) (.node domain (.union name) right)
  | rightUnion domain left name child (member : child ∈ view.members name) :
      LocalStep view pairs (.node domain left child) (.node domain left (.union name))
  | leftRef domain name right :
      LocalStep view pairs (.node domain (.mu name) right) (.node domain (.ref name) right)
  | rightRef domain left name :
      LocalStep view pairs (.node domain left (.mu name)) (.node domain left (.ref name))
  | nodeRows domain first second left right (leftMember : left ∈ view.rows first) (rightMember : right ∈ view.rows second) :
      LocalStep view pairs (.edge domain left right) (.node domain (.node first) (.node second))
  | edgeChild domain left right children (member : children ∈ left.children.zip right.children) :
      LocalStep view pairs (.node domain children.1 children.2) (.edge domain left right)

/-- Ordinary node descent reaches an edge phase below both parent constructors. -/
theorem row_weight_decreases (view : View Symbol) (weight : LocalWeight view) (first second : Nat)
    (left right : Row Symbol) (leftMember : left ∈ view.rows first) (rightMember : right ∈ view.rows second) :
    edgeWeight weight.value left right < weight.value (.node first) + weight.value (.node second) := by
  have firstPositive := weight.positive first
  have secondPositive := weight.positive second
  have bound := largest_le ((left.children.zip right.children).map fun children => weight.value children.1 + weight.value children.2)
    (weight.value (.node first) + weight.value (.node second) - 2) (by
      intro value member
      obtain ⟨children, present, rfl⟩ := List.mem_map.mp member
      have originals := List.of_mem_zip present
      have firstLess := weight.child first left leftMember children.1 originals.1
      have secondLess := weight.child second right rightMember children.2 originals.2
      omega)
  unfold edgeWeight
  omega

/-- Each source recursive call except reset decreases the explicit lexicographic measure. -/
theorem local_decreases (view : View Symbol) (pairs : List Pair) (weight : LocalWeight view)
    (child parent : Call Symbol) (step : LocalStep view pairs child parent) :
    Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt) (measure pairs weight.value child) (measure pairs weight.value parent) := by
  cases step with
  | swap domain left right larger =>
    apply Prod.Lex.right
    apply Prod.lex_def.mpr
    refine Or.inr ⟨Nat.add_comm _ _, ?_⟩
    simp [larger, greater_asymmetric left right larger]
  | both domain first second possible fresh =>
    exact Prod.Lex.left _ _ (unseen_decreases pairs domain _ _ possible fresh)
  | leftMu domain name right possible fresh =>
    exact Prod.Lex.left _ _ (unseen_decreases pairs domain _ _ possible fresh)
  | rightMu domain left name possible fresh =>
    exact Prod.Lex.left _ _ (unseen_decreases pairs domain _ _ possible fresh)
  | leftUnion domain name right child member =>
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.add_lt_add_right (weight.member name child member) _))
  | rightUnion domain left name child member =>
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.add_lt_add_left (weight.member name child member) _))
  | leftRef domain name right =>
    apply Prod.Lex.right
    apply Prod.Lex.left
    simp [weight.binder, weight.reference]
  | rightRef domain left name =>
    apply Prod.Lex.right
    apply Prod.Lex.left
    simp [weight.binder, weight.reference]
  | nodeRows domain first second left right leftMember rightMember =>
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (row_weight_decreases view weight first second left right leftMember rightMember))
  | edgeChild domain left right children member =>
    apply Prod.Lex.right
    apply Prod.Lex.left
    have bounded := largest_member ((left.children.zip right.children).map fun children => weight.value children.1 + weight.value children.2)
      (weight.value children.1 + weight.value children.2) (List.mem_map.mpr ⟨children, member, rfl⟩)
    change weight.value children.1 + weight.value children.2 < edgeWeight weight.value left right
    unfold edgeWeight
    omega

/-- No infinite source call chain can remain between closed-environment resets. -/
theorem local_wellFounded (view : View Symbol) (pairs : List Pair) (weight : LocalWeight view) :
    WellFounded (LocalStep view pairs) := by
  have lexicographic : WellFounded (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)) :=
    (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf
  exact Subrelation.wf (fun step => local_decreases view pairs weight _ _ step)
    (InvImage.wf (measure pairs weight.value) lexicographic)

end MicroCFTA.IntersectSchedule
