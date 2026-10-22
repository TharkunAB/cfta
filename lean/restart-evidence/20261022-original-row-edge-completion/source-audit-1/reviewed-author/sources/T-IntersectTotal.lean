import MicroCFTA.IntersectInput
import MicroCFTA.IntersectProgress

/-!
# Structural bounds for closed intersection subproblems

Payload containment decreases a finite structural size. A closed input can
reach only itself and smaller payloads, including after reference unfolding.
These are input representation properties. They do not mention intersection.
The schedule retains two closed roots until its next environment reset.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- Reachability follows input payloads and resolves each recursive identity. -/
inductive InputReach (view : View Symbol) (root : Input) : Input → Prop where
  | root : InputReach view root root
  | body (before : InputReach view root (.mu name)) : InputReach view root (view.body name)
  | child (before : InputReach view root (.node name)) (rowMember : row ∈ view.rows name)
      (childMember : child ∈ row.children) : InputReach view root child
  | member (before : InputReach view root (.union name)) (member : child ∈ view.members name) :
      InputReach view root child
  | reference (before : InputReach view root (.ref name)) : InputReach view root (.mu name)

/-- Reachable payloads retain the original input validity invariant. -/
theorem input_reach_valid (view : View Symbol) (inputs : FiniteInput view) (root input : Input)
    (valid : inputs.valid root) (reachable : InputReach view root input) : inputs.valid input := by
  induction reachable with
  | root => exact valid
  | body _ ih => exact inputs.body_valid _ ih
  | child _ rowMember childMember ih => exact inputs.row_valid _ ih _ rowMember _ childMember
  | member _ member ih => exact inputs.union_valid _ ih _ member
  | reference _ ih => exact inputs.reference_valid _ ih

/-- A closed root contains itself and strictly smaller reachable payloads. -/
def Below (size : Input → Nat) (root input : Input) : Prop := input = root ∨ size input < size root

/-- Finite source payload structure bounds all pairs and all closed reachable subgraphs. -/
structure InputBounds (view : View Symbol) (inputs : FiniteInput view) where
  pairs : List Pair
  pair_mem : ∀ left right, inputs.valid left → inputs.valid right → left ≠ .empty → right ≠ .empty → pair left right ∈ pairs
  localWeight : LocalWeight view
  size : Input → Nat
  body : ∀ name, inputs.valid (.mu name) → size (view.body name) < size (.mu name)
  child : ∀ name, inputs.valid (.node name) → ∀ row ∈ view.rows name, ∀ child ∈ row.children,
    size child < size (.node name)
  member : ∀ name, inputs.valid (.union name) → ∀ child ∈ view.members name, size child < size (.union name)
  closed_reach : ∀ root, inputs.valid root → closed view root = true → ∀ input,
    InputReach view root input → Below size root input

/-- One pair of closed inputs bounds the work before the next environment reset. -/
structure ClosedRoots (view : View Symbol) (inputs : FiniteInput view) where
  left : Input
  right : Input
  left_valid : inputs.valid left
  right_valid : inputs.valid right
  left_closed : closed view left = true
  right_closed : closed view right = true

/-- Swapping operands also swaps their independent closed roots. -/
def ClosedRoots.swap (roots : ClosedRoots view inputs) : ClosedRoots view inputs :=
  ⟨roots.right, roots.left, roots.right_valid, roots.left_valid, roots.right_closed, roots.left_closed⟩

/-- An input with no binder tag cannot be restored by a reference lookup. -/
def NotBinder (input : Input) : Prop := ∀ name, input ≠ .mu name

/-- Either references cannot restore the roots, or the source cutoff protects their pair. -/
def RootProtected (roots : ClosedRoots view inputs) (domain : Domain) : Prop :=
  (NotBinder roots.left ∧ NotBinder roots.right) ∨ pair roots.left roots.right ∈ domain.seen

/-- Initial work may precede insertion of the first root pair. -/
def RootStarted (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input) : Prop :=
  RootProtected roots domain ∨ (domain.free = [] ∧ domain.seen = [] ∧ left = roots.left ∧ right = roots.right)

/-- Local node calls preserve coverage, closed-root bounds, and cutoff protection. -/
structure NodeReady (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input) : Prop where
  left_reach : InputReach view roots.left left
  right_reach : InputReach view roots.right right
  domain_valid : ValidDomain view domain
  left_covered : Covers view domain left
  right_covered : Covers view domain right
  unchanged : left = roots.left → right = roots.right → domain.free = []
  started : RootStarted roots domain left right

/-- Row children are strict payload descendants of their closed roots. -/
structure EdgeReady (bounds : InputBounds view inputs) (roots : ClosedRoots view inputs)
    (domain : Domain) (left right : Row Symbol) : Prop where
  left_reach : ∀ child ∈ left.children, InputReach view roots.left child
  right_reach : ∀ child ∈ right.children, InputReach view roots.right child
  left_less : ∀ child ∈ left.children, bounds.size child < bounds.size roots.left
  right_less : ∀ child ∈ right.children, bounds.size child < bounds.size roots.right
  domain_valid : ValidDomain view domain
  left_covered : ∀ child ∈ left.children, Covers view domain child
  right_covered : ∀ child ∈ right.children, Covers view domain child
  protection : RootProtected roots domain

/-- Every closed pair starts with valid empty-domain invariants. -/
theorem roots_ready (view : View Symbol) (inputs : FiniteInput view) (roots : ClosedRoots view inputs) :
    NodeReady roots {} roots.left roots.right := by
  exact ⟨.root, .root, valid_empty view, closed_covered view {} roots.left roots.left_closed,
    closed_covered view {} roots.right roots.right_closed, by intros; rfl, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩

/-- A reachable input has size at most the size of its closed root. -/
theorem reach_size_le (bounds : InputBounds view inputs) (root input : Input)
    (valid : inputs.valid root) (isClosed : closed view root = true) (reachable : InputReach view root input) :
    bounds.size input ≤ bounds.size root := by
  rcases bounds.closed_reach root valid isClosed input reachable with rfl | less
  · exact Nat.le_refl _
  · exact Nat.le_of_lt less

/-- Reset strictly reduces the combined structural size of the two closed roots. -/
theorem reset_decreases (bounds : InputBounds view inputs) (roots : ClosedRoots view inputs)
    (domain : Domain) (left right : Input) (ready : NodeReady roots domain left right)
    (reset : (closed view left && closed view right && !domain.free.isEmpty) = true) :
    bounds.size left + bounds.size right < bounds.size roots.left + bounds.size roots.right := by
  have nonempty : domain.free ≠ [] := by
    intro empty
    simp [empty] at reset
  have one := bounds.closed_reach roots.left roots.left_valid roots.left_closed left ready.left_reach
  have two := bounds.closed_reach roots.right roots.right_valid roots.right_closed right ready.right_reach
  rcases one with sameLeft | lessLeft <;> rcases two with sameRight | lessRight
  · exact False.elim (nonempty (ready.unchanged sameLeft sameRight))
  · subst left; omega
  · subst right; omega
  · omega

/-- Enclosing pair protection survives every source binder extension. -/
theorem protected_extend (roots : ClosedRoots view inputs) (domain : Domain)
    (protection : RootProtected roots domain) (bindings : List (Nat × Input)) (key : Pair) :
    RootProtected roots (extend domain bindings key) := by
  rcases protection with nonbinders | seen
  · exact Or.inl nonbinders
  · exact Or.inr (List.mem_cons_of_mem _ seen)

/-- Opening an initial binder installs the root cutoff before any local descent. -/
theorem started_extend (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input)
    (started : RootStarted roots domain left right) (bindings : List (Nat × Input)) :
    RootProtected roots (extend domain bindings (pair left right)) := by
  rcases started with protection | ⟨_, _, rfl, rfl⟩
  · exact protected_extend roots domain protection bindings _
  · exact Or.inr (List.mem_cons_self ..)

/-- A branch that excludes both binder tags already protects its closed roots. -/
theorem started_nonbinders (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input)
    (started : RootStarted roots domain left right) (leftNot : NotBinder left) (rightNot : NotBinder right) :
    RootProtected roots domain := by
  rcases started with protection | ⟨_, _, rfl, rfl⟩
  · exact protection
  · exact Or.inl ⟨leftNot, rightNot⟩

/-- A fresh reference lookup cannot restore both protected roots. -/
theorem protected_reference_left (roots : ClosedRoots view inputs) (domain : Domain) (name : Nat) (right : Input)
    (protection : RootProtected roots domain) (fresh : pair (.ref name) right ∉ domain.seen) :
    ¬ (Input.mu name = roots.left ∧ right = roots.right) := by
  rintro ⟨same, rfl⟩
  rcases protection with nonbinders | seen
  · exact nonbinders.1 name same.symm
  · apply fresh
    simpa only [← same, pair, identity] using seen

/-- A smaller direct payload cannot equal its closed root. -/
theorem payload_ne_root (bounds : InputBounds view inputs) (root input child : Input)
    (valid : inputs.valid root) (isClosed : closed view root = true)
    (reachable : InputReach view root input) (smaller : bounds.size child < bounds.size input) : child ≠ root := by
  have bound := reach_size_le bounds root input valid isClosed reachable
  intro same
  subst child
  omega

/-- A local call after strict descent retains all required node invariants. -/
theorem ready_descend (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input)
    (leftReach : InputReach view roots.left left) (rightReach : InputReach view roots.right right)
    (valid : ValidDomain view domain) (leftCovered : Covers view domain left) (rightCovered : Covers view domain right)
    (protection : RootProtected roots domain) (changed : ¬ (left = roots.left ∧ right = roots.right)) :
    NodeReady roots domain left right :=
  ⟨leftReach, rightReach, valid, leftCovered, rightCovered,
    fun sameLeft sameRight => False.elim (changed ⟨sameLeft, sameRight⟩), Or.inl protection⟩

/-- Pair protection is invariant under canonical operand exchange. -/
theorem protected_swap (roots : ClosedRoots view inputs) (domain : Domain)
    (protection : RootProtected roots domain) : RootProtected roots.swap domain := by
  rcases protection with notBinders | seen
  · exact Or.inl notBinders.symm
  · exact Or.inr (by simpa [ClosedRoots.swap, pair_symmetric] using seen)

/-- Canonical operand exchange preserves all local node invariants. -/
theorem ready_swap (roots : ClosedRoots view inputs) (domain : Domain) (left right : Input)
    (ready : NodeReady roots domain left right) : NodeReady roots.swap domain right left := by
  refine ⟨ready.right_reach, ready.left_reach, ready.domain_valid, ready.right_covered, ready.left_covered,
    fun one two => ready.unchanged two one, ?_⟩
  rcases ready.started with protection | ⟨free, seen, one, two⟩
  · exact Or.inl (protected_swap roots domain protection)
  · exact Or.inr ⟨free, seen, two, one⟩

/-- Complete row construction retains strict child descent from both closed roots. -/
theorem ready_rows (view : View Symbol) (inputs : FiniteInput view) (freeCorrect : FreeCorrect view)
    (bounds : InputBounds view inputs) (roots : ClosedRoots view inputs) (domain : Domain)
    (first second : Nat) (ready : NodeReady roots domain (.node first) (.node second))
    (left right : Row Symbol) (leftMember : left ∈ view.rows first) (rightMember : right ∈ view.rows second) :
    EdgeReady bounds roots domain left right := by
  have firstValid := input_reach_valid view inputs roots.left _ roots.left_valid ready.left_reach
  have secondValid := input_reach_valid view inputs roots.right _ roots.right_valid ready.right_reach
  exact ⟨fun child member => .child ready.left_reach leftMember member,
    fun child member => .child ready.right_reach rightMember member,
    fun child member => Nat.lt_of_lt_of_le (bounds.child first firstValid left leftMember child member)
      (reach_size_le bounds roots.left _ roots.left_valid roots.left_closed ready.left_reach),
    fun child member => Nat.lt_of_lt_of_le (bounds.child second secondValid right rightMember child member)
      (reach_size_le bounds roots.right _ roots.right_valid roots.right_closed ready.right_reach),
    ready.domain_valid,
    fun child member => node_child_covered view freeCorrect domain first left leftMember child member ready.left_covered,
    fun child member => node_child_covered view freeCorrect domain second right rightMember child member ready.right_covered,
    started_nonbinders roots domain _ _ ready.started (by intro name same; cases same) (by intro name same; cases same)⟩

/-- Ordered child pairing gives one ready recursive call at each position. -/
theorem ready_child (bounds : InputBounds view inputs) (roots : ClosedRoots view inputs) (domain : Domain)
    (left right : Row Symbol) (ready : EdgeReady bounds roots domain left right) (children : Input × Input)
    (member : children ∈ left.children.zip right.children) : NodeReady roots domain children.1 children.2 := by
  have originals := List.of_mem_zip member
  apply ready_descend roots domain _ _ (ready.left_reach _ originals.1) (ready.right_reach _ originals.2)
    ready.domain_valid (ready.left_covered _ originals.1) (ready.right_covered _ originals.2) ready.protection
  rintro ⟨same, _⟩
  have less := ready.left_less _ originals.1
  rw [same] at less
  exact Nat.lt_irrefl _ less

/-- One successful result is stable at every sufficiently large execution bound. -/
def IntersectEventually (action : Nat → Except Error α) : Prop :=
  ∃ bound value, ∀ fuel, bound ≤ fuel → action fuel = .ok value

/-- A successful constant branch needs no recursive fuel. -/
theorem intersect_eventually_pure (value : α) : IntersectEventually (fun _ => (.ok value : Except Error α)) :=
  ⟨0, value, fun _ _ => rfl⟩

/-- Mapping a successful recursive result preserves its sufficient bound. -/
theorem intersect_eventually_map (action : Nat → Except Error α) (convert : α → β)
    (total : IntersectEventually action) : IntersectEventually (fun fuel => (action fuel).map convert) := by
  obtain ⟨bound, value, result⟩ := total
  exact ⟨bound, convert value, fun fuel enough => by dsimp only; rw [result fuel enough]; rfl⟩

/-- A finite ordered traversal has one bound sufficient for all its recursive calls. -/
theorem intersect_eventually_walk (action : Nat → α → Except Error β) (input : List α)
    (total : ∀ item ∈ input, IntersectEventually (fun fuel => action fuel item)) :
    IntersectEventually (fun fuel => walk (action fuel) input) := by
  induction input with
  | nil => exact ⟨0, [], fun _ _ => rfl⟩
  | cons first rest ih =>
    obtain ⟨headBound, value, headResult⟩ := total first (by simp)
    obtain ⟨tailBound, values, tailResult⟩ := ih (fun item member => total item (by simp [member]))
    refine ⟨max headBound tailBound, value :: values, ?_⟩
    intro fuel enough
    simp [walk, headResult fuel (by omega), tailResult fuel (by omega), Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- One source frame adds one to the sufficient recursive bound. -/
theorem intersect_eventually_succ (action : Nat → Except Error α)
    (total : IntersectEventually (fun fuel => action (fuel + 1))) : IntersectEventually action := by
  obtain ⟨bound, value, result⟩ := total
  refine ⟨bound + 1, value, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel => exact result fuel (by omega)

/-- Execute either worker with one common fuel interface. -/
def execute [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) : Call Symbol → Except Error (Shape (Payload Symbol))
  | .node domain left right => run view fuel domain left right
  | .edge domain left right => edge view fuel domain left right

/-- Each worker carries the structural invariants appropriate to its payload. -/
def WorkReady (bounds : InputBounds view inputs) (roots : ClosedRoots view inputs) : Call Symbol → Prop
  | .node domain left right => NodeReady roots domain left right
  | .edge domain left right => EdgeReady bounds roots domain left right

/-- Every covered source call eventually returns under finite closed-payload bounds. -/
theorem call_eventual [DecidableEq Symbol] (view : View Symbol) (inputs : FiniteInput view)
    (freeCorrect : FreeCorrect view) (bounds : InputBounds view inputs)
    (roots : ClosedRoots view inputs) (call : Call Symbol) (ready : WorkReady bounds roots call) :
    IntersectEventually (fun fuel => execute view fuel call) := by
  cases call with
  | node domain left right =>
    change NodeReady roots domain left right at ready
    change IntersectEventually (fun fuel => run view fuel domain left right)
    apply intersect_eventually_succ
    conv => arg 1; ext fuel; rw [run.eq_def]
    dsimp only
    by_cases empty : left = .empty ∨ right = .empty
    · simp only [ite_eq_left empty]
      exact intersect_eventually_pure _
    simp only [ite_eq_right empty]
    have leftNonempty : left ≠ .empty := fun same => empty (Or.inl same)
    have rightNonempty : right ≠ .empty := fun same => empty (Or.inr same)
    have leftValid := input_reach_valid view inputs roots.left left roots.left_valid ready.left_reach
    have rightValid := input_reach_valid view inputs roots.right right roots.right_valid ready.right_reach
    by_cases reset : (closed view left && closed view right && !domain.free.isEmpty) = true
    · simp only [ite_eq_left reset]
      have isClosed : closed view left = true ∧ closed view right = true := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at reset
        exact reset.1
      let nextRoots : ClosedRoots view inputs := ⟨left, right, leftValid, rightValid, isClosed.1, isClosed.2⟩
      have resetLess := reset_decreases bounds roots domain left right ready reset
      exact call_eventual view inputs freeCorrect bounds nextRoots (.node {} left right) (roots_ready view inputs nextRoots)
    simp only [ite_eq_right reset]
    by_cases same : left = right ∧ closed view left = true
    · simp only [ite_eq_left same]
      exact intersect_eventually_pure _
    simp only [ite_eq_right same]
    by_cases swap : greater left right = true
    · simp only [ite_eq_left swap]
      have localStep : LocalStep view bounds.pairs (.node domain right left) (.node domain left right) := .swap domain left right swap
      exact call_eventual view inputs freeCorrect bounds roots.swap (.node domain right left) (ready_swap roots domain left right ready)
    simp only [ite_eq_right swap]
    by_cases seen : pair left right ∈ domain.seen
    · simp only [ite_eq_left seen]
      exact intersect_eventually_pure _
    simp only [ite_eq_right seen]
    have possible := bounds.pair_mem left right leftValid rightValid leftNonempty rightNonempty
    split
    · next first second =>
      apply intersect_eventually_map
      have nextReady : NodeReady roots (extend domain [(first, .mu first), (second, .mu second)] (pair (.mu first) (.mu second)))
          (view.body first) (view.body second) := by
        apply ready_descend roots _ _ _ (.body ready.left_reach) (.body ready.right_reach)
          (valid_extend view domain [first, second] _ ready.domain_valid (by
            intro name member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact ready.left_covered
            · exact ready.right_covered))
          (binder_body_covered view freeCorrect domain [first, second] _ first (by simp) ready.left_covered)
          (binder_body_covered view freeCorrect domain [first, second] _ second (by simp) ready.right_covered)
          (started_extend roots domain _ _ ready.started _)
        rintro ⟨same, _⟩
        exact payload_ne_root bounds roots.left (.mu first) _ roots.left_valid roots.left_closed ready.left_reach
          (bounds.body first leftValid) same
      have localStep := LocalStep.both (view := view) domain first second possible seen
      exact call_eventual view inputs freeCorrect bounds roots (.node _ _ _) nextReady
    · next name _ =>
      apply intersect_eventually_map
      have nextReady : NodeReady roots (extend domain [(name, .mu name)] (pair (.mu name) right)) (view.body name) right := by
        apply ready_descend roots _ _ _ (.body ready.left_reach) ready.right_reach
          (valid_extend view domain [name] _ ready.domain_valid (by
            intro found member; have equal : found = name := by simpa using member
            subst found; exact ready.left_covered))
          (binder_body_covered view freeCorrect domain [name] _ name (by simp) ready.left_covered)
          (covers_extend view domain [name] _ right ready.right_covered)
          (started_extend roots domain _ _ ready.started _)
        rintro ⟨same, _⟩
        exact payload_ne_root bounds roots.left (.mu name) _ roots.left_valid roots.left_closed ready.left_reach
          (bounds.body name leftValid) same
      have localStep := LocalStep.leftMu (view := view) domain name right possible seen
      exact call_eventual view inputs freeCorrect bounds roots (.node _ _ _) nextReady
    · next name _ =>
      apply intersect_eventually_map
      have nextReady : NodeReady roots (extend domain [(name, .mu name)] (pair left (.mu name))) left (view.body name) := by
        apply ready_descend roots _ _ _ ready.left_reach (.body ready.right_reach)
          (valid_extend view domain [name] _ ready.domain_valid (by
            intro found member; have equal : found = name := by simpa using member
            subst found; exact ready.right_covered))
          (covers_extend view domain [name] _ left ready.left_covered)
          (binder_body_covered view freeCorrect domain [name] _ name (by simp) ready.right_covered)
          (started_extend roots domain _ _ ready.started _)
        rintro ⟨_, same⟩
        exact payload_ne_root bounds roots.right (.mu name) _ roots.right_valid roots.right_closed ready.right_reach
          (bounds.body name rightValid) same
      have localStep := LocalStep.rightMu (view := view) domain left name possible seen
      exact call_eventual view inputs freeCorrect bounds roots (.node _ _ _) nextReady
    · next name excluded =>
      apply intersect_eventually_map
      apply intersect_eventually_walk
      intro child member
      have protection := started_nonbinders roots domain (.union name) right ready.started
        (by intro binder same; cases same) (by intro binder same; subst right; simp_all)
      have nextReady : NodeReady roots domain child right := by
        apply ready_descend roots domain child right (.member ready.left_reach member) ready.right_reach ready.domain_valid
          (union_member_covered view freeCorrect domain name child member ready.left_covered) ready.right_covered protection
        rintro ⟨same, _⟩
        exact payload_ne_root bounds roots.left (.union name) child roots.left_valid roots.left_closed ready.left_reach
          (bounds.member name leftValid child member) same
      have localStep := LocalStep.leftUnion (view := view) (pairs := bounds.pairs) domain name right child member
      exact call_eventual view inputs freeCorrect bounds roots (.node _ _ _) nextReady
    · next name excluded excludedUnion =>
      apply intersect_eventually_map
      apply intersect_eventually_walk
      intro child member
      have protection := started_nonbinders roots domain left (.union name) ready.started
        (by intro binder same; subst left; simp_all) (by intro binder same; cases same)
      have nextReady : NodeReady roots domain left child := by
        apply ready_descend roots domain left child ready.left_reach (.member ready.right_reach member) ready.domain_valid
          ready.left_covered (union_member_covered view freeCorrect domain name child member ready.right_covered) protection
        rintro ⟨_, same⟩
        exact payload_ne_root bounds roots.right (.union name) child roots.right_valid roots.right_closed ready.right_reach
          (bounds.member name rightValid child member) same
      have localStep := LocalStep.rightUnion (view := view) (pairs := bounds.pairs) domain left name child member
      exact call_eventual view inputs freeCorrect bounds roots (.node _ _ _) nextReady
    · next name excluded excludedUnion =>
      have found := reference_resolves view freeCorrect domain name ready.left_covered
      simp only [found]
      have protection := started_nonbinders roots domain (.ref name) right ready.started
        (by intro binder same; cases same) (by intro binder same; subst right; simp_all)
      have nextReady : NodeReady roots domain (.mu name) right :=
        ready_descend roots domain _ _ (.reference ready.left_reach) ready.right_reach ready.domain_valid
          (ready.domain_valid.closed name found) ready.right_covered protection
          (protected_reference_left roots domain name right protection seen)
      have localStep := LocalStep.leftRef (view := view) (pairs := bounds.pairs) domain name right
      exact call_eventual view inputs freeCorrect bounds roots (.node _ _ _) nextReady
    · next name excluded excludedUnion excludedRef =>
      have found := reference_resolves view freeCorrect domain name ready.right_covered
      simp only [found]
      have protection := started_nonbinders roots domain left (.ref name) ready.started
        (by intro binder same; subst left; simp_all) (by intro binder same; cases same)
      have changed : ¬ (left = roots.left ∧ Input.mu name = roots.right) := by
        rintro ⟨one, two⟩
        exact protected_reference_left roots.swap domain name left (protected_swap roots domain protection)
          (by simpa [pair_symmetric] using seen) ⟨two, one⟩
      have nextReady : NodeReady roots domain left (.mu name) :=
        ready_descend roots domain _ _ ready.left_reach (.reference ready.right_reach) ready.domain_valid
          ready.left_covered (ready.domain_valid.closed name found) protection changed
      have localStep := LocalStep.rightRef (view := view) (pairs := bounds.pairs) domain left name
      exact call_eventual view inputs freeCorrect bounds roots (.node _ _ _) nextReady
    · next first second =>
      apply intersect_eventually_map
      apply intersect_eventually_walk
      intro rows member
      have originals := joined_members (view.rows first) (view.rows second) rows member
      have nextReady := ready_rows view inputs freeCorrect bounds roots domain first second ready rows.1 rows.2 originals.1 originals.2
      have localStep := LocalStep.nodeRows (view := view) (pairs := bounds.pairs) domain first second rows.1 rows.2 originals.1 originals.2
      exact call_eventual view inputs freeCorrect bounds roots (.edge _ _ _) nextReady
    · exact False.elim (leftNonempty rfl)
    · exact False.elim (rightNonempty rfl)
  | edge domain left right =>
    change EdgeReady bounds roots domain left right at ready
    change IntersectEventually (fun fuel => edge view fuel domain left right)
    apply intersect_eventually_succ
    conv => arg 1; ext fuel; rw [edge.eq_def]
    dsimp only
    by_cases arity : left.children.length ≠ right.children.length
    · simp only [ite_eq_left arity]
      exact intersect_eventually_pure _
    simp only [ite_eq_right arity]
    apply intersect_eventually_map
    apply intersect_eventually_walk
    intro children member
    have nextReady := ready_child bounds roots domain left right ready children member
    have localStep := LocalStep.edgeChild (view := view) (pairs := bounds.pairs) domain left right children member
    exact call_eventual view inputs freeCorrect bounds roots (.node _ _ _) nextReady
termination_by (bounds.size roots.left + bounds.size roots.right, measure bounds.pairs bounds.localWeight.value call)
decreasing_by
  all_goals simp_all only [ClosedRoots.swap]
  all_goals first
    | exact Prod.Lex.left _ _ resetLess
    | apply Prod.lex_def.mpr
      exact Or.inr ⟨by simp [Nat.add_comm],
        local_decreases view bounds.pairs bounds.localWeight _ _ localStep⟩

/-- Closed finite inputs have one stable exact result at every sufficiently large bound. -/
theorem finite_intersection_total [DecidableEq Symbol] (view : View Symbol) (inputs : FiniteInput view)
    (freeCorrect : FreeCorrect view) (bounds : InputBounds view inputs)
    (left right : Input) (leftValid : inputs.valid left) (rightValid : inputs.valid right)
    (leftClosed : closed view left = true) (rightClosed : closed view right = true) :
    ∃ bound result,
      (∀ fuel, bound ≤ fuel → run view fuel {} left right = .ok result) ∧
      ∀ environment term, meaning environment result term ↔
        (∃ rank, InputDerivation view left rank term) ∧ (∃ rank, InputDerivation view right rank term) := by
  let roots : ClosedRoots view inputs := ⟨left, right, leftValid, rightValid, leftClosed, rightClosed⟩
  obtain ⟨bound, result, completed⟩ :=
    call_eventual view inputs freeCorrect bounds roots (.node {} left right) (roots_ready view inputs roots)
  refine ⟨bound, result, completed, ?_⟩
  intro environment term
  exact finite_intersection_exact view inputs bound left right leftValid rightValid result
    (completed bound (Nat.le_refl _)) environment term

end MicroCFTA.IntersectSchedule
