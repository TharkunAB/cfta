import MicroCFTA.PruneCandidates
import MicroCFTA.BinderSubstitution

/-!
# Successful recursive pruning preserves languages

This proof follows every branch of the executable source schedule. It derives
cache validity, child correspondence, and complete edge-list preservation.
Its premises concern individual representation operations and the semantic
query pass. They do not assume a result for recursive pruning itself.
-/
namespace MicroCFTA.PruneCorrectness
open Language PruneSchedule PruneCandidates
variable {Node Edge Value : Type}

/-- Two nodes denote the same concrete terms. Values can include a free-variable environment. -/
def Equivalent (meaning : Node → Value → Prop) (left right : Node) : Prop :=
  ∀ value, meaning left value ↔ meaning right value

/-- Every stored identity result has the complete language of its original node. -/
def CacheValid (meaning : Node → Value → Prop) (build : Build Node) : Prop :=
  ∀ entry ∈ build.cache, Equivalent meaning entry.1 entry.2

/-- The newest cached entry is an actual entry in the identity table. -/
theorem lookup_member [DecidableEq Node] (key value : Node) (cache : List (Node × Node))
    (found : lookup key cache = some value) : (key, value) ∈ cache := by
  induction cache with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
      rcases entry with ⟨other, stored⟩
      by_cases same : key = other
      · subst other
        have equal : stored = value := by simpa [lookup] using found
        subst value
        simp
      · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, same] using found))

/-- A cache hit inherits the invariant already proved when that answer was inserted. -/
theorem lookup_valid [DecidableEq Node] (meaning : Node → Value → Prop) (build : Build Node)
    (valid : CacheValid meaning build) (key value : Node) (found : lookup key build.cache = some value) :
    Equivalent meaning key value := valid (key, value) (lookup_member key value build.cache found)

/-- Writing a proved result preserves every old cached equivalence. -/
theorem insert_valid (meaning : Node → Value → Prop) (build : Build Node) (valid : CacheValid meaning build)
    (key value : Node) (same : Equivalent meaning key value) :
    CacheValid meaning {build with cache := (key, value) :: build.cache} := by
  intro entry member
  rcases List.mem_cons.mp member with rfl | previous
  · exact same
  · exact valid entry previous

/-- Local representation and query laws needed by the source driver. -/
structure Laws (ops : Operations Node Edge) (meaning : Node → Value → Prop) (edgeMeaning : Edge → Value → Prop) : Prop where
  branches : ∀ node edges, ops.view node = .branches edges → ∀ value,
    meaning node value ↔ Denotes edgeMeaning edges value
  node : ∀ edges value, meaning (ops.node edges) value ↔ Denotes edgeMeaning edges value
  unionView : ∀ node members, ops.view node = .union members → ∀ value,
    meaning node value ↔ Denotes meaning members value
  union : ∀ members value, meaning (ops.union members) value ↔ Denotes meaning members value
  replaceChildren : ∀ edge children, All₂ (Equivalent meaning) (ops.children edge) children → ∀ value,
    edgeMeaning (ops.replaceChildren edge children) value ↔ edgeMeaning edge value
  narrow : ∀ edge value, edgeMeaning (ops.narrow edge) value ↔ edgeMeaning edge value
  emptyChild : ∀ edge, (ops.children edge).any ops.empty = true → ∀ value, ¬ edgeMeaning edge value
  binder : ∀ node body pruned, ops.view node = .binder body → Equivalent meaning body pruned →
    Equivalent meaning node (ops.rebuildBinder node pruned)
  evaluate : ∀ build edge retained next, ops.evaluate build edge = .ok (retained, next) →
    (∀ value, Denotes edgeMeaning retained value ↔ edgeMeaning edge value) ∧ next.cache = build.cache

/-- Pointwise node equivalence preserves union members, including their order and multiplicity. -/
theorem union_members (meaning : Node → Value → Prop) (left right : List Node)
    (same : All₂ (Equivalent meaning) left right) (value : Value) :
    Denotes meaning left value ↔ Denotes meaning right value := by
  induction same with
  | nil => simp [Denotes]
  | @cons first second left right head tail ih =>
      simp only [Denotes, List.mem_cons] at ih ⊢
      constructor
      · rintro ⟨node, rfl | member, accepted⟩
        · exact ⟨second, .inl rfl, (head value).mp accepted⟩
        · obtain ⟨node, member, accepted⟩ := ih.mp ⟨node, member, accepted⟩
          exact ⟨node, .inr member, accepted⟩
      · rintro ⟨node, rfl | member, accepted⟩
        · exact ⟨first, .inl rfl, (head value).mpr accepted⟩
        · obtain ⟨node, member, accepted⟩ := ih.mpr ⟨node, member, accepted⟩
          exact ⟨node, .inr member, accepted⟩

/-- A list union is the disjunction of its prefix and suffix languages. -/
theorem denotes_append (meaning : Edge → Value → Prop) (left right : List Edge) (value : Value) :
    Denotes meaning (left ++ right) value ↔ Denotes meaning left value ∨ Denotes meaning right value := by
  simp [Denotes, List.mem_append, or_and_right, exists_or]

/-- A successful source schedule preserves every node, child list, edge list, and cached identity. -/
theorem schedule_exact [DecidableEq Node] (ops : Operations Node Edge) (meaning : Node → Value → Prop)
    (edgeMeaning : Edge → Value → Prop) (laws : Laws ops meaning edgeMeaning) (fuel : Nat) :
    (∀ build node result next, CacheValid meaning build → pruneNode ops fuel build node = .ok (result, next) →
      Equivalent meaning node result ∧ CacheValid meaning next) ∧
    (∀ build children result next, CacheValid meaning build → pruneChildren ops fuel build children = .ok (result, next) →
      All₂ (Equivalent meaning) children result ∧ CacheValid meaning next) ∧
    (∀ build edges result next, CacheValid meaning build → pruneEdges ops fuel build edges = .ok (result, next) →
      (∀ value, Denotes edgeMeaning edges value ↔ Denotes edgeMeaning result value) ∧ CacheValid meaning next) := by
  induction fuel with
  | zero => exact ⟨by simp [pruneNode], by simp [pruneChildren], by simp [pruneEdges]⟩
  | succ fuel ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro build node result next valid success
        cases view : ops.view node with
        | empty =>
            simp [pruneNode, view] at success
            rcases success with ⟨rfl, rfl⟩
            exact ⟨fun _ => Iff.rfl, valid⟩
        | reference =>
            simp [pruneNode, view] at success
            rcases success with ⟨rfl, rfl⟩
            exact ⟨fun _ => Iff.rfl, valid⟩
        | branches edges =>
            cases found : lookup node build.cache with
            | some known =>
                simp [pruneNode, view, found] at success
                rcases success with ⟨rfl, rfl⟩
                exact ⟨lookup_valid meaning build valid node known found, valid⟩
            | none =>
                cases pass : pruneEdges ops fuel build edges with
                | error failure => simp [Bind.bind, Except.bind, pruneNode, view, found, pass] at success
                | ok pair =>
                    rcases pair with ⟨retained, last⟩
                    simp [Bind.bind, Except.bind, pruneNode, view, found, pass] at success
                    rcases success with ⟨rfl, rfl⟩
                    have edgesCorrect := ih.2.2 build edges retained last valid pass
                    have same : Equivalent meaning node (ops.node retained) := fun value =>
                      (laws.branches node edges view value).trans ((edgesCorrect.1 value).trans (laws.node retained value).symm)
                    exact ⟨same, insert_valid meaning last edgesCorrect.2 node (ops.node retained) same⟩
        | union members =>
            cases found : lookup node build.cache with
            | some known =>
                simp [pruneNode, view, found] at success
                rcases success with ⟨rfl, rfl⟩
                exact ⟨lookup_valid meaning build valid node known found, valid⟩
            | none =>
                cases pass : pruneChildren ops fuel build members with
                | error failure => simp [Bind.bind, Except.bind, pruneNode, view, found, pass] at success
                | ok pair =>
                    rcases pair with ⟨retained, last⟩
                    simp [Bind.bind, Except.bind, pruneNode, view, found, pass] at success
                    rcases success with ⟨rfl, rfl⟩
                    have childrenCorrect := ih.2.1 build members retained last valid pass
                    have same : Equivalent meaning node (ops.union retained) := fun value =>
                      (laws.unionView node members view value).trans
                        ((union_members meaning members retained childrenCorrect.1 value).trans (laws.union retained value).symm)
                    exact ⟨same, insert_valid meaning last childrenCorrect.2 node (ops.union retained) same⟩
        | binder body =>
            cases found : lookup node build.cache with
            | some known =>
                simp [pruneNode, view, found] at success
                rcases success with ⟨rfl, rfl⟩
                exact ⟨lookup_valid meaning build valid node known found, valid⟩
            | none =>
                cases pass : pruneNode ops fuel {build with binders := node :: build.binders} body with
                | error failure => simp [Bind.bind, Except.bind, pruneNode, view, found, pass] at success
                | ok pair =>
                    rcases pair with ⟨pruned, last⟩
                    have bodyCorrect := ih.1 {build with binders := node :: build.binders} body pruned last valid pass
                    have rebuiltCorrect := laws.binder node body pruned view bodyCorrect.1
                    by_cases fixed : ops.rebuildBinder node pruned = node
                    · simp [Bind.bind, Except.bind, pruneNode, view, found, pass, fixed] at success
                      rcases success with ⟨rfl, rfl⟩
                      exact ⟨fun _ => Iff.rfl, insert_valid meaning last bodyCorrect.2 node node (fun _ => Iff.rfl)⟩
                    · cases rerun : pruneNode ops fuel last (ops.rebuildBinder node pruned) with
                      | error failure => simp [Bind.bind, Except.bind, pruneNode, view, found, pass, fixed, rerun] at success
                      | ok pair =>
                          rcases pair with ⟨finalNode, finalBuild⟩
                          simp [Bind.bind, Except.bind, pruneNode, view, found, pass, fixed, rerun] at success
                          rcases success with ⟨rfl, rfl⟩
                          have rerunCorrect := ih.1 last _ finalNode finalBuild bodyCorrect.2 rerun
                          have same : Equivalent meaning node finalNode := fun value =>
                            (rebuiltCorrect value).trans (rerunCorrect.1 value)
                          exact ⟨same, insert_valid meaning finalBuild rerunCorrect.2 node finalNode same⟩
      · intro build children result next valid success
        cases children with
        | nil =>
            simp [pruneChildren] at success
            rcases success with ⟨rfl, rfl⟩
            exact ⟨.nil, valid⟩
        | cons child rest =>
            cases first : pruneNode ops fuel build child with
            | error failure => simp [Bind.bind, Except.bind, pruneChildren, first] at success
            | ok pair =>
                rcases pair with ⟨pruned, middle⟩
                cases tail : pruneChildren ops fuel middle rest with
                | error failure => simp [Bind.bind, Except.bind, pruneChildren, first, tail] at success
                | ok pair =>
                    rcases pair with ⟨prunedRest, last⟩
                    simp [Bind.bind, Except.bind, pruneChildren, first, tail] at success
                    rcases success with ⟨rfl, rfl⟩
                    have headCorrect := ih.1 build child pruned middle valid first
                    have tailCorrect := ih.2.1 middle rest prunedRest last headCorrect.2 tail
                    exact ⟨.cons headCorrect.1 tailCorrect.1, tailCorrect.2⟩
      · intro build edges result next valid success
        cases edges with
        | nil =>
            simp [pruneEdges] at success
            rcases success with ⟨rfl, rfl⟩
            exact ⟨fun _ => Iff.rfl, valid⟩
        | cons edge rest =>
            cases children : pruneChildren ops fuel build (ops.children edge) with
            | error failure => simp [Bind.bind, Except.bind, pruneEdges, children] at success
            | ok pair =>
                rcases pair with ⟨pruned, middle⟩
                have childrenCorrect := ih.2.1 build (ops.children edge) pruned middle valid children
                let narrowed := ops.narrow (ops.replaceChildren edge pruned)
                have narrowedCorrect (value : Value) : edgeMeaning narrowed value ↔ edgeMeaning edge value :=
                  (laws.narrow _ value).trans (laws.replaceChildren edge pruned childrenCorrect.1 value)
                cases empty : (ops.children narrowed).any ops.empty with
                | true =>
                    cases tail : pruneEdges ops fuel middle rest with
                    | error failure => simp [Bind.bind, Except.bind, pruneEdges, children, narrowed, empty, tail] at success
                    | ok pair =>
                        rcases pair with ⟨retained, last⟩
                        simp [Bind.bind, Except.bind, pruneEdges, children, narrowed, empty, tail] at success
                        rcases success with ⟨rfl, rfl⟩
                        have tailCorrect := ih.2.2 middle rest retained last childrenCorrect.2 tail
                        refine ⟨?_, tailCorrect.2⟩
                        intro value
                        have absent : ¬ edgeMeaning edge value := fun accepted =>
                          laws.emptyChild narrowed empty value ((narrowedCorrect value).mpr accepted)
                        simpa [Denotes, absent] using tailCorrect.1 value
                | false =>
                    cases evaluated : ops.evaluate middle narrowed with
                    | error failure => simp [Bind.bind, Except.bind, pruneEdges, children, narrowed, empty, evaluated] at success
                    | ok pair =>
                        rcases pair with ⟨retained, observed⟩
                        have semanticCorrect := laws.evaluate middle narrowed retained observed evaluated
                        have observedValid : CacheValid meaning observed := by
                          intro entry present
                          exact childrenCorrect.2 entry (by simpa [semanticCorrect.2] using present)
                        cases tail : pruneEdges ops fuel observed rest with
                        | error failure => simp [Bind.bind, Except.bind, pruneEdges, children, narrowed, empty, evaluated, tail] at success
                        | ok pair =>
                            rcases pair with ⟨suffix, last⟩
                            simp [Bind.bind, Except.bind, pruneEdges, children, narrowed, empty, evaluated, tail] at success
                            rcases success with ⟨rfl, rfl⟩
                            have tailCorrect := ih.2.2 observed rest suffix last observedValid tail
                            refine ⟨?_, tailCorrect.2⟩
                            intro value
                            rw [denotes_append, semanticCorrect.1, narrowedCorrect, ← tailCorrect.1]
                            simp [Denotes]

/-- Starting with an empty identity cache establishes the complete successful-driver theorem. -/
theorem prune_exact [DecidableEq Node] (ops : Operations Node Edge) (meaning : Node → Value → Prop)
    (edgeMeaning : Edge → Value → Prop) (laws : Laws ops meaning edgeMeaning) (fuel : Nat)
    (node result : Node) (next : Build Node) (success : pruneNode ops fuel {} node = .ok (result, next)) :
    Equivalent meaning node result ∧ CacheValid meaning next :=
  (schedule_exact ops meaning edgeMeaning laws fuel).1 {} node result next (by intro entry member; cases member) success


/-- Open shape equivalence quantifies over every interpretation of free recursive names. -/
def shapeMeaning (shape : Binding.Shape (BinderLanguage.Payload Symbol))
    (value : BinderLanguage.Env Symbol × Language.Term Symbol) : Prop := BinderLanguage.meaning value.1 shape value.2

/-- The recursive rebuilding law follows from least-language congruence and the actual binder cleanup. -/
theorem binder_rebuild_exact (name : Nat) (body pruned : Binding.Shape (BinderLanguage.Payload Symbol))
    (same : Equivalent shapeMeaning body pruned) :
    Equivalent shapeMeaning (.binder name body) (BinderLanguage.cleanup (.binder name pruned)) := by
  intro value
  unfold shapeMeaning
  rw [BinderLanguage.cleanup_exact]
  simp only [BinderLanguage.meaning]
  have equal := BinderLanguage.least_congr
    (fun language => BinderLanguage.meaning (BinderLanguage.bind value.1 name language) body)
    (fun language => BinderLanguage.meaning (BinderLanguage.bind value.1 name language) pruned)
    (fun language term => same (BinderLanguage.bind value.1 name language, term))
  rw [equal]

/-- Equality under one chosen environment is insufficient for recursive body replacement. -/
theorem binder_needs_uniform_body :
    let leaf : Binding.Shape (BinderLanguage.Payload Nat) := .branch ⟨0, fun _ => True⟩ []
    let environment : BinderLanguage.Env Nat := fun _ => BinderLanguage.meaning (fun _ _ => False) leaf
    (∀ term, BinderLanguage.meaning environment (.ref 0) term ↔ BinderLanguage.meaning environment leaf term) ∧
      ¬ (∀ term, BinderLanguage.meaning environment (.binder 0 (.ref 0)) term ↔
        BinderLanguage.meaning environment (.binder 0 leaf) term) := by
  dsimp only
  constructor
  · intro term
    rw [BinderLanguage.meaning]
    exact Iff.of_eq (congrFun (BinderLanguage.meaning_congr _ _ _
      (by intro name present; simp [Binding.free, Binding.freeList] at present)) term)
  · intro same
    have refEmpty := BinderLanguage.self_binder_empty
      (fun _ => BinderLanguage.meaning (fun _ _ => False) (.branch ⟨0, fun _ => True⟩ [])) 0
    have leafUnbound := BinderLanguage.unused_binder
      (fun _ => BinderLanguage.meaning (fun _ _ => False) (.branch ⟨0, fun _ => True⟩ [])) 0
      (.branch ⟨0, fun _ => True⟩ []) (by simp [Binding.free, Binding.freeList])
    have impossible := (same (.node 0 [])).mpr (by rw [leafUnbound]; simp [BinderLanguage.meaning, BinderLanguage.forest])
    rw [refEmpty] at impossible
    simp [BinderLanguage.meaning] at impossible


/-- Replacing each child by an equal language preserves its ordered concrete child tuples. -/
theorem forest_replace (meaning : Node → Value → Prop) (before after : List Node)
    (same : All₂ (Equivalent meaning) before after) (values : List Value) :
    All₂ meaning before values ↔ All₂ meaning after values := by
  induction same generalizing values with
  | nil => exact Iff.rfl
  | @cons first second before after head tail ih =>
      cases values with
      | nil => constructor <;> intro accepted <;> cases accepted
      | cons value values =>
          constructor
          · intro accepted
            cases accepted with
            | cons first rest => exact .cons ((head value).mp first) ((ih values).mp rest)
          · intro accepted
            cases accepted with
            | cons first rest => exact .cons ((head value).mpr first) ((ih values).mpr rest)

/-- The source transition constructor changes only its child list during bottom-up pruning. -/
theorem edge_replace_exact (meaning : Node → Language.Term Symbol → Prop)
    (edge : Language.Edge Node Symbol) (children : List Node) (same : All₂ (Equivalent meaning) edge.children children)
    (term : Language.Term Symbol) :
    ObservationGraph.Fits meaning {edge with children := children} term ↔ ObservationGraph.Fits meaning edge term := by
  simp only [ObservationGraph.Fits]
  constructor
  · rintro ⟨terms, shape, accepted, guard⟩
    exact ⟨terms, shape, (forest_replace meaning edge.children children same terms).mpr accepted, guard⟩
  · rintro ⟨terms, shape, accepted, guard⟩
    exact ⟨terms, shape, (forest_replace meaning edge.children children same terms).mp accepted, guard⟩

/-- Every accepted child list gives a concrete accepted value to each child state. -/
theorem forest_member (meaning : Node → Value → Prop) (children : List Node) (values : List Value)
    (accepted : All₂ meaning children values) (child : Node) (member : child ∈ children) :
    ∃ value, meaning child value := by
  induction accepted with
  | nil => simp at member
  | @cons node value nodes values head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨value, head⟩
      · exact ih later

/-- A transition with a provably empty child has no concrete terms. -/
theorem edge_empty_child (meaning : Node → Language.Term Symbol → Prop) (empty : Node → Bool)
    (sound : ∀ node, empty node = true → ∀ term, ¬ meaning node term) (edge : Language.Edge Node Symbol)
    (found : edge.children.any empty = true) (term : Language.Term Symbol) : ¬ ObservationGraph.Fits meaning edge term := by
  rintro ⟨terms, _, accepted, _⟩
  obtain ⟨child, member, emptyChild⟩ := List.any_eq_true.mp found
  obtain ⟨value, acceptedChild⟩ := forest_member meaning edge.children terms accepted child member
  exact sound child emptyChild value acceptedChild

end MicroCFTA.PruneCorrectness
