import MicroCFTA.SourceSecondaryGateProjectionComplete
import MicroCFTA.SourceSecondaryGateHeadLanguage

/-!
# Accepted subtrees through projections after clear secondary gates

The actual projection keeps each selected subtree of an accepted term.
An anchor certificate replaces whole-input closedness. Ordinary rows keep
their child positions. Recursive steps use exact actual head language.
Projection can admit additional terms because it discards ancestor guards.
-/
namespace MicroCFTA.SourceSecondaryGateProjectionLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityProjectionGraph
open SourceSecondaryGateProjectionSupport SourceSecondaryGateProjectionComplete
open InternedGuardedLanguage (meaning)

private theorem select_natural (values : List A) (index : Nat) :
    select values (Int.ofNat index) = values[index]? := by
  simp only [select, Int.ofNat_eq_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index))]
  rfl

private theorem rows_included [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (path : EqualityNormalize.Path) (index : Nat)
    (childIncluded : ∀ {value result before after},
      Project (path.map Int.ofNat) value before result after → SemanticReady before → Available before value →
      Grows anchor before → Support unconstrained anchor path value →
      ∀ holds ambient term part, meaning holds ambient value term →
        SymbolicSignedPaths.lookup term (path.map Int.ofNat) = some part → meaning holds ambient result part)
    {edges : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard}
    {results : List (Value Symbol Guard)}
    (actual : ProjectRows (path.map Int.ofNat) (Int.ofNat index) edges before results after)
    (semantic : SemanticReady before) (resident : Edges before edges) (growth : Grows anchor before)
    (supported : ∀ edge ∈ edges, ∀ child, edge.children[index]? = some child →
      Support unconstrained anchor path child)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (edge : EdgeValue Symbol Guard) (member : edge ∈ edges) (child : Value Symbol Guard)
    (found : edge.children[index]? = some child) (term part : Term Symbol)
    (accepted : meaning holds ambient child term)
    (selected : SymbolicSignedPaths.lookup term (path.map Int.ofNat) = some part) :
    ∃ result ∈ results, meaning holds ambient result part := by
  induction edges generalizing before results after with
  | nil => cases member
  | cons first edges ih =>
      cases actual with
      | missing absent rest =>
          rcases List.mem_cons.mp member with rfl | member
          · have missing : edge.children[index]? = none := by simpa only [select_natural] using absent
            rw [missing] at found
            cases found
          · exact ih rest semantic
              (fun value present => resident value (List.mem_cons_of_mem _ present))
              growth
              (fun value present => supported value (List.mem_cons_of_mem _ present)) member
      | @selected _ firstChild _ _ firstResult middle _ results _ _ firstFound firstTrace rest =>
          have firstAt : first.children[index]? = some firstChild := by simpa only [select_natural] using firstFound
          have childAvailable := semantic.ready.semantic.1.normal.facts.cached.edges first.entry.key first
            (resident first List.mem_cons_self) firstChild (List.mem_of_getElem? firstAt)
          rcases List.mem_cons.mp member with rfl | member
          · have same := Option.some.inj (firstAt.symm.trans found)
            subst child
            exact ⟨firstResult, List.mem_cons_self,
              childIncluded firstTrace semantic childAvailable growth
                (supported edge List.mem_cons_self firstChild firstAt) holds ambient term part accepted selected⟩
          · have effects := node_verified unconstrained anchor anchorSemantic anchorReady firstTrace semantic childAvailable
              growth (supported first List.mem_cons_self firstChild firstAt)
            obtain ⟨result, member, related⟩ := ih rest effects.2.1
              (fun value present => InternedEdgeResidency.edge_grows before middle effects.1.growth value
                (resident value (List.mem_cons_of_mem _ present)))
              (grows_trans growth effects.1.growth)
              (fun value present => supported value (List.mem_cons_of_mem _ present)) member
            exact ⟨result, List.mem_cons_of_mem _ member, related⟩

private theorem ordinary_included [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (path : EqualityNormalize.Path) (index : Nat)
    (childIncluded : ∀ {value result before after},
      Project (path.map Int.ofNat) value before result after → SemanticReady before → Available before value →
      Grows anchor before → Support unconstrained anchor path value →
      ∀ holds ambient term part, meaning holds ambient value term →
        SymbolicSignedPaths.lookup term (path.map Int.ofNat) = some part → meaning holds ambient result part)
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project ((index :: path).map Int.ofNat) value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (ordinary : Ordinary value)
    (supported : ∀ edge ∈ InternedEdgeResidency.nodeEdges value, ∀ child,
      edge.children[index]? = some child → Support unconstrained anchor path child)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term part : Term Symbol) (accepted : meaning holds ambient value term)
    (selected : SymbolicSignedPaths.lookup term ((index :: path).map Int.ofNat) = some part) :
    meaning holds ambient result part := by
  cases value with
  | empty => exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty term accepted)
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      cases actual with
      | ordinary rows joined =>
          have resident := InternedEdgeResidency.resident_edges before semantic.ready.semantic.1.normal.facts.linked _ available.resident
          have rowSupport : ∀ edge ∈ edges, ∀ child, edge.children[index]? = some child →
              Support unconstrained anchor path child := by
            simpa only [InternedEdgeResidency.nodeEdges] using supported
          have effects := rows_verified unconstrained anchor anchorSemantic anchorReady rows semantic resident growth rowSupport
          have exactUnion := (joined.verified effects.2.1 effects.2.2.1 effects.2.2.2).2.2.2.2 holds ambient part
          obtain ⟨edge, member, terms, rfl, children, _⟩ :=
            (InternedGuardedLanguage.laws holds ambient).node entry edges depth free term |>.mp accepted
          rw [List.map_cons, SourceEqualityNeededMeaning.lookup_cons] at selected
          obtain ⟨childTerm, atIndex, atPath⟩ := Option.bind_eq_some_iff.mp selected
          obtain ⟨child, childFound, childAccepted⟩ :=
            SourceEqualityProjectionLanguage.all₂_signed children (Int.ofNat index) childTerm atIndex
          exact exactUnion.mpr (rows_included unconstrained anchor anchorSemantic anchorReady path index childIncluded
            rows semantic resident growth rowSupport holds ambient edge member child
            (by simpa only [select_natural] using childFound) childTerm part childAccepted atPath)
      | recursive impossible _ _ => cases impossible

/-- Every selected accepted subtree survives the actual projection supported at the gate anchor. -/
theorem node_included [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {path : EqualityNormalize.Path} {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : Project (path.map Int.ofNat) value before result after)
    (semantic : SemanticReady before) (available : Available before value) (growth : Grows anchor before)
    (supported : Support unconstrained anchor path value)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (term part : Term Symbol) (accepted : meaning holds ambient value term)
    (selected : SymbolicSignedPaths.lookup term (path.map Int.ofNat) = some part) :
    meaning holds ambient result part := by
  induction path generalizing value result before after holds ambient term part with
  | nil =>
      cases actual
      cases Option.some.inj selected
      exact accepted
  | cons index path ih =>
      rcases supported with closed | ⟨anchorAvailable, gate⟩
      · exact SourceEqualityProjectionLanguage.node actual semantic available closed holds ambient term part accepted selected
      · cases value with
        | empty => exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty term accepted)
        | reference | union => cases gate
        | node entry edges depth free =>
            exact ordinary_included unconstrained anchor anchorSemantic anchorReady path index ih actual semantic available growth
              True.intro
              (by
                intro edge member child found
                exact ordinary_selected_support (Or.inr ⟨anchorAvailable, gate⟩) anchorSemantic semantic available
                  edge member child found)
              holds ambient term part accepted selected
        | mu entry body depth ordinary =>
            cases actual with
            | recursive recursive head body =>
                have effects := SourceSecondaryGateHead.head_verified gate anchorSemantic anchorAvailable semantic available growth head
                exact ordinary_included unconstrained anchor anchorSemantic anchorReady path index ih body effects.2.1
                  effects.2.2.1 (grows_trans growth effects.1.growth) effects.2.2.2
                  (by
                    intro edge member child found
                    exact head_selected_support gate anchorSemantic anchorAvailable semantic available growth head
                      edge member child found)
                  holds ambient term part
                  ((SourceSecondaryGateHeadLanguage.head_exact gate anchorSemantic anchorAvailable semantic available growth
                    head holds ambient term).mpr accepted) selected

/-- Proper supported forest projections retain the selected subtree of each accepted child forest. -/
theorem forest_included [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    {index : Nat} {path : EqualityNormalize.Path} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : State Symbol Guard}
    (actual : Forest ((index :: path).map Int.ofNat) values before result after)
    (semantic : SemanticReady before) (available : Values before values) (growth : Grows anchor before)
    (supported : ForestSupport unconstrained anchor (index :: path) values)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) ((index :: path).map Int.ofNat) = some part) :
    meaning holds ambient result part := by
  rw [List.map_cons, SourceEqualityNeededMeaning.lookup_cons] at selected
  obtain ⟨term, termAt, partAt⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨value, valueAt, valueAccepted⟩ :=
    SourceEqualityProjectionLanguage.all₂_signed accepted (Int.ofNat index) term termAt
  have found : values[index]? = some value := by simpa only [select_natural] using valueAt
  cases actual with
  | missing absent => rw [absent] at valueAt; cases valueAt
  | selected first body =>
      have same := Option.some.inj (first.symm.trans valueAt)
      subst value
      exact node_included unconstrained anchor anchorSemantic anchorReady body semantic
        (available _ (List.mem_of_getElem? found)) growth (supported _ found)
        holds ambient term part valueAccepted partAt

/-- An actual false proper forest gate retains each selected accepted subtree after later caller effects. -/
theorem false_path_included [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {index : Nat} {path : EqualityNormalize.Path}
    {values : List (Value Symbol Guard)} {initial final caller after : State Symbol Guard} {result : Value Symbol Guard}
    (gate : InternedFreshOrdinaryStatefulGateTrace.PathTrace unconstrained values (index :: path) initial false final)
    (initialSemantic : SemanticReady initial) (initialReady : InternedFreshOrdinaryMemoGateTrace.Ready initial)
    (initialAvailable : Values initial values) (callerSemantic : SemanticReady caller)
    (callerAvailable : Values caller values) (growth : Grows final caller)
    (actual : Forest ((index :: path).map Int.ofNat) values caller result after)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (terms : List (Term Symbol)) (part : Term Symbol)
    (accepted : All₂ (meaning holds ambient) values terms)
    (selected : SymbolicSignedPaths.lookup (.node symbol terms) ((index :: path).map Int.ofNat) = some part) :
    meaning holds ambient result part := by
  have anchor := SourceSecondaryGateProjectionAnchor.path_anchor unconstrained gate initialSemantic initialReady initialAvailable
  exact forest_included unconstrained final anchor.1 anchor.2.1 actual callerSemantic callerAvailable growth
    (false_path_support anchor.2.2.2.2 (by simp) anchor.2.2.2.1) holds ambient symbol terms part accepted selected

end MicroCFTA.SourceSecondaryGateProjectionLanguage
