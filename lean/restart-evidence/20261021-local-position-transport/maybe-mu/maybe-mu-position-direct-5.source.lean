import MicroCFTA.SourceCurrentNativeConstructReadback
import MicroCFTA.SourceCurrentNativeStoredMuPositivePositions
import MicroCFTA.SourceCurrentConstrainedCapStoredSubstitution
import MicroCFTA.SourceCurrentConstrainedCapNativeScope
import MicroCFTA.SourceCurrentConstrainedCapCallbackCertificates
import MicroCFTA.EqualityLeafProjectionPhysical
import MicroCFTA.InternedGateRank

/-!
# Positive positions through actual optional-binder construction

Finite Plain caps exclude constrained opaque Mu regions. Actual stored
substitution retains each positive path in the original input. Actual
optional construction uses its current ordinary callback on warm hits.
-/
namespace MicroCFTA.SourceCurrentNativeMaybeMuPositivePositions
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome work)
open InternedNestedProvenance (Values Edges)
open InternedNestedFacts (Facts)
open InternedBinderProtocol (Reference)
open InternedEdgeResidency (nodeEdges)
open InternedStoredSubstitution (Environment Replacements leaves manyLeaves edgeLeaves input encode encodeMany encodeEdges)
open InternedFreshOrdinaryConstruction (build buildMany buildEdges)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceEqualityAnnotationLanguage (Annotated)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard
local notation "Heap" => State Symbol Guard
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)

section Constructors

private theorem makeNode_positive [DecidableEq (EdgeKey Symbol Guard)] (state : Heap) (facts : Facts state) (rows : List Row)
    (resident : Edges state rows) {entry depth free path}
    (positive : PositiveAt (run (makeNode rows) state).1 path) :
    PositiveAt (.node entry rows depth free) path := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows state facts resident
  have fields := EqualityLeafProjectionPhysical.makeNode_edges rows state facts.coherent facts.linked resident
  have raw : ∀ row ∈ nodeEdges (run (makeNode rows) state).1, row ∈ rows := by
    intro row member
    exact (List.mem_filter.mp (canonicalEdges_member _ row (fields ▸ member))).1
  generalize computed : (run (makeNode rows) state).1 = result at positive ordinary raw
  cases positive with
  | root rowIndex row selected nonplain =>
      obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp (raw row (List.mem_of_getElem? selected))
      exact .root sourceIndex row found nonplain
  | child rowIndex childIndex row child selected chosen rest =>
      obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp (raw row (List.mem_of_getElem? selected))
      exact .child sourceIndex childIndex row child found chosen rest
  | member memberIndex child selected rest => cases ordinary

private theorem rows_positive (inputs : List Node) (rows : List Row)
    (covered : ∀ row ∈ rows, ∃ input ∈ inputs, row ∈ nodeEdges input) {entry depth free path}
    (positive : PositiveAt (.node entry rows depth free) path) :
    ∃ input ∈ inputs, PositiveAt input path := by
  cases positive with
  | root rowIndex row selected nonplain =>
      obtain ⟨input, member, present⟩ := covered row (List.mem_of_getElem? selected)
      cases input with
      | node source originals level names =>
          obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp present
          exact ⟨_, member, .root sourceIndex row found nonplain⟩
      | empty | reference | union | mu => cases present
  | child rowIndex childIndex row child selected chosen rest =>
      obtain ⟨input, member, present⟩ := covered row (List.mem_of_getElem? selected)
      cases input with
      | node source originals level names =>
          obtain ⟨sourceIndex, found⟩ := List.mem_iff_getElem?.mp present
          exact ⟨_, member, .child sourceIndex childIndex row child found chosen rest⟩
      | empty | reference | union | mu => cases present

private theorem ordinary_edges_rows (inputs : List Node) (rows : List Row)
    (actual : ordinaryEdges inputs = some rows) :
    ∀ row ∈ rows, ∃ input ∈ inputs, row ∈ nodeEdges input := by
  induction inputs generalizing rows with
  | nil => cases actual; intro row impossible; cases impossible
  | cons first rest ih =>
      cases first <;> simp only [ordinaryEdges] at actual <;> try contradiction
      case node entry originals depth free =>
        cases later : ordinaryEdges rest with
        | none => simp only [later, Option.map_none] at actual; cases actual
        | some outputs =>
            have same : originals ++ outputs = rows := by simpa only [later, Option.map_some, Option.some.injEq] using actual
            subst rows
            intro row member
            rcases List.mem_append.mp member with here | there
            · exact ⟨_, List.mem_cons_self, here⟩
            · obtain ⟨input, present, found⟩ := ih outputs later row there
              exact ⟨input, List.mem_cons_of_mem _ present, found⟩

private theorem flatten_positive (inputs : List Node) {input path}
    (member : input ∈ inputs.flatMap unionMembers) (positive : PositiveAt input path) :
    ∃ original ∈ inputs, PositiveAt original path := by
  obtain ⟨original, present, chosen⟩ := List.mem_flatMap.mp member
  cases original with
  | empty => cases chosen
  | union entry members depth free =>
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp chosen
      exact ⟨_, present, .member index input selected positive⟩
  | reference | node | mu =>
      have same := List.mem_singleton.mp chosen
      exact ⟨_, present, same ▸ positive⟩

private theorem makeUnion_positive [DecidableEq (EdgeKey Symbol Guard)] (state : Heap) (facts : Facts state) (inputs : List Node)
    (available : Values state inputs) {path}
    (positive : PositiveAt (run (makeUnion inputs) state).1 path) :
    ∃ input ∈ inputs, PositiveAt input path := by
  have retained : Values state (distinctNodes (inputs.flatMap unionMembers)) := by
    intro input member
    obtain ⟨original, present, chosen⟩ := List.mem_flatMap.mp (distinctNodes_member _ _ member)
    exact unionMembers_available original (available original present) input chosen
  have fromMember : ∀ input ∈ distinctNodes (inputs.flatMap unionMembers), PositiveAt input path →
      ∃ original ∈ inputs, PositiveAt original path := by
    intro input member positive
    exact flatten_positive inputs (distinctNodes_member _ _ member) positive
  cases normalized : distinctNodes (inputs.flatMap unionMembers) with
  | nil => simp only [makeUnion, normalized, run] at positive; cases positive
  | cons first rest =>
      cases rest with
      | nil =>
          exact fromMember first (by rw [normalized]; exact List.mem_singleton_self _) (by simpa only [makeUnion, normalized, run] using positive)
      | cons second tail =>
          let members := first :: second :: tail
          have memberAvailable : Values state members := by simpa only [normalized] using retained
          cases ordinary : ordinaryEdges members with
          | some rows =>
              have rowsResident := InternedEdgeResidency.ordinaryEdges_resident members rows state facts.linked
                (fun value member => (memberAvailable value member).resident) ordinary
              have structural := makeNode_positive state facts rows rowsResident
                (entry := ⟨0, .node []⟩) (depth := 0) (free := [])
                (by simpa only [makeUnion, normalized, ordinary, members] using positive)
              obtain ⟨input, present, positive⟩ := rows_positive members rows (ordinary_edges_rows members rows ordinary) structural
              exact fromMember input (by simpa only [normalized] using present) positive
          | none =>
              let key := InternedBinderProtocol.NodeKey.union (members.map Value.referenceOf)
              let identify := fun entry => Value.union entry members (maximumDepth members) (childFree members)
              let result := (nodeStep key identify state).1
              let after := (nodeStep key identify state).2
              obtain ⟨entry, fields⟩ := InternedGateRank.requested_fields key identify state facts.coherent
                (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩)
              change InternedRecordCoherence.NodeFields key entry result at fields
              have sourceResult : (run (makeUnion inputs) state).1 = result := by
                simp only [makeUnion, normalized, ordinary, members, run]
                rfl
              have sourceAfter : (run (makeUnion inputs) state).2 = after := by
                simp only [makeUnion, normalized, ordinary, members, run]
                rfl
              have completed := makeUnion_available inputs state facts.coherent facts.cached available
              have resultAvailable : Available after result := by
                simpa only [makeUnion, normalized, ordinary, members, run] using completed.2.2
              have afterCoherent : InternedRecordCoherence.Coherent after := by
                simpa only [makeUnion, normalized, ordinary, members, run] using completed.1
              cases observed : result with
              | empty | reference | node | mu => simp [observed, InternedRecordCoherence.NodeFields, key, muKey] at fields
              | union actual actualMembers depth free =>
                  simp only [observed, InternedRecordCoherence.NodeFields] at fields
                  have sameIds : members.map Value.referenceOf = actualMembers.map Value.referenceOf := by
                    exact InternedBinderProtocol.NodeKey.union.inj fields.2.1
                  have sameMembers : actualMembers = members := InternedNormalizationFree.value_lists_equal after afterCoherent
                    actualMembers members
                    (fun child member => (resultAvailable.children child (by simpa only [observed, children] using member)).resident)
                    (fun child member => by
                      rw [← sourceAfter]
                      exact (available_after_run (makeUnion inputs) state facts.coherent.valid
                        (memberAvailable child member)).resident)
                    sameIds.symm
                  have positiveResult : PositiveAt (.union actual actualMembers depth free) path := by
                    simpa only [sourceResult, observed] using positive
                  cases positiveResult with
                  | member memberIndex child selected rest =>
                      have present : child ∈ members := sameMembers ▸ List.mem_of_getElem? selected
                      exact fromMember child (by simpa only [normalized] using present) rest

end Constructors
private def Back (original result : Node) : Prop := ∀ path, PositiveAt result path → PositiveAt original path
private def RowBack (original result : Row) : Prop :=
  result.entry.key.constraint = original.entry.key.constraint ∧ All₂ Back original.children result.children

private theorem all_lookup {A B : Type} {relation : A → B → Prop} {left right}
    (paired : All₂ relation left right) (index : Nat) (value : B) (found : right[index]? = some value) :
    ∃ source, left[index]? = some source ∧ relation source value := by
  induction paired generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons first rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst value
          exact ⟨_,rfl,first⟩
      | succ index => exact ih index found

private theorem rows_back {originals results : List Row} (related : All₂ RowBack originals results)
    {entry source level names depth free path}
    (positive : PositiveAt (.node entry results depth free) path) :
    PositiveAt (.node source originals level names) path := by
  cases positive with
  | root index row selected nonplain =>
      obtain ⟨original,found,same,children⟩ := all_lookup related index row selected
      exact .root index original found (same ▸ nonplain)
  | child index childIndex row child selected chosen positive =>
      obtain ⟨original,found,same,children⟩ := all_lookup related index row selected
      obtain ⟨source,lookup,back⟩ := all_lookup children childIndex child chosen
      exact .child index childIndex original source found lookup (back _ positive)

private theorem input_available (context : List Node) (environment : Environment Symbol Guard)
    (state : Heap) (available : Values state context) (replacements : Replacements state environment) :
    Values state (context.map (input environment)) := by
  intro value member
  obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
  cases source with
  | empty | node | union | mu => exact available _ present
  | reference name =>
      cases found : environment name with
      | none => simpa only [input,found,Option.getD_none] using available _ present
      | some value => simpa only [input,found,Option.getD_some] using replacements name value found

private theorem completed_bind {A B : Type} (first : Outcome Symbol Guard A)
    (next : A → Heap → Outcome Symbol Guard B) (value : B) (after : Heap)
    (actual : first.bind next = .done value after) :
    ∃ input middle, first = .done input middle ∧ next input middle = .done value after := by
  cases first with
  | pending key state => cases actual
  | done input middle => exact ⟨input,middle,rfl,actual⟩

section Execute
variable [DecidableEq (EdgeKey Symbol Guard)]

mutual
private theorem encoded_back (context : List Node) (environment : Environment Symbol Guard)
    (value : Node) (state : Heap) (facts : Facts state) (captures : Values state context)
    (available : Available state value) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (replacements : Replacements state environment)
    (annotations : ∀ name output, environment name = some output → Annotated Plain output)
    (depth : Nat) (bounded : Cap Plain depth value) (stored : MuStored Plain state)
    (result : Node) (after : Heap)
    (actual : build (encode context [] value) (context.map (input environment)) state = .done result after) :
    Back value result := by
  have inputs := input_available context environment state captures replacements
  have originalActual := actual
  have originalCovered := covered
  rw [encode.eq_def] at actual
  split at actual
  · rename_i closed
    have member := covered value (by rw [leaves.eq_def]; simp only [closed,ite_true,List.mem_singleton])
    have lookup := InternedStoredSubstitutionBindings.global_lookup context [] [] value environment state
      facts.coherent captures member rfl
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at lookup
    have literal : input environment value = value := InternedStoredSubstitutionScope.input_closed value environment
      (List.isEmpty_iff.mp closed)
    simp only [build,List.length_nil,Nat.zero_add,lookup,Option.getD_some,literal] at actual
    cases actual
    exact fun _ positive => positive
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened,Bool.false_eq_true,ite_false] at covered
    cases value with
    | empty => simp only [build] at actual; cases actual; exact fun _ positive => positive
    | reference name =>
        have lookup := InternedStoredSubstitutionBindings.global_lookup context [] [] (.reference name) environment
          state facts.coherent captures (covered _ (by simp)) rfl
        simp only [List.nil_append,List.length_nil,Nat.zero_add] at lookup
        simp only [List.findIdx?_nil,build,List.length_nil,Nat.zero_add,lookup,Option.getD_some] at actual
        cases actual
        intro path positive
        cases found : environment name with
        | none => simp only [input,found,Option.getD_none] at positive; cases positive
        | some output =>
            exact False.elim (SourceCurrentRequiredPositivePosition.not_plain
              (by simpa only [input,found,Option.getD_some] using positive) (annotations name output found))
    | node entry originals level free =>
        simp only [build] at actual
        obtain ⟨rows,middle,made,returned⟩ := completed_bind _ _ result after actual
        have physical := InternedFreshOrdinaryFacts.buildEdges_verified (encodeEdges context [] originals)
          (context.map (input environment)) state facts inputs
        have middleFacts : Facts middle := by simpa only [made,Outcome.state] using physical.facts
        have resident := physical.result rows middle made
        have paired := encoded_rows_back context environment originals state facts captures
          (fun child member => available.children child member) covered replacements annotations depth
          (fun row member => SourceCurrentConstrainedCap.node_edge bounded row member) stored rows middle made
        have built : run (makeNode rows) middle = (result,after) := by
          exact Prod.ext (Outcome.done.inj returned).1 (Outcome.done.inj returned).2
        intro path positive
        have structural := makeNode_positive middle middleFacts rows resident
          (entry := entry) (depth := level) (free := free) (by simpa only [built] using positive)
        exact rows_back paired structural
    | union entry originals level free =>
        simp only [build] at actual
        obtain ⟨values,middle,made,returned⟩ := completed_bind _ _ result after actual
        have physical := InternedFreshOrdinaryFacts.buildMany_verified (encodeMany context [] originals)
          (context.map (input environment)) state facts inputs
        have middleFacts : Facts middle := by simpa only [made,Outcome.state] using physical.facts
        have outputs := physical.result values middle made
        have paired := encoded_many_back context environment originals state facts captures
          (fun child member => available.children child member) covered replacements annotations depth
          (fun child member => SourceCurrentConstrainedCap.union_member bounded child member) stored values middle made
        have built : run (makeUnion values) middle = (result,after) := by
          exact Prod.ext (Outcome.done.inj returned).1 (Outcome.done.inj returned).2
        intro path positive
        obtain ⟨child,member,positive⟩ := makeUnion_positive middle middleFacts values outputs
          (by simpa only [built] using positive)
        obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
        obtain ⟨original,found,back⟩ := all_lookup paired index child selected
        exact .member index original found (back _ positive)
    | mu entry body probe ordinary =>
        have plain := SourceCurrentConstrainedCapNativeScope.mu_annotated bounded
        have typed := SourceCurrentConstrainedCapStoredSubstitution.encode_typed Plain 0 context [] []
          (.mu entry body probe ordinary) environment state facts.coherent captures available
          originalCovered
          rfl (by intro _ member; cases member) annotations (.plain 0 plain)
        have checked := SourceCurrentConstrainedCapConstruction.build Plain 0
          (encode context [] (.mu entry body probe ordinary)) (context.map (input environment)) state facts inputs typed stored
        have literal : build (encode context [] (.mu entry body probe ordinary)) (context.map (input environment)) state =
            .done result after := originalActual
        have annotated := (checked.result result after literal).annotated rfl
        exact fun _ positive => False.elim (SourceCurrentRequiredPositivePosition.not_plain positive annotated)
termination_by sizeOf value

private theorem encoded_many_back (context : List Node) (environment : Environment Symbol Guard)
    (values : List Node) (state : Heap) (facts : Facts state) (captures : Values state context)
    (available : Values state values) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (replacements : Replacements state environment)
    (annotations : ∀ name output, environment name = some output → Annotated Plain output)
    (depth : Nat) (bounded : ∀ value ∈ values, Cap Plain depth value) (stored : MuStored Plain state)
    (results : List Node) (after : Heap)
    (actual : buildMany (encodeMany context [] values) (context.map (input environment)) state = .done results after) :
    All₂ Back values results := by
  cases values with
  | nil => simp only [encodeMany,buildMany] at actual; cases actual; exact .nil
  | cons value values =>
      simp only [encodeMany,buildMany] at actual
      obtain ⟨result,middle,called,later⟩ := completed_bind _ _ results after actual
      obtain ⟨outputs,final,tailDone,returned⟩ := completed_bind _ _ results after later
      simp only [Outcome.done.injEq] at returned
      obtain ⟨rfl,rfl⟩ := returned
      have inputs := input_available context environment state captures replacements
      have physical := InternedFreshOrdinaryFacts.build_verified (encode context [] value)
        (context.map (input environment)) state facts inputs
      have middleFacts : Facts middle := by simpa only [called,Outcome.state] using physical.facts
      have current (source : Node) (old : Available state source) : Available middle source := by
        simpa only [called,Outcome.state] using physical.available source old
      have firstCovered : ∀ leaf ∈ leaves value, leaf ∈ context :=
        fun leaf member => covered leaf (by simp only [manyLeaves,List.mem_append]; exact .inl member)
      have typed := SourceCurrentConstrainedCapStoredSubstitution.encode_typed Plain depth context [] [] value environment
        state facts.coherent captures (available value List.mem_cons_self) firstCovered rfl
        (by intro _ member; cases member) annotations (bounded value List.mem_cons_self)
      have kept : MuStored Plain middle := by
        simpa only [called,Outcome.state] using
          (SourceCurrentConstrainedCapConstruction.build Plain depth _ _ state facts inputs typed stored).stored
      exact .cons (encoded_back context environment value state facts captures (available value List.mem_cons_self)
        firstCovered replacements annotations depth (bounded value List.mem_cons_self) stored result middle called)
        (encoded_many_back context environment values middle middleFacts (fun source member => current source (captures source member))
          (fun source member => current source (available source (List.mem_cons_of_mem _ member)))
          (fun leaf member => covered leaf (by simp only [manyLeaves,List.mem_append]; exact .inr member))
          (fun name source found => current source (replacements name source found)) annotations depth
          (fun source member => bounded source (List.mem_cons_of_mem _ member)) kept outputs final tailDone)
termination_by sizeOf values

private theorem encoded_rows_back (context : List Node) (environment : Environment Symbol Guard)
    (rows : List Row) (state : Heap) (facts : Facts state) (captures : Values state context)
    (available : ∀ child ∈ rows.flatMap EdgeValue.children, Available state child)
    (covered : ∀ leaf ∈ edgeLeaves rows, leaf ∈ context) (replacements : Replacements state environment)
    (annotations : ∀ name output, environment name = some output → Annotated Plain output)
    (depth : Nat) (bounded : ∀ row ∈ rows, SourceCurrentConstrainedCap.Edge Plain depth row)
    (stored : MuStored Plain state) (outputs : List Row) (after : Heap)
    (actual : buildEdges (encodeEdges context [] rows) (context.map (input environment)) state = .done outputs after) :
    All₂ RowBack rows outputs := by
  cases rows with
  | nil => simp only [encodeEdges,buildEdges] at actual; cases actual; exact .nil
  | cons row rows =>
      cases row with
      | mk entry children =>
          simp only [encodeEdges,buildEdges] at actual
          obtain ⟨values,middle,called,later⟩ := completed_bind _ _ outputs after actual
          obtain ⟨edge,next,built,later⟩ := completed_bind _ _ outputs after later
          obtain ⟨edges,final,tailDone,returned⟩ := completed_bind _ _ outputs after later
          simp only [Outcome.done.injEq] at returned
          obtain ⟨rfl,rfl⟩ := returned
          have inputs := input_available context environment state captures replacements
          have physical := InternedFreshOrdinaryFacts.buildMany_verified (encodeMany context [] children)
            (context.map (input environment)) state facts inputs
          have middleFacts : Facts middle := by simpa only [called,Outcome.state] using physical.facts
          have outputsAvailable := physical.result values middle called
          have current (source : Node) (old : Available state source) : Available middle source := by
            simpa only [called,Outcome.state] using physical.available source old
          have childBound : ∀ child ∈ children, Cap Plain (depth - 1) child := by
            cases depth with
            | zero => exact fun child member => .plain 0 ((bounded _ List.mem_cons_self).2 child member)
            | succ depth => exact bounded _ List.mem_cons_self
          have childCovered : ∀ leaf ∈ manyLeaves children, leaf ∈ context :=
            fun leaf member => covered leaf (by simp only [edgeLeaves,List.mem_append]; exact .inl member)
          have typed := SourceCurrentConstrainedCapStoredSubstitution.encodeMany_typed Plain (depth - 1) context [] []
            children environment state facts.coherent captures (fun child member => available child (List.mem_flatMap.mpr ⟨_,List.mem_cons_self,member⟩))
            childCovered rfl (by intro _ member; cases member) annotations childBound
          have kept : MuStored Plain middle := by
            simpa only [called,Outcome.state] using
              (SourceCurrentConstrainedCapConstruction.buildMany Plain (depth - 1) _ _ state facts inputs typed stored).stored
          have actualEdge : run (makeEdge entry.key.symbol entry.key.constraint values) middle = (edge,next) := by
            exact Prod.ext (Outcome.done.inj built).1 (Outcome.done.inj built).2
          have edgeChecked := InternedNestedFacts.edge_verified entry.key.symbol entry.key.constraint values middle
            middleFacts outputsAvailable
          have nextFacts : Facts next := by simpa only [built,Outcome.state] using edgeChecked.facts
          have forward (source : Node) (old : Available state source) : Available next source := by
            simpa only [built,Outcome.state] using edgeChecked.available source (current source old)
          have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleFacts entry.key.symbol entry.key.constraint
            values outputsAvailable
          rw [actualEdge] at fields
          have paired := encoded_many_back context environment children state facts captures
            (fun child member => available child (List.mem_flatMap.mpr ⟨_,List.mem_cons_self,member⟩)) childCovered replacements annotations
            (depth - 1) childBound stored values middle called
          refine .cons ⟨fields.2.1,?_⟩ ?_
          · change All₂ Back children edge.children
            rw [fields.2.2]
            exact paired
          · exact encoded_rows_back context environment rows next nextFacts
              (fun source member => forward source (captures source member))
              (fun source member => forward source (available source (by simp [member])))
              (fun leaf member => covered leaf (by simp only [edgeLeaves,List.mem_append]; exact .inr member))
              (fun name source found => forward source (replacements name source found)) annotations depth
              (fun row member => bounded row (List.mem_cons_of_mem _ member))
              (by simpa only [actualEdge] using kept.makeEdge entry.key.symbol entry.key.constraint values) edges final tailDone
termination_by sizeOf rows
end

/-- An actual stored substitution retains every positive position in its finite-cap input. -/
theorem execute (value : Node) (environment : Environment Symbol Guard) (state : Heap)
    (facts : Facts state) (available : Available state value) (depth : Nat) (bounded : Cap Plain depth value)
    (replacements : Replacements state environment)
    (annotations : ∀ name output, environment name = some output → Annotated Plain output)
    (stored : MuStored Plain state) (result : Node) (after : Heap)
    (actual : InternedFreshOrdinaryStoredSubstitution.execute value environment state = .done result after)
    (path : List Nat) (positive : PositiveAt result path) : PositiveAt value path :=
  encoded_back (leaves value) environment value state facts (InternedStoredSubstitution.leaves_available value state available)
    available (fun _ member => member) replacements annotations depth bounded stored result after actual path positive

private theorem filter_positive (name : Reference) (value : Node) (state : Heap)
    (facts : Facts state) (available : Available state value) (path : List Nat)
    (positive : PositiveAt (run (withoutSelfReference name value) state).1 path) : PositiveAt value path := by
  cases value with
  | empty | reference | node | mu => exact positive
  | union entry members depth free =>
      unfold withoutSelfReference at positive
      split at positive
      · obtain ⟨child,member,rest⟩ := makeUnion_positive state facts _
          (fun child member => available.children child (List.mem_filter.mp member).1) positive
        obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp member).1
        exact .member index child selected rest
      · exact positive

private theorem callback_back (body : Node) (old marker : Reference) (state : Heap)
    (facts : Facts state) (available : Available state body) (markerAvailable : Available state (.reference marker))
    (depth : Nat) (bounded : Cap Plain depth body) (stored : MuStored Plain state)
    (result : Node) (after : Heap)
    (actual : SourceRecursiveIntersectionMaybeMu.callback old body marker state = .done result after) :
    MuStored Plain after ∧ Back body result := by
  let environment : Environment Symbol Guard := InternedStoredSubstitutionRebind.replacement old (.reference marker)
  have replacements : Replacements state environment := by
    intro name value found
    dsimp only [environment,InternedStoredSubstitutionRebind.replacement] at found
    split at found
    · cases found; exact markerAvailable
    · cases found
  have annotations : ∀ name value, environment name = some value → Annotated Plain value := by
    intro name value found
    dsimp only [environment,InternedStoredSubstitutionRebind.replacement] at found
    split at found
    · cases found; exact .reference marker
    · cases found
  have expanded := actual
  unfold SourceRecursiveIntersectionMaybeMu.callback at expanded
  obtain ⟨raw,middle,rawDone,filtered⟩ := completed_bind _ _ result after expanded
  have rawChecked := SourceCurrentConstrainedCapStoredSubstitution.execute Plain depth body environment state facts available
    bounded replacements annotations stored
  have inputs := InternedStoredSubstitution.inputs_available body environment state available replacements
  have rawPhysical := InternedFreshOrdinaryFacts.build_verified (encode (leaves body) [] body)
    ((leaves body).map (input environment)) state facts inputs
  have middleFacts : Facts middle := by simpa only [rawDone,Outcome.state] using rawPhysical.facts
  have rawAvailable := rawPhysical.result raw middle rawDone
  have middleStored : MuStored Plain middle := by simpa only [rawDone,Outcome.state] using rawChecked.stored
  obtain ⟨rfl,rfl⟩ := Outcome.done.inj filtered
  exact ⟨middleStored.preserve (InternedStoredMuOrigins.filter_noNewMu marker raw middle),
    fun path positive => execute body environment state facts available depth bounded replacements annotations stored
      raw middle rawDone path (filter_positive marker raw middle middleFacts rawAvailable path positive)⟩

/-- An actual optional-binder return retains every positive path in its original finite-cap body. -/
theorem maybeMu (pair : Nat × Nat) (body : Node) (state : Heap)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap state)
    (available : Available state body) (depth : Nat) (bounded : Cap Plain depth body)
    (stored : MuStored Plain state) (earlier : SourceCurrentNativeMuPublication.History empty state)
    (result : Node) (after : Heap)
    (actual : SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done result after)
    (path : List Nat) (positive : PositiveAt result path) : PositiveAt body path := by
  by_cases used : Reference.intersection pair.1 pair.2 ∈ body.free
  · have constructing : SourceRecursiveIntersectionMaybeMu.construct (.intersection pair.1 pair.2) body state =
        .done result after := by
      simpa only [SourceRecursiveIntersectionMaybeMu.maybeMu,used,ite_true] using actual
    obtain ⟨probe,afterDepth,ordinary,cut,raw,middle,entry,storedBody,depthDone,ordinaryDone,requestDone,
      rawDone,filtered,normal,rawAvailable,present,returned,history,unused⟩ :=
      SourceCurrentNativeConstructReadback.construct _ body state semantic available earlier result after constructing
    have depthPhysical := SourceCurrentConstrainedCapCallbackCertificates.verified body (.intersection pair.1 pair.2)
      .depth state semantic.1.normal.facts available (InternedNestedProvenance.depth_available state)
    have currentFacts : Facts afterDepth := by simpa only [depthDone,Outcome.state] using depthPhysical.facts
    have currentAvailable : Available afterDepth body := by
      simpa only [depthDone,Outcome.state] using depthPhysical.available body available
    have currentStored := (callback_back body (.intersection pair.1 pair.2) .depth state semantic.1.normal.facts
      available (InternedNestedProvenance.depth_available state) depth bounded stored probe afterDepth depthDone).1
    have finalSemantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap after := by
      change InternedFreshOrdinaryContext.Context after [] ∧ InternedFreshOrdinaryDepthHeap.Heap after
      simpa only [actual,Outcome.state] using
        SourceRecursiveIntersectionMaybeMu.semantic_context pair body state semantic.1 available semantic.2
    have noLocal : InternedFreshOrdinaryDepthHeap.usesLocal probe ordinary = false := by
      cases observed : InternedFreshOrdinaryDepthHeap.usesLocal probe ordinary with
      | false => rfl
      | true =>
          have retained :=  SourceCurrentNativeNormalizedComparison.retained_of_used entry storedBody probe ordinary
            (finalSemantic.2 _ entry storedBody probe ordinary present) observed
          rw [returned,retained] at positive
          cases positive
    have ordinaryPositive : PositiveAt ordinary path := by
      rw [(unused noLocal).1] at positive
      unfold SourceCurrentNativeCallbackErasure.eraseSelf at positive
      split at positive
      · cases positive
      · exact positive
    exact (callback_back body (.intersection pair.1 pair.2)
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel probe)) afterDepth currentFacts currentAvailable
      (InternedNestedProvenance.ordinary_available afterDepth _) depth bounded currentStored ordinary cut ordinaryDone).2
        path ordinaryPositive
  · rw [SourceRecursiveIntersectionMaybeMu.unused pair body state used] at actual
    cases actual
    exact positive

end Execute
end MicroCFTA.SourceCurrentNativeMaybeMuPositivePositions
