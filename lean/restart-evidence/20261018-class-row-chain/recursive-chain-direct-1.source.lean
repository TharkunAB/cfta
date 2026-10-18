import MicroCFTA.SourceCurrentRecursiveHeadNodeRows
import MicroCFTA.SourceCurrentStoredReconstruction

/-!
# Chronological rows of completed recursive Head exposure

The actual collector supplies each union choice and stored Mu call.
Each selected row ends at an ordinary record at its actual visit time.
Its ordered child calls replay at the final Head reader. This relation
does not identify reconstructed rows with earlier nested source bodies.
-/
namespace MicroCFTA.SourceCurrentRecursiveHeadChainRows
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceEqualityRequiredHead (Head)
open SourceCurrentRecursiveHeadRowOrigins (selfEnvironment)
open SourceCurrentStoredNodeExpansion (RowCalls)
open SourceCurrentStoredSubstitutionCalls (Calls)
open InternedBinderProtocol (NodeKey Reference)
open MergedFreshOrdinaryExposure (collect)
open MergedSourceExposure (Result)

private theorem unfolded [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary value : Value Symbol Guard)
    (before after : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry body depth ordinary))
    (closed : (Value.mu entry body depth ordinary).free = [])
    (actual : unfold (.mu entry body depth ordinary) before = .done value after) :
    Keeps before after ∧ Available after value ∧ value.free = [] := by
  have bodyAvailable := available.children body (by simp [children])
  have replacements : InternedStoredSubstitution.Replacements before (selfEnvironment entry body depth ordinary) := by
    intro name replacement found
    dsimp only [selfEnvironment] at found
    split at found
    · cases found; exact available
    · cases found
  obtain ⟨result,final,called,keeps,returned,_⟩ := SourceCurrentStoredReconstruction.execute
    body (selfEnvironment entry body depth ordinary) before ready bodyAvailable replacements
  have same : result = value ∧ final = after := Outcome.done.inj (called.symm.trans actual)
  obtain ⟨rfl,rfl⟩ := same
  exact ⟨keeps,returned,InternedFreshOrdinaryStoredSubstitution.unfold_closed _ before
    ready.semantic.1 available closed _ after actual⟩

/-- A branch retains actual union indices, Mu call heaps, and intervening cache effects. -/
inductive Chain [DecidableEq (EdgeKey Symbol Guard)] :
    State Symbol Guard → Value Symbol Guard → State Symbol Guard → Value Symbol Guard → Prop where
  /-- The initial branch starts at its available closed input. -/
  | start (ready : Ready before) (available : Available before value) (closed : value.free = []) :
      Chain before value before value
  /-- A union branch selects one literal member occurrence. -/
  | member (prefix : Chain before root current (.union entry members depth free))
      (index : Nat) (found : members[index]? = some value) : Chain before root current value
  /-- A Mu branch performs its literal repaired stored-body call. -/
  | mu (prefix : Chain before root current (.mu entry body depth ordinary))
      (actual : execute body (selfEnvironment entry body depth ordinary) current = .done value next) :
      Chain before root next value
  /-- Other collector branches can extend the current cache before this value is visited. -/
  | advance (prefix : Chain before root current value) (keeps : Keeps current next) :
      Chain before root next value

/-- Every chronological branch derives its current cache, residency, and closedness. -/
theorem Chain.verified [DecidableEq (EdgeKey Symbol Guard)]
    {before current : State Symbol Guard} {root value : Value Symbol Guard}
    (actual : Chain before root current value) :
    Keeps before current ∧ Available current value ∧ value.free = [] := by
  induction actual with
  | start ready available closed => exact ⟨SourceEqualityRequiredCache.pure_keeps _ ready,available,closed⟩
  | @member before root current entry members depth free value prefix index found ih =>
      have present := List.mem_of_getElem? found
      exact ⟨ih.1,ih.2.1.children value present,
        MergedColdReaderClosed.union_members_closed current ih.1.ready.semantic.1.normal.facts
          entry members depth free ih.2.1 ih.2.2 value present⟩
  | mu prefix called ih =>
      have last := unfolded _ _ _ _ _ _ _ ih.1.ready ih.2.1 ih.2.2 called
      exact ⟨ih.1.trans last.1,last.2⟩
  | advance prefix keeps ih => exact ⟨ih.1.trans keeps,keeps.available _ ih.2.1,ih.2.2⟩

/-- Each recorded Mu call has an exact stored-body replay at the chosen reader. -/
def Warm [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard) :
    {before current : State Symbol Guard} → {root value : Value Symbol Guard} →
    Chain before root current value → Prop
  | _,_,_,_,.start .. => True
  | _,_,_,_,.member prefix _ _ => Warm reader prefix
  | _,_,_,_,@Chain.mu _ _ _ _ _ _ entry body depth ordinary value next prefix _ =>
      Warm reader prefix ∧ execute body (selfEnvironment entry body depth ordinary) reader = .done value reader
  | _,_,_,_,.advance prefix _ => Warm reader prefix

/-- Actual call replay follows the recorded chronological growth into the final reader. -/
theorem Chain.warm [DecidableEq (EdgeKey Symbol Guard)]
    {before current reader : State Symbol Guard} {root value : Value Symbol Guard}
    (actual : Chain before root current value) (growth : Grows current reader) : Warm reader actual := by
  induction actual with
  | start => trivial
  | member prefix index found ih => exact ih growth
  | @mu before root current entry body depth ordinary value next prefix called ih =>
      have known := prefix.verified
      have last := unfolded entry body depth ordinary value current next known.1.ready known.2.1 known.2.2 called
      exact ⟨ih (grows_trans last.1.growth growth),
        InternedFreshOrdinaryStoredSubstitution.unfold_replay (.mu entry body depth ordinary)
          current reader value next known.1.ready.semantic.1.normal.facts.coherent.valid called growth⟩
  | advance prefix keeps ih => exact ih (grows_trans keeps.growth growth)

private def Occurrence [DecidableEq (EdgeKey Symbol Guard)]
    (before : State Symbol Guard) (root : Value Symbol Guard) (after : State Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  ∃ terminal entry originals depth free index,
    Chain before root terminal (.node entry originals depth free) ∧ Keeps terminal after ∧
      originals[index]? = some row

private theorem collector [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (before current : State Symbol Guard) (root : Value Symbol Guard)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (ready : Ready current)
    (tracked : ∀ value ∈ pending, Chain before root current value)
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (actual : collect fuel current seen pending = .done rows after) :
    Keeps current after ∧ ∀ row ∈ rows, Occurrence before root after row := by
  induction fuel generalizing current seen pending rows after with
  | zero =>
      cases pending with
      | nil => cases actual; exact ⟨SourceEqualityRequiredCache.pure_keeps _ ready,by simp⟩
      | cons => cases actual
  | succ fuel ih =>
      cases pending with
      | nil => cases actual; exact ⟨SourceEqualityRequiredCache.pure_keeps _ ready,by simp⟩
      | cons value rest =>
          have first := tracked value List.mem_cons_self
          have known := first.verified
          have tail : ∀ value ∈ rest, Chain before root current value :=
            fun value member => tracked value (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih current seen rest ready tail rows after actual
          | reference => cases actual
          | node entry originals depth free =>
              cases more : collect fuel current seen rest with
              | unresolved | pending | exhausted => simp only [collect,more,Result.prepend] at actual; cases actual
              | done values final =>
                  have same : originals ++ values = rows ∧ final = after := by
                    simpa only [collect,more,Result.prepend,Result.done.injEq] using actual
                  obtain ⟨rfl,rfl⟩ := same
                  have later := ih current seen rest ready tail values final more
                  refine ⟨later.1,?_⟩
                  intro row member
                  rcases List.mem_append.mp member with own | other
                  · obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp own
                    exact ⟨current,entry,originals,depth,free,index,first,later.1,found⟩
                  · exact later.2 row other
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · have more : collect fuel current seen rest = .done rows after := by
                  simpa only [collect,ite_eq_left visited] using actual
                exact ih current seen rest ready tail rows after more
              · have more : collect fuel current (entry.identity :: seen) (members ++ rest) = .done rows after := by
                  simpa only [collect,ite_eq_right visited] using actual
                apply ih current (entry.identity :: seen) (members ++ rest) ready _ rows after more
                intro value member
                rcases List.mem_append.mp member with own | other
                · obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp own
                  exact .member first index found
                · exact tail value other
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · have more : collect fuel current seen rest = .done rows after := by
                  simpa only [collect,ite_eq_left visited] using actual
                exact ih current seen rest ready tail rows after more
              · cases called : unfold (.mu entry body depth ordinary) current with
                | pending => simp only [collect,ite_eq_right visited,called] at actual; cases actual
                | done value middle =>
                    have last := unfolded entry body depth ordinary value current middle ready known.2.1 known.2.2 called
                    have more : collect fuel middle (entry.identity :: seen) (value :: rest) = .done rows after := by
                      simpa only [collect,ite_eq_right visited,called] using actual
                    have later := ih middle (entry.identity :: seen) (value :: rest) last.1.ready (by
                      intro child member
                      rcases List.mem_cons.mp member with rfl | other
                      · exact .mu first called
                      · exact .advance (tail child other) last.1) rows after more
                    exact ⟨last.1.trans later.1,later.2⟩

private theorem read_rows [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (ready : Ready before) (available : Available before value) (closed : value.free = [])
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done rows after) :
    Keeps before after ∧ ∀ row ∈ rows, Occurrence before value after row := by
  have initial : Chain before value before value := .start ready available closed
  have fallback (current : State Symbol Guard) (currentReady : Ready current)
      (prefix : Chain before value current value)
      (done : (collect fuel current [] [value]).canonical = .done rows after) :
      Keeps current after ∧ ∀ row ∈ rows, Occurrence before value after row := by
    cases called : collect fuel current [] [value] with
    | unresolved | pending | exhausted => simp only [called,Result.canonical] at done; cases done
    | done originals final =>
        have same : canonicalEdges originals = rows ∧ final = after := by
          simpa only [called,Result.canonical,Result.done.injEq] using done
        obtain ⟨rfl,rfl⟩ := same
        have reached := collector fuel before current value [] [value] currentReady (by
          intro selected member; cases List.mem_singleton.mp member; exact prefix) originals final called
        exact ⟨reached.1,fun row member => reached.2 row (canonicalEdges_member _ row member)⟩
  cases value with
  | empty | reference => cases actual; exact ⟨SourceEqualityRequiredCache.pure_keeps _ ready,by simp⟩
  | node entry originals depth free =>
      cases actual
      refine ⟨SourceEqualityRequiredCache.pure_keeps _ ready,?_⟩
      intro row member
      obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
      exact ⟨before,entry,originals,depth,free,index,initial,SourceEqualityRequiredCache.pure_keeps _ ready,found⟩
  | union => exact fallback before ready initial actual
  | mu entry body depth ordinary =>
      cases called : unfold (.mu entry body depth ordinary) before with
      | pending => simp only [MergedFreshOrdinaryExposure.nodeEdges,called] at actual; cases actual
      | done result middle =>
          have first := unfolded entry body depth ordinary result before middle ready available closed called
          cases result with
          | node nodeEntry originals level free =>
              have same : originals = rows ∧ middle = after := by
                simpa only [MergedFreshOrdinaryExposure.nodeEdges,called,Result.done.injEq] using actual
              obtain ⟨rfl,rfl⟩ := same
              refine ⟨first.1,?_⟩
              intro row member
              obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
              exact ⟨middle,nodeEntry,originals,level,free,index,.mu initial called,
                SourceEqualityRequiredCache.pure_keeps _ first.1.ready,found⟩
          | empty | reference | union | mu =>
              have more := fallback middle first.1.ready (.advance initial first.1) (by
                simpa only [MergedFreshOrdinaryExposure.nodeEdges,called] using actual)
              exact ⟨first.1.trans more.1,more.2⟩

private theorem closed_calls [DecidableEq (EdgeKey Symbol Guard)]
    (common : State Symbol Guard) (values : List (Value Symbol Guard))
    (closed : ∀ value ∈ values, value.free = []) : Calls (fun _ => none) values common values common := by
  induction values with
  | nil => exact .nil common
  | cons value values ih => exact .cons value values common common common value values
      (SourceCurrentStoredUnionObservations.closed value _ common (closed value List.mem_cons_self))
      (ih (fun value member => closed value (List.mem_cons_of_mem _ member)))

private theorem terminal_calls [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (rows : List (EdgeValue Symbol Guard)) (level : Nat) (free : List Reference)
    (common : State Symbol Guard) (ready : Ready common)
    (available : Available common (.node entry rows level free)) (closed : free = [])
    (row : EdgeValue Symbol Guard) (member : row ∈ rows) : RowCalls (fun _ => none) common row row := by
  have facts := ready.semantic.1.normal.facts
  have freeFields := InternedNormalizationFree.node_free common facts.coherent entry rows level free available.resident
  have childrenClosed : ∀ child ∈ row.children, child.free = [] := by
    intro child included
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name named
    have found := (childFree_member (rows.flatMap EdgeValue.children) name).mpr
      ⟨child,List.mem_flatMap.mpr ⟨row,member,included⟩,named⟩
    rw [←freeFields,closed] at found
    cases found
  have resident := resident_edges common facts.linked _ available.resident row member
  have fields := facts.coherent.edges row.entry.key row resident
  have key : EdgeKey.mk row.entry.key.symbol (row.children.map Value.referenceOf) row.entry.key.constraint = row.entry.key := by
    cases same : row.entry.key
    simpa only [same] using congrArg (fun children => EdgeKey.mk _ children _) fields.2.2
  have made : run (makeEdge row.entry.key.symbol row.entry.key.constraint row.children) common = (row,common) := by
    change common.edgeRecords row.entry.key = some row at resident
    simp only [makeEdge,run,key,edgeStep,Cache.intern,fields.1,keepFirst,resident,Option.getD_some]
  exact ⟨closed_calls common row.children childrenClosed,made,rfl,rfl,rfl⟩

/-- Every selected row retains a chronological terminal record and exact final warm child calls. -/
def Rows [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  ∀ (index : Nat) (row : EdgeValue Symbol Guard), (nodeEdges result)[index]? = some row →
    ∃ terminal entry originals depth free sourceIndex,
      ∃ branch : Chain before value terminal (.node entry originals depth free),
        Keeps terminal after ∧ Warm after branch ∧ originals[sourceIndex]? = some row ∧
          RowCalls (fun _ => none) after row row

/-- Initial ready closed data constructs Head and all actual chronological terminal row sources. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before) (available : Available before value)
    (closed : value.free = []) :
    ∃ result after, Head value before result after ∧ Keeps before after ∧ Available after result ∧
      result.free = [] ∧ Ordinary result ∧ Rows value before result after := by
  obtain ⟨result,after,head,keeps,returned,noFree,ordinary⟩ := Head.complete value before ready available closed
  refine ⟨result,after,head,keeps,returned,noFree,ordinary,?_⟩
  cases head with
  | read fuel edges middle exposed rebuilt =>
      have source := read_rows fuel value before ready available closed edges middle exposed
      have physical := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value before
        ready.semantic ready.covered available closed
      have resident := physical.edges edges middle exposed
      have closedEdges := physical.closed edges middle exposed
      have last := SourceEqualityRequiredCache.node edges middle source.1.ready resident closedEdges
      have exactRows := EqualityLeafProjectionPhysical.makeNode_edges edges middle
        source.1.ready.semantic.1.normal.facts.coherent source.1.ready.semantic.1.normal.facts.linked resident
      rw [rebuilt] at last exactRows
      intro index row selected
      have included : row ∈ edges := (List.mem_filter.mp
        (canonicalEdges_member _ row (exactRows ▸ List.mem_of_getElem? selected))).1
      obtain ⟨terminal,entry,originals,depth,free,sourceIndex,branch,later,found⟩ := source.2 row included
      have finalKeeps := later.trans last.1
      have known := branch.verified
      exact ⟨terminal,entry,originals,depth,free,sourceIndex,branch,finalKeeps,
        branch.warm finalKeeps.growth,found,terminal_calls entry originals depth free after finalKeeps.ready
          (finalKeeps.available _ known.2.1) known.2.2 row (List.mem_of_getElem? found)⟩

/-- An actual completed Head has the same chronological terminal-row receipts. -/
theorem actual [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before) (available : Available before value)
    (closed : value.free = []) (result : Value Symbol Guard) (after : State Symbol Guard)
    (head : Head value before result after) :
    Keeps before after ∧ Available after result ∧ result.free = [] ∧ Ordinary result ∧ Rows value before result after := by
  obtain ⟨chosen,final,produced,keeps,returned,noFree,ordinary,rows⟩ := complete value before ready available closed
  obtain ⟨rfl,rfl⟩ := produced.unique head
  exact ⟨keeps,returned,noFree,ordinary,rows⟩

end MicroCFTA.SourceCurrentRecursiveHeadChainRows
