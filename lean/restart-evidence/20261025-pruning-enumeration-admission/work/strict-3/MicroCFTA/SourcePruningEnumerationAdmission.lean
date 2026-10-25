import MicroCFTA.SourcePruningEnumerationEntry
import MicroCFTA.SourcePruningEnumerationStorage

namespace MicroCFTA.SourcePruningEnumerationAdmission
open EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Derive entry, inherited bounds and the ordinary nonterminal branch stream from the actual pending slot. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (before : EnumerationState.State Symbol Constraint) (uv : Nat)
    (storage : StorageValid before) (inside : uv < before.counter)
    (realized : PendingRealized heap before) :
    ∃ (fuel : Nat) (readValue : EnumerationState.UVarValue Symbol)
      (readAfter : EnumerationState.State Symbol Constraint),
      (∀ (extra : Nat), ExceptT.run (getValue (fuel + extra) uv before) =
        [.ok (readValue, readAfter)]) ∧
      Frame before readAfter ∧
      match readValue with
      | .unenumerated (some handle) scs =>
          ∃ (target : Nat) (decoded : InternedConstructorTemplates.Value Symbol Constraint)
            (compressed entered : EnumerationState.State Symbol Constraint),
            Frame before compressed ∧
            (∀ (extra : Nat), ExceptT.run (representative (fuel + extra) uv readAfter) =
              [.ok (target, compressed)]) ∧
            compressed.values[target]? = some (.unenumerated (some handle) scs) ∧
            lookupNode heap handle = some decoded ∧
            InternedProbeProvenance.Available heap decoded ∧ decoded.free = [] ∧
            entered = {compressed with expansionAncestry :=
              if MergedOrdinaryHeight.recursiveBoundary decoded then
                (recursionKey handle scs :: compressed.recursionAncestry target).eraseDups
              else compressed.recursionAncestry target} ∧
            (∀ (extra : Nat), ExceptT.run (SourcePruningEnumerationEntry.enter heap (fuel + extra) uv before) =
              [.ok ((target, handle, scs, decoded), entered)]) ∧
            StorageValid entered ∧ PendingRealized heap entered ∧
            (∀ sc ∈ scs, sc.var < entered.counter) ∧
            (match decoded with
            | .node _ storedEdges _ _ =>
                if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then True else
                  ∀ (selectedEdges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint)),
                    (∀ edge ∈ selectedEdges, edge ∈ storedEdges) →
                    ∃ branchRows : List (List (Except EnumerationState.Error
                        (Option (Option (Fragments.Fragment Symbol)) × EnumerationState.State Symbol Constraint))),
                      Language.All₂ (fun edge rows =>
                        if arityAllows edge.children.length scs then
                          match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
                          | none => rows = [.ok (none, entered)]
                          | some _ =>
                              ∃ (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
                                (result : Option (Fragments.Fragment Symbol))
                                (after : EnumerationState.State Symbol Constraint),
                                SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action ∧
                                Success action entered result after ∧ rows = [.ok (some result, after)] ∧
                                after.counter = after.values.length ∧ PendingRealized heap after ∧
                                StorageValid after ∧
                                (∀ (fragment : Fragments.Fragment Symbol),
                                  result = some fragment → FragmentBound after.counter fragment) ∧
                                entered.counter ≤ after.counter
                        else rows = []) selectedEdges branchRows ∧
                      SourcePruningEnumerationOrdinaryBranches.run scs selectedEdges entered = branchRows.flatten
            | _ => True)
      | _ => ∀ (extra : Nat), ExceptT.run (SourcePruningEnumerationEntry.enter heap (fuel + extra) uv before) = [] := by
  obtain ⟨fuel, readValue, readAfter, readExact, readFrame, packet⟩ :=
    SourcePruningEnumerationEntry.complete heap before uv storage inside realized
  refine ⟨fuel, readValue, readAfter, readExact, readFrame, ?_⟩
  cases readValue with
  | enumerated _fragment => exact packet
  | eliminated => exact packet
  | unenumerated node scs =>
    cases node with
    | none => exact packet
    | some handle =>
      obtain ⟨target, decoded, compressed, entered, fullFrame, captureExact,
        storedCapture, decodedLookup, available, closed, ancestry, entryExact,
        enteredStorage, enteredRealized⟩ := packet
      have enteredStored : entered.values[target]? = some (.unenumerated (some handle) scs) := by
        rw [ancestry]
        exact storedCapture
      have bounded : ∀ sc ∈ scs, sc.var < entered.counter := by
        exact enteredStorage.values _ (List.mem_of_getElem? enteredStored)
      have branchAdmission : match decoded with
            | .node _ storedEdges _ _ =>
                if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then True else
                  ∀ (selectedEdges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint)),
                    (∀ edge ∈ selectedEdges, edge ∈ storedEdges) →
                    ∃ branchRows : List (List (Except EnumerationState.Error
                        (Option (Option (Fragments.Fragment Symbol)) × EnumerationState.State Symbol Constraint))),
                      Language.All₂ (fun edge rows =>
                        if arityAllows edge.children.length scs then
                          match SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
                          | none => rows = [.ok (none, entered)]
                          | some _ =>
                              ∃ (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol)))
                                (result : Option (Fragments.Fragment Symbol))
                                (after : EnumerationState.State Symbol Constraint),
                                SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action ∧
                                Success action entered result after ∧ rows = [.ok (some result, after)] ∧
                                after.counter = after.values.length ∧ PendingRealized heap after ∧
                                StorageValid after ∧
                                (∀ (fragment : Fragments.Fragment Symbol),
                                  result = some fragment → FragmentBound after.counter fragment) ∧
                                entered.counter ≤ after.counter
                        else rows = []) selectedEdges branchRows ∧
                      SourcePruningEnumerationOrdinaryBranches.run scs selectedEdges entered = branchRows.flatten
            | _ => True := by
        cases decoded with
        | empty => trivial
        | reference _name => trivial
        | union _entry _members _depth _free => trivial
        | mu _entry _body _depthShape _ordinaryShape => trivial
        | node entry storedEdges depth free =>
          by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
          · simp only [terminal, ↓reduceIte]
          · simp only [terminal, Bool.false_eq_true, ↓reduceIte]
            intro selectedEdges selected
            exact SourcePruningEnumerationStorage.complete
              scs heap entry storedEdges selectedEdges depth free ready available closed
              selected entered enteredRealized enteredStorage bounded
      refine ⟨target, decoded, compressed, entered, fullFrame, captureExact,
        storedCapture, decodedLookup, available, closed, ancestry, entryExact,
        enteredStorage, enteredRealized, bounded, ?_⟩
      simpa only using branchAdmission

end MicroCFTA.SourcePruningEnumerationAdmission
