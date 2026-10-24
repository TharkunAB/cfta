import MicroCFTA.SourcePruningEnumerationNodes

namespace MicroCFTA.SourcePruningEnumerationIdentity
open InternedConstructorTemplates InternedRecordCoherence
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}

/-- A coherent successful lookup recovers the same encoded handle. -/
theorem lookup_encode (heap : InternedConstructorTemplates.State Symbol Guard)
    (handle : Nat) (value : InternedConstructorTemplates.Value Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (found : lookupNode heap handle = some value) : encodeNode value = some handle := by
  cases handle with
  | zero =>
      change some (.empty : Value Symbol Guard) = some value at found
      cases Option.some.inj found
      rfl
  | succ identity =>
      cases issued : heap.nodes.issued identity with
      | none =>
          simp only [lookupNode, issued] at found
          cases found
      | some key =>
          cases canonical : heap.nodes.table key with
          | none =>
              simp only [lookupNode, issued, canonical] at found
              cases found
          | some entry =>
              by_cases winner : entry.identity = identity
              · have stored : heap.nodeRecords key = some value := by
                  simpa only [lookupNode, issued, canonical, ite_eq_left winner] using found
                obtain ⟨actual, actualStored, fields⟩ := coherent.nodes key value stored
                have same : actual = entry := by
                  exact Option.some.inj (actualStored.symm.trans canonical)
                subst actual
                have carried : InternedRecordCoherence.entryOf value = some entry := by
                  exact InternedRecordCoherence.fields_entry key entry value fields
                cases value with
                | empty | reference => cases carried
                | node valueEntry _ _ _ | union valueEntry _ _ _ | mu valueEntry _ _ _ =>
                    cases Option.some.inj carried
                    simp only [encodeNode, winner]
              · simp only [lookupNode, issued, canonical, ite_eq_right winner] at found
                cases found

end MicroCFTA.SourcePruningEnumerationIdentity
