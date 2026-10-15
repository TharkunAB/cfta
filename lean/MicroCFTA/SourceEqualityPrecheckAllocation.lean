import MicroCFTA.SourceEqualityConstraintMemoAllocation

/-!
# Native equality precheck allocation receipts

Two physical empty payloads return without changing the operation state.
Other inputs combine own equalities before inherited equalities. A rejected
combination empties the children. A live combination orders the original
own records. Completed combination allocations need not become outer keys.
Runtime demand adequacy remains separate.
-/
namespace MicroCFTA.SourceEqualityPrecheckAllocation
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Valid Grows)

/-- Execute the actual native guards through the completed combination cache. -/
noncomputable def precheck (own inherited : Value) (before : State) :
    Except String SourceEqualityPrecheck.Branch × State :=
  if SourceEqualityPrecheck.isEmpty own.payload && SourceEqualityPrecheck.isEmpty inherited.payload then
    (.ok .unchanged, before)
  else
    let combined := SourceEqualityConstraintMemoAllocation.combine own inherited before
    match combined.1 with
    | .error message => (.error message, combined.2)
    | .ok .contradiction => (.ok .emptyChildren, combined.2)
    | .ok (.live _ _) => ((SourceEqualityPrecheck.unsafeOrdered own.payload).map .classes, combined.2)

/-- Both physical empty inputs retain the complete state before combination and ordering. -/
theorem precheck_empty (ownIdentity inheritedIdentity : Nat) (before : State) :
    precheck (.live ownIdentity []) (.live inheritedIdentity []) before = (.ok .unchanged, before) := rfl

private theorem combination_rejects (own inherited : SourceEqualityPrecheck.Constraint) (value : Value)
    (done : SourceEqualityInheritedPayload.combine own inherited = .ok value.payload) :
    SourceEqualityPrecheck.rejects (SourceEqualityPrecheck.combine own inherited) =
      match value with
      | .contradiction => true
      | .live _ _ => false := by
  rw [SourceEqualityInheritedPayload.combine_readback] at done
  cases combined : SourceEqualityPrecheck.combine own inherited with
  | timeout => exact False.elim (SourceEqualityPrecheck.combine_complete own inherited combined)
  | contradiction =>
      cases value with
      | contradiction => rfl
      | live identity records =>
          simp only [combined, SymbolicEqualityBridge.resultClasses, SourceEqualityPhysicalPayload.read,
            Value.payload, Except.ok.injEq] at done
          cases done
  | normalized classes =>
      cases built : SourceEqualityClassOrder.recordsOf classes with
      | none => simp only [combined, SymbolicEqualityBridge.resultClasses, SourceEqualityPhysicalPayload.read, built] at done; cases done
      | some records =>
          cases value with
          | contradiction =>
              simp only [combined, SymbolicEqualityBridge.resultClasses, SourceEqualityPhysicalPayload.read, built,
                Value.payload, Except.ok.injEq] at done
              cases done
          | live identity original => rfl

/-- The allocated precheck returns the exact existing answer and preserves valid growing caches. -/
theorem precheck_correct (own inherited : Value) (before : State) (valid : Valid before)
    (ownReady : Ready before.constraints own) (inheritedReady : Ready before.constraints inherited) :
    (precheck own inherited before).1 = SourceEqualityPrecheck.precheck own.payload inherited.payload ∧
      Valid (precheck own inherited before).2 ∧ Grows before (precheck own inherited before).2 := by
  by_cases empty : SourceEqualityPrecheck.isEmpty own.payload && SourceEqualityPrecheck.isEmpty inherited.payload
  · simp only [precheck, empty, ↓reduceIte]
    exact ⟨by simp only [SourceEqualityPrecheck.precheck, empty, ↓reduceIte], valid,
      SourceEqualityConstraintMemoAllocation.grows_refl before⟩
  · obtain ⟨result, completed, resultValid, _, payload, resultGrows⟩ :=
      SourceEqualityConstraintMemoAllocation.combine_correct own inherited before valid ownReady inheritedReady
    have tag := combination_rejects own.payload inherited.payload result payload
    cases result with
    | contradiction =>
        simp only [precheck, empty, Bool.false_eq_true, ↓reduceIte, completed]
        exact ⟨by simp only [SourceEqualityPrecheck.precheck, empty, tag, Bool.false_eq_true, ↓reduceIte], resultValid, resultGrows⟩
    | live identity records =>
        simp only [precheck, empty, Bool.false_eq_true, ↓reduceIte, completed]
        exact ⟨by simp only [SourceEqualityPrecheck.precheck, empty, tag, Bool.false_eq_true, ↓reduceIte], resultValid, resultGrows⟩

/-- Every valid ready precheck completes with the exact safe source branch and its allocation trace. -/
theorem precheck_complete (own inherited : Value) (before : State) (valid : Valid before)
    (ownReady : Ready before.constraints own) (inheritedReady : Ready before.constraints inherited) :
    ∃ branch, (precheck own inherited before).1 = .ok branch ∧
      SourceEqualityPrecheck.precheck own.payload inherited.payload = .ok branch ∧
      Valid (precheck own inherited before).2 ∧ Grows before (precheck own inherited before).2 := by
  obtain ⟨exact, afterValid, grows⟩ := precheck_correct own inherited before valid ownReady inheritedReady
  obtain ⟨branch, safe⟩ := SourceEqualityPrecheck.precheck_safe own.payload inherited.payload
  exact ⟨branch, exact.trans safe, safe, afterValid, grows⟩

end MicroCFTA.SourceEqualityPrecheckAllocation
