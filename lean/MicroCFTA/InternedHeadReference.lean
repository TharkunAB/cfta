import MicroCFTA.InternedUnionRetention

/-!
# Free references at the end of an actual stored Mu head chain

The source metadata equation for Mu removes its own interned reference.
It therefore determines the free names of a chain that ends at Rec without
any assumption about callback behavior or smart-union normalization.
-/
namespace MicroCFTA.InternedHeadReference
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedUnionSeparation
open InternedBinderProtocol (Reference NodeKey)

/-- Follow only stored Mu bodies and retain the final bare reference. -/
def terminal : Value Symbol Guard → Option Reference
  | .reference name => some name
  | .mu _ body _ _ => terminal body
  | _ => none

/-- Mask each actual enclosing binder while following the same head chain. -/
def headReference : Value Symbol Guard → Option Reference
  | .reference name => some name
  | .mu entry body _ _ => match headReference body with
      | none => none
      | some name => if name = .interned entry.identity then none else some name
  | _ => none

/-- A free reference at the head is the complete stored free-reference set. -/
theorem headReference_free (value : Value Symbol Guard) (name : Reference)
    (found : headReference value = some name) : value.free = [name] := by
  cases value with
  | empty | node | union => simp [headReference] at found
  | reference other => simpa [headReference, Value.free] using found
  | mu entry body depth ordinary =>
      cases inner : headReference body with
      | none => simp [headReference, inner] at found
      | some other =>
          by_cases bound : other = .interned entry.identity
          · simp [headReference, inner, bound] at found
          · have equal : other = name := by simpa [headReference, inner, bound] using found
            subst other
            simp [Value.free, headReference_free body name inner, bound]
termination_by sizeOf value

/-- Every stored head chain ending at Rec has either no free name or exactly
that terminal name. This includes raw unused binders. -/
theorem terminal_free (value : Value Symbol Guard) (name : Reference)
    (found : terminal value = some name) : value.free = [] ∨ value.free = [name] := by
  cases value with
  | empty | node | union => simp [terminal] at found
  | reference other => right; simpa [terminal, Value.free] using found
  | mu entry body depth ordinary =>
      rcases terminal_free body name found with closed | one
      · left; simp [Value.free, closed]
      · by_cases bound : name = .interned entry.identity
        · left; simp [Value.free, one, bound]
        · right; simp [Value.free, one, bound]
termination_by sizeOf value

/-- An open stored Mu cannot terminate its head chain at its own reference.
Such a chain would have no free names after the outer metadata deletion. -/
theorem open_terminal_not_self (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    terminal body ≠ some (.interned entry.identity) := by
  intro found
  rcases terminal_free body (.interned entry.identity) found with closed | own
  · exact opened (by simp [Value.free, closed])
  · exact opened (by simp [Value.free, own])

/-- The sole external name of an open head chain differs from the outer binder. -/
theorem open_terminal_external (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (name : Reference) (opened : (Value.mu entry body depth ordinary).free ≠ [])
    (found : terminal body = some name) :
    body.free = [name] ∧ name ≠ .interned entry.identity := by
  have different : name ≠ .interned entry.identity := by
    intro same
    apply open_terminal_not_self entry body depth ordinary opened
    simpa [same] using found
  rcases terminal_free body name found with closed | one
  · exact False.elim (opened (by simp [Value.free, closed]))
  · exact ⟨one, different⟩

/-- Maximum cached depth always bounds the consecutive head-binder count.
No child metadata equation is needed for this one-sided comparison. -/
theorem head_le_depth (value : Value Symbol Guard) : InternedGateRank.headRank value ≤ value.depth := by
  cases value with
  | empty | reference | node | union => simp [InternedGateRank.headRank, Value.depth]
  | mu entry body depth ordinary =>
      exact Nat.add_le_add_right (head_le_depth body) 1
termination_by sizeOf value

/-- Smart cleanup alone never adds a head binder. Root union normalization
has its own separate singleton analysis. -/
theorem cleanup_rank (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) :
    InternedGateRank.headRank (cleanup (.mu entry body depth ordinary)) ≤
      InternedGateRank.headRank body + 1 := by
  simp only [cleanup]
  split
  · omega
  · split <;> simp [InternedGateRank.headRank]

/-- A raw direct self-cycle is closed by the exact stored metadata equation.
The source gate stops before its nondecreasing unfolding. -/
theorem raw_self_closed (entry : Interned NodeKey) (depth ordinary : Value Symbol Guard) :
    (Value.mu entry (.reference (.interned entry.identity)) depth ordinary).free = [] := by
  simp [Value.free]

end MicroCFTA.InternedHeadReference
