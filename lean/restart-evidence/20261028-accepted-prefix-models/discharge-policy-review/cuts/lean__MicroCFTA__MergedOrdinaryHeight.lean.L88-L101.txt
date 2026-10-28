/-- The source recursive-boundary test stops at Mu and explicit union records. -/
def recursiveBoundary : Value Symbol Guard → Bool
  | .mu .. | .union .. => true
  | _ => false

/-- A closed operand without a recursive boundary is empty or an ordinary node. -/
theorem ordinary_operand (value : Value Symbol Guard) (closed : value.free = [])
    (clear : recursiveBoundary value = false) :
    value = .empty ∨ ∃ entry edges depth free, value = .node entry edges depth free := by
  cases value <;> simp_all [recursiveBoundary, Value.free]

/-- Every actual child of a closed ordinary record is closed. -/
theorem closed_child (state : State Symbol Guard) (coherent : Coherent state)
    (entry : Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Guard))
