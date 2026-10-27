/-- Clearing a stored bucket removes exactly its suspended assignment restrictions. -/
theorem clear_satisfies
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before after : State Symbol EnumGuard)
    (uv : Nat) (node : Option Nat) (scs : List Suspended)
    (stored : before.values[uv]? = some (.unenumerated node scs))
    (written : Success (setValue uv (.unenumerated node [])) before () after) :
    Satisfies language meaning assignment before ↔
      Satisfies language meaning assignment after ∧
        ∀ sc ∈ scs, Suspended.Holds assignment (assignment uv) sc := by
