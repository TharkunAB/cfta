theorem pending_write_semantics
    (language : NodeLanguage Symbol) (residualMeaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (before after : State Symbol EnumGuard)
    (uv oldHandle newHandle : Nat) (scs : List Suspended)
    (stored : before.values[uv]? = some (.unenumerated (some oldHandle) scs))
    (written : Success (setValue uv (.unenumerated (some newHandle) scs)) before () after)
    (narrows : ∀ term, language newHandle term → language oldHandle term) :
    Satisfies language residualMeaning assignment after ↔
      Satisfies language residualMeaning assignment before ∧ language newHandle (assignment uv) := by
