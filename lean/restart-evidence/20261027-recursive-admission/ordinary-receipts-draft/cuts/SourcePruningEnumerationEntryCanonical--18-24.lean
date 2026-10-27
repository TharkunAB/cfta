theorem enter_canonical
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (target handle : Nat)
    (bucket : List Suspended) (decoded : Value Symbol NativeGuard)
    (canonical : Canonical before)
    (success : Success (enter heap fuel uv) before (target, handle, bucket, decoded) after) :
    Canonical after ∧ ValidSuspended bucket := by
