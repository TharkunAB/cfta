theorem render_replays (native : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (fuel uv : Nat) :
    Replays (render (EnumGuard := EnumGuard) native marker fuel uv)
