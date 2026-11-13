# Initial preparation repair 2

Status: frozen uncompiled repair. Header52/9e1193a1 is unchanged.
Base: actual check3 source394. All earlier sources and reports remain.
The helpers and the preceding observed action/Core derivation are unchanged.

The adapter is generalized in actualPrefix with its SAME literal startup.
The proof then cases that actual Option. The none branch needs no simp.
The some branch unfolds only the pure Right equation. The unused adapted
simp argument is removed. The SAME adapted equation supplies adapt_core;
its literal startup is definitionally the existing startup alias.

The earlier invalid .ok in an empty raw-list change is now Except.ok.
Its empty list carries the existing List(Except Error(Unit x Core)) type.
This fixes only elaboration in the reject contradiction branch.

No compiler, live source, Git, board or Haskell operation was used.
