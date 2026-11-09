# Source Type boundary

The fixture uses `Library [("f", TVar "a", ["f"])] [] [] encoding`, query
argument `x : A`, goal `B`, and size two. It tests `FirstOrder`,
`Curried AnyHead Map.empty`, and `Curried OnlyDefault Map.empty`.

In `cfta-generator/src/Data/CFTA/Gen/Synthesis.hs`, `rawSearchSpace` at
lines 733–744 places the generalized component annotation below the
size-two application and outer filter. A bare component variable expands
to `allTypes`. The literal application equalities at lines 600–607 contain
`[2,0,0]`, `[2,0,1]`, and `[2,0,2]`. At the component annotation these paths
become `[0]`, `[1]`, and `[2]`. That bucket is nonempty and has no terminal.

The recursive branch in `cfta/src/Data/CFTA/Enumeration.hs` at lines
725–730 drops such descendants. The partial renderer uses
`TruncatedRecursion` at line 1053. `programRuns` at synthesis lines
904–925 uses the same underlying run mechanism and removes annotations
when it decodes a Program. `observed.txt` records the literal raw typed
marker, the explicit truncation constructor, and `f x` after decoding.
The finite accepted witness supplies `f` with `A -> B`, so this raw partial
output has a valid typing completion.

The public reduced path returns a typed run with the ordinary annotation
`A -> B`. `solutionsOfSize` returns `f x`. `programsOfSize` returns one
value. The complete output is equal in all three encodings for this input.
These observations apply to this fixture. They do not prove that reduction
removes all opaque Type descendants in every synthesis input.

The existing formal `SourceSynthesisUniverseRequiredBoundary` supplies an
analogous checked `f : a` example. Its `required_child_exceeds_application`
theorem exposes an ordinary singleton arrow annotation with three children.
It uses another query and an earlier execution. It is not a certificate for
the current shared prepared execution in this replay.

The next formal obligation is a structural result for the literal current
`requireAll` receipt. Every strict required prefix must be empty or ordinary.
Its terminal endpoints can remain opaque. The class pass and later native
edits must preserve that prefix certificate. `Annotated`, `TypePath`,
`ValueFields`, origin history and closedness do not contain this property.
The new own-terminal theorem covers direct application and filter Type
fields. The recursive Type annotation of a variable row remains separate.

No production Haskell source changes are part of this packet. No reduced
typing defect or incorrect concrete output is established.
