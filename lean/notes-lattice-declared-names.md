# Parser-validated formula name scope

`LatticeDeclaredNames` proves that successful parsing checks every free name
in the original full formula. Arithmetic parsing checks both operands before
normalization. Boolean parsing checks every child before intersection or
union. A canceled coefficient or an empty region therefore cannot hide an
unknown variable. Unsupported applications, division, modulo, casts,
conditionals, and quantifiers fail rather than bypass this check.

`term_declared`, `parseTerm_declared`, and `atom_declared` follow the actual
arithmetic calls and their error precedence. `formula_declared`,
`all_declared`, and `any_declared` follow the mutual full-formula traversal.
The proof retains the concrete declaration lookup for every free name.
`points_declared` lifts it through the public constructor. It uses actual
lookup readback to establish membership in the declaration list.

`points_scoped` discharges `OpenIntegerKeys.Scoped` after successful public
compilation over the reserved integer names. `points_leafScoped` discharges
the integer leaf's original one-value-name convention. `integerGroup_exact`
then proves the actual finite leaf's renamed tuple domain without an extra
scope premise. `elimination_declared` covers failures after parsing.
`retained_leafScoped` also validates the scope of an unbounded leaf retained
for a parent condition. Formula parsing errors remain errors.

These results close the explicit parser-to-scope boundary in
`notes-open-integer-source.md` for finite and retained unbounded leaves.
They do not claim that an unbounded leaf has a finite enumeration or known
point count. They do not prove that every later constructor computes the
correct parent formula; that remains a separate source transformation.

Validation: the pinned Lean 4.34.1 build passes. No admitted declaration or
native proof evaluation is used. No Haskell source changed.
