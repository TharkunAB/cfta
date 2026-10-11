# Attained recursive minima

`MinimumWitness.lean` closes the existence part of the minimum-size contract.
`finite_attains` proves that each finite source minimum has an actual member.
`recipe_attains` transports a witnessed recursive assumption through each
typed source operation. `finiteProbe_witness` follows every step of the actual
decreasing probe. Each retained assumption has a finite derivation.

`assumption_none_exact` proves that the probe reports no finite minimum exactly
when the typed recursive language has no finite derivation. `assumption_minimum`
proves that each successful probe returns the least attained size. Thus the
recursive compiler does not need an assumed productivity or minimum-correctness
postcondition. These results use the source metadata algorithm, not a separate
search through all terms.

The source syntax and runtime boundaries are the same as in
`notes-recursive-source.md`. These results cover one typed recursive knot.
