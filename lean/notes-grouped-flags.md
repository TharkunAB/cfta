# Closed flags of a recursive key family

`GroupedFlags.lean` models the `recurGrouped.closedIndexes` pass after keys and
minimum sizes settle. Each occurrence receives its key's fixed minimum and the
three flag sets from the preceding body build. Standard map, pay, constructor,
choice, and product operations compute the new flags. Products retain a
size-unguarded flag only beside a sibling whose minimum is zero. Pay retains
termless flags. Constructors and products remove termless flags.

`evaluate_monotone` derives monotonicity from those concrete operations.
`converge` implements the equality-stopping loop with a termination measure:
the number of false entries in the finite key/token/flag table. Each changed
pass adds an entry. `close_fixed` proves stability and `close_least` proves the
result is the least fixed point.

`Derives` specifies finite enclosing-token propagation independently of the
iteration. `close_exact` proves that the table contains every derivable flag
and no other flag. The loop therefore neither loses outer occurrences nor
invents an unsupported guard failure within this source algebra.

The domain contains the fixed body keys and enclosing tokens. A source map
with no rows is represented by the initial all-false table. The first source
key-presence check can add a body build before flag equality can stop; it does
not change the computed flags. The model covers the subsequent fixed-key loop.
The constant source flag inputs represent already constructed outer metadata.
Their own semantic correspondence remains a caller obligation.

The module does not prove that an arbitrary Haskell family builder has fixed
keys after minimum discovery or is expressible in this metadata algebra.
Nested builder translation, fresh token allocation, key-map omission, and
runtime knot evaluation remain explicit boundaries.
