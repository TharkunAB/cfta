# Shared Force and Leaf forecast review

Reviewed 2026-10-17 10:55 CEST.

`forceProfile`, `ForceReserved`, and `forceFuel` use the initial `found` value.
A hit retains the profile, needs no Target reservation, and uses zero Target fuel.
A miss uses the existing Target profile, reservation, and shared worker fuel.
The caller must set `found` to the initial target slot's `Option.isSome` value.
The caller must supply the literal `operandPaths` list used by that Force call.

`leafProfile` adds one native forecast after the exact Force profile.
`LeafReserved` supplies the Force reservation and room at that query entry.
`leafFuel` covers both stages with their maximum.
The inflation lemmas retain all four initial profile components.
The two reservation projections retain the exact intermediate profile.
The two fuel inequalities use the same Force return profile.

The three imported kernels cover a present slot, an empty missing Target,
and a singleton miss followed by a hit at the first Leaf return profile.
The third kernel derives both query reservations from one initial numeric
condition on the final computed profile. It supplies no intermediate room fact.
The kernels keep the instruction and mass ceilings symbolic.

This component specifies pure schedules. It constructs no Force, Leaf,
Target, or native execution. It proves no slot certificate or output Cap.
It adds no source-domain, guard, callback, or successful-result premise.
The initial slot certificate and the actual state joins remain caller obligations.
No Haskell source changed. No Haskell behavior defect was identified here.
