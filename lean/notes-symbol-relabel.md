# Symbol copying and equality guards

`SymbolRelabel.termMap` copies every symbol and retains child order.
`path_map` proves that path lookup commutes with this copy. It covers missing
paths. `termMap_injective` proves that an injective symbol map is injective
on complete finite trees. `equality_exact`, `equality_guard`, and `tests_exact`
then prove preservation of path equalities and their finite conjunctions.

`graphMap` follows the row copy in `Data.CFTA.mapSymbols` and the ordinary
edges of `Gen.Internal.Support.relabel`. `graph_exact` proves that the copied
graph's finite language is exactly the image of the original language.
The proof applies to cyclic graphs. Its `GuardLaw` premise is local to each
source edge and each finite term. It does not assume graph preservation.
Injective relabelling discharges this law for unchanged equality constraints.
Liquid constraints need their own symbol and annotation transport law.

`noninjective_changes_equality` proves a necessary limit. Collapsing two leaf
symbols makes a previously false path equality true. Retaining constraints
while erasing symbols is therefore not an unconditional image-language
optimization. This is a contract distinction, not a new reported source bug.

The graph theorem does not establish the recursive memo and fresh-binder
schedule of `Support.relabel`. Its port must connect those operations to the
copied finite graph. Public `mapSymbols` must also pass its ranked-alphabet
validation. Concrete inspection labels must preserve the identity required
by the semantic symbol map.

Validation: `lake -d lean build MicroCFTA.SymbolRelabel`.
