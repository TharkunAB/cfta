# State renaming and merging

`StateMap` follows `Data.CFTA.mapStates`. It gathers all rows that receive the
same name. Each transition retains its symbol, ordered children, and guard.
`edge_exact` characterizes every output transition.

`map_complete` proves that state merging retains every original accepted term.
`map_exact` proves exact language preservation when the rename is injective.
Both results include cyclic graphs. `merging_can_add_terms` gives a checked
example in which a non-injective rename adds a term at the initial state.
This is the public operation's intended merging behavior.

The finite state type represents the keys of a closed validated source table.
Concrete map ordering and identity representation remain adapters. Guards
retain their original term interpretation; the operation changes state names
only.
