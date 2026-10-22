# Stable pair writer — independent structural review (2026-10-22 01:10:50 CEST)
SOURCE-CLEAR for the bounded structural design. The exact header and proof body remain separate review gates.
I read the complete 18-line inventory, all 14 cuts across seven live sources, and the full H8 contract erratum. All source and cut pins match.
Use completed literal `.call request []` paths. Derive final Valid, all-returned, table extension and canonical presence; do not assume them.
The three paths are a direct ready hit, an original miss with a canonical reverse hit, and both misses.
Initial canonical presence excludes a missing canonical key with a returned reverse key. Valid plus all-returned alone does not exclude that state.
Derive exact cell allocation from lookupOrInsert and setStatus: old cells plus one fresh handle, or two distinct fresh handles after a strict swap.
Returned preserves old returned cells. It supplies neither complete final cell-domain coverage nor final all-returned on its own.
lookup_valid, demand_valid and finish_valid retain structural validity. lookup_extends retains key links; demand and finish retain the table.
Native steps keep the separate pair memo unchanged. Completed ret paths finish the actual one/two handles in LIFO order.
A direct ready hit retains the entire wrapper state. A swapped ready hit finishes only its new original handle; it does not run a new native edge body.
Use current operand residency and heap coherence to identify captured operands with equal identities. Key equality alone does not identify full edge values.
Retain the historical canonical writer law and actual later heap extension for hit reuse. Require a genuine current packet for each new native completion.
Keep each stored law on its canonical captured pair. This avoids assuming unproved execution symmetry for reversed requests.
The H8 contextual EdgeLaw does not imply the independent closed-edge EdgeMeaning contract. No stronger semantic claim follows from this inventory.
Keep sealed H7/H8 unchanged. Local bounded inversion may recover private native_done/ret_done facts; private friendly names cannot be imported.
Exact domain/finish lemmas and three-case inversion are the main size risks for target 260 / hard 350; no concrete body or size guarantee exists yet.
I authored earlier native-store foundations and WarmNextPacket. This reviews new composition; I ran no proof, prepared checker, runtime, Git or network action.
