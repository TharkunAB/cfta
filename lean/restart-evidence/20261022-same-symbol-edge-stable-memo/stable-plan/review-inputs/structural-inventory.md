# Stable pair writer: structural route

The smallest route uses explicit completed call paths. No general invariant for all wrapper controls is needed. [C63–106]
A strict ordering swap can call the canonical pair only once. Native steps keep the pair memo unchanged. [C63–106]
The existing private native_done and ret_done recover the actual native trace and exact pending.foldl finish memo. [C132–179]
Those helpers are private. A separate module cannot import their friendly names; additive public exposure or local literal inversion remains necessary.
At call[] entry, derive the three paths from genuine Valid, all-returned, and canonical presence: ready hit, swapped reverse hit, and both misses. [C,M,T]
A ready hit changes neither state. A swapped hit allocates and finishes only its original handle. Both misses finish one or two fresh handles. [C63–106,226–334]
The missing structural fact is the exact allocation domain: final cells come from old cells plus those fresh handles. Derive it from literal lookup/setStatus definitions. [M53–160]
Returned alone does not supply that fact. Once it is available, old all-returned plus finish_evaluating yields final all-returned. [R,T]
lookup_valid, demand_valid, finish_valid and lookup_extends preserve exact key links and table extension; demand/finish do not change the table. [M,R,C123–130]
Canonical presence is required and re-established only at completed call boundaries. Temporary published noncanonical cells can precede their canonical cells. [C63–106]
No semantic law is needed for those structural conclusions. A returned-law refinement still requires the actual canonical native completion law from its genuine current packet. [F99–146]
Use the law for the actual captured operands. At hits, current residency/coherence and key equality identify those operands; do not assume them equal. [E157–166]
Store the law for canonicalized captured pairs. This avoids an unproved execution-symmetry substitution. EdgeLaw remains fixed to source/model/ranks. [L69–81]
A generic pending-stack proof would also need exact membership, distinct handles, outstanding-cell coverage, and phase-specific canonical exceptions. It is a larger fallback, not the minimal route.
No existing public all-returned, canonical-presence, or exact allocation-domain endpoint was found in the selected wrapper/lifecycle files. No source-size promise is made before a concrete header.
This frozen inventory has no new declaration, proof body, completion premise, or future-state premise. Only reads, static hashes, and new selected cuts were made; no checker/runtime/Git/official action ran.
