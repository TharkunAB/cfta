# Exact proposed codec scope

The five STRING fragments contain context 6 lines and public headers 10 lines. They have no definition or theorem bodies. No local instance is needed.

- encodeNode uses the existing Value constructors. Empty maps to zero. Reference has no handle. Every stored node/union/Mu maps to its complete canonical entry identity plus one.
- lookupNode zero returns actual Empty. A positive handle reads the issued key, reads its canonical entry, checks that entry's identity against the requested identity, then reads its full node record. Every absent step or losing candidate returns none. Do not use a default Empty.
- available_readback cases on the actual Value. Closedness excludes Reference. Available.resident and resident_entry derive the stored payload and canonical entry for the remaining three record constructors. Coherent.valid derives the exact issued key. The decoder then returns the same complete Value. No node density, source counter bound, desired result or arbitrary decoder is an input.
- lookupNode_keeps cases on zero/successor, then the two actual Option lookups and the winner condition. Successful before-read data is retained by the exact issued history, canonical table growth and complete node-record growth in Keeps. No new replay theorem or final lookup is assumed.

The full proposed local/case inventories are in scoped-types.json. No let, obtain, helper, IH or recursive call is planned. The two named haves in available_readback are scoped independently to its three stored-constructor branches. The source can use anonymous unused constructor fields.

Root accepted the existing model-handle convention, not an extraction theorem for raw Haskell NodeId. Raw UVar IDs are separate and must remain unchanged in typing keys and hole labels. The codec has no enumeration graph/slot correctness conclusion. Initial slot realization and preservation through actual slot writes remain later consumers.

Proposed whole source:75–115 lines, hard140. The16 context/header lines, about15–22 definition lines, about30–50 proof lines, comments and ordinary spacing fit this bound. Below-target source is valid without padding. Root must review this exact proposal and separately authorize all source bodies and compiler commands.
