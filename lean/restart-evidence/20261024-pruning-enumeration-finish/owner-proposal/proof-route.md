# Body construction plan only

1. Split the two implications. The Empty implication substitutes result and reduces existing finish to raw[]. No other producer is needed there.
2. In the nonempty implication derive sourceInside/targetInside by explicit Exists.elim from the exact stored equations. Call the existing write producer once, with no extra state or successful suffix premise.
3. Match handles with sameHandle from writtenEncoded.symm.trans encoded and constructor injectivity. Substitute writtenHandle and middle using the returned exact equality. The obtained written Success is deliberately unused.
4. The local raw proof cases the five Value tags. Empty contradicts nonempty; the remaining four existing finish branches reduce to the exact assimilated singleton. No new local instance is needed.
5. Use the exact middle target read through the final source set via List.getElem?_set_ne (Ne.symm different). Derive the source read using sourceInside and List.length_set.
6. For final PendingRealized, introduce slot/node/scs/stored. Convert the actual final lookup to membership in the outer source set. The old branch returns to middleRealized via an actual oldSlot lookup. The fresh branch equates a pending constructor to eliminated and is impossible.

This is a source-level proof plan, not a Lean body or candidate. All scopes and field types are in the machine inventory.
