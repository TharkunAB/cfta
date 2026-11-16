# Proof design

UNCOMPILED. Root owns the strict compiler check.

The private KeyOrigin property states only seen=[] implies free=[]. CodeOrigin adds this property to actual node, edge, and enter domains. Each source enter also records that its identity pair is absent from its parent seen set. The enter continuation requires KeyOrigin only of the actual entered domain. These predicates contain no semantic payload or model.

The proof starts from the literal empty-domain root. It proves the source compiler and actual checked edge-body continuation preserve CodeOrigin. Physical node_started and edge_started identify the exact requested payload on warm evaluating hits. Direct node lookup uses lookupNode_direct. No inherited semantic law is needed.

The actual Trace then propagates this control property with physical validity from its own per-step checks. At its literal enter endpoint, entered_key derives the actual extension from the reached physical cache. Equality with the original singleton-seen key makes every parent seen pair equal the newly added pair. The selected source Mu guard excludes that pair from the parent. Thus parent.seen=[]; the propagated KeyOrigin supplies parent.free=[]; both key fields identify emptyKey.

This is not full operand admission. Identifying the old full U/P values, proving the old pattern closed, and applying the chronological semantic IH remain separate. The statement adds no restriction to arbitrary original full closed P. The result preserves the actual full operands and continuation and uses no extra observation step or algorithm budget.

The end statement and appendable probes were frozen before writing the proof. Their bytes remain unchanged.
