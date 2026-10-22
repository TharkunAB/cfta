This is a source-only proposal for the next semantic step. H18 remains an uncompiled candidate at this cut.
The scan calls H15 with (pivot, candidate). It tests common=candidate before common=pivot. Numeric canonical ordering does not change that control order. [S01,S09,S11]
H15 returns the SAME common and final wrapper, result residency, canonical empty-domain EdgeLaw, final Good, and actual Extension. Its remaining packet stays available to the scan. [S01]
Only EdgeLaw.sound and sound_empty_domain are needed. Neither completeness nor conversion from bounded ranks is needed. [S02,S03]
H18 supplies EdgeInputs and physical row equality for each literal operand in the SAME admitted inputModel. It does not give these facts for an arbitrary unadmitted parent. [S12]
The required parent admission is inputModel.valid(inputOf parent). H17 cluster_complete does not currently take this premise. RankedInput and Contextual do not silently supply it. [S10,S12]
Use source Facts.linked and parent availability to obtain both source row records. Transport them to the exact final heap with source-to-before growth followed by H15 Extension.heap. [S04,S05,S08]
Final Good.native.machine.1.coherent is coherence of this exact heap. With H15 result residency, edge_identity_unique converts either tested ID equality to equality of the full row payload. [S01,S04,S05,S06,S07]
Apply the canonical law at each ambient environment. If canonical ordering swapped the operands, swap the resulting conjunction only. Do not infer execution symmetry. [S01,S02,S03]
If common has the candidate identity, candidate language is included in pivot language. If it has the pivot identity, pivot language is included in candidate language. Both directions hold for every ambient environment.
Recommendation: one small completed-result deletion adapter, composed immediately with the SAME existing H15 witness in the scan proof. Do not introduce another comparison execution or a packet datatype.
An actual comparison producer that also returns both deletions is possible, but must repeat H15's long postcondition to retain the packet needed by later calls. It is larger than the adapter plus direct call-site composition.
The adapter's law, residency, coherence, and growth arguments are actual H15/source outputs at its use site. They are not new assumptions of desired success in a cluster theorem.
No exact Lean header or theorem body is authorized or included here. The declaration choice remains subject to root review.
This does not yet prove the scan's union-language invariant, clustering, node reconstruction, Mu traversal, or withoutRedundantEdges/Haskell correspondence.
Arity authored H15, H16, H17, and the H18 candidate. This inventory checks their interfaces and does not claim an independent re-proof.
