# Next all-symbol original-parent traversal inventory
Status: SOURCE-ONLY DESIGN CLEAR for the narrow chain below; no header/body/check is authorized. Measured cut: 2026-10-22T23:35:03.323265+02:00.
Primary Haskell dropRedundantEdges is concatMap reduceCluster over clusterByHash edgeSymbol. Its ruleOut checks common==candidate first, then common==pivot and promotes the existing candidate. H16 already preserves that exact order and all outcomes.
clusterByHash uses HashMap.fromListWith (++) on singleton lists, emits HashMap.elems, then reverses each bucket. H21 models that prepend/reverse content boundary. It does not implement HashMap or fix outer key order.
H21 iteration_reverse plus reverse_fromRows and old Iteration.lookup/lookup_some derive each emitted reversed bucket as the exact symbol-filtered original row list. No arity key is introduced.
H21 iteration_permutation plus Sized.groups_perm gives complete occurrence coverage despite arbitrary outer order. Duplicate occurrences remain accounted for; this is not a new Nodup or maximality theorem.
The smallest concrete stateful next result is the proposed finite list/Fin chain of actual H16 group execute equations, each with its own concrete fuel and the exact preceding returned Wrapper.
H20 already produces each completed group and its all-ambient physical union iff from the genuine fixed packet. The next proof needs a list induction generalized over the current full packet and accumulated outputs.
The packet is sufficient: H20 returns Good, Contextual, SemanticReady, Extension, Stable, native Idle, pair-table Extends, Returned and Trace from the SAME initial domain cache.
Extension.heap and Extension.history reconstruct Grows and original-issued history for the next group. Extension.trans, Cache.extends_trans and Returned.trans compose the cumulative effects.
The global source inventory and initialDomains stay fixed. Trace.next_le bounds the current domain counter for ANY number of admitted original-row comparisons.
H15 lines119–122 uses exactly that bound with Room.mono to obtain entry Room from the SAME initial tuple. Therefore no future Room premise or per-group numeric forecast is needed here.
This reuse is specific to the already proved original-source/inventory route. It does not establish finite resources for generated-parent or arbitrary recursive rebuild queries.
Outer iterator order can change native allocations, memo contents and exact output order. Retain each actual sequence; claim all-ambient union equivalence, not equality of final states across permutations.
No global common fuel or new outer interpreter is necessary for the first compositional boundary. A future executable outer control must delegate H16 and preserve all residual/error states; that work is separate.
The actual withoutRedundantEdges caller first performs mapNodesStep. Its rebuilt parents need not remain OriginalInput in the fixed source. The original-parent chain does not solve that rebase problem.
The Mu branch filters body alternatives through unfolding/substitution. It remains outside this ordinary original-parent scope. No public pass, Haskell execution refinement, convergence or whole-goal completion is claimed.
I independently reviewed this new composition inventory. I authored H21 tooling and signature/source/TYPE reviews; Arity authored H20/H21 mathematics. This is no independent re-proof of those established foundations.
All14 selected source identities and24 strict cuts are pinned. Whole snapshots support hashes; only the indexed ranges and the stated earlier complete source reviews are claimed read.
One read-only search tried absent Interned/Types.hs as well as the correct Interned/Type.hs. The correct file and edgeSymbol lines were then read; no prepared tool or root/proof failure occurred.
No Lean header/body, prepared script, compiler/runtime/capped/Git/network command or repository write was made. The proposal remains subject to a fresh declaration gate.
