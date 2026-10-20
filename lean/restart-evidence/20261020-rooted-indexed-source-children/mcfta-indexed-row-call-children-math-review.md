# Indexed RowCall children: independent mathematical review

Reviewed 2026-10-20 16:47 CEST. Result: no material issue found in candidate SHA256 `b25200251338bc2d2e71440079297bfdde29ff21160d17071a03239ce3ab56ca`.

This review covers the complete candidate and its source foundations. Exactly one public theorem is present: indexed_child. This review runs no Lean, canonical, or runtime job and adds no proof pair. It changes no candidate, frozen package, or repository file. The candidate remains outside the current Cut/SourceRows checkpoint.

## Actual call and position

The public contract at candidate lines 57–71 consumes joint Context at the source-row schedule's initial heap, a RowCall, and an exact lookup in that call's complete output children. It needs no open-value, Reached, rooted Path, closedness, or desired ancestry premise. Its actual schedule evidence is the supplied RowCall; this theorem does not produce that receipt from a source build by itself.

RowCall retains the original source row index, the exact source edge syntax, its complete output, the actual source-row prefix, the ordered child buildMany call, edge allocation, and the remaining source rows. Its children_eq field equates the physical output children with the actual child results. The candidate uses that exact equality at lines 74–76. Therefore the same childIndex selects the source syntax and the actual physical output child. It does not search by equality or use findIdx. Repeated equal children retain their actual separate positions. The original source-row index is not identified with a canonical output row index.

The private member_call proof at lines 17–54 inverts the actual ordered buildMany schedule. A completed list cannot contain a pending head or tail. At index zero it retains the actual first call and empty prefix. At successor indices it derives Context after the actual earlier source child, recurses into the actual tail, and restores exact take/drop schedules. No completion premise for another run is introduced.

## Joint Context and exact heaps

At lines 72–73 the joint Context for call.current is derived from the actual source-row prefix, using Context.edges and RowCall.earlier. It is not inferred from physical growth or from the weaker Context stored in RowCall. The private extractor then derives joint Context at the selected child's actual entry.

The public heap parameters and fields remain distinct. The parameter middle is the endpoint of the full source buildEdges list. The field call.middle is the endpoint of the selected row's child list. The field call.current is that row's entry. The existential current is the selected child's entry, and next is that child's return. The suffix starts at next and ends at call.middle. The theorem asserts no equality among these distinct stages.

## Physical and issued growth

Lines 79–90 use two actual completed prefixes: the earlier source rows from before to call.current, then the earlier children from call.current to the selected child's entry current. Each prefix is checked with FreshOrdinaryFacts.buildEdges_verified or buildMany_verified, using the facts and available inputs from its actual joint Context.

InternedNestedFacts.Verified at lines 29–34 has separate fields growth and history. Here history means Extends of nodes.issued. It is not NativeMuPublication.History. The candidate obtains physical Grows from growth and issued-name Extends independently from history, then composes both relations forward at line 97. It does not derive issued growth from ordinary Grows, and it does not infer a publication history from either relation.

The returned growth endpoints are precisely before to the selected child's ENTRY current. The theorem does not return reader issued growth, a backwards heap relation, observation invariance, or a causal publication path. The RowCall's reader parameter does not replace these actual historical source prefixes.

## Strict bound and scope

The source bound at lines 91–95 uses the exact selected child syntax in the selected original source row, then that row's exact membership in expressions. It derives `sizeOf childSyntax < sizeOf (Syntax.node expressions)`. This is a bound on the original source node associated with this RowCall. It is not a strict generated-value size/depth bound, a recursive self decrease, or a bound against an unrelated earlier writer or outer caller syntax.

The theorem remains useful for closed results and for rows that later disappear during parent normalization. It requires an actual row call and selected child, not a surviving canonical row or a completed enclosing makeNode call. It does not establish original binding ancestry or identify a current requester's source with a historical selected writer. Those producers remain separate.

The owner selection records row-child-direct-3 and row-child-public-1, one public pair, zero constructed pairs, and four owned Lean runs including two retained syntax repairs. This review inspects their source metadata only and does not count their checks again. No review build was needed.
