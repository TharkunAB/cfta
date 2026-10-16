# Current request words before physical demand

Date: 2026-10-17 01:06 CEST. Source: `SourceCurrentAllocatedRecursivePrefixWords.lean`, 102 lines, SHA256 `0d8332bb9812c2f627b4e77d969fa6c8014b4d73c0ce8e7a06adfed72076d727`.

This component derives Words and physical node/edge demand Inputs at one current instruction. It does not take a raw-prefix admission plan, WordRanges, a successful execution, or an annotated PhysicalTrace. It is one helper for the separate simultaneous raw-prefix proof.

`domain_lt` combines the actual sequential DomainAllocation.Trace with initial cache validity and strict initial headroom. A represented current domain has shifted identity at most the current raw supply, and that supply is at most `initial.next+inventory.length`. The strict room bound is `initial.next+inventory.length < 2^(bits+1)`. Width is exactly `bits+2`. The reserved empty domain identity is zero. Nonempty wrapper identities retain the source's successor shift.

`node_words` and `edge_words` combine that current domain identity bound with fixed original HEAP scope. The node supply is the initial `source.nodes.next < 2^bits`, including the interned-reference sentinel margin. The edge supply is the initial `source.edges.next ≤ 2^(bits+2)`. Neither helper requires the current or final constructor supplies to fit. Node Words follow the literal optional-key present equation; an absent key remains a bypass.

The inventory is generic. It can be the conservative computed SourceInventory or a smaller independently proved closed carrier. The actual trace is already executed history from the global initial domain cache to the current cache. It is not a future-key list. Current Domain representation may include a key that was already present initially but is outside the new-allocation inventory; initial validity and supply account for that key without assuming it was newly allocated.

`node_inputs` additionally transports original availability through actual heap Grows and issued-map Extends. `edge_inputs` transports original row residency through heap Grows; it needs no separate issued-map input. Both retain the current Domain in the current Machine. They derive PhysicalExecution.Inputs, rather than assuming the node/edge word component of those Inputs. They require neither current Good nor a future physical-readiness postcondition.

`node_words_empty` and `edge_words_empty` use the reserved zero identity directly. They need no domain allocation trace, initial domain-cache validity, or domain headroom. Initial source operand or edge supplies still apply.

## Integration

The imported `actual_enter_child_inputs` kernel starts with available original operands and an initial actual checked Machine. It derives its own one-enter domain-allocation history from the literal extended key. Kernel.entered supplies the actual returned domain. Exact key readback transfers original body scope. The new helper then derives the next child-demand Inputs from initial supply bounds. The checked state uses literal advance and retains both native memo tables and equality operations exactly. No completed child, future word plan, or desired owner/result law is supplied.

The imported `empty_domain_without_headroom` kernel derives both Words and the actual initial demand Inputs without any domain trace, domain-cache validity, or domain-capacity premise. This tests the reserved-zero case independently of the general inventory reservation.

## Validation

Pinned Lean 4.34.1 source direct1 passed with all linters and no diagnostics. Root's shared canonical `words-code-build.log` passed 1119 jobs; this component was target1118. Its source had no warnings. The shared log contains a historical dependency warning, separate from this component.

Final imported checks passed with seven public axiom/full-signature pairs and two integration pairs. Final standalone sources set all linters, explicit proofs and universes, deep terms, full names, and one million print steps. Final logs are terminal exit0 with no warning, error, `sorryAx`, omission, or truncation marker.

The first isolated public/kernel import attempts failed before elaboration because Lean resolved transitive MicroCFTA modules under the temporary output root. Those logs and exact sources remain. The final checks use the canonical imported olean and the same frozen production source. No production repair was needed.

Only the owned new production module and uniquely prefixed new evidence were written. No old source, Haskell, Git, Audit, root documentation, or older evidence was changed. No Lake build was started by this component owner. General recursive WordRanges and completion remain the separate root proof target.
