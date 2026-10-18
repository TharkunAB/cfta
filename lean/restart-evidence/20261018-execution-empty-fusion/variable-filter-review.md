# Filtered variable source case

Frozen on 2026-10-18. Source: `SourceCurrentGeneratedVariableFilter.lean`, SHA256 `1e7ea96976eb26d664c473238bc2d97743e21d4814a1ab4c8b3bf56fce6c96fb`.

## Proven contract

The sole public theorem `variable_call` retains the original symbolic inputs, both name assignments, the generated lexical `Inputs` relation, and the scoped self tests for the selected variable. It takes actual warm variable builds, actual warm root-filter calls, and actual warm stored executions at one Ready reader. It needs availability only for the selected first raw value. It does not require availability of the complete lexical lists or a global replacement map invariant.

The conclusion separates two facts: both Generated directions between the actual outputs, and physical Empty agreement. The Empty hypothesis applies only when the two selected raw values are literal references. It compares their two direct environment resolutions. It does not assume a final output equation, a full-parent output relation, or an Empty law for an opaque captured value.

## Reference branch

`GeneratedLexicalCases.paired` and an indexed ordered-slot selection supply the mutual Generated relation for the resolved reference values. A literal reference is unchanged by root self filtering, including the bare-self case. Its actual stored execution returns the exact environment resolution at the same reader. The restricted reference Empty hypothesis gives the separate physical Empty conclusion.

## Fixed capture branch

The selected slot retains one identical captured value and equal maps on its raw free names. Symbolic variable lookup proves that every raw free name contributes a fixed label to the exact variable Scope. The scoped self tests therefore imply `name = firstOwn iff name = secondOwn` on those raw free names.

If the own names are equal, their actual filters are equal. If they differ, the self tests prove both own names absent from the raw free names. Normal available union fields then show both filters return the original value without effects. This argument retains full union and open Mu captures. It does not infer a global alias or freshness law from source syntax.

A separate actual-filter free-name inclusion proof shows that filtering adds no free names. For a union it reads the normalized free names from actual constructor readback and selects an original retained member. Thus equal raw free-name bindings imply equal filtered free-name bindings. Actual filter effects provide filtered-value availability. `execute_congr` then gives exact equality of the two actual outputs. Reflexive Generated membership and physical Empty agreement follow from that equality.

There is no BinderFree, closedness, Cap, or physical word restriction. The proof does not weaken alias premises in other source cases. It uses precisely the scoped self tests needed by the variable case. It makes no reader-transport or completion claim beyond its supplied literal successful calls.

## Source-built integration

`VariableFilterKernels.fixed_and_reference` constructs a closed source from the empty heap. Its body is the union of its self reference and a nullary ordinary leaf. Initial source execution derives a Ready reader and an available open union capture. Filtering this actual capture at Depth is nontrivial: the raw union differs from the returned leaf. Two maps agree on the capture's raw free name and differ on an unrelated name. The integration invokes `variable_call`; its reference Empty hypothesis is vacuous in this fixed union case.

The same checked theorem also invokes `variable_call` for two distinct varying bare-self references. Their maps both resolve the selected name to Empty. The exact Scope contains Depth and the varying label. Both self-test cases are checked explicitly. The input relation and resolved Empty hypothesis are derived directly. These applications exercise both proof branches, with no supplied desired output relation.

The public constructed theorem forwards a private checked witness with a byte-identical statement. Its full print retains the complete public statement and proof alias. This is one constructed pair, not a general source induction theorem.

## Validation and attempts

Selected production strict `variable-filter-direct-3` passes with a literal zero-byte log. Canonical `variable-filter-canonical-1` passes 601 jobs without warnings. Full group `variable-filter-public-1` passes one complete declaration/proof/axiom report. Constructed strict `variable-filter-kernels-1` passes with a literal zero-byte log. Full constructed group `variable-filter-kernels-public-1` passes one report. Both full groups pass the hardened checker with all eight options and only standard axioms.

All Lean jobs use pinned Lean 4.34.1, a five-minute cap, and verified memory.max = memory.high = 4294967296 with memory.swap.max = 0. Failed direct attempts 1 and 2 are retained. Attempt 1 contains private unused-instance warnings and elaboration errors. Attempt 2 contains two remaining elaboration errors. No failed or warned check is selected.

This component adds one public theorem and one constructed theorem, with no auxiliary pair. It changes no older module or evidence. The owner manifest excludes all root mutable files and other-agent files. General Generated Empty fusion and general binder simulation remain open.
