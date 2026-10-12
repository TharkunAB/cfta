# Recursive join support and inspection fields

## Support correspondence

`RecursiveJoinSupportSemantics` defines the size-erased language of each
independent `KeyedSource.Recipe`. `denotes_iff_derives` equates this language
with finite source derivations. `derives_closed` supplies the induction
principle used to close the recursive family. It does not assume a complete
family language law.

`RecursiveJoinSupportView` retains the support graph, its applicative spine,
and its source label-closing operation. Each constructor proves its own
language law. Join roots retain `JoinN`, `CenterKeyed`, `ArgKeyed`, both
copies of every argument key, and every path equality. Labels replace a
join root label and retain its constraints. Flat choice keeps branch
wrappers until closing distributes over the original branches.

`RecursiveJoinSupportBody` composes these fields alongside `CheckedBody`.
The heterogeneous argument chain supplies each operand's independent term
recipe and support. Its `fold_exact` theorem derives the complete join
language from these operands. Finite leaves supply only their own support
provenance and callback law. The module does not assume a whole-body or
whole-family correspondence theorem.

`RecursiveJoinSupportFamily.graph` ties one shared binder around the keyed
`Family` alternatives. Every recursive occurrence and public member keeps
the constrained `AtKey` boundary. `member_exact` equates this actual graph
language with finite independent source derivations. The proof requires
complete keys and injective key codes. It does not require a recursion
guard. `family_exact` then uses the source size guard to equate this language
with the independently compiled term classes. `selected_accepted` places
every successful decoder result in the public member support.

`RecursiveJoinSupportExamples` supplies the finite provenance for the
existing heterogeneous two-key example. `checked_same` proves that this
independent support construction preserves its complete checked program.
`all_members_exact` proves the support correspondence for every term and
key. `delayed_accepted` checks the nested join through two recursive steps.

The support language forgets rank multiplicity and size. It does not equate
support cardinality with the number of generator ranks. Graph alternatives
represent the source alternatives before interning and reduction. These
proofs do not identify their list order with Haskell node identity order.

## Diagnostic assembly

`RecursiveJoinInspection` keeps the original label and predicate beside
each optional display name. `erase_annotate` preserves every child and
binder when plain inspection is built. `keys_lookup` and `arguments_lookup`
place each argument name on both copies of its exact positional join key.
`erase_join`, `erase_occurrence`, and `erase_family` retain the complete
unreduced source constructors and their constraints.

Maps and pay preserve the diagnostic record. Choice retains a name only
when all alternatives have that name. Application and join clear their
result name. Label closing keeps the operand name. Closing an empty choice
retains the unreachable labelled child that the source constructs;
`label_empty_choice` checks this diagnostic detail.

`RecursiveJoinInspectionBody` compiles these fields independently of the
value, term, mass, and inverse fields. Its finite leaves supply their own
diagnostic descriptor validity. Every constructor derives its closing
invariant locally. `family_body_valid` closes this invariant against the
separate diagnostic recursive context. `named_checked` and `named_family`
prove that a diagnostic name cannot alter the checked generator.

`RecursiveJoinInspectionExamples` gives different names to the Boolean
and natural-number operands in the same mutual join family. Its
`checked_same` theorem retains the original complete checked program;
`delayed_decoder_unchanged` retains the independently selected term.

Inspection is a diagnostic record. These modules do not identify its
language with semantic support. Names affect diagnostic node identity,
and the source reduces join support but retains the unreduced diagnostic
graph. Rendering, hash-consing order, and reduction are separate concerns.
The closing descriptors cover generated pure, application, choice, join,
and ordinary outer layers. Arbitrary externally supplied opaque binder
roots and mixed private root collections need additional descriptors.

## Validation and remaining boundary

Pinned Lean 4.34.1 builds the support and named inspection examples. The
isolated dependency audit permits only `propext`, `Classical.choice`, and
`Quot.sound`. All new proofs use checked constructor laws and finite-leaf
contracts. There are no admitted proofs or native-evaluation axioms.

The support and inspection decorators preserve `CheckedBody` separately.
The weighted flags and optional term-field dispatch use the separate
runtime modules. A single source-to-Lean extraction theorem for every
Haskell record field is still outside these modules. In particular, these
proofs do not establish arbitrary builder schema stability across the
different source probing contexts, host integer safety, or lazy-knot
productivity.
