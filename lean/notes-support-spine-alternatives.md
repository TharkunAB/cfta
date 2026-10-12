# Grouped function spines

A retained group can contain several private Apply roots. When that group
is the function child of a later application, the old support helper retains
the group as one child. The term callback instead flattens each selected
Apply term. Closing the application then produces terms outside its support.

The source now returns a list of ordered child sequences from
`applicationLeftSupport`. It appends the next argument to each sequence.
`labelSupportWith` emits one labelled edge for each complete sequence.
It does not form a product of children from separate alternatives.
Ordinary roots remain opaque. Choice, JoinN, and recursive boundaries also
remain opaque on the function side.

`SupportSpineAlternatives.prefixes_exact` proves that the child sequences
denote exactly the forests returned by the term callback. `close_exact`
proves exact language equality after the labelled constructor closes them.
Operands can contain arbitrary recursive support graphs. The recognizer
model assumes valid private Pure and Apply shapes. The production fallback
retains malformed or constrained private roots without flattening them.
Such roots are outside this constructor theorem.

The checked examples prove that the old fallback loses a pair, that the
repair accepts it, and that the repair does not introduce crossed pairs.
`repro/GroupedSpine.hs` checks seven reachable public generator variants.
They include correlated pairs, nested grouped applications, nullary Pure,
ordinary indexed leaves, and opaque Choice roots. Each variant compares
complete support and inspection term sets with decoded terms. It also
checks inverse ranks.

Validation: the pinned Lean build and axiom audit pass. The existing Nix
suites pass 602 examples: 274 core, 193 generator, and 135 refinement.
