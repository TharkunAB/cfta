# Source selection origins

SourceSynthesisSelectionOrigins proves nine pointwise origin laws for the
ordered GHC subsequence and permutation workers ported in
SourceSynthesisSelections. The laws include the last matching names-only
table lookup. Repeated names need no distinctness premise.

The actual Lake target and own-source report pass. checked.json records the
source hash and all theorem axioms. Only propext and Quot.sound occur.

This result does not prove permutation completeness, lookup-domain closure,
or native lazy table realization.

Run check.py serially through the repository's 4 GiB capped proof workflow.
No build archive is required.
