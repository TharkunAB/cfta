# Ordered plan embedding review

The module embeds the three existing ordered plan relations into the new
recursive normalized relation. It adds no execution premise.

The node case keeps every original row occurrence as a witness in both
directions. The child and union cases keep order and length. The binder
case uses the original common-reference body premise at every reference.
The proof uses structural descent on the first syntax or row list.

The result permits unchanged and recaptured ordered subplans inside the
new construction proof. It does not derive a relation from callback
history. It does not prove reconstruction through prior union normalization.
It does not assert equality of arbitrary execution states or pending keys.

No existing public reflexivity law was found for the old ordered relation.
This module adds no separate reflexivity family. Runtime integration belongs
to the main normalized construction component. This component counts three
public proof pairs and no constructed execution pair.

Immutable direct attempt 4 passes with all linters and an empty log.
Canonical target 1 passes 116 jobs. Public probe 1 prints all three complete
signatures, proof terms, and axiom reports. The reports use only propext and
Quot.sound. No printer omission or diagnostic appears in the selected log.

Direct attempts 1 to 3 retain failed elaboration diagnostics. Attempt 4 uses
the explicit equations of the well-founded relation definitions. All runs
record actual memory.max and memory.high of 4294967296 bytes and swap.max
of zero. The maximum observed peak is 174 MiB.
