[2026-11-14 16:58 CET]

Status: UNCOMPILED. Root owns all validation and publication.

This source-only packet adds the first missing physical child classification
for the mixed M half. It reuses the already checked original source row
producer. It does not execute another source build or callback replay.
The exact original full-closure header and the current coupled A/M header
are copied byte for byte and remain OPEN.

Existing fact and the new proof

Ownership.current_stored_universe_rows already supplies the exact body node,
arrow row, original catalog alignment, and child = marker or refU. It also
supplies the marker's leaf readback, closedness, and original availability.
The new private marker_atomless proof derives atoms(marker) = [] from that
actual leaf row. It does not assume a new marker resource or type closure.

The first public theorem is:
  current_stored_universe_body_physical_children_after_growth

It takes only the same accepted source, successful original build, observed
stored Mu, and current Facts plus source heap growth. It returns the same
literal body/marker/arrow/catalog readback, body availability, actual grown
row residency, and marker closedness, availability, and atomlessness.
Every actual body child is the original refU, or the same closed atomless
marker. Grown availability comes from the stored full Mu and its actual
body/arrow child records. No issued-history hypothesis is invented to
transport source marker availability.

The second public theorem is:
  current_stored_universe_body_ordinary_child_requests_after_mixed_extension

It fixes the literal SAME original entered(U,P) once. At any actual later
valid Extension, it reads the body rows and a closed available ordinary Q
with only original-U atoms and height(Q) <= height(P). For every physical
body-row child and Q-row child it derives:

* body child = original refU, or an available closed atomless marker;
* Q child availability, closedness, and original-U-only atoms;
* height(Q child) < height(P), from actual ordinary child descent;
* for any actual Q-child identity, its separation from P's identity,
  both sorted pair inequalities, both ORIGINAL-domain cutoff exclusions,
  the actual Domain invariant, and full original-U binding lookup.

The pair freshness comes directly from the checked source freshness law.
It concerns the original entered domain and the same original full U at
that later heap. No alternate entry is allocated. The theorem is stronger
than a zip-only classification: all physical child combinations satisfy it.
For either operand order, apply it to the members obtained by
List.of_mem_zip on the actual ordered child request. It does not change a
walk, hash-join occurrence, or constructor result.

Private helper access

The classification module imports and uses only existing PUBLIC names.
It does not call either checked private ordered step from an import.
private-helper-access-plan.md records the exact declarations and source
pins. private-helper-bridges.PROPOSED.patch is a separate future append-only
access patch. It is not needed to check this module. Each proposed public
auxiliary induction-step theorem calls the corresponding existing private
helper inside that helper's owning module. Existing headers and proof bytes
stay unchanged. No full proof is duplicated. Root can check those two thin
bridges when it starts composing the simultaneous induction.

Remaining induction work

The new producer supplies the concrete child-case split for ordinary mixed
body calls. It is not a completed native M step and has no fuel/result/IH
premise. The actual lower-fuel calls still need these genuine induction
cases: refU/Q-child uses the M induction hypothesis with the derived strict
height; marker/Q-child uses closed-call reset to the empty domain and a
smaller-fuel A hypothesis. Empty and exhausted calls must preserve their
actual guard order. Body/Q sorting and cutoff exclusion must be derived
before applying the checked ordinary node step. Original-U alias leaves
must use the checked later-entry alias laws. Union priority must use the
actual ordered union step. The outer Mu case and simultaneous source A/M
induction remain OPEN.

No claim of generated-type closure, arbitrary source enumeration, or finite
same-original-root witnesses is made. Consistent assignments, parked backward
recompletion, typing, language, LPO, streams, counts, weights, ranks, and
compiled-Haskell correspondence remain unchanged and separate.

Only source inspection and SHA/byte checks ran. No compiler, Nix, Lake, heavy
job, live write, Git write, board post, or child agent ran here.
