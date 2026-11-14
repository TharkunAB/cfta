# Fixed identity eager expansion

Created: 2026-11-14 14:03 CET.

The candidate starts from the frozen prepared candidate c2478790.
It adds one IdentityPrefixCheckpoint import and one isolated
ActualIdentityEagerExpansion section in lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean.
Removing these two insertions recovers every byte of the prepared base.
All operational definitions, old configured headers and old proofs remain exact.

The private identity_eager_expansion_resources theorem fixes Unit metadata,
literal identity narrowing, empty templates, no stop, and no preference.
Its recursive premise is the same fixed-identity resource induction target at
the smaller recursive depth. Its other inputs are the original Packet, Fits,
Heap, reservation, selection bounds, initial suspended mass, and actual chosen
expansion. It has no Key, fits, admits, or future-prefix-provider input.

The proof calls the checked identity_checkpoint_resources producer directly.
It handles the actual three stable phases:
- Parked: obtain the returned Packet from CurrentPrefixResources and use the
  produced parked mass bound. Blocked restart emits no output. Other restarts
  use the smaller-depth identity induction target and the reserved fallback plan.
- Empty: obtain the actual reached Post, Fits and Heap from CurrentPrefixResources.
  Return the actual empty completion and pad the resources to the eager plan.
- Nonempty: obtain the returned Packet and Post from CurrentPrefixResources.
  Use the produced Ready, stored bucket, IncomingAvoid, original bucket-length
  bound, and exact suspended mass. Call eager_prepared_resources_with_narrow
  at literal identity. Compose the actual prefix and prepared execution at one
  common fuel, including the exact original queries.

No configured checkpoint_resources, legacy PrefixValid, packet_prefix_complete,
retained_le, or narrowed_admission call supplies a prefix field.
No prefix capability is assumed. No operational worker is introduced.

The import traversal found 2131 transitive project modules.
IdentityPrefixCheckpoint has no path to SharedEagerReservation.
The import therefore creates no cycle. All traversed project sources exist.
The exact module list is in import-closure.json.

Prepared-base SHA-256: c24787902552349475663ab7fff7924eb9d0a1808f0a753e0ec90ee39998ec58
Candidate SHA-256: fd86480dd9ea76d468e66951471a87f10a93a103237c4a20e63585baa239b41f
Line delta: +152.

The candidate is UNCOMPILED. Only source and import-graph checks were run.
The root must inspect and compile it. No compiler, Lake, Nix, heavy job, Git write,
network request, board operation, subagent, or live source write was run here.

This is an expansion prerequisite. It does not close the identity depth proof,
the separate every-workFuel worker target, or the original-root joint witness.
The full target remains one finite accepted term of the same original root with
one consistent assignment for every actual emitted partial root, including parked
backward recompletion. All original typing, depth adequacy and completeness,
default LPO, reduction and refolding, both language directions, stream order,
multiplicity and lazy demand, exact accepted terms per node-count size, counts,
weights, training, both rank/unrank inverses, host bounds and compiled Haskell
correspondence remain in scope.

Files:
- SourcePruningEnumerationSharedEagerReservation.lean: full candidate.
- original.lean: exact frozen prepared input.
- identity-expansion.patch: minimal unified diff.
- identity-expansion-section.lean: the new isolated section.
- identity-expansion-header.lean: the new internal theorem header.
- import-closure.json and checks.json: static checks.
- SHA256SUMS: packet hashes, excluding itself.
