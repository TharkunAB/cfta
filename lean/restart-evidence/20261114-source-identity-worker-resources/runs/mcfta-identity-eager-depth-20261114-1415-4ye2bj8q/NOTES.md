# Actual fixed identity eager resource completion

Created: 2026-11-14 14:15 CET.

The candidate adds only ActualIdentityEagerDepthClosure to the fd86480d base.
Removing this section recovers every byte of that base. All old configured
headers, proof bodies, operations, and checked identity expansion bytes remain.

The public runEager_identity_finite_complete_resources header exactly matches
INTERNAL-RESOURCE-TARGET-HEADER-UNCOMPILED.lean.txt in the repository checkpoint.
It fixes Unit metadata, literal identity narrowing, empty templates, no stop,
and no preference. It has exactly the original Packet, Fits, Heap, selection,
mass, and reservation inputs. No future prefix, output, callback, or provider
premise is added. No artificial configured Key, fits, or admits value is chosen.

Two private proofs supply the public theorem:
- identity_resume_eager_zero_resources proves the four actual zero-depth
  decisions directly for resumeWithNarrow. Stop metadata and done outputs retain
  their exact current packet. Stuck emits no output. Expand returns the actual
  exhausted receipt with the original optional endpoint. Every case retains
  the full OutcomeResources and every emitted output resource.
- identity_eager_resume_complete inducts on the actual recursive depth with
  EagerResumeWithNarrowComplete at fixed literal identity. At positive depth,
  none, done, and stuck use the zero-result law and resource growth. Expand
  calls the checked identity_eager_expansion_resources with the smaller-depth
  induction result. Each constructed outcome is stable at every bound + extra.

The public proof uses runEagerWithNarrow by its actual definition. It does not
relate execution to a configured surrogate. No import or operational change is
needed. No producer gap was found while constructing the proof.

Base SHA-256: fd86480dd9ea76d468e66951471a87f10a93a103237c4a20e63585baa239b41f
Candidate SHA-256: 35901fc6dd9143e783d45df6d70126a69ac88d160082c69351e409cad8a6d238
Exact public-header SHA-256, including final newline: a5ca05322c240e42fbd765260d181265243a78469574d46fcb353157c52568be
Line delta: +130.

The candidate is UNCOMPILED. Only source-preservation and header checks were run.
The root must inspect and compile it. No compiler, Lake, Nix, heavy job, Git write,
network request, board operation, subagent, or live source write was run here.

This theorem closes only the proposed RESOURCE completion target if Lean checks
it. The bound is an existential stable-completion threshold at each fixed finite
recursive depth. The theorem does not prove safety at every smaller work fuel,
a finite accepted term of the original root, or a common satisfying assignment.
The full target remains one finite accepted term of the same original root with
one consistent assignment for every actual emitted partial root, including
parked backward recompletion. All original typing, depth adequacy and completeness,
default LPO, reduction and refolding, both language directions, stream order,
multiplicity and lazy demand, exact accepted terms per node-count size, counts,
weights, training, both rank/unrank inverses, host bounds and compiled Haskell
correspondence remain in scope.

Files:
- SourcePruningEnumerationSharedEagerReservation.lean: full candidate.
- original.lean: exact fd86480d input.
- identity-depth.patch: minimal unified diff.
- identity-depth-section.lean: the new isolated section.
- PUBLIC-EXACT-HEADER.lean.txt: exact intended public theorem header.
- checks.json: source and header checks.
- SHA256SUMS: packet hashes, excluding itself.
