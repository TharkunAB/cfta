# Single narrowing backend: checked components and unfinished compatibility

Status: LOCAL DRAFT. The full Audit did not pass. The patch is not an imported
Lean module. The checked baseline is e06ef03f8cce13f3d4647a337b61e8c106414ece.
The baseline is pushed to formalize. It includes the accepted-producer root scan
origin theorem. Its joint finite-completion obligation remains open.

live-draft.patch records all eleven current Lean changes against that baseline.
The patch adds one native-narrowing parameter to one action, prefix and recursive
backend. The old entry points are configured wrappers. Existing theorem
statements and hypotheses stay unchanged. Five wrapper equations use rfl.
The remaining edits change explicit reductions in existing proofs.

The three owning modules and the three standalone totality modules passed strict
checks. Four further changed proof modules also passed strict checks. The
independent import checks passed for five wrapper laws and three standalone laws.
All eight axiom reports use only the standard Lean axioms.

The full Audit exposed fifteen proof-script errors in four further modules.
Root interrupted its Lake process with SIGINT during a disk-space investigation.
The checker recorded audit exit -2. No full Audit success or new global semantic
theorem is claimed. Keep the actual diagnostics in check8/audit-build.txt.

The uncompiled-prefix-repair-proposal directory contains a source review of two
of the four failing modules. Those candidates are not applied. They add four
explicit reductions. Three sites fold the new preparation to the same old
configured call before using the existing receipt. Root must compile them.

For reproduction, start from the baseline, check and apply live-draft.patch,
then run the saved checks inside the project Nix shell. Use the heavy-management
4 GiB cap and one Lean thread. The check scripts retain their original absolute
runtime paths. Copy them to the stated runtime path or adjust that path for a
separate checkout. Check1 uses the original three-file candidate. Checks2 through
8 retain exact source patches and hashes for their own stage. Earlier three-file
candidates and the source review are in the preceding committed checkpoints.
No compiler archive is stored here.

Free space fell from about 323 GiB to about 106 GiB on the shared filesystem.
A directory scan measured about 49 GiB in /tmp, of which about 48 GiB was in
/tmp/claude-1000. The Lean build measured 7.2 GiB. Free space continued to fall
after the audit stopped. These measurements do not identify the remaining disk
use. Do not delete another process's files. The completed home and project scans
are saved here. local-models uses about 400 GiB; the proof checkout uses about
23 GiB. These sizes do not establish which directory grew. No compiler remains
active from the interrupted audit.

Matti plans Liquid Haskell contracts for the implementation. Use acceptance and
finite-completion predicates that match Lean. Verify the real calling code and
its preconditions. Useful contracts cover interning, cache and alias invariants,
finite-completion preservation by native operations and required-path changes,
and one shared completion through eager enumeration and parked restart. These
are recommendations. No Liquid Haskell implementation contract was added or
checked. A correspondence argument is still required for a Lean end-to-end claim.
No Haskell source changed. Record every future Haskell fix in FINDINGS.md.

The canonical board readback is saved here. It records post f0453ef4-1b69-4677-
8a37-4d10e3465147, sequence 1279. Earlier proof work, failures and plans remain
preserved in the previous source-only checkpoints and in the root handoff files.
