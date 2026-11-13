# Selected function boundary source packet

Root checked the final private theorem with strict warnings and standard axioms.
The associated proof commit is `f93d80f072257cb4714ed649780efffc8cfef4eb`.
This packet does not add a public theorem or a full-build result.

The family contains three exact source stages:

- Initial 121 lines, `853efcf0`: uncompiled and superseded before the Root check.
- Revised 122 lines, `01f30ff3`: strict failure. Both tuple witnesses used the old
  compiled equation after the case split had rewritten the expected equation.
- Repaired 122 lines, `5bb2c548`: strict PASS. Root changed those two witnesses to
  `rfl`. The actual private axiom print lists `propext`, `Classical.choice`, and
  `Quot.sound` only. The 62-line header is unchanged in every stage.

The baseline occurs once. Two zero-context unified patches reconstruct the
later stages. Separate zero-context patches reconstruct both actual instrumented
checks and the frozen header from empty text. The Root reports, stdout, checker,
and peak summaries are the small original files. No build archive is included.
The failed check prints `sorryAx` during error recovery. It is not proof evidence.

`python3 reconstruct.py` verifies all text hashes, exact patch preimages, source
stages, instrumentation, frozen header, and stored Root diagnostics without a
compiler, GNU patch, Git, subprocess, or source mutation. Optional arguments are
`--extract /tmp/CHOSEN-DIRECTORY` and `--check-imports /home/tritlo/Code/mcfta`.
The original strict checker is `provenance/root-check-draft.py`. Root must run it
in the approved 4 GiB cgroup. Its report hashes the instrumented source.
No compiler or GNU patch replay was run during this packet preparation.

The theorem uses the unchanged actual source app guard and the same precheck
and shared ScanReads. Required starts at that scan's returned heap and Memos.
It derives the finite Type-path subset and retains the real prefix, function,
and suffix read endpoints. An empty subset copies only the function slot at its
actual site. It does not make the whole four-child call an identity operation.

The result does not establish later intersection survival, an invariant for all
Type values, joint aliases or residual satisfaction, model existence, complete
output typing, or Haskell correspondence. No Haskell edit, defect, or fix is
established. Earlier source files and failed artifacts remain unchanged.

Root later replayed all five source, instrumentation, and header patches with
GNU patch --fuzz=0. Each output hash matched. Current import hashes also matched.
The exact receipt is verified/root-gnu-replays.json. No compiler was repeated.
Run python3 verified/verify-gnu.py PACKET REPOSITORY NEW_OUTPUT to repeat that check.
The original preparation receipt still describes its earlier pure check.
