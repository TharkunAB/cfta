# Root review layout

- SELECTION.json fixes two components and the topological order Gate -> Skip.
- SOURCE-BASELINE-PINS.json binds all 6,278 current Source files and four
  toolchain files to the final publication pin map for Source 1a3de82a.
- RECEIPT-PINS.json binds the final Source and publication evidence. It does
  not bind mutable handoff prose or a future checkpoint receipt.
- OWNER-BEFORE.lean.txt is the entire normal 5,721-byte gate owner. Its
  candidate must equal this owner plus the frozen append, with no new import.
- Each selected FIRST, raw source, probe, manifest, Source pin map and
  dependency artifact is checked before runtime allocation.
- prepare-private-check.py may run only from the named new Work directory
  and must be byte-exact to this packet. Its first mutation is runtime.mkdir.
- check-driver.py.txt runs two real Lean commands. shadow-compile.py.txt is
  byte-exact to the previously checked two-owner shadow worker.
- Both fresh output names are excluded from symlinks and refused if already
  present. Source declarations and default proof limits remain unchanged.
- Normal staging and Source commit are not actions of this controller. Their
  prior push gate uses the final authoritative receipt dynamically.
