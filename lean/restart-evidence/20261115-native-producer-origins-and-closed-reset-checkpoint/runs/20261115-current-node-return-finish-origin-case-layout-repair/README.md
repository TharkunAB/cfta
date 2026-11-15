# Node return origin case-layout repair

Status: UNCOMPILED. Root owns strict validation.

The original 289-line candidate failed. It has zero proof credit. Its raw
source and strict log remain unchanged. ORIGINAL-FAILURE.txt copies that log.

This repair changes two proof sites only. It uses ite_eq_left in place of
the deprecated if_pos rewrite. It puts the grouped Code case alternatives on
one line so that the read case is parsed as an alternative. The public header
is byte-exact SHA256 64ac3ff5d7ced321138dff4e6eef049289a14c1c0ae9099debfa75cc46c52676.
No premise, conclusion, fuel, endpoint, linter option or heartbeat changes.

The intended result is one actual same-trace finish prefix from a returned
cell at complete empty native initialization. Earlier compiler dispatch is
separate work. No full native C/M or finite joint-witness closure is claimed.
No compiler, live Source, Git, board, runtime or /tmp action was performed.
