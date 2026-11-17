# Explicit polymorphic type parameters at the tail equality call

Status: COMPLETE PROOF-ONLY REPAIR, UNCOMPILED. Root alone checks.

The actual first diagnostics at original line113 cannot infer width, Output and
Reason when the private equality helper is only partially applied. This repair
adds exactly `(width := width) (Output := Output) (Reason := Reason)` to THAT call.
No callback, trace, height premise, index, endpoint or supplied fuel changed.
The frozen public header ae246455, preamble and probes remain byte-exact.
Every byte outside that one private helper-call text remains unchanged.
The original failed source/log/manifest stay immutable with zero proof credit.

The proof still extracts guarded_lower's same eager child trace and transports
only the literal remaining callback function using equality on original inputs.
There is no trace construction from output equality, Canonical, Packet, model
or future resource premise. Limits, options and universe generality are unchanged.
No compiler, Source/Audit, Git, board or temporary-path action was performed.
