# Actual prefix shape and history proof repair

Status: UNCOMPILED. This packet repairs frozen 386, which retains the one-line
instance scope correction to 9cdc. Root reported five errors in the pinned
9cdc check. The two new explicit theorem headers remain byte for byte.
All initial premises, source constructors and resource conclusions are unchanged.

The shape proof transports the exact residual with Eq.trans and congrArg.
It derives a concrete length equality, reverts that equality and splits the
selected children list. The nonempty case contradicts its length. This removes
the unnecessary simpa and unavailable List.length_eq_zero.mp name.

The resource induction previously destructured its full previous TupleInputs
proof to obtain a current Packet witness. That destructuring removed previous
before forward prefix composition. Each constructor now extracts that witness
inside a scoped subproof. The full previous history stays in the outer scope
and supplies Root's tuple_inputs_extend_current_head call. The source origin
binder and exact observed endpoints stay unchanged.

The two constructor cases and shape proof are the only changed proof sites.
All other frozen386 source bytes can be recovered by reverting these sites.
All original full-worker/prepared target files are unchanged. This candidate
has no compilation or axiom credit until Root checks the entire module.
The actual empty-tail callback, general ordinary rows with children, full scan,
full worker and common finite completion remain OPEN. No Haskell defect was
found. No Haskell or FINDINGS file changed. No compiler, live-source, Git,
board or tmp write occurred. The clear-writing checks were applied.
