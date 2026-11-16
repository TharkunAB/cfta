# Original outer depth goal

`DEPTH-GOAL-HEADER.lean.txt` states the exact existing global structural depth
predicate. It has no structural IH or resource provider as an external premise.
`GLOBAL-DEPTH-DEFINITION.lean.txt` copies that existing predicate for review only.

The runtime branches are in `SharedPreparedRecursiveChildPolicy.resumeWithNarrow`.
The following source cases remain for the outer proof assembly.

- No next decision and `done` emit the unchanged input cache. Use full history
  reflexivity with the original Packet safety and held isolation.
- `stuck` and zero-depth `expand` emit nothing.
- A continuing parked prefix restarts at smaller depth. This packet composes
  the original prefix history with that genuine smaller-depth IH.
- Empty or rejected narrowed receipts emit nothing.
- A continuing narrowed prefix runs actual preparation. Compose the actual
  prefix history with the successful preparation companion. That companion
  covers the ordinary scan and opaque or terminal callbacks.
- Other malformed, failed, or stopped prefix shapes emit nothing.

The successful preparation and opaque companions can return earlier outputs
before a later stop. The outer proof must retain those outputs. It must not
replace those branches with an empty-output claim.

The global depth theorem and original public 906 result remain unproved here.
The finite accepted completion and one compatible assignment remain separate
semantic objectives after structural history is closed.
