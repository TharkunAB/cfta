# Current recursive control checks

Checked on 2026-10-17 at 01:10 CEST.

`SourceCurrentAllocatedRecursivePrefixControl.lean` has 125 lines. Final SHA256:
`e548c81b8f6e65975efaa2135fca76c2defb516de95017f6aec6445ce0cecded`.

`Certified` maps code to the combined local compiler certificate. An edge-body
control retains exact original row scope, domain inventory membership, current
`EdgeReady`, and its physical continuation. `edge_body` constructs the natural
resident-edge return certificate. `body_code` certifies only the code emitted
by the supplied actual checked body yield, at the same returned machine.

`words` combines original source key bounds with current domain representation
and actual domain history from `PrefixState.Current`. `inputs` derives the
current physical check from those words and the same local operands. `entered`
derives the exact local allocation-key admission. None takes `WordRanges`,
future enter admission, a physical trace, or recursive semantic completion.

The resource arguments are initial domain-cache validity, initial original
node supply `< 2^bits`, initial original edge supply `≤ 2^(bits+2)`, and strict
initial domain-inventory headroom `< 2^(bits+1)`. The full current state includes
physical and semantic readiness and past allocations. This component derives
only the CURRENT instruction's checks. It does not establish that the local
certificate or current state facts survive every arbitrary raw prefix.

Validation:

- `control-direct-1.log`: pinned direct Lean, all linters, exit 0, no diagnostics.
- `control-canonical.log`: owned copy of root's completed canonical build,
  exit 0, 1131 jobs. Only the historical dependency warning appears.
- `control-public-1.log`: 10 imported public declaration pairs with printed
  axioms and explicit full signatures; exit 0, no diagnostics.
- `control-kernels-2.log`: three imported integration pairs; exit 0, no
  diagnostics. Each theorem prints its axioms and explicit full signature.

The kernels construct a source node request certificate and derive current words,
physical inputs, and enter admission without supplied word checks. A second
kernel follows the SAME checked body yield through physical fields, operation
cache growth, current state preservation, and emitted code certification. The
third reads an original binder from the actual grown heap, then derives the
following node request's word and physical checks at that same state.

No production file changed after the recorded source hash. No older proof,
Haskell source, Audit, root document, or Git state was changed by this component.
The failed first kernel draft and its matching source remain available.
