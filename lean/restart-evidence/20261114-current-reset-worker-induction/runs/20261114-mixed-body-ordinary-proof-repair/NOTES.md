# Proof-only repair for the selected ordinary body step

Status: UNCOMPILED. The original packet and failed strict check stay intact.

The repair changes only the public proof. Each Bool case now uses explicit
change statements to normalize the selected decision, payload and actual native
call before rewriting execute/onNode/selected. The body equality is applied
only after that branch has been selected. This avoids a restricted simp pass
leaving if false=true and if true=true inside the actual decision.

The reached machine now uses the exact congrArg Result.state returned equality.
Equality transport supplies native validity and Extension at that same endpoint.
It does not ask simp to identify a differently presented result expression.

Both theorem headers, the entire private payload proof and both original target
headers remain byte-identical. No premise or conclusion changed. The actual
ordinary selection remains an auxiliary case premise. The full original and
coupled goals remain OPEN. No compiler/live module/Git/board/child action or
Haskell change was made. Static assertions and hashes do not prove elaboration.
