# Whole A proof repair

Status: UNCOMPILED REPAIR. The original whole A candidate failed its private
check. Neither version receives theorem credit from this packet. Root remains
the sole compiler and live writer.

Date: 2026-11-14 19:44 CET.

## Exact input

Original candidate SHA256:
`77c3187a8804b51a2c6455efda7e404325b57dcdf1742c2c93ade5140ca9de55`.

Failed log:

    lean/restart-evidence/20261114-whole-A-reference-and-empty-eager-check/SourceSynthesisCurrentUniverseEmptyDomainInduction.txt

The log reports failed endpoint transport, a Bool precedence error in the reset
proof, and a 200,000-heartbeat timeout. A recovery axiom report after failed
elaboration is not a successful proof check.

## Repairs

1. Normalize the ACTUAL returned equation to the same explicit `initial` used by
   the native resource theorem. Apply `congrArg Result.state` to that equation.
   Transport native validity and extension through the resulting state equality.
   No endpoint equality is assumed or supplied by another provider.
2. Prove empty-domain reset false directly with `Bool.and_false` at the actual
   source definition. The former unparenthesized `&& false = false` expression
   parsed through a Bool/Prop coercion. It did not state the intended equation.
3. Replace the three global `simp_all` calls in Bool case proofs with direct
   constructor cases and the actual failed true-guard hypothesis. This avoids
   simplifying the full coupled IH and cache context to prove a Bool equation.
4. Scope `maxHeartbeats 2000000` to this one theorem. This changes the elaboration
   budget only. It does not disable a linter or alter a proposition.

The theorem header, complete coupled IH at smaller fuel, literal empty
domain, source initializer, case dispatch and exact result property are
byte-identical to the original. No hypothesis was added, removed or changed.
The original full and coupled open headers are also byte-identical copies.

`minimal.patch` records all proof changes. `STATEMENT-CHECKS.json` records the
header comparisons only. No compiler or elaborator was run here.

## Scope

The module still proposes the entire A induction step, rather than a selected
wrapper. It does not prove the whole M step or complete the simultaneous target.
No old packet, live module, Git state, board or Haskell source changed.

Whole M work was reassigned before a scratch module or draft directory was
created. The alias/U audit was delivered to Root in messages. This packet
contains only the requested whole A repair.
