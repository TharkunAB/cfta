# Finite varying-label comparison helpers

The module proves three finite-support lemmas. It does not prove the full
normalized comparison or the private stored-Mu law.

`support_varying_member` derives the lexical origin of a surviving varying
label. `deep_transport_on` uses that origin and the explicit slot coverage
to transport deep-name absence. `extend_fresh_on` checks only the new local
label and the mapped outer label list. Neither assignment must be injective.
Names assigned to other labels have no required property.

The proof keeps the two actual completed builds and their literal heaps.
The existing Context and DepthHeap hypotheses justify the symbolic
observations. The finite helper introduces no new output law, global
freshness condition, or future execution premise.

The production source matches the immutable direct-2 snapshot. That strict
check passed with an empty log. The canonical single target passed 329 jobs.
The imported public group contains three complete signature, proof, and
axiom checks. It has no printer omissions. The only reported axioms are
propext, Classical.choice, and Quot.sound. No extra constructed scenarios
were requested for these support lemmas.

The first direct attempt did not start Lean. The sandbox could not connect
to the user systemd bus. Its source, command, raw log, and exit status remain
in this component. The second strict attempt, canonical build, and public
checks ran with actual MemoryMax and MemoryHigh of 4294967296 bytes and
MemorySwapMax of zero.
