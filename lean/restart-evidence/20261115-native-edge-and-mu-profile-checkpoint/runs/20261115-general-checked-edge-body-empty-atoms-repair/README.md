# Checked edge-body Empty atom repair

Status: UNCOMPILED proof-only repair. The validation owner must run the strict check. The original 345-line candidate failed Root batch46091 terminal1 at its private Empty helper. The recovered theorem contains sorryAx and has zero final theorem credit. The original source, header and diagnostic log remain unchanged.

The only proof change replaces cases member with simp only [InternedBoundaryAtoms.atoms, List.not_mem_nil] at member. This is the reduction already used by the public ClosedResetProfile module's private profile_empty proof. It exposes the actual empty atom list before eliminating impossible membership.

The complete public header, declaration, main public proof, original raw counts, endpoint equations, child induction contract, source scope and probes remain byte-exact. PROOF-ONLY.diff records the single changed line. The new private helper extract matches the repaired raw module.

ORIGINAL-README.md preserves the full scope and remaining gaps. The original accepted source, stored full U, full original P and original coupled target copies are unchanged. This is an elaboration repair. It adds no assumption, helper interface, resource setting or Haskell change. No compiler, live source, Git, board or /tmp operation was run.
