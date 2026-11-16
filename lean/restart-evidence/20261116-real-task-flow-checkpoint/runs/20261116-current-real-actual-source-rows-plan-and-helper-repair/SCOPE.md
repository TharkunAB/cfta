# Real row-plan and helper-name repair

Status: UNCOMPILED. Root owns the compiler and publication.

This packet preserves all four frozen header files and the appendable probes
byte-for-byte. The original main header SHA256 remains
`f89c11cb8704ec5ad33686ef8e6b91d139cd0326dbe33558bf1bc4371b712bfc`.
The generic row resource header remains `7c1cb217...`.

The proof changes exactly two sites. The selected-frame generation proof
calls the existing generic real_rows_guarded_children_eq helper. The original
wrong name actual_source_guarded_children_eq had no declaration. The static
row forecast proof uses `simpa only [nodePlan] using later` instead of
`exact later`. This exposes the nodePlan successor equation under the local
opacity attribute. The static plans and all runtime budgets stay unchanged.

PROOF-ONLY.diff records both changes. Every other proof term remains exact.
The old raw candidate and its actual failed log remain unchanged. The old
candidate has no whole-proof credit. The other combined-job errors belong
to the other packets and are outside this repair.

The shared definitions and actual_emitted_complete_mono still occur once
in the checked nil/root packet. Append this repaired APPEND after that
packet. Do not append the old rows packet too. The original packet SCOPE.md
records the full source construction and dependency layout. No live source,
Git state, /tmp file, board note, or root documentation was changed.
