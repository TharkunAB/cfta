# Selected-return record layout repair

The original batch 21212 failed before the selected-return declaration was created.
Two multiline record fields ended their constructor applications too early.
The repair joins those two application lines. It changes no non-whitespace header
byte, premise, argument, conclusion, fuel, result, or proof limit.

The corrected selected-return FIRST was saved before the unchanged proofs were
copied. Its bytes change. The original FIRST was not successfully elaborated.
The tuple and captured FIRSTs and all three proof bodies stay exact. Both growth
owners stay exact in their original packet. All old packets and the rejected run
remain intact. This packet retains the entire checked Source65 owner as a prefix.
It does not claim exact old candidate prefixes after repairing their earlier header.

The failed batch has zero credit. This repair is uncompiled. It proposes the same
three private clauses. The full worker and finite completion targets remain open.
No Haskell source or normal Lean source changed.
