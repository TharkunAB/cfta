# Independent review of generated lexical cases

Frozen on 2026-10-18. Source: `SourceCurrentGeneratedLexicalCases.lean`, SHA256 `938d1f6b521c7f14196cb3944ae90eb70cfbda178a31efd20dcdae17cd527ed2`.

No material issue was found. The review read both public proofs and their `ReaderReplacementSlots.reference` and private `slot_result` dependencies. It ran no new Lean build.

`paired` converts the actual generated lexical spine to the existing ordered `Paired` relation. Reference inputs already carry both resolved Generated directions. Fixed non-reference inputs retain the exact captured value and equal maps on all free names. Fixed reference inputs require a separate case: agreement at their single free name gives equal resolved values, so both directions are reflexive. Empty lexical lists and ordering are retained.

`variable_call` uses this derived pairing in the existing actual variable theorem. Its only completed-execution premises are the two literal source-variable-then-stored-execute equations. It returns both Generated directions and equality of the two output heaps. It does not claim either output heap equals the entry reader. Initial availability of the left lexical list suffices: corresponding opaque captures are identical, and reference slots execute by direct environment resolution. Coherence justifies execute-congruence for equal captured values under free-name map agreement.

No observation relation or desired parent output law is assumed. This is the unfiltered variable case. It proves no root-self-filter clause, general binder clause, or general Directed law. Those boundaries agree with the module header.

Reused evidence: `lexical-direct-2` passes with a literal zero-byte log; `lexical-canonical-1` passes 600 jobs without warnings; `lexical-public-1` passes two full declaration/proof/axiom reports under all eight required print options. Limits are memory.max = memory.high = 4294967296, memory.swap.max = 0, and five minutes. The toolchain is Lean 4.34.1. The hardened checker accepts only standard axioms and no proof omissions. This review adds zero public, constructed, or auxiliary pairs and reuses two existing public pairs.
