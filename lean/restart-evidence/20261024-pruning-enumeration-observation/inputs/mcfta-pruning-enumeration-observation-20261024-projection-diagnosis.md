# Observation projection elaboration diagnosis

[2026-10-24 05:24:06 CEST] Source-only diagnosis: disable match hypothesis generalization on the local observed projection. I read all four exact failed inputs/deltas and complete raw logs, the current candidate, the actual imported observer-success theorem, and active Lean4.34.1 Match elaborator sections160–162,862–916 and1117–1128. I ran no compiler, reviewed script, Git command or repository write. Root owns the candidate and any next trial. This note does not claim that a proposed repair has compiled.

The required last conjunct of getUnexpandedNode_success is the plain one-discriminant projection of the SAME storedValue. In failed attempts2/3, the context explicitly prints the local observed definition as a TWO-discriminant match over storedValue and the dependent stored proof. These are different elaborated terms, so bare rfl does not close their equality. This is an elaboration-shape issue, not a missing successful-read or realization assumption.

Attempt1 supplies rfl and leaves this mismatch. Attempt2 cases on storedValue while leaving observed folded, so observed still refers to the generalized original match. Attempt3 unfolds observed, exposing the captured proof, then cases/generalize fails because that proof's type still mentions the discriminant. Attempt4 moves stored below the projection and restores rfl; its log still reports the projection mismatch. That log alone does not print the new elaborated observed body, so I do not infer the precise additional captured hypothesis in attempt4. The executable read, after state and all other proof fields are unchanged across these deltas.

Active Match.generalize at879–916 defaults to true, finds local variables that depend on discriminants, and extends BOTH the discriminant list and branch patterns. This directly matches the two-discriminant term printed in attempts2/3. With false, the function returns the original discriminants/match type/alternatives immediately at882–883. The parser explicitly accepts the flag at161.

The smallest next trial is therefore the existing local binding with only the supported flag added:

```lean
let observed : Option Nat := match (generalizing := false) storedValue with
  | .unenumerated pending _ => pending
  | _ => none
```

The result type Option Nat is constant. Branches use no dependent witness, so no generalization is needed. This restores the literal projection shape used in the imported observer theorem and should permit the existing rfl; Root's actual compile must decide that. All six public headers and their assumptions remain unchanged. Do not add an output equality premise, change the observer, replace the selected stored slot, assume right success or clear storage requirements.

If an explicit fallback is required, active elabMatchAux1121–1123 automatically sets generalizing=false for an explicitly provided motive. A constant motive to Option Nat expresses the same intended projection. A fresh pure lambda parameter can also isolate this match from the dependent local context, but it is larger than the single flag and is unnecessary unless the bounded trial shows another problem. These are diagnosis suggestions, not authored body changes.

Exact inspected input pins:

- source-check-1/MicroCFTA/SourcePruningEnumerationObservation.lean: 7271 bytes; SHA256 6f363665b9aa2d053df6b723a37128ffaa38372f461286612231e7a3df6dbe66.
- source-check-1/raw.log: 381 bytes; SHA256 edddf88fc4c3f2cfccfef705f222c8da2675640171fdefeb99fa3bfd9deee6b7.
- source-check-1/report.json: 687 bytes; SHA256 5c908101f090123e61bb82309490f00389635acb4b0a6f2870422aa25466e833.
- source-check-2/MicroCFTA/SourcePruningEnumerationObservation.lean: 7302 bytes; SHA256 afd575e6a2d9d47c5b3978777b4461fee9df128ef0c8957755a22a37652e9097.
- source-check-2/raw.log: 4852 bytes; SHA256 a441bddac0ad3417cadbdbc7268e2875e44eaaa4e253404d941dc9868335d490.
- source-check-2/report.json: 688 bytes; SHA256 48efb73f444b036cceff30f3ae952a7a93f944e297aa772f8ffd366d9337b19c.
- source-check-3/MicroCFTA/SourcePruningEnumerationObservation.lean: 7325 bytes; SHA256 024d49ebd4d8ef203f0f225b00ef6216c95b1d4082129848d402f7605ea400e8.
- source-check-3/raw.log: 1751 bytes; SHA256 d4fda51ea6142467670dd1ad2ea23bc00709e39cd95ce426d3b493d4202bb210.
- source-check-3/report.json: 688 bytes; SHA256 3e06f75d96cd5b3d81b26dafb260d1056d7e2a3b6ef140d772b470d81933281c.
- source-check-4/MicroCFTA/SourcePruningEnumerationObservation.lean: 7271 bytes; SHA256 077d840a43f71cbca684deb9af8f3a14a189c35e70788f17466c74282a93a6b7.
- source-check-4/raw.log: 381 bytes; SHA256 80872f29654ea639a3ee22fc1e1a8a5aaf77ab16bb3ca7271fd6e3aeab11ac4c.
- source-check-4/report.json: 687 bytes; SHA256 6a020e28d4b60c56ade99b31a6c5be2f7a6bf3af13aefe5415ca1c1c2d933743.
- /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Lean/Elab/Match.lean: 62136 bytes; SHA256 960a0ebf9a66c247496fc1fc12083a77e9e0a931646458a78d55f058c133db22.
- /home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationNodeObservation.lean: 4323 bytes; SHA256 0dc7f259885a4c5a914aed2d7a62030b18cc87fc37962ffe438c146b6459d06d.
