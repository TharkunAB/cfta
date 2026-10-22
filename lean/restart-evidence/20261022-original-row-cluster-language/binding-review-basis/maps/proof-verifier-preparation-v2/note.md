H20 saved-proof verifier V2. SOURCE ONLY. This package supersedes V1 for future binding.
Root source review found a literal substring defect before any prepared verifier execution. This was not a runtime verifier or Lean failure.
V1 is copied byte for byte under frozen-v1 and remains unchanged at its original path.
The sole code change prepends LF to the row-binding literal. Both count and position now use the same complete-line literal.
The exact one-line patch has a byte-identical deletion inverse. All 232 lines, 105 assertions and 28 pending tokens otherwise remain unchanged.
The root-approved 393-line source c045f16537a73802338f3777a6137b3f58a2c26adcd00c8ceef2fb0dabc12b15 is retained only for static predicate validation.
The raw row text occurs three times. LF plus the exact row line occurs once, at source line 300. The intended source order is unchanged.
The contract, source-history, scope and token maps are byte-identical to V1. Expanded IH remains review-only and absent from compiled declarations.
Guard authored this adaptation and FULL tooling. Root identified the defect. Arity authored the retained proof body; no proof-body review is claimed here.
Python syntax and byte/hash predicates only were checked. No prepared script, compiler, Lean/Lake, runtime, capped, Git or network action was run; no repository file was written.
Required independent whole-source review and root actual-binding review remain pending. No actual proof outcome is asserted by this tooling preparation.
