# Prepend grouping precheck V2
Status: FINAL/FROZEN SOURCE-ONLY UNCOMPILED PROPOSAL. No Lean check has run.
The only source change is line34: cases table query becomes cases table rowKey. The preceding same rewrite normalizes the lookup to rowKey, so the case split must use that normalized expression.
This is a source-review correction requested by root and Required. It is not a compiler failure or a new mathematical premise.
The whole85-line V2 source was read. Context, all nine headers, all three equations and the generalized IH remain exact. The token inverse recovers frozen V1 byte-for-byte.
The entire V1 package, its original source/addition patch/pins and the exact V1-to-V2 patch remain. V1 and the FULL tooling packets are unchanged.
No helper, theorem, assumption, linter exception or declaration-limit change was added. All source/API pins remain live-equal.
No compiler, prepared tool, runtime, Git, network or repository write ran. Root and independent whole-source review must precede root-owned checks.
