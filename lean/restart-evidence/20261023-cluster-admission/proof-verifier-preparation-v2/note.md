# Verifier V2 source repair
V1 remains immutable under frozen-v1. It was not executed.
The selected V2 has 387 ordinary lines and 195 assertions. The hard limit is 450.
Only local fragment matching uses a column-preserving bullet view.
Context, public headers, source hashes and declaration inventories still use raw bytes.
The variant/artifact disjointness guard is unchanged.
Root revised the history by removing six duplicate artifact rows. All six variants remain.
The revised history has 585 artifact rows. Its independent review and Root gate are copied.
The bound-data change is only the actual revised history bytes and SHA256.
The selected code also pins the resulting new bound-data SHA256.
Exact V1-to-V2 code, data and history patches are retained.
All job facts remain: 12 jobs, 9 source jobs, 2 focused builds, 1 Audit and 3 failed source jobs.
The frozen metadata cut remains 40 jobs and 2 failures. These are separate counts.
Audit remains 3648 build jobs and 75525 theorem dependencies.
Required authored this source repair. Arity independently reviewed V1 and the repair scope.
No selected verifier was imported or executed. No compiler, Git, network or repository write ran.
Root and an independent reviewer must inspect this V2 before installation or execution.
