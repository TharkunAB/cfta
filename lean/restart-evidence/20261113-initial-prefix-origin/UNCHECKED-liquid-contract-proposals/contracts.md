# Production contracts for the remaining formalization gaps

These are proposed contracts. No Liquid Haskell check was run. No production
source changed. This note uses the current source files listed in pins.json.

1. Checked constructors and canonical records.
   `mkEdge` and `mkNode` are in `cfta/src/Data/CFTA/Interned/Type.hs:563`
   and `:582`. The useful local contract says: a retained edge has the exact
   supplied symbol, ordered children and guard; its guard is noncontradictory
   and fits the child arity. A rejected edge becomes the existing empty
   sentinel. A node contains exactly the nonempty input edges, modulo the
   actual Set order and deduplication. These facts match the Lean checked
   allocation, physical residency, full-field readback and guard-projectability
   interfaces. Do not assert that every syntactically noncontradictory guard
   has a model.
   The underlying canonical-value contract belongs to `intern` in
   `cfta/src/Data/CFTA/Interned/Cache.hs:169` and `insertHashed` at `:147`:
   existing keys keep the stored winner; repeated equal keys return that
   winner; new records retain their full key. The implementation uses global
   tables, unsafeDupablePerformIO and atomic IORef updates. A trusted contract
   for this primitive is a separate boundary from a proof of the primitive,
   its concurrency behavior, or machine-Int identity supply.

2. Actual narrowing and source-row transport.
   `reduceEdgeIntersection` at `cfta/src/Data/CFTA/Equality/Operations.hs:156`
   calls `reduceEqConstraints` at `:194`; its required-path traversal is
   `requireAll` at `:279`. A useful contract retains the original symbol and
   complete guard while recording how each actual output row and ordered
   child comes from the input and its path edits. The path-only case should
   establish the exact language restriction to terms containing the requested
   paths. The equality case must state preservation of the original guarded
   language, including inherited equality constraints and the checked empty
   fallback. At `reducePartially'` (`:76`), compose those receipts over the
   actual rows rather than replacing them with output membership alone.
   This directly helps the present source-origin gap: an actual narrowed
   function/Type read must be linked to the original candidate row through
   the edits that really ran. A result may retain a source call whose child
   value has changed; equality to the original whole parent is too strong.
   Termination of arbitrary recursive reduction remains a separate theorem;
   the current source explicitly limits its established termination cases
   in the comment at lines 129–142.

3. Eager child enumeration and its real continuation.
   `enumerateNode` is at `cfta/src/Data/CFTA/Enumeration.hs:720` and
   `enumerateEdgeWith` at `:764`. The latter prepares the actual ordered
   children with zipWithM, installs equality UVars, and records residuals.
   Useful contracts retain representative/store/waiting-index validity,
   exact suspended obligations, protected old slots, and the fragment role
   assigned to each Program or Type position. The contract must apply to
   each actual success and its reached state. It must preserve the real
   failure and callback behavior.
   The concrete CPS implementation is `EnumerateM` at `:328`, bind at `:348`,
   Alternative at `:353`, and `branches` at `:372`. Bind executes a child's
   continuation before the next sibling alternative. Alternatives restart
   from the captured branch state. Global constructor/memo effects are not
   rolled back by this branch-local EnumerationState. These are valuable
   operational contracts for matching the checked Lean eager resource/role
   induction to Haskell. A bound on allocations alone proves neither lazy
   demand order nor termination of an arbitrary continuation.

4. One accepted completion at the public output boundary.
   `runsFrom` at `cfta/src/Data/CFTA/Enumeration.hs:1285` completes enumeration,
   renders the root, then renders the ordered residual fragments. Its marker
   rendering uses `expandUVarWith` at `:1076` and `expandTermFragWith` at `:1057`.
   The synthesis path is `solutionsOfSize` at
   `cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:973`, through `programsIn`
   at `:969`; `application` (`:638`) and `ofType` (`:654`) fix the Type/Program
   positions and their equality guards.
   The missing end-to-end target is one shared finite substitution for all
   retained Type holes and aliases, yielding a term accepted by the original
   synthesis space and satisfying the returned residual obligations together.
   `Data.CFTA.Equality.Operations.accepts` at line 48 is the existing ordinary
   acceptance API. The public theorem must specify the actual supported
   synthesis input domain and preserve the emitted partial-Type scope.
   Separate witnesses for each hole, positive minimumSizes values, finished
   enumeration, and successful marker rendering do not establish this joint
   statement. `runsFrom` also deliberately returns residual obligations, so
   unconditional satisfaction for arbitrary constrained automata is not the
   local API contract. It requires a genuine source-specific completion proof
   or an actual check, not an assumed output-model contract.

The first three groups provide reusable local structural, semantic, and
operational facts. The fourth is the global completion claim that those facts
must support. Adding it as an assumption would leave the principal gap open.
Repeated-name Liquid work remains externally owned. No Haskell fix or defect
was established in this read-only audit.
