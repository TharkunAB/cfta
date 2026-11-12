# Current source typing and ordinary eager descent

Checked 2026-11-12 18:11 CET. Base `35fe4e4f7c195830ae8ece7b501b967f4c287db5`. Integrated main `e53852064d3ef5a2eafec47d754c27504b11de5f`.

Six modules, 1112 source lines, six public laws. All strict own-source checks pass. The complete Audit and all seven portable checks pass. The graph has 5836 live modules, seven affected modules and 4833 Audit imports. Audit emits 94090 axiom reports. All 262073 previous Audit bytes remain after six imports. Only propext, Classical.choice and Quot.sound appear in the six public axiom reports.

The statements below observe the modeled current source and native algorithms. They do not verify the Haskell compiler, fixed host word capacity, complete default enumeration, exact required-token coverage or unrestricted ordinary completeness.

## Checked source contracts

### SourceSynthesisCurrentApplicationTyping

The actual four-child forest and canonical application PCS guard join the SAME function and argument Typed/Projection/annotation receipts. The result is ordinary application typing, its exact raw result annotation, and the same Program projection. Marker shape and Fun/2 conversion follow from checked inverse Type laws. No admission premise is added for rigid query types.

Source: 120 lines; SHA256 `8562b57f63c11e4ee91a0d58d6773d1b2de60773b526b87b8355517c3baf2013`.
Packet: `lean/restart-evidence/20261112-current-application-typing`. Public laws: 1.

```lean
theorem application_typed [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query)
    (functionExpression argumentExpression : Expression)
    (annotation actualMarker functionTerm argumentTerm : Term Symbol)
    (functionProgram argumentProgram : Program) (functionType argumentType : Ty)
    (children : forest (SourceEqualityPCSGuard.holds formulas solver) []
      (mapChildren literal [(context lib query).types, arrowMarker top,
        functionExpression, argumentExpression])
      [annotation, actualMarker, functionTerm, argumentTerm])
    (guardHeld : SourceEqualityPCSGuard.holds formulas solver
      (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
      (.node (literal "app") [annotation, actualMarker, functionTerm, argumentTerm]) = true)
    (functionTyped : Typed lib query functionProgram functionType)
    (functionProjection : Projection literal Prod.fst functionTerm functionProgram)
    (functionAnnotation : functionTerm.atPath [0] = some (candidateRigid functionType))
    (argumentTyped : Typed lib query argumentProgram argumentType)
    (argumentProjection : Projection literal Prod.fst argumentTerm argumentProgram)
    (argumentAnnotation : argumentTerm.atPath [0] = some (candidateRigid argumentType)) :
    ∃ resultType : Ty,
      Typed lib query (.app functionProgram argumentProgram) resultType ∧
      annotation = candidateRigid resultType ∧
      Projection literal Prod.fst
        (.node (literal "app") [annotation, actualMarker, functionTerm, argumentTerm])
        (.app functionProgram argumentProgram) := by
```

### SourceSynthesisCurrentLeafTyping

Actual current size-one row membership and the SAME accepted term derive the exact singleton candidateRigid annotation, ordinary variable typing, decoder, projection and count one. The result retains original group/rho/demanded-image origins, argument-only role origins, or canonical query-row membership with the ORIGINAL last lookup. Duplicate names and arbitrary avoid rules remain permitted.

Source: 169 lines; SHA256 `2d6ce46bd86ddd25d01037c08d6066ca3720ccbe4c9bcbb60c0c023181e473e1`.
Packet: `lean/restart-evidence/20261112-current-leaf-typing`. Public laws: 1.

```lean
theorem size_one_typed
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {lib : Library} {query : Query} {asArgument : Bool}
    {expression : Expression} {term : Term Symbol}
    (member : expression ∈ termsRows (context lib query) asArgument 1)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ name typ,
      term = .node (literal name) [candidateRigid typ] ∧
      Typed lib query (.var name) typ ∧
      term.atPath [0] = some (candidateRigid typ) ∧
      Projection literal Prod.fst term (.var name) ∧
      toProgram literal Prod.fst term = .var name ∧
      (toProgram literal Prod.fst term).components = 1 ∧
      ((∃ entry ∈ lib.libraryGroups, ∃ rho : String → Ty,
          name = entry.1 ∧ typ = substTy rho entry.2.1 ∧
          ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2.1) →
            RawAdmitted (constructorCatalog lib query) (rho raw)) ∨
       (asArgument = true ∧ ∃ entry ∈ lib.libraryArgumentOnly, ∃ rho : String → Ty,
          name = entry.1 ∧ typ = substTy rho entry.2 ∧
          ∀ raw, variableSymbol raw ∈ variables (encodeTy entry.2) →
            RawAdmitted (constructorCatalog lib query) (rho raw)) ∨
       ((name, typ) ∈ queryBindings query ∧
          queryLookup query.queryArguments name = some typ)) := by
```

### SourceSynthesisCurrentRelevantTyping

Direct strong induction observes the actual successful relevantRows result. Empty selections use terms_typed. Singleton selections derive winning-row origins from resolveSelection_subset and use size_one_typed. Actual successful split/offset traversals supply smaller calls and application_typed. The same Program/decoder/count/annotation receipt holds for arbitrary names, avoid rules and duplicate query bindings. No general relevant-to-terms inclusion is asserted.

Source: 227 lines; SHA256 `70c34e5d6cdfbcc5e666e7a0dad0767db29f7376e249e5662c0992e2a85f8b73`.
Packet: `lean/restart-evidence/20261112-current-relevant-typing`. Public laws: 1.

```lean
theorem relevant_typed
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool) (count : Nat)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument count names = .ok rows)
    (expression : Expression) (member : expression ∈ rows) (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program typ, Typed lib query program typ ∧ Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧ program.components = count ∧
      term.atPath [0] = some (candidateRigid typ) := by
```

### SourceSynthesisCurrentRootTyping

Actual current firstOrderRaw success and SAME canonical-PCS acceptance derive the exact filter wrapper, SAME body, ordinary Typed Program at the ORIGINAL query goal, both exact goal annotations, SAME projection/decoder and signed.toNat component count. The proof observes actual returned mapM chunks and uses their relevant_typed receipts. Rigid goal reification and the actual filter PCS class justify only the documented Fun/2 type conversion. It requires no Eligible, avoid=[], query/goal admission, model, Room or future typed-child supplier.

Source: 102 lines; SHA256 `36f09cb8c1c077539a854576d7ef944b18f41786bf24f25d5cd1249ddc4a36c3`.
Packet: `lean/restart-evidence/20261112-current-root-typing`. Public laws: 1.

```lean
theorem firstOrderRaw_typed [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program body,
      term = .node (literal "filter") [candidateRigid query.queryGoal, body] ∧
      Typed lib query program query.queryGoal ∧
      term.atPath [0] = some (candidateRigid query.queryGoal) ∧
      body.atPath [0] = some (candidateRigid query.queryGoal) ∧
      Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧
      program.components = signed.toNat := by
```

### SourceSynthesisCurrentTermsTyping

Strong induction covers every actual unrestricted termsRows branch and arbitrary count. Size-two filtered avoid pools embed semantically into genuine full size-one pools. The receipt retains one SAME Typed Program, projection, decoder, exact component count and raw annotation. No future child typing or admission premise appears.

Source: 209 lines; SHA256 `d75ddcd0f2dfc2e0f306e2f5df0869d36c4fa1855191ac4c2006d8c39ef37185`.
Packet: `lean/restart-evidence/20261112-current-terms-typing`. Public laws: 1.

```lean
theorem terms_typed [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool) (count : Nat)
    (expression : Expression) (term : Term Symbol)
    (member : expression ∈ termsRows (context lib query) asArgument count)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program typ, Typed lib query program typ ∧ Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧ program.components = count ∧
      term.atPath [0] = some (candidateRigid typ) := by
```

### SourcePruningEnumerationSharedEagerUnaryNullaryResources

A genuine current ordinary unary parent descends into its ordinary child with exactly one stored and selected nullary row. ONE accepted-own producer and ONE checked nullary producer derive both actual source/cached/raw prefixes, all endpoint Packets, unchanged full Caller/inventory/Memos/query, Post/Fits/physical Heap, exact fresh-slot sum, protection/order/pending/origins, and one coupled final assignment at before/own/child/final endpoints. The all-fuel CPS identity prepends the inner receipt to the FULL complete or stopped consumer result. It asserts no resource preservation or work bound for arbitrary consume.

Source: 285 lines; SHA256 `8ebbb7fcfb9e2639b7749905b40038af52f7de1295185599f0a922df4e37789e`.
Packet: `lean/restart-evidence/20261112-shared-eager-unary-nullary-resources`. Public laws: 1.

```lean
theorem visitSelected_unary_nullary_model_packet
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List Edge) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : Edge) (scs : List Suspended) (child : Node)
    (childEntry : Cache.Interned InternedBinderProtocol.NodeKey) (leaf : Edge)
    (childDepth : Nat) (childFree : List InternedBinderProtocol.Reference) (edgesOf : Node → List Edge)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry rows depth free))
    (parentClosed : free = []) (selected : edge ∈ rows) (unary : edge.children = [child])
    (childShape : child = .node childEntry [leaf] childDepth childFree)
    (leafNullary : leaf.children = []) (selector : edgesOf child = [leaf])
    (ordinary : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ordinaryNonterminal (descendScs 0 scs ++ descendScs 0 (suspendedVars before.core.counter tries)) child = true)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol) (term whole : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc)
    (old : AssignmentOrigins whole before.core.counter assignment) (origin : Origin whole term) :
    ∃ (tries childTries : List EqualityTrie.Trie) (residual childResidual : Option Constraint)
      (action childAction : OwnAction) (own childOwn childAfter after : Cached)
      (bucket : List Suspended) (childTerm : Term Symbol) (extended : Nat → Term Symbol),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      SourcePruningEnumerationConstraint.project leaf.entry.key.constraint = some (childTries, childResidual) ∧
      (∀ trie ∈ tries, EqualityTrie.Valid trie) ∧ (∀ trie ∈ childTries, EqualityTrie.Valid trie) ∧
      arityAllows edge.children.length scs = true ∧ arityAllows leaf.children.length bucket = true ∧
      bucket = descendScs 0 scs ++ descendScs 0 (suspendedVars before.core.counter tries) ∧
      SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((edge.entry.key.symbol,
          [(child, bucket, SourcePruningEnumerationShallowChild.prepareChild bucket child)], residual), own)] ∧
      ExceptT.run (action before.core) = [.ok ((edge.entry.key.symbol,
        [(child, bucket, SourcePruningEnumerationShallowChild.prepareChild bucket child)], residual), own.core)] ∧
      own.core = suspendedState tries.length before.core ∧
      SourcePruningEnumerationEdgePrefix.prepare bucket leaf = some childAction ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap bucket leaf own =
        some [((leaf.entry.key.symbol, [], childResidual), childOwn)] ∧
      ExceptT.run (childAction own.core) = [.ok ((leaf.entry.key.symbol, [], childResidual), childOwn.core)] ∧
      childOwn.core = suspendedState childTries.length own.core ∧
      childAfter = SelectedEdge.finish childResidual (.node leaf.entry.key.symbol []) childOwn ∧
      after = SelectedEdge.finish residual (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) childAfter ∧
      Packet formulas solver inventory caller memos metadata own ∧
      Packet formulas solver inventory caller memos metadata childAfter ∧
      Packet formulas solver inventory caller memos metadata after ∧
      Post formulas solver inventory caller caller memos ∧ Fits seed.2 caller.checked ∧
      Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      after.core.counter = before.core.counter + tries.length + childTries.length ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ level bound, EnumerationOrder.Stratified before.core level bound →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel bound) ∧
      FragmentBound after.core.counter (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) ∧
      PendingFragment after.core (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) ∧ InputsPending after.core scs ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended before.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended own.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended childAfter.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended after.core ∧
      Fragments.fill extended (.node leaf.entry.key.symbol []) = childTerm ∧
      Fragments.fill extended (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) = term ∧
      AssignmentOrigins whole after.core.counter extended ∧
      (∀ sc ∈ scs, Suspended.Holds extended term sc) ∧
      ∀ checkEmpty r n p h k (consume : SelectedEdge.Result width → Fold),
        visitSelected (eagerChild checkEmpty r n p h k edgesOf) consume scs edge caller before memos.query =
          match consume (.complete (.node edge.entry.key.symbol [.node leaf.entry.key.symbol []]) caller memos.query after) with
          | .complete processed outputs finalCaller finalQueries =>
              .complete (.complete (.node leaf.entry.key.symbol []) caller memos.query childAfter :: processed) outputs finalCaller finalQueries
          | .stopped processed outputs current =>
              .stopped (.complete (.node leaf.entry.key.symbol []) caller memos.query childAfter :: processed) outputs current := by
```

## Actual repairs and source distinctions

Application120 passed unchanged. Leaf167 first failed because a private proof projected a forest conjunction before reducing mapChildren/forest; Leaf169 adds that reduction only. Terms207 passed the kernel build but strict checking found redundant automatic Formula equality binders; Terms209 adds two scoped omit wrappers and keeps the public header and proof unchanged. Relevant227 first captured a default Formula equality instance in Receipt before the section instance; the repair moves Receipt after that instance and opens the existing top name. Its public header is unchanged. Root102 first needed an explicit existing PCS class and removal of two unused simp arguments; its frozen public header is unchanged. Unary278 needed final CacheValid/Stratified transport from retained endpoint fields and expansion of local after/fragment definitions in its CPS proof. Unary285 keeps the exact frozen public header and all endpoint results. No lint was disabled and no new axiom was introduced.

The runtime retains original source snapshots, notes and exact failed-check logs. These small text files are not binary build archives. Every committed final source and checker is independently reproducible from this branch. Historical source-pinned Haskell counterexamples remain pinned to their original source revisions.

A concrete non-inclusion uses f:A→B, query x:A and libraryAvoid=[(["f"],none)]. The size-two unrestricted default function pool excludes f. A nonempty relevant selection ["x"] instead splits into an empty-selection size-one function pool and the required x row; it can accept f x. This is a source-domain distinction, not a Haskell defect. The direct relevant induction proves typing for both domains without claiming their inclusion.

The current source result preserves ordinary type conversion modulo Fun/2. It does not claim raw type syntax equality or GHC name-resolution priority. Duplicate query names use the LAST original type. Component/query names may collide. The inverse leaf records explicit row origins. Ordinary source soundness does not yet produce the marked-token eligibility certificate needed to pair with the existing forward completeness domain.

## Haskell and upstream status

Upstream was refreshed before publication; main remains `e53852064d3ef5a2eafec47d754c27504b11de5f`. No production Haskell or Cabal file changed. The earlier focused merged Synthesis test run remains the applicable runtime check: 16 examples, zero failures. No new full runtime suite, corpus run or benchmark is claimed.

The external Liquid reader defect remains recorded in root FINDINGS.md, with post1182, exact examples, main revision and external ownership. The planned LAST type AND refinement repair is not reported pushed or merged. This packet does not implement or rerun that repair.

## Reproduction and boundaries

Each of the six packet checkers emits explicit #check and #print axioms for every public theorem and pins its source SHA256. The compatibility checker pins the complete reverse dependency closure and the unchanged earlier Audit suffix. Portable results record cwd=/tmp for every checker. All jobs use the project Nix shell, LEAN_NUM_THREADS=1, memory.max=memory.high=4294967296 and memory.swap.max=0.

The eager theorem covers genuine ordinary unary-to-nullary descent. Its arbitrary consumer is an observed CPS parameter; no finite work or model-preservation property of that unrestricted consumer is inferred. General descent still needs a physical-payload forecast for counter/mass growth, success multiplicities and ordered query costs, followed by specialization to the actual recursive continuation. Complete/default lazy enumeration, order/multiplicity, all reached closure, rank/unrank inverses and Haskell runtime correspondence remain separate full-system contracts.

## Runtime next audit: current-relevant-root-typing-next.md

# Current relevant and root reverse typing

Frozen read-only audit, 2026-11-12 17:55 CET. No source or compiler changes.
This cut observes actual current source evaluation. It does not prove native execution.

Use the existing `Program`, ordinary `Typed`, `Projection`, and `candidateRigid`.
Here `Symbol := SourceObservations.Label FullSyntax.Formula`,
`literal := SourceSynthesisLabelProgramBuildRoles.literal`,
`context := SourceSynthesisCurrentContext.context`, and
`H := SourceEqualityPCSGuard.holds formulas solver`.
The headers use the existing mapped source evaluator and formula equality instance.

```lean
variable [DecidableEq FullSyntax.Formula]

theorem relevant_typed
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (asArgument : Bool) (count : Nat)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument count names = .ok rows)
    (expression : Expression) (member : expression ∈ rows) (term : Term Symbol)
    (accepted : evaluate H [] (mapSyntax literal expression) term) :
    ∃ program typ,
      Typed lib query program typ ∧ Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧ program.components = count ∧
      term.atPath [0] = some (candidateRigid typ)

theorem firstOrderRaw_typed
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (term : Term Symbol)
    (accepted : evaluate H [] (mapSyntax literal expression) term) :
    ∃ program body,
      term = .node (literal "filter") [candidateRigid query.queryGoal, body] ∧
      Typed lib query program query.queryGoal ∧
      term.atPath [0] = some (candidateRigid query.queryGoal) ∧
      body.atPath [0] = some (candidateRigid query.queryGoal) ∧
      Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧
      program.components = signed.toNat
```

The first proof follows the actual `relevantRows` definition by strong induction on count.
Observe its actual resolution result, then its actual size and winner branches.
An unresolved key contradicts `returned`; an empty winner delegates to `terms_typed`.
For a singleton winner at count one, observe the same selected query row.
`SelectionOrigins.resolveSelection_subset` derives its membership in current argumentEdges.
Those edges are the mapped `queryBindings query`; `queryBindings_member` gives LAST lookup.
Lift its same accepted singleton edge into the full argument-row pool and use `size_one_typed`.
This lift concerns only that source row; it asserts no general relevant-to-terms inclusion.
The insufficient-size branch has an empty output, so it cannot contain `expression`.
In the remaining branch, observe the actual split and offset traversals and their flatten.
Retain their actual successful child calls with the literal take/drop name keys.
Split subtypes give both child counts strictly below count; apply the induction hypotheses.
Invert actual accepted unions to retain the same functionTerm and argumentTerm.
Pass their derived typing/projection/annotation receipts to `application_typed` once.
Its result and the child component counts give the complete receipt at count.
No prior child typing, key resolution, or source-success supplier becomes a public premise.

`mapM_success_all₂` records each same successful traversal, without another producer.
`SymbolicDriver.all₂_right_forall` transfers the per-action property to returned outputs.
Alternatively `all₂_forall_iff` plus `All₂.imp` gives the same transfer.
No new selection engine or typing judgment is needed.

The root proof unfolds only the same actual current `firstOrderRaw` result.
The negative branch contradicts `returned`; observe its one successful permutation mapM.
Invert the actual filter, its candidate union, and the returned flattened chunk membership.
Apply `relevant_typed` to that chunk and the same body term.
Use `current_typeNode_only` on the actual goal field, with no goal-universe premise.
The actual filter PCS guard equates paths `[0]` and `[1,0]`.
Together with the body annotation, it equates `candidateRigid typ` and the goal encoding.
`candidateRigid_eq_iff` derives ordinary raw-type equivalence.
`Typed.conversion` then types the same Program at the original query goal.
The filter projection retains that same Program and the chunk's signed.toNat count.
Root marker shape here is the source `filter` wrapper, not a default enumeration marker.

Do not prove `relevantRows` soundness by a general inclusion in `termsRows`.
A concrete source distinction uses group `f : A -> B`, query `x : A`, and
`libraryAvoid = [(["f"], none)]`, with no other component or argument-only rows.
At size two, termsRows omits the special rule because its optional argument set is none.
Its default function pool excludes f; its only query function candidate is x.
Thus the exact source application with function leaf f is absent from that pool.
The nonempty relevant key ["x"] instead has split one and offset zero.
Its function call is relevantRows false 1 [], which delegates to the unfiltered size-one pool.
Its argument call is relevantRows true 1 ["x"], which selects x.
Thus its actual application row accepts f x under the ordinary A/B annotations.
This distinction does not establish a Haskell defect or affect ordinary typing soundness.

Exact checked/source dependencies, relative to lean/MicroCFTA/:
- SourceSynthesisFirstOrderConstruction.lean:84 (termsRows), 112 (relevantRows).
- SourceSynthesisCurrentConstruction.lean:20 (actual current firstOrderRaw).
- SourceSynthesisSelectionOrigins.lean:190 (resolveSelection_subset, duplicates allowed).
- SourceSynthesisPr211QueryBindings.lean:62 (queryBindings_member, original LAST lookup).
- SourceSynthesisCurrentLeafTyping.lean:92 (169 lines, strict PASS).
- SourceSynthesisCurrentApplicationTyping.lean:41 (application_typed, strict PASS).
- SourceSynthesisCurrentRigidTypeReification.lean:102 (current_typeNode_only).
- SourceSynthesisPr210TypeReflection.lean:171 (candidateRigid_eq_iff).
- SymbolicNormalization.lean:283 (mapM_success_all₂); SymbolicScope.lean:159 (all₂_right_forall).
- R248 runtime SourceSynthesisCurrentTermsTyping.lean:128 (Beta's frozen public header; check pending).
  Its node_inclusion:46, union_receipt:74, application_receipt:89 are PRIVATE.
  Do not call their mangled names. A visibility-only export can reduce repeated shape glue.

Required token coverage is a separate property. Empty required selections use unrestricted terms.
Those terms can add query uses beyond the requested occurrences. Retain duplicates and LAST types.
Ordinary typing alone does not claim an exact permutation of all Program query uses.
This cut permits arbitrary avoid rules and duplicate names. It needs no Eligible certificate,
query/goal admission, model, Room, future typed child, native endpoint, or whole worker completion.


## Runtime next audit: current-source-eligibility-next.md

# Exact current source admission after ordinary typing

Read-only audit, 2026-11-12 18:09 CET. No proof or runtime claim is added.
The existing predicate is CurrentProgramAdmission.Eligible:31. There is no
separate exported RawEligible in the inspected current modules.

## One exact next public observer

Proposed module: SourceSynthesisCurrentRootEligibility.lean. Use the existing
Eligible, Program, Projection, candidateRigid, Symbol and literal definitions.

```lean
theorem root_eligible [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal expression) term) :
    ∃ program tokens,
      Eligible lib query true program query.queryGoal tokens ∧
      tokens.Perm query.queryArguments ∧
      Projection literal Prod.fst term program ∧
      toProgram literal Prod.fst term = program ∧
      program.components = signed.toNat ∧
      term.atPath [0] = some (candidateRigid query.queryGoal)
```

This reverse direction can retain arbitrary avoids. Its .ok input is the actual
output identity. It does not take Eligible, Typed, coverage or future membership
as a supplier. The certificate and projected Program refer to the SAME term.
The raw goal stays ORIGINAL; Eligible.conversion permits only existing Equivalent.

## Minimal strengthening of the existing source induction

Naked Typed does not retain source roles, demanded images or marked origins.
Strengthen the structural receipt used by current leaf/terms/relevant proofs
with Eligible at the ACTUAL asArgument role and exact marked token list.
Do not try to recover these facts from the final ordinary typing proof alone.

CurrentLeafTyping.size_one_typed:92 already returns each actual group/argument-only
binding, per-use rho, demanded RawAdmitted images, or canonical query origin.
Build Eligible.group, argumentOnly or unmarked queryArgument from that origin.
The argument-only origin retains asArgument=true. Do not infer origins only from
decoded names: component and query names may collide and remain permitted.

At applications, retain the two child Eligible certificates with roles false/true.
ApplicationTyping.application_typed supplies arrow/domain Equivalent conversions
and the SAME result annotation. The actual first forest slot supplies universe
membership for that annotation. CurrentTypeAdmission.universe_member_iff_admitted:228
then gives RawAdmitted for precisely the chosen codomain. Its topHeld premise is
derived by SourceEqualityPCSConstructors.top_true. Use Eligible.application.
No blanket admission premise is needed for rigid query types or the root goal.
GeneralizeReification.generalize_instance:431 already extracts each group's rho.

Unrestricted terms select no marked tokens, so their strengthened receipt uses [].
Reuse the actual size2 filtered-pool embedding and size3+ induction. Avoid pruning
changes which rows exist; it does not invalidate certificates for selected rows.
Relevant induction must stay direct: size2 relevant rows need not belong to the
avoid-pruned termsRows table. Empty selections delegate to strengthened terms.

For relevant recursion, GENERALIZE over an arbitrary ORIGINAL token list tokens
whose map Prod.fst equals the requested names key. At a marked singleton, use
Eligible.queryToken with the token's ORIGINAL payload and the actual LAST lookup
type. Its constructor deliberately does not require token.2 to equal that type.
For take/drop branches, split this token list at the ACTUAL resolved-winner offset.
resolveSelection_spec:190 preserves the winner's full name sequence, and
resolveSelection_length:216 preserves repeated-name multiplicity. List.map_take,
List.map_drop and take_append_drop align children and reconstruct the SAME tokens.
Never assume winner payloads equal the original earlier duplicate payloads.
Unmarked subtrees may add query uses; marked coverage is not the whole use multiset.

At the root, SelectionClosure.permutations_spec:226 and CurrentContext's
context_argument_names:128 give a permutation of ORIGINAL argument names.
Lift that name permutation to original argument PAIRS, retaining multiplicity.
The small pure helper needed is: selected.Perm (original.map f) implies an
original-permuted list tokens with tokens.map f=selected. No injectivity of f
is valid or required. Init/Data/List/Perm.lean has Perm.map:213, but the inspected
file has no converse lift. Prove this helper privately if no imported law applies.
The generalized relevant receipt then gives exact original-token coverage.
The filter's actual equality plus rigid uniqueness permits Eligible.conversion
to queryGoal. Decoder/projection equality identifies the SAME counted Program.

## Honest iff and boundaries

Under lib.libraryAvoid=[], the proposed reverse observer and existing
CurrentRelevantAdmission.uses_root_member:296 give a projected-language iff:
an actual accepted root term decoding to program at Int.ofNat program.components
exists iff some tokens satisfy Eligible true program queryGoal tokens and
tokens.Perm ORIGINAL queryArguments. This is existential annotation acceptance,
not a finite-enumeration, native worker or termination result.

The unrestricted all-avoids iff is false for this certificate. A source-level
boundary is empty query, groups f:A->B and x:A, goal B, avoid=[([f],none)].
Eligible admits f x with []; termsRows size2 removes f from the fallback pool,
and empty relevant selection delegates there. This is not a new runtime finding.
Typed alone is also weaker: an argument-only f used as an application function
can type ordinarily, but Eligible requires that child role=false. A group variable
image e can type ordinarily while demanded RawAdmitted permits only a..d there.
Neither boundary justifies restricting all rigid query/goal variables.

No new typing judgment, uniqueness gate, global substitution, admitted query/goal,
compiler, repository edit, Haskell change or historical packet change is proposed.


## Runtime next audit: current-eager-general-next.md

# R248: the next unbounded eager proof

Status: READ-ONLY UNPROVED PLAN. ROOT reports Unary285/8ebbb7fc strict PASS1.
All source paths below are relative to lean/MicroCFTA/. No source changed here.

Choose ONE new module: SourcePruningEnumerationSharedEagerScalarObservers.
Prove bounds on the INPUTS of actual selected-edge consumers at arbitrary
ordinary height. This is a numerical CPS observer, not another finite-depth
example or a resource assertion about an unrestricted consumer's final result.

## Derived forecast

Define nodePlan edgesOf value B from the literal current immutable payload and
bucket-length bound B. Use a tuple (C,G,M,Q): success multiplicity, maximum extra
counter, maximum extra suspended mass, combined incoming-query steps.
Fallback is (1,1,B,B+1). For an ordinary node take componentwise maxima between
fallback and the ordered-row aggregate. The maximum covers terminal buckets.
For each literal selected row inspect its CURRENT Constraint.project. None has
(C,G,M,Q)=(0,0,0,0): the actual unhandled row stops without invoking done.
For Some(tries,residual), let W=tries.length. Its own prefix adds W counter and
ZERO suspended mass. Every child bucket has length at most B+W. A child below
the parent height uses nodePlan child (B+W); a nondecreasing child uses fallback,
matching the actual runtime rank guard. No future selection/availability fact
is needed for this forecast. Actual source selector membership later removes
that guard fallback, by SharedEagerChildren.prepared_child_eager:184.

For a tuple: C=product C_i; G=sum G_i; M=sum M_i;
Q=sum_i ((product_(j<i) C_j)*Q_i). The empty tuple has (1,0,0,0).
For rows: C=sum C_row; G=max G_row; M=max M_row; Q=sum Q_row.
Add W to each supported row's G. Count literal row OCCURRENCES, including
repeats. A rejected or stopped prefix executes less than this full forecast.
Thus Core growth uses branch maxima, while shared native query work uses an
ordered sum and tuple-tail multiplicities. Neither uses processed.length.
selectedPlan edgesOf edge B uses the same projection/tuple rule with plain
nodePlan children, matching visitSelected(eagerChild ...) without an outer rank.

## Exact proposed public CPS observer header

Use existing aliases Receipt=SelectedEdge.Result and Fold=NativeContinuations.Result
Output Reason width. G/M select components of selectedPlan; inline the match.

```lean
theorem visitSelected_callback_bounds
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (scs : List Suspended) (edge : Edge) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    let plan := selectedPlan edgesOf edge scs.length
    ∀ left right : Receipt width → Fold,
      (∀ receipt,
        (match receipt with
        | .complete _ _ _ after | .rejected _ _ after =>
            after.core.counter ≤ before.core.counter + G plan ∧
            suspendedBound after.core ≤ suspendedBound before.core + M plan
        | .stopped _ _ candidate => ∀ after, candidate = some after →
            after.core.counter ≤ before.core.counter + G plan ∧
            suspendedBound after.core ≤ suspendedBound before.core + M plan
        | .unhandled => True
        | .finalizeStopped .. => False) → left receipt = right receipt) →
      visitSelected (eagerChild checkEmpty r n p h k edgesOf)
        left scs edge caller before queries =
      visitSelected (eagerChild checkEmpty r n p h k edgesOf)
        right scs edge caller before queries
```

G/M/selectedPlan above are proposed definitions.
The implication characterizes reachable callback inputs; it supplies no future
model/Packet/Room/completion or consumer work bound.
It preserves the ENTIRE Fold, including every receipt, output and stopped endpoint.
The internal node lemma similarly relates done/stopped callbacks only on their
bounded input caches; candidate=None requires callback equality without a bound.

## Proof cut and exact existing head/tail laws

Private well-founded IH: height incoming, generalized over ALL current buckets,
Caller, Queries, Cached, fuels and both actual CPS callbacks. Private tuple and
row-list inductions run inside that IH. Do not expose childIH publicly.
SharedEagerChildren.eagerChild_ordinary:165 gives the actual scan, with guarded
recursive children. The true rank branch invokes IH; the false branch uses
SharedChildScalarBounds.ChildDispatch.observed_scalar_bounds:24 (all outcomes).
SharedChildVisitors.visitChildren:33 invokes each tuple tail INSIDE the head's
success callback. SharedBranching.scan:29 reuses the captured Cached for every
sibling, but threads the actual native endpoint AFTER the full head/tail result.
Case-split the SAME CachedOwn.prepare. Derive projection internally from its
supported-singleton branch; OwnInputShape.prepare_inputs:32 gives exact staged
inputs. EdgeScalarBounds.CachedOwn.prepare_scalars:70 gives exact own growth
and mass. CostBounds.descend_length_le:17/suspended_length:23 bound child buckets.
Residual finish changes only obligations (SharedSelectedContinuations:427).
Use the existing unhandled/rejected/stopped arms unchanged; do not assume success.

A later visitCapturedWith hook observer follows from this SAME operation and
EdgeScalarBounds.Finalize.run_scalars:138. Finalization adds no counter or mass;
its failure has its actual unfinished receipt (SharedChildVisitors:79–90).
No second read, copier, cached prefix, child producer or callback may be run.

## Boundary

The scalar CPS theorem can close G/M at all ordinary depths. Pure C/Q algebra
alone does NOT certify actual callback counts or native query traces: the
existing Fold has no call-count field. Do not publish Q as a checked execution
bound until an actual-call observer/trace lemma relates it to this SAME CPS run.
Q counts combined incoming steps, not low-level workFuel or machine instructions.
Arbitrary consume can mutate caller/memos or stop; current payload cannot bound
its native work or preserve its model. For the real driver, derive that work by
an INTERNAL outer recursive-depth IH on actual continueWith/resumeWithChild,
then inner height IH; append each callback forecast at its actual reached Seed.
The explicit CURRENT arithmetic capacity of the derived whole plan remains
necessary. IncomingReservation.advance_add:43 and reserved_of_final_capacity:134
compose existing steps; SharedRecursiveReservation.step/stage:49/53 show phase
order, but their old shallow edge forecast must be replaced.
Keep all-row resource safety separate from chosen-model progress. The latter
must retain original-variable agreement, both before/after Satisfies and origins;
OwnChildModelProgress.accepted_own_children_origins:233 derives its prefix.
The old tail model transport is SharedChildTraversalModelResources:34/56.
Keep full Post/Memos/metadata/Packet/Fits/Heap at each actual callback boundary.
consumeSelected:42 prepends INNER receipts; old sibling count bound at
SharedPreparedFiniteSiblingResources:207 cannot index eager work. At the outer
boundary SharedPreparedRecursive.finish:62 discards processed on complete only;
attach counting/physical-history observations BEFORE finish. Its stopped case
retains the exact prefix. Source reach, adequate outer depth, all-alternative
model progress, default order, lazy effects and Haskell correspondence stay open.
