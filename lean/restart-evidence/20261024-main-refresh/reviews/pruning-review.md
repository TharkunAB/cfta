# New main: rewrite and pruning review

Reviewed at 2026-10-24 00:44 CEST. Range: `794903b3fbad3becb8b28736fc33463760731fc7` to authoritative main `6b62b4afefca80bb05f5a37546212a99980aa3df`.

Two concrete ordering defects affect the new opt-in `PathOrder`. The default remains `KnuthBendix`. No repository change or Haskell compilation was performed by this reviewer. Root has now confirmed both defects with native GHC 9.14.1 probes against the actual public packages. The log is `/tmp/mcfta-main-refresh-20261024/pending-probes-v2.log:7–17`. Root changed only temporary printing and warning details; the original probe hashes below remain unchanged. A small independent static translation also reproduces both defects.

## Findings

1. **Annotated LPO comparison is not transitive.** In `specftacular/src/Specftacular/Rewriting.hs:1095–1114`, LPO compares program heads but uses full annotated equality to skip equal arguments. If neither direction succeeds, it falls back to raw `Term` order. With `PathOrder ["e","c","f"]`, use the parametric signature `f :: A -> B -> Int`, `[] :: [A]`, `c :: Bool`, `d :: Char`, `e :: Int` and these three Int terms:

   ```text
   s = f ([] :: [A]) (c :: Bool)
   t = f ([] :: [B]) (d :: Char)
   u = f ([] :: [A]) (e :: Int)
   compare s t = LT; compare t u = LT; compare u s = LT
   ```

   Different first-argument annotations block LPO comparison for the first two pairs. Raw comparison then reads the partial application's result annotation, with `Bool < Char < Int`. Equal first arguments in the last pair expose the precedence `c > e`. `canonicalTypes` preserves this distinction. This violates the exported comparator's total-order contract. It is passed to `sortBy` at `Specftacular.hs:1141` and controls rewrites through `orderGreater` at `Rewriting.hs:166–167`.

   Native probe: `/tmp/mcfta-main-refresh-20261024-pruning-inputs/LpoComparatorRegression.hs`, SHA256 `4c0be1cfd8595a75a1b6ebb304934f9e57191196fec71472cc8043c976b1fc0e`. It uses public `con`, `termType`, `typeSkeletonToTerm`, `canonicalTypes`, and `termCompare`. It validates every application and all three result types. It expects the cycle before and after canonicalization.

2. **Uncurried LPO reverses order in a function application context.** This defect does not depend on annotation fallback. Let `f :: (A -> A) -> A -> A`, `a :: A -> A`, `x :: A` and use `PathOrder ["f","a"]`:

   ```text
   compare (f a) a = GT
   compare ((f a) x) (a x) = LT
   ```

   The first comparison uses the subterm case. In the second, head `a` outranks `f`; `a x` also exceeds both `a` and `x`. These are valid terms for the genuine parametric constants `f = id`, `a = id`, and `x = A 0`. `rewriteStep` explicitly rewrites function positions (`Rewriting.hs:252–254`). Therefore local LPO decrease does not establish whole-term decrease. The termination explanation above `normalForm` is invalid for this order. A rewrite loop has not been executed in this review.

   Native probe: `/tmp/mcfta-main-refresh-20261024-pruning-inputs/LpoContextRegression.hs`, SHA256 `f921007f5b624f1dac4334343e606002dcb21372d5f4d5f9053613aed0d65694`. It uses the same public annotation validator and checks the equal input types and equal context result types.

For the first defect, compare erased programs throughout ground LPO, including subterm equality and lexicographic equality. Use the existing KBO/type order only when erased programs are equal. This removes the arbitrary fallback between different programs. The unchanged typed-template LPO is conservative relative to that erasure change: its successful equality checks still imply erased equality. This repair alone leaves finding 2. A complete design must establish an order compatible with actual applicative contexts, for example an applicative path order with an explicit application symbol. Restricting function-position rewriting would change behavior and would also require changes to anywhere-template pruning. Do not claim termination from the partial annotation repair.

## Intended semantics and review result

- **Typed rewriting.** Rules now fix the selected order, index left-hand program shapes, and retain typed matching after the index. Shape selection ignores annotations but only selects candidates; `matchTyped` still checks them. Uniform type-independent orientation is separate from the ground order check. Otherwise both usable directions remain available. Term-variable and type-variable namespaces are distinct. Type matching is consistent within one substitution. Completion normalizes only uniformly decreasing rules, limits program size and annotation depth, and clears its normal-form cache after a new rule. These bounds limit completion coverage; they do not prove a complete equational theory.
- **Generalized laws.** `generalizeLaw` infers a shared type scheme, allocates independent carrier variables, checks both sides' types and result equality type, and retests the proposal. A rejected or unavailable proposal preserves the original law. This remains finite testing under the documented parametric-carrier contract. A false accepted law can remove later candidates.
- **Oracle pruning.** `prunedTerms` suspends partial template matches in branch-local state. A complete match rejects the branch. Resume resolves UVar representatives. Root/arity indexes select candidates without declaring a match. Annotation-free early matching omits the arrow marker only under the fixed encoding assumption. The main caller disables pruning if a type constructor has the reserved `app/4` shape (`Specftacular.hs:1050`). Only linear rewrite templates become independent wildcard holes (`Rewriting.hs:277–315`).
- **Phase 4.** `prunedPrograms` leaves type positions open and advances `PartialTyping` on program expansions. Narrowing checks annotation compatibility and constant compatibility. The caller then reconstructs and validates a typing with `generalizeCarriersWithin`; it does not evaluate placeholder annotations. No additional concrete defect was found in these paths. Completeness still requires monotone typing checks, correct representative/role tracking, and preservation by the actual lower-level enumeration callbacks.
- **Compiled pruning.** `preparePruning` admits annotation-free patterns on a finite program DAG. It retains original edge constraints and opaque annotation nodes, excludes at each rebuilt program node, then reduces equalities once. Unknown shapes, recursive program nodes, mixed roles, cycles, or rejected caps return the original graph and full oracle list. The residual list drops a template only after structural inclusion succeeds. Input/output caps do not bound transient allocation. Its stated contract is complete finite term language after exclusion, not equality of ambiguous run multiplicities or recursive annotation cutoff streams (`CompiledPruning.hs:1–17,158–223`).

The lower-level CFTA operations must preserve that exact distinction. The new frontend depends on actual template exclusion, equality reduction, branch-local oracle state, UVar representative resolution, and stop/narrow callbacks. The extra `mergeTypeAlternatives` after compiled pruning (`Specftacular.hs:1245–1246`) is another correspondence boundary. Exact accepted terms, run occurrences, search order, and cutoff streams are different contracts. No broad language-preservation claim follows from this source review.

## Goldens and Lean coverage

The updated six golden cases run checked and unchecked **phase 1** (`Golden.hs:155–157`). The new KBO/LPO list cases both use size 5. They intentionally retain different law representatives; the LPO case prints reversal over append directly. They do not test phase-4 typing, the two order laws above, compiled-versus-oracle language equality, or recursive cutoff behavior. LPO can increase program size, so pruning can remove a term whose smaller ordered representative exceeds the requested size bound. This coverage loss is documented in `Rewriting.hs:141–150`; it must remain explicit.

Existing Lean results provide components, not a refinement of this new frontend:

- `Template.restrict_exact` proves explicit-state template restriction against `Template.Matches`.
- `SourceTemplateAnywhere.matchesNowhere_correct` proves complete-term absence at every existing subterm. Its module explicitly excludes the source exclusion allocator.
- `SourceTemplateShapeSplits.accepted_child_splits` proves surviving filled choices with source child shapes, order, and duplicate multiplicity. It explicitly excludes full `edgeCopies` scheduling and exclusion semantics.
- `SourceListSortOrdered.sortBy_ordered` requires a transitive relation and compatible comparisons. It does not prove either LPO or KBO satisfies those premises. Finding 1 blocks the LPO instantiation.
- `GraphRewrite.rows_preserve_language` requires exact local row meaning. It does not supply the new compiled-pruning correspondence.

No `lpoCompare`, `kboCompare`, `pruningTemplates`, `prunedPrograms`, `PartialTyping`, or `CompiledPruning` refinement was found in the Lean source modules. Open obligations are the actual term-order laws and rewrite termination; typed matching/substitution and critical-pair correspondence; sound pruning-template extraction from valid equations; branch-local partial matching and phase-4 typing completeness; actual finite-DAG compilation/exclusion/reduction correspondence; and the composition with enumeration, type merging, randomized validation, and runtime specialization. Existing H38 counter results do not discharge these frontend obligations.

## Retained evidence

`/tmp/mcfta-main-refresh-20261024-pruning-inputs/` retains complete Rewriting upstream diff, both new pruning modules, full new Types source and diff, golden harness and diff, README and diff, the two native probes, and the independent static model. `review-inputs.json` pins the authoritative source identities and the relevant live Lean components. Its SHA256 is `36fae28259e1b1866bf56122f0127a20771dfdf7d02232b31fe5b8d297658faf`. Root owns native probe execution, repository repair decisions, merge validation, and publication. Native confirmation is recorded in `native-confirmation.json`; the retained 17-line log excerpt pins this review cut without pinning later output from the broader probe job.
