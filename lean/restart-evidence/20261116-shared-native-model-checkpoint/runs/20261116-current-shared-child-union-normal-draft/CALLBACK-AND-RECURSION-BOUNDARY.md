# Actual operation and callback boundary

| Existing actual API | Exact scope and use |
| --- | --- |
| SharedSelectedContinuations.ChildDispatch.observe, SharedSelectedContinuations.lean:46 | Actual empty/nonterminal/terminal dispatcher. The terminal branch is SharedCachedTerminal.raw. |
| ChildDispatch.run and erase, same source:64/87 | Optional cache metadata retains the same raw observation and caller. |
| ChildTraversal.run, same source:211 | Actual ordered list recursion. The smaller argument is the remaining list. Native/check fuels do not decrease. |
| SharedChildVisitors.visitChildren_shallow, SharedChildVisitors.lean:107 | Exact callback factorization through ChildTraversal.run. The complete callback receives its proved normal returned caller. The stopped callback receives the proved normal observation caller. |
| SharedEagerChildren.eagerChild, SharedEagerChildren.lean:134 | Recurses on MergedOrdinaryHeight.height incoming. The literal runtime guard requires height child < height incoming. The false guard calls shallowVisit. No child-height decrease can be invented. |
| SharedPreparedRecursiveChildPolicy.resumeWithNarrow | The actual worker restart recurses on recursiveFuel. Its smaller-depth result must be established in the worker induction. |

The arbitrary done/stopped callbacks of shallowVisit can return a new caller. The child operation theorem alone does not prove normality after executing them. The real worker must prove those concrete continuations by its genuine list/height/depth induction. An assumed arbitrary future callback law would leave that worker obligation open.

The proposed component proves the pre-callback endpoint facts directly and proves the entire concrete shallow ChildTraversal. It adds no model, history, normality-of-future-output or callback-supplier premise. It preserves all original ordered child occurrences and stopping observations. The full single-assignment completion objective remains unchanged.
