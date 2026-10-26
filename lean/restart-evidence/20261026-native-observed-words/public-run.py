import json
import subprocess
import sys
from pathlib import Path

area = Path('/tmp/mcfta-native-observed-words-20261026')
declarations = [
    'SourceCurrentAllocatedNativeObservedWords.inputs_words',
    'SourceCurrentAllocatedNativeObservedWords.trace_wordRanges',
    'SourceCurrentAllocatedTargetQuery.Step.wordRanges',
    'SourceCurrentAllocatedTargetQuery.Step.verified_observed',
    'SourceCurrentAllocatedTargetQuery.finite_initial',
    'SourceCurrentAllocatedTargetQuery.raw_done_verified_initial',
    'SourceCurrentAllocatedTargetQuery.receipt_post',
    'SourceCurrentAllocatedTargetQuery.Step.caller_post',
    'SourceCurrentAllocatedTargetQuery.raw_done_caller_initial',
    'SourceCurrentAllocatedNativeWordBoundary.witness',
    'SourceCurrentAllocatedTargetQuery.Step',
    'SourceCurrentAllocatedTargetQuery.Step.verified',
    'SourceCurrentAllocatedTargetQuery.finite',
    'SourceCurrentAllocatedTargetQuery.Receipt',
    'SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges',
    'SourceCurrentAllocatedPartialInvariant.Post',
    'SourcePruningEnumerationRecursive.callback_prefix_complete',
    'SourcePruningEnumerationRecursive.captured_post',
    'SourcePruningEnumerationRecursive.run',
    'SourceCurrentColdFiniteWarmCalls.constructed_node_calls',
]
(area / 'public-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
raise SystemExit(subprocess.run([sys.executable, str(area / 'check.py'), 'public', 'public-final-1', *declarations]).returncode)
