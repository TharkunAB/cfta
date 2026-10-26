import json
import subprocess
import sys
from pathlib import Path

area = Path('/tmp/mcfta-native-uniform-prefix-20261026')
declarations = [
    'SourcePruningEnumerationPreparedFuel.native_moreFuel',
    'SourcePruningEnumerationPreparedFuel.nonempty_moreFuel',
    'SourcePruningEnumerationPrefixHistory.complete',
    'SourcePruningEnumerationSelectedStep.PrefixValid',
    'SourcePruningEnumerationSelectedStep.prefix_complete',
    'SourcePruningEnumerationSelectedStep.restart_prefix_complete',
    'SourcePruningEnumerationPrefixPacket.prefix_context',
    'SourcePruningEnumerationPrefixPacket.prefix_cache_valid',
    'SourcePruningEnumerationNativeBranchCompletion.cacheValid_keeps',
    'SourcePruningEnumerationNativeBranchCompletion.cacheValid_post',
    'SourcePruningEnumerationSelectedStep.Valid',
    'SourcePruningEnumerationSelectedStep.complete',
    'SourcePruningEnumerationSelectedStep.run_eq_legacy',
    'SourcePruningEnumerationSelectedStep.prefix_no_ordinary',
    'SourcePruningEnumerationSelectedOrdinary.complete_with_history',
    'SourcePruningEnumerationRecursive.run',
    'SourcePruningEnumerationRecursive.continueWith_exact',
    'SourcePruningEnumerationRecursive.completed_head',
    'SourceCurrentColdFiniteWarmCalls.constructed_node_calls',
]
(area / 'public-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
raise SystemExit(subprocess.run([sys.executable, str(area / 'check.py'), 'public', 'public-final-1', *declarations]).returncode)
