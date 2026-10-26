import json
import subprocess
import sys
from pathlib import Path

area = Path('/tmp/mcfta-native-recursive-packet-20261026')
declarations = [
    'SourcePruningEnumerationRecursive.Packet',
    'SourcePruningEnumerationRecursive.captured_post',
    'SourcePruningEnumerationRecursive.callback_frame',
    'SourcePruningEnumerationRecursive.receipt_packet',
    'SourcePruningEnumerationRecursive.prefix_packet',
    'SourcePruningEnumerationRecursive.packet_prefix_complete',
    'SourcePruningEnumerationRecursive.callback_complete',
    'SourcePruningEnumerationRecursive.callback_prefix_complete',
    'SourcePruningEnumerationReceiptCallbackFuel.completes',
    'SourcePruningEnumerationReceiptCallback.completes',
    'SourcePruningRecordTypes.recordTypes_inl_complete_bounded',
    'SourcePruningRecordTypes.recordTypes_moreFuel',
    'SourcePruningEnumerationSelectedStep.PrefixValid',
    'SourcePruningEnumerationSelectedStep.prefix_complete',
    'SourcePruningEnumerationSelectedStep.restart_prefix_complete',
    'SourcePruningEnumerationSelectedStep.Valid',
    'SourcePruningEnumerationSelectedStep.complete',
    'SourcePruningEnumerationSelectedStep.run_eq_legacy',
    'SourcePruningEnumerationRecursive.run',
    'SourcePruningEnumerationRecursive.continueWith_exact',
    'SourcePruningEnumerationRecursive.completed_head',
    'SourceCurrentColdFiniteWarmCalls.constructed_node_calls',
]
(area / 'public-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
raise SystemExit(subprocess.run([sys.executable, str(area / 'check.py'), 'public', 'public-final-1', *declarations]).returncode)
