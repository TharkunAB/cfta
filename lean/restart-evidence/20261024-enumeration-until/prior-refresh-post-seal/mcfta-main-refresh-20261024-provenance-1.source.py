import json
from pathlib import Path

here = Path('/home/tritlo/Code/mcfta/lean/restart-evidence/20261024-main-refresh')
path = here / 'provenance-clarification.json'
assert not path.exists() and not (here / 'SHA256SUMS').exists()
path.write_text(json.dumps({
    'status': 'ADDITIVE_AUTHORSHIP_CLARIFICATION',
    'previous_reports_unchanged': True,
    'merge_negative_depth_repair_typing_probe_and_documents': 'Root',
    'core_integration_probe': 'Guard',
    'original_LPO_regressions': 'Arity',
    'temporary_strict_warning_adaptations_and_native_execution': 'Root',
    'final_document_and_repair_reviewer': 'Required',
    'clarification': 'The final review uses Root as shorthand for probe ownership. The original core and LPO probe authors are listed here. Required authored none of these probes. Review independence remains valid.'
}, indent=2) + '\n')
print('PASS: additive probe authorship clarification retained before the seal.')
