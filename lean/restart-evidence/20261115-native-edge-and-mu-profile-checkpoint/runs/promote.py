from pathlib import Path
import hashlib
import json
import shutil

work = Path(__file__).parent
base = Path('lean/restart-evidence')
specs = [
    ('20261115-current-same-prefix-edge-child-result-draft',
     'SourceCurrentAllocatedNativeSamePrefixEdgeChildResult',
     '17008f09917e2c8503806b9d6e458d1656efeeae8720cc27bb003cd13bd24664',
     ['edge_child_law_at_node_finish'], '20261115-native-checked-edge-profile-empty-atoms-check', None),
    ('20261115-general-checked-edge-body-empty-atoms-repair',
     'SourceCurrentAllocatedNativeCheckedEdgeBodyProfile',
     '9f08518407af9e39923e7bd258d298688be713106201a151f3259e212bcee1bc',
     ['edge_body_children_profile_of_fuel_induction'], '20261115-native-checked-edge-profile-empty-atoms-check',
     '20261115-general-checked-edge-body-profile-draft'),
    ('20261115-current-closed-universe-mu-profile-local-fold-repair',
     'SourceCurrentAllocatedNativeClosedUniverseMuProfile',
     '2e46fa6cd3be882299e3f6e53d498eba8821bda2bd71e3841315036cafa214e2',
     ['closed_universe_mu_profile_trace_result'], '20261115-native-closed-mu-profile-local-fold-check',
     '20261115-current-closed-universe-mu-profile-draft'),
    ('20261115-current-node-query-dispatch-origin-draft',
     'SourceCurrentAllocatedNativeNodeQueryDispatchOrigin',
     '649779a1ee8db9f062e46c50d504cd32ba0f53a7f6ad97c165a7ff7ddaad99ad',
     ['actual_node_query_dispatch_from_initial_query_finish'], '20261115-native-query-dispatch-and-ordered-entry-check', None),
    ('20261115-current-ordered-original-entry-empty-key-fold-repair',
     'SourceCurrentNativeOrderedOriginalEntry',
     'f880da50c7eac28f14907a01f9705120ef6f68d2e3e626d36419644cb4551863',
     ['ordered_original_entry_common_operands'], '20261115-native-query-dispatch-and-ordered-entry-check',
     '20261115-current-ordered-original-entry-receipt-draft'),
]


def declaration(text: str, name: str) -> str:
    start = text.index('theorem ' + name + '\n')
    return text[start:text.index(' := by', start)]


promotion = []
for folder, module, digest, statements, checked_run, original_folder in specs:
    raw = base / folder / (module + '.lean')
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    checked = json.loads((base / checked_run / 'checked.json').read_text())
    assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in checked['checks'])
    if original_folder:
        original = base / original_folder / raw.name
        for name in statements:
            assert declaration(raw.read_text(), name) == declaration(original.read_text(), name)
    public = Path('lean/MicroCFTA') / raw.name
    assert not public.exists()
    shutil.copyfile(raw, public)
    promotion.append({'module': module, 'raw': str(raw), 'sha256': digest, 'public_statements': statements})
(work / 'promotion.json').write_text(json.dumps(promotion, indent=2) + '\n')
print(json.dumps({'modules': len(promotion), 'statements': 5, 'original_public_headers_unchanged': True}))
