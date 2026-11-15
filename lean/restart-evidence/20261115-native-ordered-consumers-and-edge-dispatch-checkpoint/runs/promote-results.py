from pathlib import Path
import hashlib
import json
import shutil

work = Path(__file__).parent
base = Path('lean/restart-evidence')
checked = json.loads((base / '20261115-native-ordered-results-edge-dispatch-and-cm-support-check/checked.json').read_text())
assert all(item['exit'] == 0 and not item['nonstandard_axioms'] for item in checked['checks'])
specs = [
    ('20261115-current-ordered-mixed-reference-node-profile-draft',
     'SourceCurrentAllocatedNativeOrderedMixedReferenceNodeProfile',
     'a9aa811dbc329c92c198ffd804ddb9613cc9f20687169c948bf0a7fc84387d97',
     ['current_stored_universe_reference_node_profile_of_fuel_induction_ordered_entry'], False),
    ('20261115-original-m-native-union-profile-draft',
     'SourceCurrentAllocatedNativeMixedUnionProfile',
     '490248c2036d3155268f980a40c4619e6f64788e98f06856d01e7959648b147e',
     ['current_stored_universe_mixed_union_body_profile_of_fuel_induction'], False),
    ('20261115-current-edge-query-dispatch-origin-draft',
     'SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin',
     '50b5d96c40df1d92d0ad714926a388fc3b44c75d4726fe6c0dfa8f00c0fb87be',
     ['actual_edge_query_dispatch_from_initial_query_finish'], False),
    ('20261115-current-general-cm-history-support-proof-repair',
     'SourceCurrentAllocatedNativeGeneralCMHistoryDefinitions',
     '30015e38fd7c9863f46ea384926997b48a956704d91984cf5e029386448dcf80',
     ['AuthenticEntry', 'MixedQualified', 'NodeResult', 'EdgeResult'], True),
]
promotion = json.loads((work / 'promotion.json').read_text())
for folder, module, digest, statements, definitions_only in specs:
    raw = base / folder / (module + '.lean')
    assert hashlib.sha256(raw.read_bytes()).hexdigest() == digest
    public = Path('lean/MicroCFTA') / raw.name
    assert not public.exists()
    shutil.copyfile(raw, public)
    item = {'module': module, 'raw': str(raw), 'sha256': digest, 'public_statements': statements}
    if definitions_only:
        item.update({'namespace': 'SourceCurrentAllocatedNativeGeneralCMHistory',
                     'definitions_only': True, 'general_C_M_theorem_proved': False,
                     'private_support_standard_probes': 7})
    promotion.append(item)
(work / 'promotion.json').write_text(json.dumps(promotion, indent=2) + '\n')
print(json.dumps({'new_modules': 6, 'new_theorems': 5, 'explicit_predicate_definitions': 4,
                  'full_native_C_M_history_proved': False}))
