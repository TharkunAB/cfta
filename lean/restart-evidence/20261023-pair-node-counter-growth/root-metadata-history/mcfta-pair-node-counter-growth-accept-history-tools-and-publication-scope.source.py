exec(compile(open('/tmp/mcfta-pair-node-counter-growth-root-common.py').read(), '/tmp/mcfta-pair-node-counter-growth-root-common.py', 'exec'))
import ast

collector = Path('/tmp/mcfta-pair-node-counter-growth-source-history-preparation')
collector_peer = Path('/tmp/mcfta-pair-node-counter-growth-source-history-tool-audit')
publication = Path('/tmp/mcfta-pair-node-counter-growth-publication-scope-plan')
publication_peer = Path('/tmp/mcfta-pair-node-counter-growth-publication-scope-review')
checked_package(collector,'1c0d482a3dfe53516c046dfcd3cf0d2fc2e81f5d7101cbe6b6ba87a898a54f78','626b47bddc7df1fb9fe7b397d3e3152958ff8e2b2f3b7a67f280743893b12ab9')
checked_package(collector_peer,'a40d90761b6f9e5bde43b223750383323c7ff0161a9bbc7b1e5f8bd690bdb077','184453fe3566c050c04f029b6157cde0d61c4a21a0283719dc0ada5ff452900f')
checked_package(publication,'e088c026c59d984e3a9401ba71011b6073e9907c180097a0c6d7948794f487ec','7d77bf7b401e4d4504e4a5748b4e618cb7e8e8589c798f7eea69740e2e033748')
checked_package(publication_peer,'10e7ec6394f224f1336ca4df5e379d7e5405e4d0b38d2e547f4f25a70fc8db04','8f38c0e1e01a52d1d7e0070319cdb218cd41d473cf1d4375b7db8e1277a5fd6d')
assert sha(collector_peer / 'review.json') == '48e9e7cc3fc91d2ba95d3de4f1175018a8b08fdf64c107fc2ad1cc2d12a91b80'
assert sha(publication_peer / 'review.json') == 'e905de55308e100a7e614dba1a3df24b94e10d5494ed8b17f9b463a7534a6d19'
assert load(collector_peer / 'review.json')['status'] == load(publication_peer / 'review.json')['status'] == 'CLEAR'
code = collector / 'selected/source-history.py'
assert len(code.read_bytes().splitlines()) == 78 and sha(code) == '4bd2e8f38bb3b49dc3ad5d663e3f03a7a95135469255a54b89f40364da58a3a9'
assert sum(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(code.read_text()))) == 14
assert (collector / 'selected/root-common.py').read_bytes() == (HERE / 'root-common.py').read_bytes() == Path('/tmp/mcfta-pair-node-counter-growth-root-common.py').read_bytes()
assert not (HERE / 'source-history.py').exists() and not (HERE / 'root-metadata-history').exists()
assert load(HERE / 'root-source-history-scope-gate.json')['selected_authoring_authorized']
archive(collector,'source-history-preparation')
archive(collector_peer,'source-history-tool-audit')
archive(publication,'publication-scope-plan')
archive(publication_peer,'publication-scope-audit')
(HERE / 'source-history.py').write_bytes(code.read_bytes())
save('root-source-history-tool-gate.json',dict(status='ACCEPTED_COMPLETE_HISTORY_COLLECTOR_FOR_EXECUTION',
    module=NAME,collector_sha256=sha(HERE / 'source-history.py'),root_complete_selected_basis_78_and_common_46_lines_read=True,
    root_whole_forward_changes_and_14_guards_read=True,selected_hard_stop=90,
    all_generic_guards_retained=True,complete_inventory_and_counts_dynamic=True,
    independent_review_sha256=sha(collector_peer / 'review.json'),execution_authorized=True))
save('root-publication-scope-gate.json',dict(status='ACCEPTED_SOURCE_ONLY_THREE_LOCAL_PUBLICATION_TOOL_SCOPE',
    module=NAME,root_complete_26_line_plan_101_basis_lines_and_44_guards_read=True,
    source_target=101,source_hard_stop=110,all_generic_guards_retained=True,
    public_definitions=1,public_theorems=2,document_writer_separate=True,
    runtime_actual_proof_SHA_only=True,actual_metric_binding_required=True,
    both_saved_modes_before_proof_commit_and_documents=True,network_in_selected_tools=False,
    independent_review_sha256=sha(publication_peer / 'review.json'),
    selected_authoring_authorized=True,selected_activation_authorized=False))
print('Activated the reviewed history collector and accepted the separate local publication source scope.')
