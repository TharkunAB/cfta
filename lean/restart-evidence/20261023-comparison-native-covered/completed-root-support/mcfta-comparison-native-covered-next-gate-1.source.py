import runpy
globals().update(runpy.run_path('/tmp/mcfta-comparison-native-covered-root-common.py'))
owner = Path('/tmp/mcfta-comparison-native-covered-generated-root-inventory')
review = Path('/tmp/mcfta-comparison-native-covered-next-inventory-audit')
checked_package(owner, 'bf8232a86cbfa82d51ea7e97472b5fbf70e78b30b480d681634997a6003b332d', 'e0acca95ee6bfde5b6c566e14ccef7b5aaebcb554490b40e3dfcc980219b341a')
checked_package(review, '58f2fa255b29419343f377fce19fcf6582504072a562bfef59e407fd06df913a', '3d6eb2e2752cd40482f0767cf46b6668df864b0d2f90b38ba2e0a9051c446b94')
assert load(review / 'review.json')['status'] == 'CLEAR'
index = load(owner / 'source-index.json')
cuts = lines = 0
for item in index['sources']:
    source = Path(item['source'])
    assert sha(source) == item['sha256'] and source.stat().st_size == item['bytes']
    raw = source.read_bytes().splitlines(keepends=True)
    assert len(raw) == item['lines']
    for cut in item['cuts']:
        path = owner / cut['path']
        assert path.read_bytes() == b''.join(raw[cut['start'] - 1:cut['end']])
        assert sha(path) == cut['sha256'] and path.stat().st_size == cut['bytes']
        cuts += 1
        lines += len(path.read_bytes().splitlines())
assert len(index['sources']) == 19 and cuts == 35 and lines == 606
archive(owner, 'next-inventory')
archive(review, 'next-inventory-audit')
save('root-next-inventory-review.json', dict(status='ROOT_ACCEPTED_SOURCE_ONLY',
    root_all_cuts_and_assessment_read=True, cuts=cuts, lines=lines, live_source_identities=19,
    independent_review_sha256=sha(review / 'review.json'),
    existing_inventory_model_transport_acknowledged=True,
    same_cluster_group_rebuild_invariants_missing=True, new_source_resources_separate=True,
    future_header_body_capacity_or_compiler_authorized=False, whole_goal_complete=False))
(HERE / 'NEXT-TARGET.md').write_text('''# Next proof target

H28 passes strict, public readback and the aggregate Audit on one unchanged source.
It preserves native Covered through the same original-row comparison result.
The whole goal remains ACTIVE. H6 constructed_node_calls remains strongest combined.

The next substantive obligation is native Covered and captured canonical pair admission
through the actual H20 cluster induction, then the exact H22 group chain and H23 rebuild.
Use one H28 comparison witness and H25 completed_admitted on that same done equation.
Carry both invariants through all branches and actual intermediate states.
Do not choose another comparison to certify a previously selected chain.

Existing public APIs already derive generated-root Original/admission, concrete inventory
Agreement with exact old ranks, native Contextual/Covered rebase and pair Stable rebase.
They need the actual returned invariants. Generic model parameters are not automatically
the concrete Inventory.inputs. Retain that correlation explicitly.

New-source Room, domain-history inventory reindexing and the next fixed-width reserve
remain separate obligations. Source growth does not derive stronger Room.
DirectEdgeWordRanges already applies once the exact new scope/readiness/Room are proved.
Do not reset caches, widen the width or assume future capacity.

Read next-inventory/assessment.md, resource-boundary.md and the independently reviewed cuts.
This inventory authorizes no future header, body or capacity claim.
No Haskell repair was added. FINDINGS retains the external repair index first.
''')
print(json.dumps(dict(status='PASS', sources=19, cuts=35, lines=606)))
