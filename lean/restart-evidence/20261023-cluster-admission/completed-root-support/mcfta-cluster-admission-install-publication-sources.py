exec(compile(open('/tmp/mcfta-cluster-admission-root-common.py').read(), '/tmp/mcfta-cluster-admission-root-common.py', 'exec'))
import shutil
owner = Path('/tmp/mcfta-cluster-admission-publication-preparation')
review = Path('/tmp/mcfta-cluster-admission-publication-source-audit')
checked_package(owner, '6cf388f719fbf87db4480968931e2223917744064b400537ce4797a2886eda17', '657e5beb3b74abefadc241994ce8dd4c1af1abb0a8580fb2389b0a9087a6f48a')
checked_package(review, '70295c19ded4153ecd912dbf3240b486e579245702e81bf12de2c96711921d56', '88e5147f25c0f54bdfbee932e3f6a1a7c9538f99b8a60946fbf77eafe88b1112')
assert load(review / 'review.json')['status'] == 'CLEAR'
archive(owner, 'publication-preparation')
archive(review, 'publication-source-audit')
for name, digest in [('proof-commit.py', '729843f89b8e4c68f0c5476ac1bee16405e021279c5b1e11efd426676813111b'), ('final-publication.py', 'b4fa4c716e6b04e0e74211ce72b10c21e73a3564a1cd7c1cea5045cb34b60863')]:
    assert not (HERE / name).exists() and sha(owner / name) == digest
    shutil.copy2(owner / name, HERE / name)
save('root-publication-source-review.json', {
    'status': 'ACCEPTED_REVIEWED_SOURCE_INSTALLED_WITH_SEPARATE_ACTIVATION_GATES',
    'root_whole_selected_lines_read': 75, 'root_whole_predecessor_lines_read': 47,
    'independent_review_sha256': sha(HERE / 'publication-source-audit/review.json'),
    'proof_committer_sha256': sha(HERE / 'proof-commit.py'),
    'local_publisher_sha256': sha(HERE / 'final-publication.py'),
    'proof_commit_requires_both_standalone_modes_and_exact_four_file_scope': True,
    'publisher_requires_final_publication_gate_and_seal': True,
    'publication_scope': 'LOCAL_ONLY', 'network_commands_in_programs': 0,
    'root_push_authorization': 'Standing explicit user authorization to push formalize.',
    'no_execution_result_claimed': True,
})
print('PASS: reviewed proof committer and local publisher installed; actual execution gates remain')
