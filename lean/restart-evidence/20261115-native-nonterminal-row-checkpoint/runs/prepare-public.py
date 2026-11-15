from pathlib import Path
import hashlib
import json

root = Path('/home/tritlo/Code/mcfta')
work = Path(__file__).parent
runtime = root / 'lean/restart-evidence/20261115-native-nonterminal-row-publication'
runtime.mkdir()
promotion = json.loads((work / 'promotion.json').read_text())
exports = json.loads((work / 'visibility-exports.json').read_text())
modified = json.loads((work / 'modified-public.json').read_text())
assert len(promotion) >= 3
references = ['MicroCFTA.' + item['module'] + '.' + name
              for item in promotion for name in item['public_statements']]
for item in exports:
    references += ['MicroCFTA.' + Path(item['path']).stem + '.' + name for name in item['exports']]
modules = [item['module'] for item in promotion]
strict_modules = modules + [Path(item['path']).stem for item in exports] + [item['module'] for item in modified]
probereferences = references + ['MicroCFTA.'+item['module']+'.'+name for item in modified for name in item['public_statements']]
for item in promotion:
    raw = root / item['raw']
    public = root / 'lean/MicroCFTA' / (item['module'] + '.lean')
    assert raw.read_bytes() == public.read_bytes()
audit_path = root / 'lean/MicroCFTA/Audit.lean'
audit = audit_path.read_text()
lines = audit.splitlines(keepends=True)
last = max(index for index, line in enumerate(lines) if line.startswith('import '))
imports = ['import MicroCFTA.' + name + '\n' for name in modules
           if 'import MicroCFTA.' + name + '\n' not in lines]
lines[last + 1:last + 1] = imports
audit = ''.join(lines)
for reference in references:
    assert '#print axioms ' + reference + '\n' not in audit
    audit += '#check @' + reference + '\n#print axioms ' + reference + '\n'
audit_path.write_text(audit)
expected = 319 + len(references)
probe = ''.join('import MicroCFTA.' + name + '\n' for name in strict_modules)
probe += '\n' + ''.join('#check @' + ref + '\n#print axioms ' + ref + '\n' for ref in probereferences)
probe += '\n' + (work/'EndpointWarmProbes.lean.txt').read_text()
(runtime / 'IndependentProbes.lean').write_text(probe)
strict = '''from pathlib import Path
import hashlib,json,subprocess
root=Path('/home/tritlo/Code/mcfta')
pins=json.loads((Path(__file__).parent/'source-pins.json').read_text())
def verify():
    for path,digest in pins.items():
        assert hashlib.sha256((root/path).read_bytes()).hexdigest()==digest,path
'''
strict += 'for name in ' + repr(strict_modules) + ':\n'
strict += '''    verify()
    subprocess.run(['lake','env','lean','-j1','-DwarningAsError=true','MicroCFTA/'+name+'.lean'],cwd=root/'lean',check=True)
    verify()
'''
(runtime / 'strict-modules.py').write_text(strict)
template = (root / 'lean/restart-evidence/20261115-open-replay-and-same-trace-publication/check.py').read_text()
driver = template[:template.index('commands=')]
commands = [('public-build','exec lake build',0),
            ('strict-changed-modules','exec python3 '+str(runtime/'strict-modules.py'),0),
            ('independent-imports','exec lake env lean -j1 -DwarningAsError=true '+str(runtime/'IndependentProbes.lean'),len(probereferences)),
            ('audit-build','exec lake build MicroCFTA.Audit',0),
            ('audit-strict','exec lake env lean -j1 -DwarningAsError=true MicroCFTA/Audit.lean',expected)]
driver += 'commands = ' + repr(commands) + '\nfor name,command,count in commands:\n    run(name,command,count)\n'
driver += '''match=re.search(r'Checked axiom dependencies of (\\d+) MicroCFTA theorems\\.',(runtime/'audit-strict.txt').read_text())
assert match
'''
driver += 'assert checks[-1]["total_axiom_reports"] == ' + str(expected) + '\n'
report = {'actual_prefix_remaining_inputs_proved':True,
          'actual_all_source_body_returned_preservation_proved':True,
          'actual_closed_self_raw_body_result_proved':True,
          'actual_mismatch_raw_body_result_and_endpoint_proved':True,
          'global_self_mismatch_query_laws_proved':True,
          'global_self_mismatch_actual_initialization_proved':True,
          'global_literal_pure_query_history_proved':True,
          'source_terminal_cutoffs_from_pure_history_proved':True,
          'actual_source_operation_prefix_proved':True,
          'source_scoped_query_induction_proved':True,
          'global_matching_top_row_history_proved':True,
          'source_diagonal_row_prescribed_inputs_proved':True,
          'source_diagonal_initialized_row_readback_proved':True,
          'source_qualified_full_C_M_history_proved':False,
          'nonterminal_auxiliary_replay_proved':False,
          'raw_mu_cutoff_replay_proved':True,
          'source_body_first_actual_mu_cutoff_proved':True,
          'global_nonterminal_mu_cutoff_history_proved':True,
          'source_initialized_mu_cutoff_composition_proved':True,
          'raw_reference_replay_proved':True,
          'source_body_first_reference_read_proved':True,
          'global_body_first_reference_cutoff_history_proved':True,
          'source_initialized_reference_cutoff_composition_proved':True,
          'global_nonterminal_matching_top_row_history_proved':True,
          'source_body_first_nonterminal_row_inputs_proved':True,
          'source_diagonal_first_actual_body_reference_read_proved':True,
          'source_initialized_nonterminal_row_composition_proved':True,
          'raw_right_mu_unused_predicate_replay_proved':True,
          'source_diagonal_same_key_row_inputs_proved':True,
          'all_actual_producer_families_proved':False,
          'whole_native_history_returned_footprint_proved':False,
          'whole_source_task_induction_proved':False,
          'all_same_branch_removed_history_extracted':False,
          'whole_output_satisfies_proved':False,
          'joint_finite_completion_proved':False,
          'compiled_haskell_correspondence_proved':False,'haskell_changed':False}
driver += 'report = ' + repr(report) + '\n'
driver += 'report.update({"individual_reports":'+str(expected)+',"source_pins_unchanged":True,"at":datetime.datetime.now().astimezone().isoformat(),"limits":limits,"checks":checks,"audited_theorems":int(match.group(1))})\n'
driver += '(runtime/"checked.json").write_text(json.dumps(report,indent=2)+"\\n")\nprint(json.dumps(report),flush=True)\n'
(runtime / 'check.py').write_text(driver)
sources = sorted((root / 'lean/MicroCFTA').glob('*.lean'))
pins = sources + [root / name for name in ['shell.nix','lean/lean-toolchain','lean/lakefile.toml','lean/lake-manifest.json']]
pins += [runtime / name for name in ['IndependentProbes.lean','strict-modules.py','check.py']]
pins.append(Path(__file__))
pins += [root / item['raw'] for item in promotion + modified]
pins += [work/name for name in ['EndpointWarmProbes.lean.txt','promotion.json','modified-public.json']]
(runtime / 'source-pins.json').write_text(json.dumps({str(path.relative_to(root)):hashlib.sha256(path.read_bytes()).hexdigest()
                                                   for path in pins},indent=2)+'\n')
surface = {'modules':modules,'new_statements':len(references)-sum(len(item['exports']) for item in exports),
           'visibility_exports':sum(len(item['exports']) for item in exports),'probe_references':probereferences,
           'modified_existing_modules':[item['module'] for item in modified], 'source_nonterminal_row_integration_probes':1,
           'sources':len(sources),'direct_audit_imports':sum(line.startswith('import ') for line in audit.splitlines()),
           'expected_explicit_reports':expected,'public_run':str(runtime)}
(work / 'public-surface.json').write_text(json.dumps(surface,indent=2)+'\n')
print(json.dumps(surface))
