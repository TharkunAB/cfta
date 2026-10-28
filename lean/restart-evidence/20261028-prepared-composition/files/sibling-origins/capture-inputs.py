from pathlib import Path
import hashlib,json
root=Path('/home/tritlo/Code/mcfta');out=Path('/tmp/mcfta-prepared-composition-20261028/sibling-origins')
def sha(b):return hashlib.sha256(b).hexdigest()
specs=[
('CONTEXT.md',[(1,180)],'Domain terminology through the recorded glossary cut; uncut remainder unreviewed.'),
('lean/MicroCFTA/SourcePruningEnumerationPreparedFiniteSiblingCoverage.lean',[(1,168),(169,322),(323,475)],'WHOLE original indexed coverage declaration and proof reviewed; actual prefix, Caller/full Memos and earlier-stop shape.'),
('lean/MicroCFTA/SourcePruningEnumerationPreparedFiniteSiblingResources.lean',[(35,145)],'Complete original resource declaration plus actual head and suffix resource admissions. Other proof portions unreviewed.'),
('lean/MicroCFTA/SourcePruningEnumerationPreparedFiniteHeadOrigins.lean',[(1,155)],'Complete origin-aware head declaration and actual finite_complete discharge/old resource call. Remaining older proof is an unreviewed current dependency.'),
('lean/MicroCFTA/SourcePruningEnumerationPreparedFiniteSiblingCertificates.lean',[(1,131)],'WHOLE indexed receipt/output/stopped certificates and actual Post-prepend proofs.'),
('lean/MicroCFTA/SourcePruningEnumerationNativeLanguage.lean',[(75,106)],'Exact original-cache satisfies_keeps language transport; uncut module body unreviewed.'),
('lean/MicroCFTA/SourcePruningEnumerationContinuationInvocation.lean',[(1,99)],'WHOLE actual complete-prefix-to-invocation proof with original occurrence and stopping branches.'),
('lean/MicroCFTA/SourcePruningEnumerationPreparedFiniteResources.lean',[(1,79)],'WHOLE genuine finite-depth induction and original resource corollary, no completion assumption.'),
('lean/MicroCFTA/SourcePruningEnumerationOrigins.lean',[(1,76)],'Actual term-path and assignment-origin definitions, old-prefix transport; remaining foundation unreviewed in this task.')]
records=[]
for rel,spans,scope in specs:
 p=root/rel;b=p.read_bytes();lines=b.splitlines(keepends=True);d=out/'sources'/p.name;d.write_bytes(b);cuts=[]
 for a,z in spans:
  z=min(z,len(lines)); cb=b''.join(lines[a-1:z]);c=out/'cuts'/f'{p.stem}-L{a}-L{z}{p.suffix}';c.write_bytes(cb)
  cuts.append({'path':str(c.relative_to(out)),'bytes':len(cb),'sha256':sha(cb),'first_line':a,'last_line':z})
 records.append({'source':str(p),'whole':{'path':str(d.relative_to(out)),'bytes':len(b),'sha256':sha(b)},'cuts':cuts,'scope':scope})
(out/'source-index.json').write_text(json.dumps({'sources':records},indent=2)+'\n')
old=(root/'lean/MicroCFTA/SourcePruningEnumerationPreparedFiniteSiblingCoverage.lean').read_text();new=(out/'drafts/v1/SourcePruningEnumerationPreparedFiniteSiblingOrigins.lean').read_text()
def beforeobserver(s):
 start=s.index('theorem alternatives_finite_complete_resources_');end=s.index('      ∀ extra,\n        let work :=',start)
 return s[start:end]
original=beforeobserver(old);recovered=beforeobserver(new).replace('theorem alternatives_finite_complete_resources_origins','theorem alternatives_finite_complete_resources_accepting',1)
assert original==recovered
for name,b in [('complete-admission-resource-prefix-original.lean',original.encode()),('complete-admission-resource-prefix-recovered.lean',recovered.encode())]:
 (out/'cuts'/name).write_bytes(b)
# Compare directly with the entire original finite resource declaration.
resource=(root/'lean/MicroCFTA/SourcePruningEnumerationPreparedFiniteSiblingResources.lean').read_text();rs=resource.index('theorem alternatives_finite_complete_resources\n');re=resource.index(' := by',rs);rd=resource[rs:re]
completeBinder='    (recursive : SourcePruningEnumerationPreparedRecursive.Complete (bits := bits) holeKey fits admits graph templates\n      checkEmpty edgesOf stop order formulas solver recursiveFuel)\n'
assert completeBinder in rd
recovered_resource=recovered.replace('theorem alternatives_finite_complete_resources_accepting','theorem alternatives_finite_complete_resources',1)
assert recovered_resource.endswith(' ∧\n');recovered_resource=recovered_resource[:-3]
assert recovered_resource==rd.replace(completeBinder,'',1)
(out/'cuts/complete-original-resource-declaration.lean').write_text(rd)
(out/'cuts/resource-declaration-with-completion-discharged.lean').write_text(recovered_resource)
comparison={'scope':'Literal entire original coverage admission and ENTIRE resource-result prefix, including theorem name before the universal semantic observer; original semantic observer is intentionally replaced, not claimed literally retained','original_coverage_prefix_bytes':len(original.encode()),'original_coverage_prefix_sha256':sha(original.encode()),'coverage_resource_prefix_identical':True,'entire_old_resource_declaration_bytes':len(rd.encode()),'entire_old_resource_declaration_sha256':sha(rd.encode()),'same_resource_declaration_after_discharging_only_Complete':True,'removed_binder':completeBinder,'complete_discharge':'No public recursive premise. The actual head_finite_complete_resources_origins derives PreparedRecursive.finite_complete internally once per head and then calls its genuine resource producer. The sibling proof consumes that head theorem directly.'}
(out/'old-contract-comparison-v1.json').write_text(json.dumps(comparison,indent=2)+'\n')
print(json.dumps(comparison,indent=2))
