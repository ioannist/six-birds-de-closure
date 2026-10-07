def original_audit_types(types):
 prefix='SbtCosmo.Derivation.GroundOriginalAuditNonidentifiability.'
 required_parts={
  'offsets_injective':['Function.Injective','GroundOriginalOffsets.offsets'],
  'finite_readout_eq_verdict':['Fin 18','finiteReadout i =','GroundOriginalOffsetSixty.verdict i'],
  'actual_passing_split_pair':['GroundOriginalOffsetSixty.Tests 0','GroundOriginalOffsetSixty.Tests 3','finiteReadout 0 =','finiteReadout 3','offsets 0 ≠','offsets 3'],
  'finite_admitted_offset_count':['Finset.image','finiteReadout i = true','card = 15'],
  'no_finite_readout_decoder':['¬∃ decode','∀ (i : Fin 18)','decode (','finiteReadout i','offsets i'],
  'all_original_has_limit':['Fin 18','HasLimit i'],
  'limit_readout_true':['Fin 18','limitReadout i = true'],
  'infinite_admitted_offset_count':['Finset.image','limitReadout i = true','card = 18'],
  'no_limit_readout_decoder':['¬∃ decode','∀ (i : Fin 18)','decode (','limitReadout i','offsets i']}
 for short,parts in required_parts.items():
  parser.require_parts(re.sub(r'\s+',' ',types[prefix+short]),*parts)

def candidate():
 parent_plan,parent_files,parent_names,parent_full=_parent_candidate()
 assert all(sha(CANDIDATE/p)==h for p,h in load(CANDIDATE/'file-manifest.json').items())
 plan=load(CANDIDATE/'installation-plan.json')
 assert (plan['native_modules'],plan['native_fresh_declarations'],plan['prospective_default_declarations'])==(1772,20798,32574)
 assert plan['parent_header_candidate_plan_sha256']==sha(PARENT/'installation-plan.json')
 assert sha(CANDIDATE/'proposed_registered_files.tar.gz')==plan['source_archive_sha256']
 files={}
 with tarfile.open(CANDIDATE/'proposed_registered_files.tar.gz','r|gz') as tar:
  for m,row in zip(tar,plan['targets'],strict=True):
   assert m.isfile() and m.name==row['path'] and not Path(m.name).is_absolute() and '..' not in Path(m.name).parts
   raw=tar.extractfile(m).read();assert len(raw)==row['size'] and rawsha(raw)==row['sha256']
   assert m.name not in files;files[m.name]=raw
 assert len(files)==plan['source_archive_members']==1786
 assert plan['modules'][:-1]==parent_plan['modules']
 assert plan['topological_order'][:-1]==parent_plan['topological_order']
 addon=ROOT/'results/original_audit_nonidentifiability_production_candidate_2026-10-05'
 assert all(sha(addon/p)==h for p,h in load(addon/'file-manifest.json').items())
 ep=load(addon/'production-plan.json');row=plan['modules'][-1]
 assert row['group']=='original_audit_nonidentifiability' and ep['modules']==1 and ep['declarations']==9
 assert row['module']==ep['module']=='SbtCosmo.Derivation.GroundOriginalAuditNonidentifiability'
 assert row['declared_theorems']==ep['names'] and row['source_sha256']==ep['source_sha256']==sha(row['candidate_source'])
 assert row['target']=='lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean'
 added={str(p.relative_to(addon)):p.read_bytes() for p in (addon/'lean').rglob('*.lean')}
 assert len(added)==3 and set(files)==set(parent_files)|set(added) and not set(parent_files)&set(added)
 assert all(files[p]==raw for p,raw in added.items())
 assert all(files[p]==raw for p,raw in parent_files.items() if p not in {'lean/lakefile.lean','lean/manifests/check_axioms.lean'})
 anchor=b'    `SbtCosmo.Derivation.GroundSourceNormalizationFailure]'
 assert parent_files['lean/lakefile.lean'].count(anchor)==1
 assert files['lean/lakefile.lean']==parent_files['lean/lakefile.lean'].replace(anchor,b'    `SbtCosmo.Derivation.GroundSourceNormalizationFailure,\n    `'+row['module'].encode()+b']')
 suffix=('\nimport '+row['module']+'\n\n'+''.join('#print axioms '+n+'\n' for n in ep['names'])).encode()
 assert files['lean/manifests/check_axioms.lean']==hoist(parent_files['lean/manifests/check_axioms.lean']+suffix)
 assert rawsha(files['lean/manifests/check_axioms.lean'])==plan['header_repair']['native_repaired_sha256']
 assert plan['header_repair']['parent_native_repaired_sha256']==parent_plan['header_repair']['native_repaired_sha256']
 assert plan['header_repair']['ordered_parent_native_query_prefix_preserved']==32565
 assert plan['group_counts']==dict(parent_plan['group_counts'],original_audit_nonidentifiability={'modules':1,'declarations':9})
 names=parent_names+ep['names'];full=parent_full+ep['names']
 assert len(set(names))==20798 and len(set(full))==32574
 assert parser.declarations(files[row['target']].decode())==ep['names']
 assert re.findall(r'^#print axioms (\S+)',files['lean/manifests/check_axioms.lean'].decode(),re.M)==full
 modules={r['module']:r for r in plan['modules']};position={m:i for i,m in enumerate(plan['topological_order'])}
 assert len(modules)==len(position)==1772 and set(modules)==set(position)
 for r in plan['modules']:
  for imp in parser.imports(files[r['target']].decode()):
   if imp in position:assert position[imp]<position[r['module']]
   else:assert imp in plan['external_imports']
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:axiom|constant)\s',parser.uncomment(files[row['target']].decode()),re.M)
 assert plan['original_audit_addon_plan_sha256']==sha(addon/'production-plan.json')
 return plan,files,names,full

def original_audit_proof_gate(plan):
 packet=ROOT/'results/original_audit_nonidentifiability_checked_2026-10-05'
 addon=ROOT/'results/original_audit_nonidentifiability_production_candidate_2026-10-05'
 checkpoint=ROOT/'results/original_audit_nonidentifiability_dependency_checkpoint_2026-10-05'
 for p in [packet,addon,checkpoint]:assert all(sha(p/f)==h for f,h in load(p/'file-manifest.json').items())
 d=load(packet/'checkpoint-verification.json');ep=load(addon/'production-plan.json');cp=load(checkpoint/'checkpoint-verification.json')
 rows=[r for r in plan['modules'] if r['group']=='original_audit_nonidentifiability'];assert len(rows)==1
 row=rows[0];names=row['declared_theorems']
 assert d['checked_modules']==1 and d['checked_declarations']==9 and d['standard_only']
 assert d['compile_terminal_exit_code']==d['audit_terminal_exit_code']==0
 assert d['names']==ep['names']==names
 assert row['source_sha256']==d['source_sha256']==ep['source_sha256']==sha(row['candidate_source'])
 assert ep['checked_packet_manifest_sha256']==cp['parent_packet_manifest_sha256']==plan['original_audit_checked_manifest_sha256']==sha(packet/'file-manifest.json')
 assert plan['original_audit_addon_plan_sha256']==sha(addon/'production-plan.json')
 assert plan['original_audit_dependency_manifest_sha256']==sha(checkpoint/'file-manifest.json')
 compile_terminal=load(packet/'compile-terminal.json');audit_terminal=load(packet/'audit-terminal.json')
 assert compile_terminal['terminal_exit_code']==audit_terminal['terminal_exit_code']==0
 private='/tmp/de_original_audit_nonidentifiability_v3';src=private+'/lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean';obj=private+'/GroundOriginalAuditNonidentifiability.olean'
 assert compile_terminal['command']==['lake','env','lean','-R',private+'/lean','-o',obj,src]
 assert audit_terminal['command']==['/home/ioannis/.elan/toolchains/leanprover--lean4---v4.28.0/bin/lean',private+'/Audit.lean']
 assert compile_terminal['cwd']==audit_terminal['cwd']==str(ROOT/'lean')
 assert compile_terminal['environment_overrides']=={'LEAN_NUM_THREADS':'4'}
 assert audit_terminal['environment_overrides']['LEAN_NUM_THREADS']=='4'
 assert audit_terminal['environment_overrides']['LEAN_PATH'].split(':')[0]==private+'/audit-overlay'
 assert compile_terminal['unchanged_inputs'] and compile_terminal['changed_inputs']==[]
 assert compile_terminal['source_sha256']==d['source_sha256']==sha(packet/'lean/SbtCosmo/Derivation/GroundOriginalAuditNonidentifiability.lean')
 assert compile_terminal['object_sha256']==sha(packet/'GroundOriginalAuditNonidentifiability.olean')
 assert compile_terminal['log_sha256']==sha(packet/'compile.log')
 assert compile_terminal['freeze_sha256']==sha(packet/'compile-source-freeze.json')
 assert audit_terminal['audit_source_sha256']==sha(packet/'Audit.lean') and audit_terminal['log_sha256']==d['audit_log_sha256']==cp['parent_audit_log_sha256']==sha(packet/'audit.log')
 assert audit_terminal['freeze_sha256']==sha(packet/'audit-source-object-freeze.json')
 query='import '+row['module']+'\nset_option warningAsError true\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names)
 assert (packet/'Audit.lean').read_text()==query
 for log in [packet/'compile.log',packet/'audit.log']:assert not re.search(r'error:|warning:',log.read_text())
 parser.axiom_entries((packet/'audit.log').read_text(),names)
 original_audit_types(parser.statement_entries((packet/'audit.log').read_text(),names))
 am=load(checkpoint/'archive-manifest.json');archive=checkpoint/'checked_sources_objects_receipts.tar.gz'
 assert sha(archive)==am['archive_sha256']
 archived={}
 with tarfile.open(archive,'r|gz') as tar:
  for m,e in zip(tar,am['entries'],strict=True):
   assert m.isfile() and m.name==e['name'] and m.size==e['size']
   assert not Path(m.name).is_absolute() and '..' not in Path(m.name).parts
   h=hashlib.sha256()
   with tar.extractfile(m) as stream:
    for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
   assert h.hexdigest()==e['sha256'];assert m.name not in archived;archived[m.name]=e['sha256']
 assert len(archived)==cp['archive_members_verified']==2674 and cp['checked_declarations']==9 and cp['standard_only']
 for p,h in load(packet/'file-manifest.json').items():assert archived['checked_packet/'+p]==h
 assert archived['checked_packet/file-manifest.json']==sha(packet/'file-manifest.json')
 cf=load(packet/'compile-source-freeze.json');af=load(packet/'audit-source-object-freeze.json')
 assert len(cf)==2658 and len(af)==cp['bound_inputs']==d['bound_inputs']==2660
 assert all(af[p]==h for p,h in cf.items())
 for name,h in af.items():
  p=Path(name)
  if p.is_relative_to(ROOT):arc='repo/'+str(p.relative_to(ROOT))
  else:
   assert p.is_relative_to(Path(private));arc='private/'+str(p.relative_to(private))
  assert archived[arc]==h
  # Historical objects are explicitly preserved in the checked archive.
  # Current source equations and pinned configuration must still agree.
  if p.is_relative_to(ROOT) and '/.lake/build/' not in str(p) and p!=ROOT/'lean/lakefile.lean':assert sha(p)==h
 historical_lake=af[str(ROOT/'lean/lakefile.lean')]
 assert cp['preserved_lakefile_sha256']==historical_lake
 installed_lake=next(r['sha256'] for r in plan['targets'] if r['path']=='lean/lakefile.lean')
 assert sha(ROOT/'lean/lakefile.lean') in {historical_lake,installed_lake}
 assert d['project_dependency_modules']==cp['project_dependency_modules']==1327
 return dict(declarations=9,standard_only=True,archived_members=2674,historical_inputs=2660,actual_registered_execution=False)
