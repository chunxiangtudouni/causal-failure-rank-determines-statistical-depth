"""Read-only S7 readiness check. Exit0=ready for Root's final decision,
exit2=structurally valid but incomplete, exit1=stale/broken bindings.
This script never edits source, ledger, receipt, matrix or any report.
"""
import argparse,hashlib,json,re,subprocess,sys
from pathlib import Path

ap=argparse.ArgumentParser();ap.add_argument('--matrix',default='.lake/workpads/PStar_S7_GLOBAL_MATRIX_001.json');ap.add_argument('--census',default='.lake/workpads/PStar_S7_GLOBAL_CENSUS_001.json');ap.add_argument('--receipt',default='.lake/workpads/PStar_S7_GLOBAL_ACCEPTED_RECEIPT_010.json');ap.add_argument('--manifest',default='.lake/workpads/PStar_S7_GLOBAL_MANIFEST_001.json');args=ap.parse_args()
b=Path.cwd();p=b.parent/'compatibility_structure_research/submission_2026-10-27';errors=[];incomplete=[]
def digest(q):return hashlib.sha256(Path(q).read_bytes()).hexdigest()
def load(q):return json.loads(Path(q).read_text(encoding='utf-8-sig'))
def check(ok,msg):
 if not ok:errors.append(msg)
def match(path,expected,label):
 q=Path(path);q=q if q.is_absolute() else b/q
 if not q.exists():errors.append('MISSING '+label+': '+str(path));return False
 good=digest(q)==expected
 if not good:errors.append('SHA_MISMATCH '+label+': '+str(path))
 return good
matrix=load(b/args.matrix);census=load(b/args.census);receipt=load(b/args.receipt)
manifest_path=b/args.manifest
if manifest_path.exists():
 manifest=load(manifest_path)
 for record in manifest['package']:match(record['path'],record['sha256'],'frozen global package')
 selected={(b/args.matrix).resolve(),(b/args.census).resolve(),(b/matrix['immutable_open_target_spec_snapshot']).resolve()}
 packaged={(b/record['path']).resolve() for record in manifest['package']}
 check(selected<=packaged,'selected matrix/census/original-spec snapshot must themselves be explicitly bound by selected manifest')
else:errors.append('MISSING global frozen manifest; package must be explicitly frozen')
check(digest(b/args.receipt)==matrix['accepted_receipt']['sha256'],'selected whole receipt must be exactly the epoch explicitly bound by this matrix')
for record in matrix['sector_reports']:match(record['path'],record['sha256'],'sector review')
for record in matrix['A17_final_handoff']['files']:match(record['path'],record['sha256'],'A17 final handoff')
check(matrix['A17_final_handoff']['state'].startswith('RECEIVED_AND_READ'),'A17 final handoff pending/unaccepted by scope matrix')
check(len(matrix['A17_final_handoff'].get('exact_existing_A_IDs',[]))==44,'A-sector existing sub-ID census must be exact44, excluding A19')

baseline=load(p/'checks/lean-baseline.json');source_records=census['source_inputs'];check(len(source_records)==16,'frozen source input count differs from16')
canonical=''.join(name+' '+baseline['source_hashes'][name]+'\n' for name in sorted(baseline['source_hashes']))
check(hashlib.sha256(canonical.encode()).hexdigest()==matrix['source_baseline']['source_manifest_sha256'],'canonical source manifest authority mismatch')
check(baseline['source_manifest_sha256']==census['frozen_source_manifest_sha256'],'census baseline mismatch')
match(p/baseline['pdf'],matrix['source_baseline']['pdf_sha256'],'frozen PDF')
texts={}
for record in source_records:
 match(p/record['path'],record['sha256'],'frozen original');texts[record['path']]=(p/record['path']).read_text(encoding='utf-8').splitlines()
 check(len(texts[record['path']])==record['line_count'],'original line count changed '+record['path'])
check(set(record['path'][len('manuscript/'):] for record in source_records)==set(baseline['source_hashes']),'actual16-source graph differs from baseline')

ledger=p/'DEPENDENCIES.md';live_rows={}
for n,line in enumerate(ledger.read_text(encoding='utf-8-sig').splitlines(),1):
 fields=[x.strip() for x in line.strip().strip('|').split('|')]
 if len(fields)==6 and re.fullmatch(r'[A-Z]\d+[a-z]?',fields[0]):live_rows[fields[0]]=dict(line=n,original=fields[1],claim=fields[2],declarations=fields[3],dependencies=fields[4],status=fields[5])
ids=[r['id'] for r in matrix['claim_rows']];idset=set(ids)
check(len(ids)==253 and len(idset)==253,'matrix must cover exactly253 unique existing IDs')
check(idset==set(live_rows),'matrix/unique-ledger ID sets differ')
stale_rows=[]
for row in matrix['claim_rows']:
 live=live_rows.get(row['id'],{})
 for field in ['original','claim','declarations','dependencies','status']:
  if live.get(field)!=row[field]:stale_rows.append((row['id'],field))
 check(bool(row.get('original_source_bindings')),'ID lacks exact original anchor '+row['id'])
 check(bool(row.get('census_records')),'ID lacks census disposition '+row['id'])
 for binding in row['formal_bindings']:check(binding['declaration'] in matrix['formal_declarations'],'missing formal declaration '+binding['declaration'])
if stale_rows:errors.append('Matrix is stale against sole ledger; refresh only derived bindings: '+str(stale_rows[:16]))
open_ids=[ID for ID,row in live_rows.items() if row['status']!='已闭合']
if open_ids:incomplete.append('OPEN_ORIGINAL_IDS '+','.join(open_ids))

_S7_PRIVATE_PAPER_SPECS = {'PaperProofs.Common.Native.B23PaperClosure.FullPaperClaims': {'claim_id': 'B23', 'module': 'RootPaper_B23_Interface007', 'source_sha256': 'ad5778166fea968f3ec9887455e186841fe9611f6b22896d662027b28e63302c', 'line': 18, 'declaration_source_end': 23, 'full_declaration_source': 'def FullPaperClaims : Prop := RootPaper.B23.FullPaperClaims\n\nend PaperProofs.Common.Native.B23PaperClosure\n\nnamespace RootPaper.B23.Interface\n', 'signature_start': 'def FullPaperClaims : Prop := RootPaper.B23.FullPaperClaims'}, 'PaperProofs.Structure.LaminarTree.L01PaperClosure.FullPaperClaims': {'claim_id': 'L01', 'module': 'RootPaper_L01_Interface006', 'source_sha256': 'cdf44a9e620df2ecd9a9aa5f5a29ef089619d5bdcec6bbd206656aa67fffa79b', 'line': 17, 'declaration_source_end': 22, 'full_declaration_source': 'def FullPaperClaims : Prop := RootPaper.L01.FullPaperClaims\n\nend PaperProofs.Structure.LaminarTree.L01PaperClosure\n\nnamespace RootPaper.L01.Interface\n', 'signature_start': 'def FullPaperClaims : Prop := RootPaper.L01.FullPaperClaims'}}

_S7_REGISTERED_SOURCE_INDEX = None

def _s7_locator_need(ok, message):
    if not ok:
        raise ValueError(message)

def _s7_locator_rel(value):
    _s7_locator_need(isinstance(value, str) and value and "\\" not in value,
                     "missing/non-POSIX project-relative path")
    parts = value.split("/")
    _s7_locator_need(all(part not in ("", ".", "..") and
                         re.fullmatch(r"[A-Za-z0-9_.-]+", part) for part in parts),
                     "invalid/escaping relative path")
    q = Path(value)
    _s7_locator_need(not q.is_absolute() and not q.drive and q.as_posix() == value,
                     "noncanonical project-relative path")
    _s7_locator_need((b / q).resolve().is_relative_to(b.resolve()),
                     "path escapes the actual project root")
    return value

def _s7_locator_receipt_sha(rel):
    pins = receipt.get("verified_progress_sha256")
    _s7_locator_need(isinstance(pins, dict), "selected receipt lacks source fingerprints")
    value = pins.get("lean/" + rel)
    _s7_locator_need(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value),
                     "selected receipt omits exact path: " + rel)
    return value

def _s7_locator_bound_json(rel, declared_sha=None):
    rel = _s7_locator_rel(rel)
    expected = _s7_locator_receipt_sha(rel)
    if declared_sha is not None:
        _s7_locator_need(declared_sha == expected,
                         "registration/selected-receipt SHA mismatch: " + rel)
    raw = (b / rel).read_bytes()
    _s7_locator_need(hashlib.sha256(raw).hexdigest() == expected,
                     "current bytes/selected-receipt SHA mismatch: " + rel)
    return json.loads(raw.decode("utf-8-sig"))

def _s7_registered_source_index():
    global _S7_REGISTERED_SOURCE_INDEX
    if _S7_REGISTERED_SOURCE_INDEX is not None:
        return _S7_REGISTERED_SOURCE_INDEX
    registry = _s7_locator_bound_json("ProofDeps/proof-packages.json")
    _s7_locator_need(isinstance(registry, dict) and type(registry.get("version")) is int and
                     registry["version"] == 1 and isinstance(registry.get("packages"), list) and
                     registry["packages"], "invalid/empty bound proof registry")
    registered = registry["packages"]
    _s7_locator_need(all(isinstance(r, dict) and
                         set(r) == {"name", "path", "manifest", "sha256"} for r in registered),
                     "unsupported registry entry")
    names = [r["name"] for r in registered]
    _s7_locator_need(all(isinstance(n, str) and
                         re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", n) for n in names) and
                     len(names) == len(set(n.casefold() for n in names)),
                     "duplicate/invalid registered package names")
    roots = [_s7_locator_rel(r["path"]) for r in registered]
    folds = [r.casefold() for r in roots]
    _s7_locator_need(all(r.startswith("ProofDeps/") for r in roots) and
                     len(folds) == len(set(folds)) and
                     not any(a.startswith(z + "/") for a in folds for z in folds if a != z),
                     "unknown/overlapping registered roots")
    index = {}
    module_folds = set()
    path_folds = set()
    for reg, root in zip(registered, roots):
        _s7_locator_need(isinstance(reg["sha256"], str) and
                         re.fullmatch(r"[0-9a-f]{64}", reg["sha256"]),
                         "registered manifest SHA missing/invalid")
        manifest_rel = root + "/" + _s7_locator_rel(reg["manifest"])
        mf = _s7_locator_bound_json(manifest_rel, reg["sha256"])
        _s7_locator_need(isinstance(mf, dict) and isinstance(mf.get("sources"), list),
                         "bound manifest lacks private sources")
        for row in mf["sources"]:
            _s7_locator_need(isinstance(row, dict), "invalid manifest source row")
            module = row.get("module")
            _s7_locator_need(isinstance(module, str) and
                             re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", module) and
                             module != "PaperProofs" and not module.startswith("PaperProofs."),
                             "invalid/private-source module identity")
            src = row.get("source")
            _s7_locator_need(isinstance(src, dict), "manifest source object missing")
            source_rel = _s7_locator_rel(src.get("path"))
            _s7_locator_need(source_rel == module.replace(".", "/") + ".lean",
                             "registered source path/module mismatch")
            _s7_locator_need(isinstance(src.get("sha256"), str) and
                             re.fullmatch(r"[0-9a-f]{64}", src["sha256"]),
                             "manifest source SHA missing")
            full_rel = root + "/" + source_rel
            _s7_locator_need(module.casefold() not in module_folds and
                             full_rel.casefold() not in path_folds,
                             "overlapping/duplicate registered source identity")
            module_folds.add(module.casefold())
            path_folds.add(full_rel.casefold())
            index[full_rel] = (module, src)
    _S7_REGISTERED_SOURCE_INDEX = index
    return index

def _s7_module_locator(name, d):
    path = d["path"]
    if path.startswith("PaperProofs/"):
        return d["module"] == Path(path).with_suffix("").as_posix().replace("/", ".")
    if name not in _S7_PRIVATE_PAPER_SPECS:
        if path.startswith("ProofDeps/"):
            errors.append("REGISTERED_SPEC_LOCATOR_NOT_ALLOWLISTED " + name)
            return False
        return d["module"] == Path(path).with_suffix("").as_posix().replace("/", ".")
    try:
        cfg = _S7_PRIVATE_PAPER_SPECS[name]
        path = _s7_locator_rel(path)
        _s7_locator_need(path.startswith("ProofDeps/"), "external paper spec is not registered")
        item = _s7_registered_source_index().get(path)
        _s7_locator_need(item is not None, "external paper spec has no exact registered source row")
        module, src = item
        _s7_locator_need(module == cfg["module"] == d["module"],
                         "matrix/registered/allowed real module mismatch")
        _s7_locator_need(d["name"] == name and d["local"] == "FullPaperClaims" and
                         d["kind"] == "def" and d["is_private"] is False,
                         "external exception is only the two public spec defs")
        _s7_locator_need(d["sha256"] == src["sha256"] == cfg["source_sha256"] ==
                         _s7_locator_receipt_sha(path),
                         "matrix/manifest/frozen-spec/receipt source SHA mismatch")
        raw = (b / path).read_bytes()
        _s7_locator_need(hashlib.sha256(raw).hexdigest() == src["sha256"] and
                         type(src.get("bytes")) is int and len(raw) == src["bytes"],
                         "actual registered source bytes mismatch")
        lines = raw.decode("utf-8-sig").splitlines()
        _s7_locator_need(type(d["line"]) is int and type(d["declaration_source_end"]) is int and
                         d["line"] == cfg["line"] and
                         d["declaration_source_end"] == cfg["declaration_source_end"],
                         "external exact declaration span mismatch")
        span = "\n".join(lines[d["line"] - 1:d["declaration_source_end"]])
        _s7_locator_need(span == d["full_declaration_source"] == cfg["full_declaration_source"] and
                         d["signature_start"] == cfg["signature_start"],
                         "registered actual source/matrix exact full declaration mismatch")
        return True
    except (OSError, ValueError, TypeError, KeyError, UnicodeError) as exc:
        errors.append("REGISTERED_SPEC_LOCATOR_FAIL " + name + ": " + str(exc))
        return False

decls=matrix['formal_declarations'];direct=matrix['direct_formal_sources']
for record in direct:match(record['path'],record['live_sha256'],'matrix formal source')
for name,d in decls.items():
 check(name==d['name'],'declaration key/name mismatch '+name)
 check(_s7_module_locator(name,d),'declaration module locator mismatch '+name)
 check(digest(b/d['path'])==d['sha256'],'declaration source no longer equals frozen source '+name)

# Verify the exact frozen source spans, every nonblank original line's
# disposition, and all22 explicit environments by a fresh actual scan.
for block in census['source_dispositions']:
 check(set(block['claim_ids'])<=idset,'census invents unknown ID')
 if block['bearing']:check(bool(block['claim_ids']),'unclaimed bearing source block')
 lines=texts[block['source']];snippet='\n'.join(lines[block['start']-1:block['end']])
 check(hashlib.sha256(snippet.encode()).hexdigest()==block['span_text_sha256'],'source-span text mismatch '+block['source']+':'+str(block['start']))
line_gaps=[];line_overlaps=[]
for source,lines in texts.items():
 for n,line in enumerate(lines,1):
  if not re.split(r'(?<!\\)%',line)[0].strip():continue
  owners=[x for x in census['source_dispositions'] if x['source']==source and x['start']<=n<=x['end']]
  if not owners:line_gaps.append((source,n))
  if len(owners)>1:line_overlaps.append((source,n))
check(not line_gaps,'unclaimed original lines '+str(line_gaps[:10]));check(not line_overlaps,'overlapping original dispositions '+str(line_overlaps[:10]))
actual_env=[]
for source,lines in texts.items():
 stack=[]
 for n,line in enumerate(lines,1):
  for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',re.split(r'(?<!\\)%',line)[0]):
   cmd,kind=m.groups()
   if cmd=='begin':stack.append((kind,n))
   else:
    if not stack or stack[-1][0]!=kind:errors.append('unbalanced original environment '+source+':'+str(n));continue
    k,a=stack.pop()
    if k in ['theorem','lemma','proposition','corollary','remark','definition']:actual_env.append((source.removeprefix('manuscript/'),a,n,k,tuple(re.findall(r'\\label\{([^}]+)\}','\n'.join(lines[a-1:n])))))
expected_env=[(e['source'],e['start'],e['end'],e['kind'],tuple(e['labels'])) for e in census['explicit_environments']]
check(len(actual_env)==22 and sorted(actual_env)==sorted(expected_env),'actual22-environment census mismatch')
for e in census['explicit_environments']:check(bool(e['claim_ids']) and set(e['claim_ids'])<=idset,'unclaimed explicit theorem environment')

# Original OPEN target specs are fixed independently of later proof bindings.
specs=load(b/matrix['immutable_open_target_spec_snapshot'])
for ID,records in specs.items():
 for record in records:
  d=decls.get(record['name']);check(d is not None,'original whole target declaration removed '+record['name'])
  if d:check(hashlib.sha256(d['full_declaration_source'].encode()).hexdigest()==record['declaration_text_sha256'],'original whole specification text changed; requires semantic review '+ID)
  if d and record['name'] in _S7_PRIVATE_PAPER_SPECS and d['path'].startswith('ProofDeps/'):
   cfg=_S7_PRIVATE_PAPER_SPECS[record['name']]
   check(ID==cfg['claim_id'],'registered paper spec mapped to wrong original ID '+ID)
   check(record.get('source')==d['path'] and record.get('source_sha256')==d['sha256'] and record.get('line')==d['line'],'registered spec snapshot/source locator mismatch '+ID)
   check(record.get('full_original_declaration')==d['full_declaration_source'],'registered spec snapshot/body mismatch '+ID)
 pending=matrix['deferred_full_goal_specs'][ID]
 if not pending['whole_target_proof_bindings']:incomplete.append('MISSING_WHOLE_PROOF_BINDING '+ID)
 else:
  for binding in pending['whole_target_proof_bindings']:
   name=binding['declaration'];check(name in decls,'new whole proof declaration missing '+ID+':'+name)
   if name in decls:
    check(decls[name]['kind'] in ('theorem','lemma'),'new whole proof must be a theorem '+ID)
    check(decls[name]['path'].startswith('PaperProofs/'),'whole proof must be a canonical formal module '+ID)
    check(receipt['verified_progress_sha256'].get('lean/'+decls[name]['path'])==decls[name]['sha256'],'whole proof not certified by selected new receipt '+ID)
  if pending.get('new_whole_receipt_epoch')!=matrix['accepted_receipt']['epoch']:incomplete.append('WHOLE_PROOF_EPOCH_NOT_REBOUND '+ID)
  evidence=pending.get('ordinary_public_original_type_evidence')
  if not evidence:incomplete.append('MISSING_ORDINARY_FULL_ORIGINAL_TYPE_CALL '+ID)
  else:
   check(evidence.get('actual_exit')==0,'ordinary original-type call failed '+ID)
   check(set(evidence.get('original_spec_declarations',[]))==set(pending['original_spec_declarations']),'ordinary caller must explicitly bind ALL exact original whole target types '+ID)
   match(evidence['source_path'],evidence['source_sha256'],'ordinary original-type caller '+ID)
   match(evidence['log_path'],evidence['log_sha256'],'ordinary original-type caller log '+ID)

# A historical010 source list cannot certify live011 modules. Scan ALL live
# formal source files rather than treating matrix's303 reviewed anchors as
# equivalent to the whole current project's imported module closure.
live_paths=[x.replace('\\','/') for x in subprocess.check_output(['rg','--files','PaperProofs','-g','*.lean'],text=True,encoding='utf-8').splitlines()]
if (b/'PaperProofs.lean').exists():live_paths.append('PaperProofs.lean')
uncertified=[]
for path in sorted(set(live_paths)):
 expected=receipt['verified_progress_sha256'].get('lean/'+path)
 if digest(b/path)!=expected:uncertified.append(path)
if uncertified:incomplete.append('LIVE_FORMAL_SOURCE_NOT_CERTIFIED_BY_SELECTED_RECEIPT count='+str(len(uncertified)))
if receipt['audit_coverage'].get('source_module_count')!=len(set(live_paths)):incomplete.append('WHOLE_AUDIT_MODULE_COUNT_STALE accepted='+str(receipt['audit_coverage'].get('source_module_count'))+' live='+str(len(set(live_paths))))
check(receipt['build']['returncode']==0 and receipt['audit']['returncode']==0,'selected whole receipt build/audit actual exits not0')
check(receipt['audit_coverage'].get('all_source_modules_imported_all') is True,'selected audit must import ALL source/private module data')
check(receipt['frozen']['source_manifest_sha256']==baseline['source_manifest_sha256'],'whole receipt wrong frozen manuscript')
check(receipt['ledger'].get('claim_count')==253,'whole receipt wrong original ID count')
check(receipt['ledger'].get('main_independent_of_appendix_D') is True,'main proof chain reverse-depends on independent Paid appendix')
if not receipt['ledger'].get('all_claims_closed'):incomplete.append('SELECTED_WHOLE_RECEIPT_NOT_ALL253_CLOSED')
for kind in ['build','audit']:
 record=receipt[kind];candidates=[Path(record['log'])]
 epoch=matrix['accepted_receipt']['epoch']
 m=re.search(r'(RootBatch\d+)\.receipt',str(args.receipt))
 if m:epoch=m[1]
 candidates+=[b/'.lake/workpads'/(epoch+('.audit.log' if kind=='audit' else '.build.log'))]
 # Accepted012/013 keep immutable logs in their numbered archive directory.
 # Candidate discovery never replaces the receipt's exact SHA requirement.
 candidates+=[b/'.lake/workpads'/(epoch+'_accepted_logs')/('axioms.log' if kind=='audit' else 'build.log')]
 valid=[q for q in candidates if q.exists() and digest(q)==record['log_sha256']]
 if not valid:errors.append('Cannot bind actual archived '+kind+' log for selected receipt; supply matching immutable archive')
 elif kind=='audit':
  audit_text=valid[0].read_text(encoding='utf-8-sig')
  check('AXIOM_AUDIT_PASS' in audit_text and 'new_axioms=0' in audit_text and 'forbidden_dependencies=0' in audit_text,'whole actual audit log is not the accepted no-new-axiom PASS')

ready=not errors and not incomplete
result=dict(metadata_consistency_pass=not errors,final_acceptance_ready_for_Root_decision=ready,global_s7_complete=False,Root_final_acceptance_required=True,existing_ID_count=len(ids),formal_reference_count=sum(len(r['formal_bindings']) for r in matrix['claim_rows']),formal_declaration_count=len(decls),direct_reviewed_sources=len(direct),live_project_source_files=len(set(live_paths)),live_sources_uncertified_by_selected_receipt=len(uncertified),uncertified_examples=uncertified[:8],explicit_environment_count=len(actual_env),source_disposition_count=len(census['source_dispositions']),unclaimed_original_lines=len(line_gaps),open_original_IDs=open_ids,errors=errors,incomplete_reasons=incomplete,meaning='Exit0 only means all evidence is ready for Root final acceptance; script never declares globalS7 complete. Exit2 diagnoses expected open goals/stale whole receipt. Exit1 means broken/stale derived bindings must be repaired before acceptance.')
print(json.dumps(result,ensure_ascii=False,indent=2));sys.exit(1 if errors else (0 if ready else 2))
