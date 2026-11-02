"""Generate a NEW S7 metadata candidate from actual accepted inputs; never run S7/Lean or edit official files."""
import argparse,ast,copy,datetime,hashlib,json,re,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parent.parent
SUBMISSION=PROJECT.parent/"compatibility_structure_research/submission_2026-10-27"
ANCESTRY=HERE/"RootPaper014_S7_Ancestry001.json"
EXTRA_BINDINGS=HERE/"RootPaper014_S7_Bindings002.json"
PREP=HERE/"ROOT_PAPER_S7_TARGETS014_PREP002.json"
BASE=HERE/"PStar_S7_GLOBAL_MATRIX_001.json"
SPECS=HERE/"PStar_S7_GLOBAL_ORIGINAL_TARGET_SPECS_001.json"
CENSUS=HERE/"PStar_S7_GLOBAL_CENSUS_001.json"
INDEX=HERE/"PStar_S7_GLOBAL_DECL_INDEX_001.json"
VERIFIER=HERE/"PStar_S7_GLOBAL_verify_003.py"
def need(ok,message):
    if not ok:raise ValueError(message)
def load(path):return json.loads(Path(path).read_text(encoding="utf-8-sig"))
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def located(path):
    q=Path(path);return q if q.is_absolute() else PROJECT/q
def locator(path):
    q=Path(path).resolve()
    return q.relative_to(PROJECT).as_posix() if q.is_relative_to(PROJECT) else q.as_posix()
def current_rows():
    out=[]
    for n,line in enumerate((SUBMISSION/"DEPENDENCIES.md").read_text(encoding="utf-8-sig").splitlines(),1):
        f=[x.strip() for x in line.strip().strip("|").split("|")]
        if len(f)==6 and re.fullmatch(r"[A-Z]\d+[a-z]?",f[0]):
            x=dict(zip(["id","original","claim","declarations","dependencies","status"],f));x["ledger_line"]=n;out.append(x)
    return out
def validate_rows(rows,ancestry):
    need(len(rows)==253 and len({x["id"] for x in rows})==253,"sole ledger must have exactly253 original IDs")
    live={x["id"]:x for x in rows}
    need(all(x["status"]=="已闭合" for x in rows),"actual sole ledger acceptance is incomplete")
    for old in ancestry["accepted251_ledger_rows"]:
        need(all(live[old["id"]][k]==old[k] for k in old),"old251 row changed; explicit semantic review required: "+old["id"])
    for ID,old in ancestry["paper_original_fields"].items():
        need(all(live[ID][k]==v for k,v in old.items()),"paper original anchor/dependencies changed: "+ID)
def validate_receipt(r,baseline):
    need(r.get("build",{}).get("returncode")==0 and r.get("audit",{}).get("returncode")==0,"actual full build/audit receipt required")
    need(r.get("ledger",{}).get("claim_count")==253 and r["ledger"].get("all_claims_closed") is True,"actual accepted whole ledger receipt required")
    need(r["ledger"].get("main_independent_of_appendix_D") is True,"main/Paid independence not established")
    need(r.get("audit_coverage",{}).get("all_source_modules_imported_all") is True,"full normal private/import-all coverage required")
    need(r.get("proof_dependencies",{}).get("original_module_count")==4297,"actual complete registered4297 source union required")
    need(r["proof_dependencies"].get("new_axioms")==r["proof_dependencies"].get("forbidden_dependencies")==0,"registered actual owner audit policy incomplete")
    need(set(r["proof_dependencies"].get("allowed_axioms",[]))=={"propext","Classical.choice","Quot.sound"},"Std3-only registered credit required")
    need(r.get("frozen",{}).get("source_manifest_sha256")==baseline["source_manifest_sha256"],"receipt changed frozen manuscript")
    need(isinstance(r.get("verified_progress_sha256"),dict),"selected actual receipt has no source fingerprints")
def actual_log(record,epoch,kind,receipt_path):
    found=re.search(r"(RootBatch\d+)\.receipt",str(receipt_path))
    if found:epoch=found[1]
    candidates=[located(record["log"]),HERE/(epoch+(".audit.log" if kind=="audit" else ".build.log")),
                HERE/(epoch+"_accepted_logs")/("axioms.log" if kind=="audit" else "build.log")]
    valid=[q for q in candidates if q.is_file() and sha(q)==record["log_sha256"]]
    need(bool(valid),"No actual log matching003's receipt/epoch candidates: "+kind)
    return valid[0]
def clean(text):
    result=[];depth=0;instr=False;i=0
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;result.append('  ');i+=2
            elif text.startswith('-/',i):depth-=1;result.append('  ');i+=2
            else:result.append('\n' if text[i]=='\n' else ' ');i+=1
        elif instr:
            if text[i]=='\\' and i+1<len(text):result.append('  ');i+=2
            elif text[i]=='"':instr=False;result.append(' ');i+=1
            else:result.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('/-',i):depth=1;result.append('  ');i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i)
            if j<0:j=len(text)
            result.append(' '*(j-i));i=j
        elif text[i]=='"':instr=True;result.append(' ');i+=1
        else:result.append(text[i]);i+=1
    return ''.join(result)
def scan_small(path,pin):
    raw=located(path).read_text(encoding="utf-8-sig").splitlines()
    code=clean("\n".join(raw)).splitlines();ns="";stack=[];out=[];contexts={};vs=[];us=[]
    for n,line in enumerate(code,1):
        st=re.sub(r"^@\[[^\]]*\]\s*","",line.strip());contexts[n]=dict(variables=list(vs),universes=list(us))
        m=re.match(r"namespace\s+([^\s]+)",st)
        if m:stack.append(("namespace",ns,list(vs),list(us)));ns=(ns+"."+m[1]).strip(".");continue
        if re.match(r"(?:(?:public|protected|private)\s+)?section(?:\s|$)",st) or st=="mutual":
            stack.append(("section",ns,list(vs),list(us)));continue
        if re.match(r"end(?:\s|$)",st):
            if stack:_,ns,vs,us=stack.pop()
            continue
        if st.startswith("variable "):
            a=[raw[n-1].strip()];k=n
            while k<len(raw) and code[k].strip().startswith(("(","{","[")):a.append(raw[k].strip());k+=1
            vs.append(dict(line=n,text="\n".join(a)))
        elif st.startswith("universe "):us.append(dict(line=n,text=raw[n-1].strip()))
        m=re.match(r"(?:(?:noncomputable|protected|private|public|unsafe|partial|nonrec)\s+)*(def|theorem|lemma|structure|inductive|abbrev|opaque|axiom|instance)\s+([^\s({:]+)",st)
        if m:
            local=m[2];name=local.removeprefix("_root_.") if local.startswith("_root_.") else (ns+"."+local).strip(".")
            out.append(dict(name=name,local=local,kind=m[1],path=path,line=n,sha256=pin,signature_start=line.strip(),is_private="private" in st[:m.start(1)].split()))
    for i,d in enumerate(out):
        end=out[i+1]["line"]-1 if i+1<len(out) else len(raw)
        d.update(module=Path(path).with_suffix("").as_posix().replace("/","."),full_declaration_source="\n".join(raw[d["line"]-1:end]),
                 declaration_source_end=end,lexical_active_section_context=contexts[d["line"]],
                 type_evidence_kind="Existing lexical source-span convention; no new kernel/semantic proof acceptance")
    return out
def resolve_row(row,index,base_decls):
    prefix="";refs=[]
    for token in row["declarations"].split("；"):
        token=re.sub(r"（.*?）","",token).strip().removeprefix("历史负面：")
        need(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*",token) is not None,"unsupported ledger token: "+row["id"]+":"+token)
        wanted="PaperProofs."+token if token.startswith(("Paid.","Common.","Statistics.","Structure.","Star.","Retained.")) else prefix+token
        matches=[d for d in index if d["name"]==wanted]
        pub=[d for d in matches if not d["is_private"]]
        if pub:matches=pub
        if not matches:
            matches=[d for d in index if d["name"]==token or d["name"].endswith("."+token)]
            pub=[d for d in matches if not d["is_private"]]
            if pub:matches=pub
        unique={(d["name"],d["path"],d["line"]):d for d in matches}
        need(len(unique)==1,"missing/ambiguous actual declaration: "+row["id"]+":"+token)
        d=next(iter(unique.values()));prefix=d["name"].rsplit(".",1)[0]+"."
        need(d["name"] in base_decls,"new declaration lacks exact accepted source span: "+d["name"])
        refs.append(dict(ledger_token=token,declaration=d["name"]))
    return refs
def verifier_helpers(receipt):
    t=ast.parse(VERIFIER.read_text(encoding="utf-8"))
    nodes=[n for n in t.body if (isinstance(n,ast.FunctionDef) and n.name.startswith("_s7_")) or
           (isinstance(n,ast.Assign) and any(isinstance(q,ast.Name) and q.id.startswith("_S7_") for q in n.targets))]
    env=dict(json=json,hashlib=hashlib,re=re,Path=Path,b=PROJECT,receipt=receipt,errors=[])
    exec(compile(ast.fix_missing_locations(ast.Module(body=nodes,type_ignores=[])),"<actual003-locator-helpers>","exec"),env)
    return env
def generate(args):
    need(args.receipt and args.epoch and args.out_dir and args.tag,"--receipt/--epoch/--out-dir/--tag are actual required inputs")
    need(re.fullmatch(r"[A-Za-z0-9_]+",args.epoch) and re.fullmatch(r"[A-Za-z0-9_]+",args.tag),"invalid epoch/tag")
    rp=located(args.receipt).resolve();receipt=load(rp);anc=load(ANCESTRY);prep=load(PREP);matrix=load(BASE);census=load(CENSUS);specs=load(SPECS)
    validate_receipt(receipt,matrix["source_baseline"]);rows=current_rows();validate_rows(rows,anc)
    need(len(census["source_inputs"])==16 and len(census["explicit_environments"])==22 and len(census["source_dispositions"])==131,"inherited census identity changed")
    need(matrix["A17_final_handoff"]["state"].startswith("RECEIVED_AND_READ"),"accepted A17 handoff missing")
    if "epoch" in receipt:need(receipt["epoch"]==args.epoch,"receipt epoch disagrees with explicit actual epoch")
    fp=receipt["verified_progress_sha256"];rsha=sha(rp)
    normal=[k for k in fp if k=="lean/PaperProofs.lean" or (k.startswith("lean/PaperProofs/") and k.endswith(".lean"))]
    need(len(normal)==receipt["audit_coverage"]["source_module_count"] and len(normal)>=1923,"actual normal source inventory incomplete")
    decls=matrix["formal_declarations"];index=load(INDEX)
    extra=load(EXTRA_BINDINGS)
    closing_pins=dict(anc["accepted_closing_source_pins"])
    for path,pin in extra["additional_accepted_source_pins"].items():
        need(path not in closing_pins or closing_pins[path]==pin,"closing source variant conflict: "+path)
        closing_pins[path]=pin
    for path,pin in closing_pins.items():
        need(fp.get("lean/"+path)==pin,"accepted251 closing source changed: "+path)
        scanned=scan_small(path,pin);index.extend(scanned)
        for d in scanned:
            if not d["is_private"]:decls[d["name"]]=d
    for name,d in prep["formal_declaration_payload"].items():
        need(fp.get("lean/"+d["path"])==d["sha256"],"new spec/theorem not registered in selected actual receipt: "+name)
        decls[name]=copy.deepcopy(d);index.append(copy.deepcopy(d))
    helper=verifier_helpers(receipt)
    for name,d in decls.items():
        need(fp.get("lean/"+d["path"])==d["sha256"],"historical formal source no longer matches selected receipt: "+name)
        d["prior_acceptance_provenance"]=copy.deepcopy(d.get("receipt_binding"))
        d["receipt_binding"]=dict(epoch=args.epoch,receipt_sha256=rsha,accepted_source_sha256=d["sha256"],
            live_source_sha256=d["sha256"],state="selected_actual_receipt_pin; actual current bytes checked by separate003")
        if name in prep["formal_declaration_payload"]:need(helper["_s7_module_locator"](name,d),"; ".join(helper["errors"]))
    by={r["id"]:r for r in matrix["claim_rows"]}
    for live in rows:
        old=by[live["id"]];old.update(live)
        if live["id"] in ("A19","B23","L01","D25","D26","D27","D29","D36"):old["formal_bindings"]=resolve_row(live,index,decls)
        old["acceptance_kind"]="paper_scope_complete_original_claim" if live["id"] in ("B23","L01") else old.get("acceptance_kind")
        if live["id"] in ("B23","L01"):
            old["whole_goal_boundary"]="Complete paper-scope target and actual type evidence; prior stronger Bool target retained unchanged separately."
            t=prep["paper_targets"][live["id"]]
            old["paper_scope_transition"]=dict(source_preparation=locator(PREP),selected_actual_receipt_epoch=args.epoch,
                original_paper_bindings=copy.deepcopy(t["original_paper_bindings"]),
                canonical_spec=t["canonical"]["spec_declaration"],canonical_theorem=t["canonical"]["theorem_declaration"],
                real_spec_owner=t["private_interface"]["module"],registered_spec_source=t["private_interface"]["registered_source_path"],
                complete_Root_full_spec=copy.deepcopy(t["root_full"]),necessary_public_quantifiers=copy.deepcopy(t["necessary_public_quantifiers"]),
                legacy_strengthened_target_mapping=copy.deepcopy(t["legacy_strengthened_target_mapping"]),
                semantic_review_references=copy.deepcopy(t["semantic_review_references"]),actual_registered_locator_verified=True,
                old_Bool_definition_redefined=False)
            old["scope_evidence"]=list(old.get("scope_evidence",[]))+[locator(PREP),".lake/workpads/ROOT_PAPER_S7_SCOPE_TRANSITION_20261102_001.md"]
        elif live["id"] in anc["prior_six_deferred"]:
            old["acceptance_kind"]="previously_accepted_original_whole_target; ancestry retained"
            old["scope_evidence"]=list(old.get("scope_evidence",[]))+[anc["prior_six_deferred"][live["id"]]["ancestry"]]
    specs.update(copy.deepcopy(prep["new_original_target_snapshot_payload"]))
    deferred=copy.deepcopy(anc["prior_six_deferred"])
    for ID in ("B23","L01"):deferred[ID]=copy.deepcopy(prep["paper_targets"][ID]["future_deferred_full_goal_spec"])
    for ID,pending in deferred.items():
        pending["new_whole_receipt_epoch"]=args.epoch
        need(set(pending["original_spec_declarations"])=={x["name"] for x in specs[ID]},"whole spec set mismatch: "+ID)
        ev=pending["ordinary_public_original_type_evidence"]
        need(ev["actual_exit"]==0 and set(ev["original_spec_declarations"])==set(pending["original_spec_declarations"]),"exact ordinary evidence mismatch: "+ID)
        need(located(ev["source_path"]).is_file() and sha(located(ev["log_path"]))==ev["log_sha256"],"historical/current exact caller source/log missing or mismatched: "+ID)
        ev["source_pin_credit"]="Previously frozen actual typed-consumer source pin reused without old proof bytehash; separate003 checks current source bytes"
        for binding in pending["whole_target_proof_bindings"]:
            name=binding["declaration"];need(name in decls and decls[name]["kind"] in ("theorem","lemma") and decls[name]["path"].startswith("PaperProofs/"),"canonical-only whole theorem missing: "+ID)
        for sr in specs[ID]:
            need(sr["name"] in decls and hashlib.sha256(decls[sr["name"]]["full_declaration_source"].encode()).hexdigest()==sr["declaration_text_sha256"],"immutable exact spec changed: "+ID)
    out=located(args.out_dir).resolve();need(out.is_relative_to(HERE),"output directory must stay under workpads")
    prefix="RootPaper014_S7_"+args.tag
    targets=dict(matrix=out/(prefix+"_MATRIX.json"),spec=out/(prefix+"_TARGETS.json"),manifest=out/(prefix+"_MANIFEST.json"))
    need(not any(q.exists() for q in targets.values()),"new numbered outputs must not overwrite anything")
    matrix.update(accepted_receipt=dict(epoch=args.epoch,path=locator(rp),sha256=rsha,build_exit=receipt["build"]["returncode"],audit_exit=receipt["audit"]["returncode"],ledger_state=receipt["ledger"].get("state_counts")),
        created_from_ledger=dict(path=locator(SUBMISSION/"DEPENDENCIES.md"),sha256=sha(SUBMISSION/"DEPENDENCIES.md")),
        immutable_open_target_spec_snapshot=locator(targets["spec"]),deferred_full_goal_specs=deferred,
        original_census_file=locator(CENSUS),global_s7_complete=False,Root_acceptance_required=True,
        generation_status="ACTUAL_INPUT_METADATA_CANDIDATE_NOT_S7_ACCEPTANCE",preserved_old251_ancestry=locator(ANCESTRY),
        preserved_old_Bool_snapshot=locator(SPECS))
    roots={}
    for d in decls.values():roots[d["path"]]=dict(path=d["path"],live_sha256=d["sha256"],source_pin_credit="selected actual receipt;003 checks current bytes")
    matrix["direct_formal_sources"]=sorted(roots.values(),key=lambda d:d["path"])
    package={}
    def include(path,expected=None):
        path=located(path);need(path.is_file(),"missing required metadata/caller asset: "+str(path))
        if path.suffix==".lean":
            need(expected is not None,"Lean source requires an existing published pin: "+str(path))
            value=expected
            credit="reused existing accepted source pin; actual bytes remain independently checked by003"
        else:
            value=sha(path)
            need(expected is None or value==expected,"pinned semantic metadata changed: "+str(path))
            credit="actual metadata/log bytes"
        package[locator(path)]=dict(path=locator(path),sha256=value,bytes=path.stat().st_size,pin_credit=credit)
    for p in [BASE,SPECS,CENSUS,PREP,ANCESTRY,EXTRA_BINDINGS,VERIFIER,Path(__file__).resolve(),rp]:include(p)
    for e in matrix["sector_reports"]:include(e["path"],e["sha256"])
    for e in matrix["A17_final_handoff"]["files"]:include(e["path"],e["sha256"])
    for p in anc["semantic_credit_paths"]:include(p)
    for kind in ("build","audit"):include(actual_log(receipt[kind],args.epoch,kind,rp),receipt[kind]["log_sha256"])
    for p in deferred.values():
        e=p["ordinary_public_original_type_evidence"];include(e["source_path"],e["source_sha256"]);include(e["log_path"],e["log_sha256"])
    # Hash in-memory NEW metadata, not old proof products; writing starts only after all input checks.
    def encoded(obj):return (json.dumps(obj,ensure_ascii=False,indent=2)+"\n").encode("utf-8")
    buffers={targets["matrix"]:encoded(matrix),targets["spec"]:encoded(specs)}
    for p,raw in buffers.items():package[locator(p)]=dict(path=locator(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
    mf=dict(batch=prefix,created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        global_s7_complete=False,Root_final_acceptance_required=True,accepted_receipt_epoch=args.epoch,
        package=list(package.values()),original_IDs=253,frozen_input_sources=16,explicit_environments=22,source_dispositions=131,
        scope="Actual-input candidate only. Existing251 semantic credit reused; only B23/L01 paper target scope changes. Root separately executes003 and signs final semantics.")
    buffers[targets["manifest"]]=encoded(mf);out.mkdir(parents=True,exist_ok=True)
    for p,raw in buffers.items():
        with p.open("xb") as f:f.write(raw)
    print(json.dumps(dict(generated={k:locator(p) for k,p in targets.items()},receipt_epoch=args.epoch,
        global_s7_complete=False,Root_final_acceptance_required=True,full_S7_executed=False,
        next_command=["python",locator(VERIFIER),"--matrix",locator(targets["matrix"]),"--census",locator(CENSUS),"--receipt",locator(rp),"--manifest",locator(targets["manifest"])]),ensure_ascii=False,indent=2))
def self_test():
    a=load(ANCESTRY);rows=copy.deepcopy(a["accepted251_ledger_rows"])+[dict(id=k,status="已闭合",claim="synthetic",declarations="synthetic",**v) for k,v in a["paper_original_fields"].items()]
    validate_rows(rows,a);bad=copy.deepcopy(rows);bad[0]["claim"]+=" changed"
    try:validate_rows(bad,a);raise AssertionError("old251 mutation accepted")
    except ValueError:pass
    bad=copy.deepcopy(rows);next(x for x in bad if x["id"]=="B23")["dependencies"]+=" changed"
    try:validate_rows(bad,a);raise AssertionError("paper dependency mutation accepted")
    except ValueError:pass
    try:validate_receipt({},{"source_manifest_sha256":"synthetic"});raise AssertionError("missing receipt accepted")
    except ValueError:pass
    print(json.dumps(dict(synthetic_schema_checks_passed=True,actual_receipt_used=False,generated_matrix_spec_manifest=False,
        full_S7_executed=False,Lean_invocations=0,proof_source_product_hashes=0),indent=2))
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--receipt");ap.add_argument("--epoch");ap.add_argument("--out-dir");ap.add_argument("--tag");ap.add_argument("--self-test",action="store_true")
    a=ap.parse_args()
    if a.self_test:self_test()
    else:generate(a)
if __name__=="__main__":
    try:main()
    except (OSError,ValueError,KeyError,TypeError,AssertionError) as e:
        print("S7_GENERATOR_REFUSED: "+str(e),file=sys.stderr);sys.exit(1)
