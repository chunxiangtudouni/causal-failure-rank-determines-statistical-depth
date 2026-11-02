"""Check frozen inputs, the single claim ledger, imports, build and axiom audit.

This does not certify that the human census contains every mathematical claim,
or that a Lean statement means the same thing as the paper. Those remain
explicit manual gates even when this program exits successfully.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

from verify_proof_dependencies import verify_registered_packages, _header_imports


PROJECT = Path(__file__).resolve().parents[1]
SUBMISSION = PROJECT.parent / "compatibility_structure_research" / "submission_2026-10-27"
LEDGER = SUBMISSION / "DEPENDENCIES.md"
BASELINE = SUBMISSION / "checks" / "lean-baseline.json"
RECEIPT = SUBMISSION / "checks" / "lean-formalization-receipt.json"
CLAIM_ID = re.compile(r"(?:M|A|B|R|L|C|D)\d+[a-z]?")
STATES = ("已陈述", "条件接通", "已闭合", "—")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def progress_fingerprint() -> dict[str, str]:
    paths = [PROJECT / "PaperProofs.lean", PROJECT / "AuditAll.lean",
             PROJECT / "lean-toolchain", PROJECT / "lakefile.toml",
             PROJECT / "lake-manifest.json", Path(__file__).resolve(),
             PROJECT / "scripts" / "verify_proof_dependencies.py", LEDGER]
    paths.extend((PROJECT / "PaperProofs").rglob("*.lean"))
    return {str(path.relative_to(PROJECT.parent)).replace("\\", "/"): sha256(path)
            for path in sorted(paths)}


def check_frozen() -> dict:
    baseline = json.loads(BASELINE.read_text(encoding="utf-8-sig"))
    source = SUBMISSION / "manuscript"
    hashes = {name: sha256(source / name) for name in baseline["source_hashes"]}
    assert hashes == baseline["source_hashes"], "Frozen source hash mismatch"
    canonical = "".join(f"{name} {hashes[name]}\n" for name in sorted(hashes))
    manifest_hash = hashlib.sha256(canonical.encode("utf-8")).hexdigest()
    assert manifest_hash == baseline["source_manifest_sha256"], "Canonical manifest mismatch"
    pdf_hash = sha256(SUBMISSION / baseline["pdf"])
    assert pdf_hash == baseline["pdf_sha256"], "Frozen PDF hash mismatch"

    visited: set[str] = set()

    def visit(name: str) -> None:
        if name in visited:
            return
        visited.add(name)
        text = (source / name).read_text(encoding="utf-8-sig")
        for child in re.findall(r"\\input\{([^}]+)\}", text):
            target = (Path(name).parent / child).with_suffix(".tex").as_posix()
            visit(target)

    visit(baseline["source_entry"].removeprefix("manuscript/"))
    assert visited == set(hashes), "Actual input graph differs from frozen manifest"
    ledger_text = LEDGER.read_text(encoding="utf-8-sig")
    for label in baseline["main_labels"]:
        assert label in ledger_text, f"Missing main label: {label}"
    return {"sources": len(hashes), "source_manifest_sha256": manifest_hash,
            "pdf_sha256": pdf_hash, "actual_input_graph_matches": True}


def closure(graph: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    active: set[str] = set()

    def visit(node: str) -> None:
        assert node not in active, f"Dependency cycle at {node}"
        if node in seen:
            return
        assert node in graph, f"Unknown dependency: {node}"
        active.add(node)
        for dep in graph[node]:
            visit(dep)
        active.remove(node)
        seen.add(node)

    visit(start)
    return seen


def check_ledger() -> dict:
    claims = {}
    for line in LEDGER.read_text(encoding="utf-8-sig").splitlines():
        if not line.startswith("|"):
            continue
        columns = [part.strip() for part in line.split("|")[1:-1]]
        if not columns or not CLAIM_ID.fullmatch(columns[0]):
            continue
        assert len(columns) == 6, f"Malformed ledger row: {columns[0]}"
        key, source, statement, declaration, dependencies, state = columns
        assert key not in claims, f"Duplicate claim ID: {key}"
        assert state in STATES, f"Unknown state: {key} {state}"
        assert state == "—" or not declaration.startswith("—"), f"State without Lean declaration: {key}"
        claims[key] = {"source": source, "statement": statement,
                       "declaration": declaration, "state": state,
                       "dependencies": [] if dependencies == "—" else dependencies.split(",")}
    assert claims, "No claim rows found"
    graph = {key: item["dependencies"] for key, item in claims.items()}
    for key in graph:
        deps = closure(graph, key)
        if not key.startswith("D"):
            assert not any(dep.startswith("D") for dep in deps), f"Main claim depends on D: {key}"
    counts = {state: sum(item["state"] == state for item in claims.values()) for state in STATES}
    return {"claim_count": len(claims), "state_counts": counts,
            "acyclic": True, "main_independent_of_appendix_D": True,
            "not_yet_stated": [key for key, value in claims.items() if value["state"] == "—"],
            "first_round_all_claims_stated": counts["—"] == 0,
            "all_claims_closed": counts["已闭合"] == len(claims),
            "human_census_exhaustiveness_verified_by_script": False,
            "paper_statement_equivalence_verified_by_script": False}


def check_imports(external_graph: dict[str, list[str]]) -> dict:
    graph = dict(external_graph)
    ordinary = {}
    for path in sorted((PROJECT / "PaperProofs").rglob("*.lean")):
        name = ".".join(path.relative_to(PROJECT).with_suffix("").parts)
        imports = _header_imports(path.read_bytes())
        if name in graph:
            assert imports == graph[name], f"Formal frontier import metadata mismatch: {name}"
        ordinary[name] = imports
        graph[name] = imports
    project_prefixes = ("PaperProofs.", "Common.", "Structure.", "Paid.", "RootD27", "RootA19", "RootPaper")
    for name, imports in graph.items():
        for dep in imports:
            assert not dep.startswith(project_prefixes) or dep in graph, f"Missing preserved source origin: {name} -> {dep}"
    graph = {name: [dep for dep in imports if dep in graph] for name, imports in graph.items()}

    def is_paid(name: str) -> bool:
        return name.startswith(("PaperProofs.Paid.", "Paid.", "RootD27"))

    for name in graph:
        deps = closure(graph, name)
        if not is_paid(name):
            assert not any(is_paid(dep) for dep in deps), f"Main Lean module imports Paid: {name}"
    return {"modules": len(graph), "ordinary_formal_modules": len(ordinary),
            "preserved_private_modules": len(set(external_graph) - set(ordinary)),
            "acyclic": True, "main_independent_of_paid_modules": True}


def check_audit_coverage() -> dict:
    expected = {"PaperProofs"}
    expected.update(".".join(path.relative_to(PROJECT).with_suffix("").parts)
                    for path in (PROJECT / "PaperProofs").rglob("*.lean"))
    auditor = (PROJECT / "AuditAll.lean").read_text(encoding="utf-8-sig")
    imported_all = set(re.findall(r"(?m)^\s*(?:public\s+)?import\s+all\s+"
                                 r"(PaperProofs(?:\.[A-Za-z0-9_]+)*)", auditor))
    assert expected <= imported_all, f"Audit does not import all of: {sorted(expected - imported_all)}"
    return {"all_source_modules_imported_all": True, "source_module_count": len(expected)}


def run_checked(args: list[str], log_name: str) -> dict:
    log_dir = PROJECT / ".lake" / "verification"
    log_dir.mkdir(parents=True, exist_ok=True)
    completed = subprocess.run(args, cwd=PROJECT, encoding="utf-8", errors="replace",
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log_path = log_dir / log_name
    log_path.write_text(completed.stdout, encoding="utf-8")
    assert completed.returncode == 0, f"Command failed; see {log_path}\n{completed.stdout[-6000:]}"
    return {"command": args, "returncode": completed.returncode,
            "log": str(log_path), "log_sha256": sha256(log_path)}


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--build-no-work", action="store_true",
                        help="Require the complete normal Lake build to be current; never launch stale work")
    parser.add_argument("--audit", action="store_true")
    parser.add_argument("--audit-gated", action="store_true",
                        help="Run the full official audit under Recovery2 and the 2048 MiB Lean limit")
    options = parser.parse_args()
    if options.build:
        parser.error("Unrestricted parallel --build is disabled. Build explicit new modules through Recovery2 after parent --no-build checks, then use --build-no-work.")
    dependencies = verify_registered_packages(PROJECT, progress_fingerprint())
    fingerprint = dependencies["fingerprint"]
    result = {"recorded_at_utc": datetime.now(timezone.utc).isoformat(),
              "verified_progress_sha256": fingerprint,
              "frozen": check_frozen(), "ledger": check_ledger(),
              "imports": check_imports(dependencies["graph"]),
              "proof_dependencies": dependencies["summary"]}
    lake = os.environ.get("PAPER_PROOFS_LAKE") or str(
        Path(os.environ["USERPROFILE"]) / ".elan" / "bin" / "lake.exe"
    )
    def guarded_run(args: list[str], log_name: str) -> dict:
        nonlocal dependencies
        before = dependencies["fingerprint"]
        try:
            return run_checked(args, log_name)
        finally:
            dependencies = verify_registered_packages(PROJECT, progress_fingerprint())
            assert before == dependencies["fingerprint"], "Source, proof dependency, configuration or ledger changed during verification"

    if options.build_no_work:
        result["build"] = guarded_run([lake, "--no-build", "--wfail", "build"], "build.log")
        result["build"]["policy"] = "Full normal Lake current check; stale work fails without compiling"
    if options.audit or options.audit_gated:
        result["audit_coverage"] = check_audit_coverage()
        powershell = str(Path(os.environ.get("SystemRoot", r"C:\Windows")) /
                         "System32" / "WindowsPowerShell" / "v1.0" / "powershell.exe")
        gate = PROJECT / ".lake" / "workpads" / "ROOT_LEAN_RECOVERY_20261030.ps1"
        assert gate.is_file(), "Missing required Recovery2 gate"
        quote = lambda value: "'" + str(value).replace("'", "''") + "'"
        audit_args = ["env", "lean", "-M2048", "-DautoImplicit=false",
                      "-DwarningAsError=true", "-DElab.async=false", "AuditAll.lean"]
        command = ("[Console]::OutputEncoding=[System.Text.UTF8Encoding]::new($false); "
                   "$ErrorActionPreference='Stop'; & " + quote(gate) + " -Executable " + quote(lake) +
                   " -Arguments @(" + ",".join(quote(a) for a in audit_args) + "); exit $LASTEXITCODE")
        result["audit"] = guarded_run([powershell, "-NoProfile", "-NonInteractive", "-ExecutionPolicy",
                                       "Bypass", "-Command", command], "axioms.log")
        result["audit"]["policy"] = "Actual full formal module-origin/private audit; Recovery2/-M2048; complete frozen external-origin coverage separately byte-bound"
        assert "AXIOM_AUDIT_PASS" in (PROJECT / ".lake" / "verification" / "axioms.log").read_text(), \
            "Audit completed without its explicit pass marker"
    result["overall_goal_complete"] = False
    result["meaning"] = "Checks of current progress only; pending statements and proofs remain."
    assert fingerprint == dependencies["fingerprint"], "Project or proof dependency changed during verification"
    RECEIPT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
