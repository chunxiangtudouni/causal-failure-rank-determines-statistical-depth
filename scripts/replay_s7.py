"""Replay the frozen S7 checker with explicit, recorded local file locators.

Original evidence is never changed. Derived copies only replace historical
caller/log locations and the corresponding receipt/matrix hash references.
The frozen manuscript is supplied externally and is never copied into this
repository. An ephemeral filesystem view supplies the checker's original
sibling-directory layout without changing its source.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

sys.stdout.reconfigure(encoding="utf-8")
ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formalization/lean"
WORK = LEAN / ".lake/workpads"
SUBMISSION = ROOT / "formalization/compatibility_structure_research/submission_2026-10-27"
load = lambda p: json.loads(p.read_text(encoding="utf-8-sig"))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def verify_external_submission(directory, matrix):
    directory = directory.expanduser().resolve()
    if directory.is_relative_to(ROOT):
        raise ValueError("--submission-dir must be outside this Lean repository.")
    baseline_file = SUBMISSION / "checks/lean-baseline.json"
    if sha(baseline_file) != matrix["source_baseline"]["sha256"]:
        raise ValueError("The preserved frozen-manuscript baseline does not match the accepted matrix.")
    baseline = load(baseline_file)
    canonical = "".join(name + " " + baseline["source_hashes"][name] + "\n"
                        for name in sorted(baseline["source_hashes"]))
    if hashlib.sha256(canonical.encode()).hexdigest() != matrix["source_baseline"]["source_manifest_sha256"]:
        raise ValueError("The frozen source manifest does not match the accepted matrix.")
    verified = []
    expected = [("manuscript/" + name, digest)
                for name, digest in sorted(baseline["source_hashes"].items())]
    if baseline["pdf_sha256"] != matrix["source_baseline"]["pdf_sha256"]:
        raise ValueError("The frozen PDF baseline does not match the accepted matrix.")
    expected.append((baseline["pdf"], baseline["pdf_sha256"]))
    for relative, digest in expected:
        file = directory / relative
        if not file.is_file():
            raise ValueError("External frozen manuscript file missing: " + str(file))
        if sha(file) != digest:
            raise ValueError("External frozen manuscript SHA256 mismatch: " + str(file))
        verified.append({"path": relative, "sha256": digest})
    return directory, {"submission_directory": str(directory),
                       "baseline_sha256": sha(baseline_file),
                       "verified_files": verified, "verified_before_checker": True,
                       "manuscript_copied_into_repository": False}


def shadow_project(directory, submission):
    """Expose read-only inputs at the unchanged checker's fixed relative paths."""
    lean = directory / "formalization/lean"
    lean.mkdir(parents=True)
    for source in LEAN.iterdir():
        if source.name != "ProofDeps":
            (lean / source.name).symlink_to(source, target_is_directory=source.is_dir())
    # The checker requires registered source realpaths to stay inside its Lean
    # root. Real directories and hard-linked files preserve that containment.
    # Products/evidence are not read by this checker; the separate frozen byte
    # guard remains the operation that verifies that payload.
    for parent, directories, files in os.walk(LEAN / "ProofDeps"):
        directories[:] = [name for name in directories
                          if name not in ("artifacts", "evidence", ".lake", ".git")]
        source_parent = Path(parent)
        target_parent = lean / "ProofDeps" / source_parent.relative_to(LEAN / "ProofDeps")
        target_parent.mkdir(parents=True, exist_ok=True)
        for name in files:
            source, target = source_parent / name, target_parent / name
            try:
                os.link(source, target)
            except OSError:
                shutil.copy2(source, target)
    paper = lean.parent / "compatibility_structure_research/submission_2026-10-27"
    paper.mkdir(parents=True)
    for name in ("checks", "DEPENDENCIES.md"):
        source = SUBMISSION / name
        (paper / name).symlink_to(source, target_is_directory=source.is_dir())
    for name in ("manuscript", "output"):
        (paper / name).symlink_to(submission / name, target_is_directory=True)
    return lean


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--submission-dir", type=Path,
                        help="External frozen submission directory containing manuscript/ and output/pdf/submission-paper.pdf.")
    args = parser.parse_args()
    if args.submission_dir is None:
        parser.error("The Lean repository does not bundle a manuscript. Supply --submission-dir /path/to/frozen-submission; both its original sources and PDF are required.")
    if shutil.which("rg") is None:
        parser.error("Install ripgrep and put rg on PATH before replaying S7.")
    original_matrix = WORK / "RootPaper014_S7_Final002/RootPaper014_S7_014_MATRIX.json"
    original_manifest = WORK / "RootPaper014_S7_Final002/RootPaper014_S7_014_MANIFEST.json"
    original_receipt = WORK / "RootPaper014.receipt_001.json"
    locator_map = load(ROOT / "artifacts/locator-map.json")
    matrix, manifest, receipt = map(load, [original_matrix, original_manifest, original_receipt])
    submission, manuscript_check = verify_external_submission(args.submission_dir, matrix)
    original_claims = copy.deepcopy(matrix["claim_rows"])
    original_declarations = copy.deepcopy(matrix["formal_declarations"])
    original_fp = copy.deepcopy(receipt["verified_progress_sha256"])
    output_parent = LEAN / ".review-runs"
    output_parent.mkdir(exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix="s7-", dir=output_parent))
    edits = []

    def local_locator(old, expected):
        entry = locator_map["locators"].get(old)
        if entry is None:
            candidate = Path(old)
            if candidate.is_absolute() or (len(old) > 1 and old[1] == ":"):
                raise ValueError("Unmapped historical path: " + old)
            result = old
        else:
            assert entry["sha256"] == expected
            result = entry["local_relative_to_lean"]
            edits.append({"from": old, "to": result, "sha256": expected})
        file = (LEAN / result).resolve()
        if not file.is_relative_to(ROOT) or sha(file) != expected:
            raise ValueError("Local evidence mismatch: " + result)
        return result

    for slot in matrix["deferred_full_goal_specs"].values():
        evidence = slot["ordinary_public_original_type_evidence"]
        for field, hash_field in [("source_path", "source_sha256"), ("log_path", "log_sha256")]:
            evidence[field] = local_locator(evidence[field], evidence[hash_field])
    for kind, filename in [("build", "build.log"), ("audit", "axioms.log")]:
        old = receipt[kind]["log"]
        new = ".lake/workpads/RootPaper014_accepted_logs/" + filename
        expected = receipt[kind]["log_sha256"]
        archived_log = LEAN / new
        if sha(archived_log) != expected:
            raise ValueError("Archived log SHA256 mismatch: " + new)
        legacy = ".lake/verification/" + filename
        entries = [record for record in manifest["package"] if record["path"] == legacy]
        if (len(entries) != 1 or entries[0]["sha256"] != expected
                or entries[0]["bytes"] != archived_log.stat().st_size):
            raise ValueError("Frozen manifest log binding mismatch: " + legacy)
        entries[0]["path"] = new
        receipt[kind]["log"] = new
        edits.append({"from": old, "to": new, "sha256": expected})
        edits.append({"from": legacy, "to": new, "sha256": expected, "scope": "manifest.package"})
    assert receipt["verified_progress_sha256"] == original_fp
    assert matrix["claim_rows"] == original_claims and matrix["formal_declarations"] == original_declarations

    def save(name, value):
        p = output / name
        p.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        return p

    manuscript_file = save("external-manuscript-verification.json", manuscript_check)
    receipt_file = save("proof-receipt.locators.json", receipt)
    matrix["accepted_receipt"]["path"] = receipt_file.relative_to(LEAN).as_posix()
    matrix["accepted_receipt"]["sha256"] = sha(receipt_file)
    matrix_file = save("matrix.locators.json", matrix)
    for p in [receipt_file, matrix_file, manuscript_file]:
        manifest["package"].append({"path": p.relative_to(LEAN).as_posix(), "sha256": sha(p)})
    manifest["portable_locator_derivation"] = {
        "original_matrix_sha256": sha(original_matrix), "original_manifest_sha256": sha(original_manifest),
        "original_receipt_sha256": sha(original_receipt), "file_locator_edits": edits,
        "claim_rows_and_declaration_text_unchanged": True, "verified_fingerprint_unchanged": True,
        "external_manuscript_verification": manuscript_file.relative_to(LEAN).as_posix(),
        "manuscript_locator_method": "Temporary sibling-directory view; unchanged checker source and frozen baseline."}
    manifest_file = save("manifest.locators.json", manifest)
    command = [sys.executable, str(WORK / "PStar_S7_GLOBAL_verify_003.py"),
               "--matrix", str(matrix_file), "--manifest", str(manifest_file),
               "--census", str(WORK / "PStar_S7_GLOBAL_CENSUS_001.json"), "--receipt", str(receipt_file)]
    with tempfile.TemporaryDirectory(prefix="lean-s7-locators-") as temporary:
        shadow_lean = shadow_project(Path(temporary), submission)
        completed = subprocess.run(command, cwd=shadow_lean, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / "verify.log").write_bytes(completed.stdout)
    report = {"actual_exit": completed.returncode, "command": command, "derived_directory": str(output),
              "historical_evidence_unchanged": True, "file_locator_edits": edits, "new_Lean_runs": 0,
              "external_submission_verification": manuscript_check,
              "checker_sha256": sha(WORK / "PStar_S7_GLOBAL_verify_003.py"),
              "manuscript_copied_into_repository": False,
              "meaning": "Portable locator replay of the existing S7 checker with SHA256-verified external frozen sources/PDF; not a fresh source build or historical collector replay."}
    save("replay-report.json", report)
    print(completed.stdout.decode("utf-8-sig"), end="")
    print("Portable replay record: " + str(output / "replay-report.json"))
    raise SystemExit(completed.returncode)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, AssertionError) as error:
        print("S7 replay could not run: " + (str(error) or "evidence consistency check failed"), file=sys.stderr)
        raise SystemExit(2)
