"""Verify published Lean source hashes and recorded acceptance metadata.

This source-only check neither reads compiled payloads nor runs Lean. It does
not replay a kernel audit or certify a new build of the published sources.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "formalization/lean"
SUBMISSION = ROOT / "formalization/compatibility_structure_research/submission_2026-10-27"


def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def inside(root, relative):
    path = Path(relative)
    need(not path.is_absolute() and ".." not in path.parts,
         "Non-relative source path: " + str(relative))
    result = root / path
    need(result.resolve().is_relative_to(root.resolve()),
         "Source path escapes its published root: " + str(relative))
    return result


def check_file(path, expected, size=None):
    need(path.is_file(), "Missing source or metadata file: " + str(path))
    if size is not None:
        need(path.stat().st_size == size, "Source size mismatch: " + str(path))
    actual = digest(path)
    need(actual == expected, "SHA256 mismatch: " + str(path))
    return actual


def source_inventory(root):
    """Enumerate source files without entering omitted payload directories."""
    result = set()
    for parent, directories, files in os.walk(root):
        directories[:] = [name for name in directories
                          if name not in ("artifacts", "evidence", ".lake", ".git")]
        for name in files:
            if name.endswith(".lean"):
                result.add((Path(parent) / name).relative_to(root).as_posix())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true",
                        help="Compatibility flag. All runs verify source SHA256 hashes only.")
    if "--full-bytes" in sys.argv[1:]:
        parser.error("--full-bytes was removed. This repository distributes sources, not the historical compiled payload. Run the default source check or rebuild with Lean separately.")
    parser.parse_args()

    official = load(SUBMISSION / "checks/lean-formalization-receipt.json")
    fingerprints = official["verified_progress_sha256"]

    def accepted_file(relative, expected=None, size=None):
        need(relative in fingerprints, "Receipt does not bind: " + relative)
        if expected is not None:
            need(fingerprints[relative] == expected,
                 "Manifest/receipt SHA256 mismatch: " + relative)
        return check_file(inside(LEAN.parent, relative), fingerprints[relative], size)

    # Successful exits in the accepted records are historical metadata, not
    # new build/audit results produced by this check.
    work = LEAN / ".lake/workpads"
    decision_file = work / "RootPaper014_S7_ROOT_ACCEPTANCE001.json"
    check_file(decision_file, official["global_s7_acceptance"]["sha256"])
    decision = load(decision_file)
    selected_file = work / "RootPaper014.receipt_001.json"
    selected_sha = official["selected_immutable_proof_epoch"]["sha256"]
    need(selected_sha == decision["proof_receipt"]["sha256"],
         "Acceptance records select different proof receipts.")
    check_file(selected_file, selected_sha)
    selected = load(selected_file)
    need(fingerprints == selected["verified_progress_sha256"],
         "Current receipt differs from the selected accepted source fingerprints.")
    need(official["overall_goal_complete"] and official["global_s7_complete"]
         and decision["global_s7_complete"] and decision["overall_goal_complete"],
         "Historical final acceptance metadata is incomplete.")
    need(official["ledger"]["all_claims_closed"]
         and official["ledger"]["claim_count"] == decision["formal_closed"]
         == decision["original_claims"] == 253,
         "Historical registered-claim count differs from 253 closed claims.")
    need(official["build"]["returncode"] == official["audit"]["returncode"] == 0,
         "Historical receipt does not record successful build/audit exits.")
    need(official["ledger"]["main_independent_of_appendix_D"]
         and official["imports"]["main_independent_of_paid_modules"],
         "Historical main/paid dependency separation is missing.")

    expected_formal = {key.removeprefix("lean/") for key in fingerprints
                       if key == "lean/PaperProofs.lean"
                       or key.startswith("lean/PaperProofs/") and key.endswith(".lean")}
    actual_formal = {"PaperProofs/" + name for name in source_inventory(LEAN / "PaperProofs")}
    if (LEAN / "PaperProofs.lean").is_file():
        actual_formal.add("PaperProofs.lean")
    need(actual_formal == expected_formal,
         "Formal source inventory differs from the accepted receipt. Missing: "
         + str(sorted(expected_formal - actual_formal)[:8]) + "; extra: "
         + str(sorted(actual_formal - expected_formal)[:8]))
    need(len(actual_formal) == official["audit_coverage"]["source_module_count"] == 1923,
         "Formal source count differs from the historical 1,923-module inventory.")
    formal_hashes = {name: accepted_file("lean/" + name) for name in sorted(actual_formal)}
    accepted_file("lean/AuditAll.lean")
    accepted_file("compatibility_structure_research/submission_2026-10-27/DEPENDENCIES.md")

    # Product/evidence-asset records in the historical manifest remain metadata.
    # This check reads only its source, configuration and source-coverage pins.
    accepted_file("lean/ProofDeps/proof-packages.json")
    registry = load(LEAN / "ProofDeps/proof-packages.json")
    need(registry["version"] == 1 and len(registry["packages"]) == 1,
         "Unexpected published proof-package registration.")
    package = registry["packages"][0]
    need(package["name"] == "d27_proof_deps"
         and package["path"] == "ProofDeps/MainD_Original_014",
         "Unexpected frozen proof-package identity.")
    package_root = inside(LEAN, package["path"])
    manifest_relative = package["path"] + "/" + package["manifest"]
    accepted_file("lean/" + manifest_relative, package["sha256"])
    manifest = load(inside(LEAN, manifest_relative))
    need(manifest["package_name"] == package["name"], "Proof-package name mismatch.")
    coverage_relative = package["path"] + "/" + manifest["coverage"]["path"]
    accepted_file("lean/" + coverage_relative, manifest["coverage"]["sha256"])
    coverage = load(inside(LEAN, coverage_relative))

    private_paths, origins = set(), {}
    for row in manifest["sources"]:
        source = row["source"]
        relative, module = source["path"], row["module"]
        need(relative == module.replace(".", "/") + ".lean",
             "Private source/module identity mismatch: " + relative)
        need(relative not in private_paths and module not in origins,
             "Duplicate private source or module: " + relative)
        private_paths.add(relative)
        origins[module] = accepted_file("lean/" + package["path"] + "/" + relative,
                                        source["sha256"], source["bytes"])
    need(private_paths == source_inventory(package_root),
         "Private source inventory differs from its frozen manifest.")
    need(len(private_paths) == manifest["counts"]["private_sources"]
         == official["imports"]["preserved_private_modules"] == 3833,
         "Private source count differs from 3,833.")
    need(len(manifest["formal_frontier"]) == 464,
         "Historical formal source frontier differs from 464.")
    for row in manifest["formal_frontier"]:
        relative, module = row["source"], row["module"]
        need(relative == module.replace(".", "/") + ".lean",
             "Formal frontier source/module identity mismatch: " + relative)
        need(relative in formal_hashes and formal_hashes[relative] == row["sha256"],
             "Formal frontier source SHA256 mismatch: " + relative)
        need(module not in origins, "Duplicate source origin: " + module)
        origins[module] = row["sha256"]
    need(len(origins) == 4297 and origins == coverage["source_origin_sha256"],
         "Actual source hashes differ from the complete 4,297-origin coverage map.")
    need(coverage["complete_actual_origin_coverage"] and not coverage["uncovered_origins"],
         "Historical source-origin coverage is incomplete.")
    need(coverage["new_axioms"] == coverage["forbidden_dependencies"] == 0
         and set(coverage["allowed_axioms"]) == {"propext", "Classical.choice", "Quot.sound"},
         "Historical allowed-axiom metadata mismatch.")

    configuration_count = 0
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        accepted_file("lean/" + name)
        configuration_count += 1
    for row in manifest["configuration"]:
        accepted_file("lean/" + package["path"] + "/" + row["path"],
                      row["sha256"], row["bytes"])
        configuration_count += 1
    with (LEAN / "lakefile.toml").open("rb") as source:
        configuration = tomllib.load(source)
    lock = load(LEAN / "lake-manifest.json")
    need(configuration["name"] == lock["name"] == "paper_proofs",
         "Project configuration/lock identity mismatch.")
    need((LEAN / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0",
         "Lean toolchain differs from the accepted version.")
    requirements = {row["name"]: row for row in configuration["require"]}
    locked = {row["name"]: row for row in lock["packages"]}
    need(requirements["mathlib"]["rev"] == locked["mathlib"]["inputRev"] == "v4.35.0",
         "Mathlib revision differs between the configuration and lock.")
    need(requirements[package["name"]]["path"] == locked[package["name"]]["dir"]
         == package["path"], "Local dependency path differs from its lock/registration.")

    result = {"source_inventory_pass": True, "source_SHA256_pass": True,
              "formal_sources": len(actual_formal), "private_sources": len(private_paths),
              "formal_source_frontier": len(manifest["formal_frontier"]),
              "verified_source_origins": len(origins), "configuration_files_checked": configuration_count,
              "historical_paper_claims": "253/253", "historical_S7": True,
              "historical_acceptance_metadata_pass": True,
              "compiled_payload_required": False, "compiled_payload_checked": False,
              "new_Lean_runs": 0,
              "meaning": "SHA256 verification of all published formal/private sources, configuration locks and historical acceptance metadata. No compiled payload, new source build, kernel audit or new manuscript S7 acceptance was performed."}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("Source review failed: " + str(error), file=sys.stderr)
        raise SystemExit(1)
