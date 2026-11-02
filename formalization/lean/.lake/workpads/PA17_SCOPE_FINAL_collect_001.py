"""Read-only source fingerprints for the bounded A-sector scope report."""
from pathlib import Path
import hashlib
import json
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[3]
LEAN = ROOT / "lean"
PAD = LEAN / ".lake/workpads"

def record(path):
    data = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}

names = [
    "Game", "UsedGame", "Rank", "Capacity", "LaminarTree",
    "LaminarExtension", "IndexedNormalize", "IndexedDescent",
    "IndexedIntersectionRAM", "RawClosureRAM", "IndexedAncestors",
    "LaminarTable", "IndexedTable", "IndexedQuery", "LaminarRankExtraction",
    "IndexedStaticMetadata", "IndexedUsedCounts", "ControllerBoundaries",
    "RawTreePreprocessingA06Closure", "AlgorithmClaims",
    "PA17_FullGivenTree_049", "PA17_WrappedNatRAM_038c",
    "PA17_PackedPhase_045f", "PA17_UniformGenerator_035ai",
    "PA17_QueryCounts_008", "PA17_GeneratorStatic_048d",
]
source = [record(LEAN / "PaperProofs/Structure" / f"{name}.lean") for name in names]
section = ROOT / "compatibility_structure_research/submission_2026-10-27/manuscript/sections"
expected = {
    "laminar.tex": "34264488235813d5edf4f3f9ee7b507874d57b03910289742a27266de65a5d37",
    "laminar-proofs.tex": "e4349779cd119f9389649e77a9d614996e89382910940d0a6b0b24ee8ecbcb0b",
}
manuscript = []
for name, frozen in expected.items():
    rec = record(section / name)
    rec.update(frozen_sha256=frozen, matches_frozen=rec["sha256"] == frozen)
    manuscript.append(rec)
acceptance = json.loads((PAD / "RootBatch004.acceptance.json").read_text(encoding="utf-8-sig"))
build = (PAD / "RootBatch004.build.log").read_text(encoding="utf-8-sig")
audit = (PAD / "RootBatch004.audit.log").read_text(encoding="utf-8-sig")
ledger = ROOT / "compatibility_structure_research/submission_2026-10-27/DEPENDENCIES.md"
ledger_text = ledger.read_text(encoding="utf-8-sig")
evidence = {
    "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "A01-A18 incl subIDs and complete original A17; not global S7",
    "method": "read-only source and existing acceptance evidence; no fresh compiler run",
    "formal_sources": source,
    "manuscript": manuscript,
    "manuscript_all_match_frozen": all(x["matches_frozen"] for x in manuscript),
    "existing_coordinator_acceptance": {
        "original_A17_accepted": "A17" in acceptance["accepted_original_targets"],
        "receipt_sha256": acceptance["receipt_sha256"],
        "receipt_time": acceptance["receipt_time"],
        "final_manuscript_acceptance_complete": acceptance["final_manuscript_acceptance_complete"],
        "build_success_lines": [x for x in build.splitlines() if "Build completed successfully" in x],
        "axiom_audit_lines": [x for x in audit.splitlines() if "AXIOM_AUDIT_PASS" in x],
        "ledger_A17_lines": [{"line": i, "text": x} for i, x in enumerate(ledger_text.splitlines(), 1)
                             if x.startswith("| A17 |")],
    },
    "bound_files": [record(path) for path in [
        ledger, PAD / "RootBatch004.acceptance.json", PAD / "RootScopeAcceptance_004.md",
        PAD / "RootBatch004.build.log", PAD / "RootBatch004.audit.log",
        PAD / "PA17_A17_SCOPE_REVIEW_050.md", PAD / "PA17_HANDOFF_011.md",
        PAD / "PA17_SCOPE_FINAL_001.md", Path(__file__).resolve(),
    ]],
}
output = PAD / "PA17_SCOPE_FINAL_evidence_001.json"
if output.exists():
    raise SystemExit("immutable output already exists")
output.write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"formal_source_count": len(source),
                  "manuscript_all_match_frozen": evidence["manuscript_all_match_frozen"],
                  "original_A17_accepted": evidence["existing_coordinator_acceptance"]["original_A17_accepted"],
                  "evidence": record(output)}, ensure_ascii=False))
