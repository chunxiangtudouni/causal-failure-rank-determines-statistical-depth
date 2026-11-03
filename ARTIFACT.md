# Formalization review and reproduction

This Lean source repository accompanies **Causal Failure Rank Determines Statistical Depth** by Zhaochen Zang, Zhongnian Li, Ziyue Jin and Xinzheng Xu. The authors are affiliated with the School of Computer Science and Technology / School of Artificial Intelligence, China University of Mining and Technology. Zhongnian Li is the corresponding author, at zhongnianli@gmail.com.

The [public repository](https://github.com/chunxiangtudouni/causal-failure-rank-determines-statistical-depth) provides formal sources, locked dependency versions and historical acceptance records. The [current-paper correspondence](docs/current-paper-correspondence.md) navigates from the paper's results to formal statements. The [complete claim index](docs/paper-to-lean.md) retains all 253 original IDs and historical manuscript anchors.

## 1. Check source integrity

From the repository root, with Python 3.11 or later:

```console
python scripts/review_snapshot.py
```

This verifies the recorded source SHA256 values and historical acceptance metadata. The inventory includes 1,923 formal source files and 3,833 private source files; historical coverage records identify 4,297 source origins. The check needs no Lean compiler or compiled dependency products. It verifies source integrity and recorded acceptance, rather than running the proof kernel again.

## 2. Prepare the unified source workspace

```console
python scripts/build_from_source.py --prepare-only
```

Preparation creates the ignored `.source-build/` workspace, copies source bytes without changing the accepted source files, and checks the internal module/import graph. It generates a single Lake library containing 5,758 modules, including the audit entry points. The generated dependency lock retains the exact external Git revisions from the original root manifest.

The unified view is needed because private sources also import formal `PaperProofs` modules. Compiling the private package in isolation before the formal package would not respect those dependencies. The helper instead preserves module identities in one source tree and lets Lake follow the import graph. The original private-package configuration and source inventory remain unchanged.

Preparation is the script's default mode and requires neither Lean nor network access. Its byte-copy and internal dependency checks have passed. This result does not check external-module availability or elaborate the generated Lake configuration; those are checked during an actual build.

## 3. Build from source explicitly

Install Elan and the pinned `leanprover/lean4:v4.35.0` toolchain, then run from the repository root:

```console
python scripts/build_from_source.py --build
```

The helper prepares the same workspace, runs Mathlib's `lake exe cache get`, and then invokes:

```console
lake --wfail build ProofSources:leanArts
```

These Lake commands run inside `.source-build/`. The generated library includes `PaperProofs.lean`, the formal and private modules, and `Audit.lean`/`AuditAll.lean`. Mathlib is locked to revision `56a005855ea17e0b0958f73ec801ae140b0a1679`; the transitive dependency revisions are also preserved. The helper checks that Lake has not changed those dependency revisions after each command.

To skip downloading the Mathlib cache and compile missing dependencies instead:

```console
python scripts/build_from_source.py --build --no-mathlib-cache
```

The `--threads 1` or `--threads 2` option sets `LEAN_NUM_THREADS`, with 2 as the default. This controls Lean runtime threads. The `--memory-mb` option sets Lean's per-process memory threshold, with 4096 as the default. Adjust it to fit the build and available memory. The generated configuration preserves `Elab.async=false`, `autoImplicit=false` and warnings as errors. The historical execution used at most two compiler slots.

A source rebuild starting from a clean checkout completed on macOS arm64 with Lean v4.35.0 on 3 November 2026. All 5,758 project modules compiled. The formal-owner `AuditAll` run checked 47,803 declarations across 1,923 formal modules and reported zero new axioms and zero forbidden dependencies. The audit uses the archived private-owner coverage records described below.

## 4. Read the historical proof and axiom evidence

The accepted proof epoch is `RootPaper014`. The historical ledger records 253 closed claims. Its S7 manuscript review covered 22 explicit environments and 131 source dispositions. The original claim ledger and acceptance metadata remain under `formalization/compatibility_structure_research/submission_2026-10-27/`.

The historical formal audit covered 48,349 declarations in 1,923 modules, with zero new axioms and zero forbidden dependencies. Its allowed axioms were `propext`, `Classical.choice` and `Quot.sound`. Private-source coverage and owner-audit reports are retained as historical records. Their product inventories record the original acceptance context, rather than asserting that this source publication contains the old generated products.

`AuditAll.lean` is the formal-owner/private audit entry point. Registered non-exposed `FullPaperClaims` exports were classified by their actual module owners, and their definition bodies and private `rfl` bindings were audited without adding them to the axiom allowlist. Read complete Lean types, assumptions, closing declarations and the theorem index when assessing the correspondence. The current-paper mapping provides result navigation; historical S7 acceptance is not a new line-by-line acceptance of the revised exposition.

## 5. Optional frozen-manuscript correspondence replay

A complete line-by-line S7 replay additionally requires the corresponding frozen submission directory supplied separately, containing `manuscript/` and `output/pdf/submission-paper.pdf` with the accepted hashes. Install `ripgrep`, ensure that `rg` is on `PATH`, and pass that directory explicitly:

```console
python scripts/replay_s7.py --submission-dir /path/to/frozen/submission
```

This optional operation checks the original manuscript correspondence rather than compiling Lean proofs. Machine-local paths are handled through separate derived locator records without overwriting accepted matrices or receipts. Derived results go to the ignored `formalization/lean/.review-runs/` directory. Routine source verification does not require the manuscript or PDF.

The historical S7 checker's generic `global_s7_complete` flag is a readiness interface; the archived Root semantic acceptance records the final historical decision. Checks that require original compiled products or original product-bound evidence are not default checks of this source publication.

## 6. Legacy verifier behavior

The retained `formalization/lean/scripts/verify_formalization.py` is an acceptance implementation. Calling its `main`, even without flags, writes a progress receipt and sets its generic completion flag false. Use the repository-level source checker for routine verification.

The original frozen-package guard expects historical product and evidence bytes. A source rebuild must not silently replace those expectations with newly generated hashes. Keep fresh build and audit results separate from the accepted historical records.
