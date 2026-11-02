# Causal Failure Rank Determines Statistical Depth

Lean 4 formalization accompanying **Causal Failure Rank Determines Statistical Depth**, by **Zhaochen Zang, Zhongnian Li, Ziyue Jin, and Xinzheng Xu**.

School of Computer Science and Technology / School of Artificial Intelligence, China University of Mining and Technology. Corresponding author: [Zhongnian Li](mailto:zhongnianli@gmail.com).

[Paper-to-Lean correspondence](docs/current-paper-correspondence.md) · [Artifact guide](ARTIFACT.md) · [中文说明](README.zh-CN.md)

The development connects causal allocation games to compact algorithms and statistical price laws for reliable sequential execution. It includes the laminar safety representation, the fixed-graph price law, retained-allocation and star results, executable controller guarantees, and the independent paid extension. The `RootPaper014` formalization snapshot closes **253/253 registered claims** and includes the completed **S7 manuscript correspondence review** dated 2 November 2026.

## Read the paper and proofs

Use the [correspondence table](docs/current-paper-correspondence.md) to locate each principal result in Lean. The [full claim index](docs/paper-to-lean.md) preserves all 253 registered IDs and the original source anchors. [PaperProofs.lean](formalization/lean/PaperProofs.lean) is the public library entry point. This repository distributes the formalization, its dependencies and checking records; manuscript files are distributed separately.

The controller implementation results close at the following declarations.

| Result | Module | Closing declaration |
|---|---|---|
| Rational preparation and native-controller computation | [B23PaperClosure.lean](formalization/lean/PaperProofs/Common/B23PaperClosure.lean) | `PaperProofs.Common.Native.B23PaperClosure.full_paper_claims` |
| Compact leading-price controller | [L01PaperClosure.lean](formalization/lean/PaperProofs/Structure/L01PaperClosure.lean) | `PaperProofs.Structure.LaminarTree.L01PaperClosure.full_paper_claims` |

Both prove their complete paper-level `FullPaperClaims` specifications. Computation bounds retain the stated input-bit and numerical-quota dependence. The exact interfaces and their resource conditions are linked in the correspondence table.

The historical S7 acceptance is bound to a frozen manuscript by its source and PDF hashes. The acceptance records remain intact. The [current correspondence table](docs/current-paper-correspondence.md) maps the reorganized paper to those claims using stable labels and actual Lean declarations.

## Check the formalization snapshot

The source inventory check requires Python 3.11 or later.

```console
python scripts/review_snapshot.py
```

This command checks source hashes and historical acceptance metadata without compiling Lean proofs. The [artifact guide](ARTIFACT.md) explains source rebuilding and optional S7 replay when the separate hash-matching frozen manuscript is available. S7 replay also requires [`ripgrep`](https://github.com/BurntSushi/ripgrep), with `rg` on `PATH`.

## Build from source

The repository includes all 3,833 proof-dependency sources and the main formalization. It does not distribute precompiled dependency packages, and Git LFS is not required. Prepare the unified source workspace from the repository root:

```console
python scripts/build_from_source.py --prepare-only
```

The workspace combines the main library and local proof sources under their original module names so that Lake can build their interleaved dependencies. See [ARTIFACT.md](ARTIFACT.md) for the pinned toolchain, build command, resource controls, and axiom-audit entry point.

The project pins Lean `v4.35.0`, Mathlib `v4.35.0`, and the resolved transitive dependencies. For interactive reading with Lean's VS Code extension, open the generated source-build workspace after preparing its dependencies.

## Repository layout

```text
docs/current-paper-correspondence.md
                                  current statements and Lean entry points
docs/paper-to-lean.md              complete original 253-claim index
ARTIFACT.md                       evaluation and reproduction instructions
scripts/                          source checks and source-build preparation
artifacts/                        historical evidence location map
formalization/
  lean/
    PaperProofs.lean               public import entry point
    PaperProofs/                   structural and statistical development
    ProofDeps/MainD_Original_014/  proof-dependency sources and inventories
    AuditAll.lean                  axiom audit entry point
    lean-toolchain                exact Lean version
    lakefile.toml                  project options and dependencies
    lake-manifest.json            dependency lock
    .lake/workpads/                curated acceptance evidence
  compatibility_structure_research/submission_2026-10-27/
                                  original claim ledger and acceptance metadata
```

The internal directory relationships preserve the paths and hashes used by the acceptance metadata. The ignore rules exclude generated build workspaces, compiled products, downloaded Mathlib checkouts, and manuscript files.

## Trust and scope

The archived axiom audit covers 1,923 formal modules and 48,349 declarations. Its allowed axioms are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The historical proof-dependency records cover 4,297 source origins and 39 owner audits. The [artifact guide](ARTIFACT.md) distinguishes those archived results from source-hash checking, correspondence replay, and a new kernel build.

## Citation and license

Citation metadata is available in [CITATION.cff](CITATION.cff). The repository is [chunxiangtudouni/causal-failure-rank-determines-statistical-depth](https://github.com/chunxiangtudouni/causal-failure-rank-determines-statistical-depth).

No project license has been granted in this repository.
