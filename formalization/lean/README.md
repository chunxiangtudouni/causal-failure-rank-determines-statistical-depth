# Formal Lean project

This is the unchanged Lean project layout inside the accompanying GitHub artifact. Start with the [repository README](../../README.md), [evaluation guide](../../ARTIFACT.md), and [paper-to-Lean map](../../docs/paper-to-lean.md).

`PaperProofs.lean` is the public entry point. `PaperProofs/` contains the topic-organized formalization; `ProofDeps/MainD_Original_014/` retains every proof-dependency source with its original module identity. This repository distributes source files and dependency locks, without precompiled dependency packages. Follow the repository evaluation guide to prepare a unified source build.

Lean is pinned to 4.35.0 and dependencies are locked. `AuditAll.lean` is the formal-owner/private axiom audit entry point. The scripts under this directory are retained historical acceptance implementations, including the original compiled-product guard. The legacy verifier writes a receipt and expects the historical inputs. Use the repository's source-check and source-build commands instead.

The accepted snapshot closes all 253 registered claims and includes the completed S7 correspondence review. Current theorem numbering and principal declarations are listed in the [current manuscript correspondence](../../docs/current-paper-correspondence.md).
