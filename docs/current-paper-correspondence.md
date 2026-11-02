# Current manuscript and accepted formalization

The current manuscript is **Causal Failure Rank Determines Statistical Depth**, by **Zhaochen Zang, Zhongnian Li, Ziyue Jin, and Xinzheng Xu**. All authors share the affiliation **School of Computer Science and Technology / School of Artificial Intelligence, China University of Mining and Technology**. Zhongnian Li is the corresponding author.

This is a Lean formalization repository. It does not distribute manuscript PDFs or TeX sources. The table below records the sixth draft's compiled cross-references as of 2 November 2026. Manuscript labels and source locations are provenance metadata for the statements, not links to manuscript files hosted here.

## Relationship to the frozen manuscript

The historical `RootPaper014` acceptance covers 253 registered claims and the S7 correspondence for a frozen manuscript titled **Hierarchical Correction Rights and Reliable Sequential Execution: Causal Safety and Statistical Depth**. That manuscript is archived separately, outside this repository. The retained claim ledger and acceptance metadata preserve its historical identifiers and source anchors. Lean proof sources, proof dependencies and acceptance evidence retain their original identities.

The current paper reorganizes the exposition. It presents the general fixed-graph price law before the laminar computation theorem, brings consequences together in Section 4, and adds a separate formalization appendix. The following crosswalk locates the corresponding registered claims and their actual Lean declarations. It is a navigation aid for the editorial revision. It does not constitute a new line-by-line S7 acceptance of the sixth draft, and the historical acceptance remains bound to the frozen manuscript.

## Main statement crosswalk

| Current statement and section | Stable label | Frozen statement | Registered claim ID | Lean closing declaration |
|---|---|---|---|---|
| Theorem 3.1, Section 3.1, Fixed-graph price law | `thm:price` | `Theorem 3; Section 4; sections/prices.tex:40` | B24 | [`PaperProofs.Common.StatisticalInput.fixedGraphPriceLaw`](../formalization/lean/PaperProofs/Common/HealthyPriceClosure.lean#L23) |
| Theorem 3.2, Section 3.2, Common-tree safety representation | `thm:laminar` | `Theorem 2; Section 3; sections/laminar.tex:25` | A19 | [`PaperProofs.Structure.LaminarTree.CompactControllerA19Closure.fullClaims`](../formalization/lean/PaperProofs/Structure/CompactControllerA19Closure.lean#L14) |
| Corollary 4.1, Section 4.1, A compact leading-price controller | `cor:computable-price` | `Corollary 5; Section 4; sections/prices.tex:128` | L01 | [`PaperProofs.Structure.LaminarTree.L01PaperClosure.full_paper_claims`](../formalization/lean/PaperProofs/Structure/L01PaperClosure.lean#L11) |
| Corollary 4.2, Section 4.1, Retained-port girth and circuit heads | `thm:retained` | `Corollary 4; Section 4; sections/prices.tex:108` | R05 | [`RootRetainedComplete.retainedPriceClaims`](../formalization/lean/PaperProofs/Retained/RootRetainedComplete_001.lean#L27) |
| Proposition 4.3, Section 4.2, Three prices on the same star | `prop:star` | `Proposition 1; Section 1; sections/introduction.tex:41` | C12 | [`PaperProofs.Star.PStarCompletePrice043.c12Claims`](../formalization/lean/PaperProofs/Star/PStar_CompletePrice_043.lean#L20) |

The price law and the laminar representation have different scopes. `B24` concerns fixed compatibility graphs under the statistical model and original resource qualification. `A19` supplies compact causal allocation for laminar eligibility. `L01` connects that compact implementation to the price controller. The retained result uses its matching-state argument, and the star comparison includes an independent late-report information bound.

## Computation and independent paid extension

The registered claim IDs also distinguish implementation guarantees from the principal mathematical statements.

| Current location | Registered claim ID | Lean closing declaration |
|---|---|---|
| Rational preparation and native-controller computation in Appendix B.5 and Appendix E | B23 | [`PaperProofs.Common.Native.B23PaperClosure.full_paper_claims`](../formalization/lean/PaperProofs/Common/B23PaperClosure.lean#L12) |
| Theorem D.1 (`thm:paid:separation`) | D29 | [`PDLower.nativeSeparationClaims`](../formalization/lean/PaperProofs/Paid/PDLower_NativeFinal_001.lean#L15) |
| Corollary D.2 (`cor:fixed-pool-price`) | D36 | [`PDLower.fixedPoolNativePriceClaims`](../formalization/lean/PaperProofs/Paid/PDLower_PriceFinal_001.lean#L15) |
| The implementation argument for Theorem D.10 | D25 | [`PDROC.calibratedImplementationClaims`](../formalization/lean/PaperProofs/Paid/PDROC_CalibratedAssembly_004.lean#L18) |
| Theorem D.10 (`thm:paid:native-eight`) | D26 | [`PDROC.calibratedNativeEightClaims`](../formalization/lean/PaperProofs/Paid/PDROC_CalibratedAssembly_004.lean#L26) |
| Explicit computation and bit lengths in Appendix D | D27 | [`PDCompute.computationalClaims`](../formalization/lean/PaperProofs/Paid/PDCompute_Complete_001.lean#L12) |

For `B23` and `L01`, the closing declarations consume their respective `FullPaperClaims` specifications. Their exact types are defined in [the B23 interface](../formalization/lean/ProofDeps/MainD_Original_014/RootPaper_B23_Interface007.lean#L18) and [the L01 interface](../formalization/lean/ProofDeps/MainD_Original_014/RootPaper_L01_Interface006.lean#L17). The historical Bool/ISA specifications and the old `CompactPrice.FullClaims` declaration are preserved as distinct specifications. The paper-level closing theorems should not be read as proofs of those stronger historical targets.

The computation bounds retain the stated input-bit and numerical-quota dependence. They do not assert polynomial dependence on the logarithm of an arbitrary numerical quota. Appendix D retains its separate shared-pool and actual-payment assumptions.

## Full claim index and checking

The [complete paper-to-Lean index](paper-to-lean.md) preserves all 253 original IDs, frozen source anchors, definitions, assumptions, dependencies, and formal bindings. Use it when an intermediate lemma or model condition is needed. The [public library entry point](../formalization/lean/PaperProofs.lean) imports the closing modules.

The [artifact guide](../ARTIFACT.md) distinguishes source-hash checks, historical manuscript-correspondence evidence, and a new Lean source rebuild. Any replay requiring the frozen manuscript must use the separately held original sources and PDF. This crosswalk was prepared by reading compiled manuscript labels and existing Lean declarations. No Lean proof was rebuilt to create it.
