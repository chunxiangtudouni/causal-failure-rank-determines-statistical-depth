# PA17 A01-A18 sector: final read-only source/scope review001

2026-10-30. This is the assigned A-sector contribution to S7, not a global
S7 acceptance. No manuscript, formal Lean source, master ledger or acceptance
receipt was modified. No new Lean build/test is claimed by this report.
The accompanying evidence001.json records the current read-only fingerprints.

Within the reviewed original A01-A18/A17 statements, implementation interfaces
and cited proof chains, no material quantifier shrinkage or unpaid oracle was
identified. The existing formal acceptance of A17 is independently evidenced by
RootBatch004.acceptance.json and its archived whole-build/axiom logs. This source
review neither replaces those kernel checks nor closes any other original ID.

## Frozen manuscript and original semantic layer

The theorem is the frozen laminar.tex:24-49 with laminar-proofs.tex, not a new
claim inventory. Its positive-q given-tree bounds distinguish capacity-storage
BITS from ordinary indexing words. The original explicit-incidence construction
bound and q=0 boundary are separate assertions. Every existing A01-A18 sub-ID
is retained; no component or conversation adds another completed original ID.

| IDs | Reviewed source and original obligation | Scope finding |
|---|---|---|
| A01-A02 | Game.Plan/Play/Safe, safe_cons_succ_iff, budget_recurrence | Safety is existential causal Plan followed by universal actual plays; recurrence is proved from that independent game. Correct/error continuations differ, selected tool is observed before later adversarial choices, and first failure stops. No preselected error subset or DP-defined safety replaces the game. |
| A03-A05 | Game.errorRank/safe_iff_lt_errorRank, finite/no-tools/terminal bounds; UsedGame bridges | Rank is minimum unsafe budget or infinity, finite bound derives from actual play, and used D corresponds to remaining universe minus D with actual insertion/erasure. No finite-only rank qualification. |
| A06/a-d | LaminarTree/node caches, RawTreePreprocessingA06Closure.fullClaims | Universal original raw-incidence machine target has a no-parameter closure. all_prefix_safe quantifies every Nat clock, including after real HALT; accepting laminar and rejecting nonlaminar branches use the same fixed program. Original q>0 only; no caller tree/card/trace/prefix-safety witness. Universe plus singletons and dedup preserve repeated/empty stages, order and tools absent from every stage. |
| A07-A08 | Capacity.capacityFamily, downward/free/zero and vector_ne_void | Family always contains empty used set; with singleton coverage zero vector denotes exactly that set and is distinct from VOID. Empty capacity family is not silently encoded as a zero vector. |
| A09/a-d | IndexedNormalize, IndexedIntersectionRAM.prepared_normalization_correct_run | Bottom-up normalization preserves the original family under its original bounded-vector hypotheses. The real 176t primitive trace includes encoded HALT. Indexed host operations are semantic code, not assumed constant-time array mutation; static preparation/shared loading and finite words are charged by A06/A17. |
| A10/a-b | LaminarExtension.extension_iff_ancestorSlack; IndexedDescent | Original normalized and feasible-used hypotheses are retained. Actual cached descent follows real first-hit children; visited nodes plus child probes <=2t. This local bound does not include constructing counts/metadata or the full machine. |
| A11/a-e, A12 | ancestor/raw closure and intersection; CapacityEntry denote | Raw extension scans actual raw support; intersection performs coordinate min then normalization. Empty/VOID branches and zero ancestor are exact. The 414t raw closure /239t extension /274t intersection statements are local Nat-address components; caller lookup results or output bits are not supplied for free. |
| A13/a-e | LaminarTable/IndexedTable, IndexedCellRAM | All suffix/budget rows are stored and represent the independently defined SafeUsed. q+2 budgets include 0 and q+1; q=0 uses the original direct branch/empty cache. 523t cell trace is not itself the full table or fixed uniform finite-word implementation. |
| A14 | LaminarRankExtraction.built_extractedRank_eq_errorRank | Real finite membership scan through1..q+1 returns first unsafe budget; finite-rank bound justifies no first false = infinity. No Safe decision oracle or rank answer input. |
| A15/a-b | IndexedQuery actual storedPositiveRow, stored_query_* and table plan extraction | good/bad/current rank and none/some maximizer match the independent game. Bad-budget tests are antitone; actual first-false scan selects an original cached slack descent; all-true case gives infinite successor. Empty eligibility, arbitrary used sets, q=0 and N=0 remain. Exponentially expanded Plan is a semantic extraction, not the compact controller implementation. |
| A16/a | Rank/errorRank_cons, maximizing/infinite child; genericRank | Recurrence/min/good>=bad/maximizer are derived from causal semantics. Generic finite graph rank can be exponential; it is not substituted for the polynomial laminar method. |
| A18 | ControllerBoundaries | Deleting initially unavailable tools preserves laminarity and agrees exactly with union into used. Singleton cache retains even never-appearing tools. Nonterminal infinite rank returns an actual compatible unused tool with infinite successor. q=0 active rank1/bad0/toolnone and terminal rank infinity are independent semantic boundary results. |

## A17 full original implementation and quantifiers

Formal AlgorithmClaims.FullGivenTreeClaims is the original existential:
positive constant, positive wordFactor and ONE implementation chosen before
all q/full inputs, satisfying both NatRAMImplementationClaims and
PackedImplementationClaims. Formal PA17FullGivenTree049.fullGivenTreeClaims
has no arguments and constructs this exact type, with constant2^58,
wordFactor32 and the same PA17WrappedNatRAM038a implementation on both sides.
It is the formally integrated target accepted in RootBatch004.

| Original part | Source-level verification |
|---|---|
| Inputs and finite widths | Positive q is the original A17 given-tree domain, not a new condition; N=0 is allowed. Width is32*clog2(N+q+2), not a fixed32bit machine. givenTreeROM contains raw stage/node incidence plus tree parent/degree/children; no card/count/leaf/rank/answer or trace is added as caller input. |
| Full table and rolling | Nat claims require actual full-table correctness, leading capacity bound on every execution prefix and separate index-word allocation. Rolling is an additional same-implementation phase with two stage layers and original initial rank/row, not a replacement for the table. |
| Query from arbitrary workspace | Nat query quantifies EVERY heap satisfying original table correctness, leading capacity<=q and allocated word Fits. No pre-zeroed scratch, precomputed metadata/counts, small index-value or extra VOID<=nodeCard qualification. Physical query quantifies every BitVec heap with decoded table/capacity correctness; word Fits is intrinsic. VOID payload may be arbitrary within the original leading-capacity<=q bound. |
| Actual request reuse | pathExecute and PathClaims pass the ENTIRE preceding output heap to the next query. Only PC/registers start afresh. Quantification is over arbitrary request lists of length<=N and therefore covers realized causal histories; no old scratch snapshot or caller-decoded/repacked table is restored. |
| Real physical packing | PackedPhaseRefines contains actual PackingRunCorrect, final register equality, equality for every allocated logical word and every physical prefix capacity bound, plus genuine HALT. The code uses actual bit/word operations and charged accesses; it does not erase packed semantics via a map to logical instructions. Seven spill words are accounted for and physically wiped. |
| Storage | Physical capacity words*bits are bounded by capWords*capacityWidth+(indexWords+1)*bits. Capacity bits and index words are distinct original resources; code, ROM and indexing memory must not be described as entirely O(work*log(q+2)) bits. |
| Fixed uniform six-program generator | UniformCodeGenerationClaims chooses ONE finite generator BEFORE all N/q/t, with only ROM[N,q,t]. It actually computes dimensions, measures and emits six complete programs with length prefixes, copies the output and HALTs. Original q>0,t>0,t<=N+q+1 are retained. Target output/code, path and arithmetic answers are not ROM inputs. |
| Static Fits vs universal execution | Specialization(0,1,1) proves all literals of the same dimension-independent source fit64, INCLUDING unexecuted repeat bodies. Universal six_checked/generator_word and actual word/resource bounds prove executions for all eligible dimensions. Counter20's erasure is only from a linear-small-value invariant; lexical/code Fits and all true repeat obligations remain. |
| Costs and initialization | totalBuildCost includes ROM/code loading, zero heap initialization,8 initial register/PC writes and the real trace/HALT. totalQueryCost includes q+1 new stage/used words, code,8 and trace/HALT; static tree ROM is shared from build and every access remains charged. Generator separately charges ROM3, its code, actual heap initialization,8 and dynamic trace. Physical refinement is a constant-factor composition with these Nat costs;2^58 is not claimed to be the minimum combined direct physical coefficient. |

Two distinctions matter for later summaries. First, the actual query count pass
in PA17_QueryCounts_008 is O(qt), whereas laminar-proofs.tex:255 describes an
O(t) counting method. The implemented pass is charged within the original TOTAL
query bound O((q+1)t); this report does not claim it implements that O(t) pass.
Second, A17's given-tree interface does not prove A06 preprocessing merely by
accepting a tree; A06 now has its own independently accepted no-argument closure.
The q=0 direct controller remains the separate A18 boundary.

## Evidence and limits

RootBatch004 acceptance records original A17, archived whole build4352jobs and
AXIOM_AUDIT_PASS declarations29987/new_axioms0/forbidden_dependencies0, and a
matching receipt fingerprint. Current DEPENDENCIES.md explicitly keeps A17
closed under batch004. Those are existing formal coordinator checks; no new
test count or fresh compiler run is asserted by this read-only review.

Prior private050 independent public consumer and scope report are supporting
historical evidence only. The current formal AlgorithmClaims/049 interfaces
and current boundary/semantic sources were read directly; current hashes and
frozen-manuscript fingerprint comparison appear in evidence001.json.

No material A-sector scope gap was identified in the reviewed chain. This
bounded finding does not certify all proofs independently of Lean, the entire
S7 review, A19 persistent callbacks, B23 bit complexity, L01 statistical/machine
integration, the later Bool TM0 division assignment or final manuscript-wide
acceptance. Those retain their own original targets and coordinator decisions.
