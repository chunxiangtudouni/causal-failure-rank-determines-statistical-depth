# Root batch 001: six definition/scope entries and the B02 universe bridge

Static acceptance evidence, 2026-10-30. This is not a second claim ledger.
The six existing IDs below are accepted at their original scope; final S7
still checks the complete frozen manuscript. No manuscript source is changed.

## Original entries and exact evidence

- M01, model.tex:4–18: Common/Model.lean:23 uses a finite tool type and an
  ordered finite compatibility list. Statistics/Experiment.lean:24 encodes
  rational nondegenerate prior, finite rational full-support normalized
  distinct channels and strictly positive rational review fee as original
  model data. Common/Input.lean supplies the same rational nonnegative
  correction fees. Generated-history freshness is separately proved by M04;
  it is not silently assumed from the finite input structure.
- M09a, prices.tex:20–26: Common/NativeExecution.lean:137–201 defines actual
  eventual success, all-finite-prefix supremum of the complete actual bill,
  measurable success/bill, failure probability and ENNReal integral, then
  takes the risk-constrained Policy infimum. It neither discards failed or
  nonreturned paths nor filters finite expected bills; empty feasible sets
  retain the complete-lattice infimum. Policy measurability and actual-Step
  legality are explicit at lines106–110.
- M09, prices.tex:15–18,43–48: the same input/contract/accounting feed the
  original whole-task value. NativeSeed.value_le_policy_any_seed (172) and
  value_eq_strategyValue (190), plus NativePartial.partialValue_eq_value
  (279), remove seed-universe and finite-next-action restrictions. Their
  risk/bill preservation proofs are already formal, not new assumptions.
- B07, price-proofs.tex:59–75: HealthyValue.healthyPenalty (89) is an
  independent fresh-suffix AvailablePolicy infimum of actual observation
  charge plus one failure penalty, using the original experiments and
  actual available-tool legality. AvailableValue:178 handles arbitrary
  seed universes; accounting/contract equivalences precede canonicalization.
  healthyPenaltyReal (123) converts only after finite-penalty finiteness.
  The existing B09 applies at first entry. No middle-review history is
  reinterpreted as a fresh prior, and Bellman is not the definition of G.
- C01a, introduction.tex:32–56 and star-proofs.tex:3–6: Star/Model.lean:303
  retains q>=2, the original rational BSC and nonnegative correction fee;
  all stages and both orders use the identical experiment. BinarySymmetric
  divergence_eq_kappa and coefficient_eq_a prove the actual KL/coefficient
  formula. Star/Model.lean:333–367 keeps I's execution deadline parameter,
  copies quota/H/H0 verbatim into all three contracts, and defines each
  value by the same whole-policy Native.value. This accepts no C12 price.
- B02, price-proofs.tex:5–12: the old localValue definition remains an
  independent infimum over genuine measurable sequential tests, including
  non-MAP and infinite charges. The new Statistics/LocalSeedScope.lean
  proves exact seed disintegration of the observation charge, conditional
  error and complete objective using Tonelli, for arbitrary Seed universes.
  fixedSeedTest keeps the exact same stopping and stopped-decision functions.
  localValue_le_test_any_seed (133) bounds every original randomized test,
  with no finite-ET/finite-cost/optimizer assumption and with infinite
  penalty allowed. localValue_eq_deterministic (146) proves equality of
  infima, not existence of a minimizing test. Thus the old Type-0 spelling
  no longer excludes larger seed universes from this local comparison.

## Verification

RootLocalSeedScope001.lean and formal Statistics/LocalSeedScope.lean have
identical bytes. Formal target build actually exit0 (3170 jobs).
RootLocalSeedScope001.Public.lean ordinary public import directly applies
the arbitrary-universe lower, exact seed-integral identity and independent
deterministic-inf equality. It actually exit0, and all ten new owned
definitions/theorems report only propext/Classical.choice/Quot.sound.
Logs: RootLocalSeedScope001.formal-build.log and
RootLocalSeedScope001.public-axioms.log. Final whole-project build/audit and
receipt binding belong to this coherent Root batch, after all ledger edits.

The accompanying PRet terminal-pair and PDMenu endpoint components do not
close R02, D16 or D17. Their original pending full targets stay pending.
