module

public import PaperProofs.Retained.PRet_FreshHeadPolicy_079

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshContinuationPolicy096

open Common Common.Native MeasureTheory PRetFreshHeadPolicy079

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The F comparator retains old H in its terminal success predicate. Its
head error therefore advances WITHOUT a current-window head payment; the
actual chosen full child runs with all tools through the public suffix lift. -/
def postHeadRaw (head : I.Stage) (good bad : PolicyRule (I.freshSuffix 1) Seed) : PolicyRule I Seed :=
  fun seed history =>
    if historyCursor history = 0 then .advance head else
      let before := history.take (history.idxOf (.advanced head) + 1)
      let child := if historyWritten history head = (historyReport history head).map Prod.fst then good else bad
      bellmanLiftedAfter 1 before child seed history

theorem measurable_postHeadRaw (head : I.Stage) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad) : MeasurableRule (postHeadRaw head good bad) := by
  apply measurable_from_prod_countable_left
  intro history
  by_cases hc : historyCursor history = 0
  · simpa only [postHeadRaw, hc, ite_true] using
      (measurable_const (a := Action.advance head) : Measurable (fun _ : Seed => Action.advance head))
  · let before := history.take (history.idxOf (.advanced head) + 1)
    let lowered := bellmanSuffixHistoryLower 1 (historyActions before).length (history.drop before.length)
    have hm (child : PolicyRule (I.freshSuffix 1) Seed) (hchild : MeasurableRule child) :
        Measurable (fun seed : Seed => bellmanLiftedAfter 1 before child seed history) := by
      exact (measurable_of_countable (referenceSuffixActionLift I 1 (historyActions before).length)).comp
        (hchild.comp (measurable_id.prodMk (measurable_const (a := lowered))))
    by_cases hb : historyWritten history head = (historyReport history head).map Prod.fst
    · simpa only [postHeadRaw, hc, ite_false, hb, ite_true] using hm good hgood
    · simpa only [postHeadRaw, hc, ite_false, hb] using hm bad hbad

/-- A REAL full fresh Policy with three genuine measurable components.
No near-optimality/termination/risk/cost certificate is a Policy field. -/
noncomputable def twoContinuationPolicy (input : StatisticalInput I) (head : I.Stage)
    (test : (input.experiment head).AdmissibleRule Seed) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad) :
    Policy input (freshContract I) .uncapped (zeroNormalAccounting I) Seed :=
  PRetFreshHeadPolicy079.policy input head test (postHeadRaw head good bad) (measurable_postHeadRaw head good bad hgood hbad)

end PaperProofs.Retained.PRetFreshContinuationPolicy096
