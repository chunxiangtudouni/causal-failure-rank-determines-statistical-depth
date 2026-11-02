module

public import PaperProofs.Retained.PRet_EarlyReports_034
public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetActualReportedErrors048

open Common Common.Native PRetEarlyReports034

variable {I : Instance}

/-- The source's actual ordinary write and early report use the same REAL
serial. Reported error decoding does not invent a truth bit or handle. -/
theorem prefix_reportedError {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting source seed truth tapes n s) (stage : I.Stage) :
    reportedError s.history stage = (s.ledger.written stage).map (fun bit => bit != s.ledger.truth stage) := by
  unfold reportedError
  rw [prefix_historyWrite input C mode accounting source seed truth tapes hp stage,
    prefix_historyReport_early input C hearly mode accounting source seed truth tapes hp stage]
  cases hw : s.ledger.written stage with
  | none => simp only [Option.map_none, Option.bind_eq_bind, Option.bind_none]
  | some bit =>
    obtain ⟨clock, hreport⟩ := prefix_written_reported input C hearly mode accounting source seed truth tapes hp stage
      (by rw [hw]; exact Option.some_ne_none _)
    simp only [hreport, Option.map_some, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]

/-- Exact old-H interpretation at any actual source Prefix, including
failed/unfinished ones. Both sides are the existing ORIGINAL definitions. -/
theorem prefix_reportedErrors {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting source seed truth tapes n s) (next : ℕ) :
    reportedErrors I s.history next = ordinaryMismatches s.ledger ∩ pastStages I next := by
  ext stage
  simp only [reportedErrors, pastStages, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter, mem_ordinaryMismatches]
  rw [prefix_reportedError input C hearly mode accounting source seed truth tapes hp stage]
  cases hw : s.ledger.written stage <;> cases ht : s.ledger.truth stage <;> simp [and_comm]

end PaperProofs.Retained.PRetActualReportedErrors048
