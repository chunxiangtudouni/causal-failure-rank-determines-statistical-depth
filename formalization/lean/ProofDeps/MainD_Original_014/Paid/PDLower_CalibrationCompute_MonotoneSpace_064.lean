module

public import Paid.PDLower_CalibrationCompute_Space_011
public import Paid.PDROC_D27Prepare_Output_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- Lift an actual per-step live-set monotonicity proof to every genuine
prefix state. The fixed no-release calibration program will supply the
step property; this lemma makes no program-correctness claim itself. -/
theorem chain_live_subset_final (program : Program) (input : List Cell)
    (monotone : ∀ before after,step program input before=some after → before.live⊆after.live) :
    ∀ (trace : List State) (final : State),
      trace.IsChain (fun a b => step program input a=some b) → trace.getLast?=some final →
      ∀ state∈trace,state.live⊆final.live := by
  intro trace
  induction trace with
  | nil => intro _ _ _ state member; cases member
  | cons before tail ih =>
    intro final chain last state member
    cases tail with
    | nil =>
      have finalSame : before=final := Option.some.inj last
      have same : state=before := List.mem_singleton.mp member
      subst state
      subst final
      exact fun _ member => member
    | cons after rest =>
      have parts := List.isChain_cons_cons.mp chain
      have later := ih final parts.2 (by simpa only [List.getLast?_cons_cons] using last)
      rcases List.mem_cons.mp member with same|member
      · subst state
        exact (monotone before after parts.1).trans (later after (by simp))
      · exact later state member

theorem chain_workingCells_le_final (program : Program) (input : List Cell)
    (monotone : ∀ before after,step program input before=some after → before.live⊆after.live)
    (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => step program input a=some b)) (last : trace.getLast?=some final) :
    ∀ state∈trace,workingCells state≤workingCells final := by
  intro state member
  have live := Finset.card_le_card (chain_live_subset_final program input monotone trace final chain last state member)
  have output := (PDROC.D27Prepare.Output.chain_prefix_final program input trace final chain last state member).length_le
  simp only [workingCells]
  omega

/-- A final-footprint bound is sufficient ONLY after actual step-chain
monotonicity has been established. Operand-bit bounds do not follow. -/
theorem chain_peakCells_le_final (program : Program) (input : List Cell)
    (monotone : ∀ before after,step program input before=some after → before.live⊆after.live)
    (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => step program input a=some b)) (last : trace.getLast?=some final) :
    peakCells trace≤workingCells final :=
  peakCells_le_of_forall trace (workingCells final)
    (chain_workingCells_le_final program input monotone trace final chain last)

theorem chain_standalone_record_bound (program : Program) (input : List Cell)
    (monotone : ∀ before after,step program input before=some after → before.live⊆after.live)
    (trace : List State) (before final : State) (base M : ℕ) (extra : List Cell)
    (chain : trace.IsChain (fun a b => step program input a=some b)) (last : trace.getLast?=some final)
    (frame : Frame before final base M) (output : final.output=before.output++extra)
    (inputRecords : workingCells before≤registers.length+rowWidth M) (length : extra.length≤rowWidth M) :
    peakCells trace≤38*(M+1) := by
  have endBound := frame.workingCells_le extra output
  have envelope := standaloneRecordEnvelope M
  have finalBound : workingCells final≤38*(M+1) := by omega
  exact (chain_peakCells_le_final program input monotone trace final chain last).trans finalBound

end PDLower.CalibrationCompute
