module

public import PaperProofs.Paid.PDROC_Simulator_013

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem simulatorDrawAt_some_spec (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (seed : Seed) (entry : List (VisibleEvent P.sharedInstance)) (tape : P.experiment.Tape)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee source stage seed entry tape = some draw) :
    draw.record.decision = optionWriteBit draw.action ∧ draw.action ≠ .review stage := by
  by_cases ht : headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, entry) tape = ⊤
  · simp only [simulatorDrawAt, ht, ↓reduceIte, reduceCtorEq] at hd
  · simp only [simulatorDrawAt, ht, ↓reduceIte] at hd
    have heq := Option.some.inj hd
    subst draw
    refine ⟨rfl, ?_⟩
    let stop := headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, entry) tape
    have hn : stop = (stop.toNat : ℕ∞) := (ENat.natCast_toNat_eq_self.mpr ht).symm
    exact headExitStop_hits (P.input fee hfee) stage (simulatorPrewriteRule P source) (seed, entry) tape stop.toNat hn

theorem simulatorSeedDraw_some_spec (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (stage : P.sharedInstance.Stage)
    (entry : List (VisibleEvent P.sharedInstance)) (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorSeedDraw P fee hfee source seed stage entry = some draw) :
    draw.record.decision = optionWriteBit draw.action ∧ draw.action ≠ .review stage :=
  simulatorDrawAt_some_spec P fee hfee source stage seed.1 entry (seed.2.1 stage) draw hd

/-- At an unwritten current port, an allowed non-review non-write action
can only terminate. This is a genuine existing permission predicate. -/
theorem historyAllowsAction_unwritten_terminal {I : Instance}
    (history : List (VisibleEvent I)) (stage : I.Stage) (action : Action I)
    (hc : historyCursor history = stage.val) (hw : historyWritten history stage = none)
    (hr : action ≠ .review stage) (hwrite : optionWriteBit action = none)
    (ha : historyAllowsAction history (reserialAction history (fun _ bit => bit) action)) :
    action = .stop ∨ action = .abandon := by
  cases action with
  | review other =>
    have heq : other = stage := Fin.ext (ha.1.symm.trans hc)
    exact (hr (heq ▸ rfl)).elim
  | write other bit => cases hwrite
  | advance other =>
    have heq : other = stage := Fin.ext (ha.1.symm.trans hc)
    exact (ha.2 (heq.symm ▸ hw)).elim
  | allocate handle tool | execute handle tool =>
    have heq : handle.stage = stage := Fin.ext (ha.1.symm.trans hc)
    have hvalid := ha.2.1
    unfold historyValidHandle at hvalid
    simp only [reserialHandle_stage] at hvalid
    cases hp : historyReport history handle.stage with
    | none => simp only [hp] at hvalid
    | some packet =>
      simp only [hp] at hvalid
      have hwrong := hvalid.1
      have hw' : historyWritten history handle.stage = none := heq.symm ▸ hw
      rw [hw'] at hwrong
      cases hwrong
  | stop => exact Or.inl rfl
  | abandon => exact Or.inr rfl

end PDROC
