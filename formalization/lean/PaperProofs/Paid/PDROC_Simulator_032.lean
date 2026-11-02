module

public import PaperProofs.Paid.PDROC_Simulator_031

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- A complete actual written-stage exit is exactly the source's finite
postwrite transducer. The exit clock includes every real correction step. -/
theorem simulator_postwrite_exit_of_source_run (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (seed : SimulatorSeed P Seed) (world vworld : (P.input fee hfee).World)
    (astart vstart : ℕ) (stage : P.sharedInstance.Stage) (actualBit virtualBit : Bool)
    (hwa : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
      (seed, world) astart).ledger.written stage = some actualBit)
    (hwv : (run (P.input fee hfee) C.val .uncapped accounting source
      (seed.1, vworld) vstart).ledger.written stage = some virtualBit)
    (hvc : (run (P.input fee hfee) C.val .uncapped accounting source
      (seed.1, vworld) vstart).cursor = stage.val)
    (hh : simulatorShadow P fee hfee source seed
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) astart).history =
      (run (P.input fee hfee) C.val .uncapped accounting source (seed.1, vworld) vstart).history) :
    ∃ exit : ℕ, exit ≤ 3 ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) (astart + exit)).halted = true ∨
        stage.val < (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (astart + exit)).cursor) ∧
      simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) (astart + exit)).history =
        postwriteStageTrace source seed.1 stage
          (run (P.input fee hfee) C.val .uncapped accounting source (seed.1, vworld) vstart).history 3 := by
  classical
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let E := fun k : ℕ => (run input C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).halted = true ∨
    stage.val < (run input C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).cursor
  have hwvn : (run input C.val .uncapped accounting source (seed.1, vworld) vstart).ledger.written stage ≠ none := by
    rw [hwv]
    exact Option.some_ne_none virtualBit
  have hthree := run_written_stage_exit_within_three input C.val C.property .uncapped accounting source hl
    (seed.1, vworld) vstart stage hvc hwvn
  have he : ∃ k : ℕ, E k := ⟨3, hthree⟩
  let exit := Nat.find he
  have hExit : E exit := Nat.find_spec he
  have hBound : exit ≤ 3 := Nat.find_min' he hthree
  have hbefore (k : ℕ) (hk : k < exit) :
      (run input C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).halted = false ∧
      (run input C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).cursor = stage.val := by
    have hnot : ¬ E k := Nat.find_min he hk
    refine ⟨Bool.eq_false_iff.mpr (fun hh => hnot (Or.inl hh)), ?_⟩
    have hlo := run_cursor_monotone input C.val .uncapped accounting source hl (seed.1, vworld) (Nat.le_add_right vstart k)
    change (run input C.val .uncapped accounting source (seed.1, vworld) vstart).cursor ≤
      (run input C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).cursor at hlo
    rw [hvc] at hlo
    have hhi : ¬ stage.val < (run input C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).cursor :=
      fun h => hnot (Or.inr h)
    omega
  have hwritten (k : ℕ) :
      (run input C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).ledger.written stage ≠ none := by
    rw [run_written_some_after input C.val .uncapped accounting source hl (seed.1, vworld) vstart k stage virtualBit hwv]
    exact Option.some_ne_none virtualBit
  have hTrace (k : ℕ) :
      postwriteStageTrace source seed.1 stage (run input C.val .uncapped accounting source (seed.1, vworld) vstart).history k =
        (run input C.val .uncapped accounting source (seed.1, vworld) (vstart + min k exit)).history := by
    induction k with
    | zero => simp only [postwriteStageTrace, Nat.zero_min, Nat.add_zero]
    | succ k ih =>
      rw [postwriteStageTrace, ih]
      by_cases hk : k < exit
      · rw [Nat.min_eq_left hk.le]
        obtain ⟨vn, _, vp⟩ := run_has_prefix input C.val .uncapped accounting source hl (seed.1, vworld) (vstart + k)
        have vstep := run_actualStep_of_active input C.val .uncapped accounting source hl (seed.1, vworld)
          (vstart + k) (hbefore k hk).1
        have hnext := postwriteStageStep_eq_nextHistory input C.val .uncapped accounting source seed.1
          (input.truthAt vworld) (worldTapes input vworld) stage vp (hbefore k hk).1 (hbefore k hk).2 (hwritten k) vstep
        simpa only [Nat.min_eq_left (by omega : k + 1 ≤ exit), Nat.add_assoc] using hnext
      · have hke : exit ≤ k := by omega
        rw [Nat.min_eq_right hke, Nat.min_eq_right (by omega : exit ≤ k + 1)]
        obtain ⟨vn, _, vp⟩ := run_has_prefix input C.val .uncapped accounting source hl (seed.1, vworld) (vstart + exit)
        exact postwriteStageStep_freeze_at_exit input C.val .uncapped accounting source seed.1
          (input.truthAt vworld) (worldTapes input vworld) stage vp hExit
  have hsync := simulator_postwrite_run_shadow_upto P fee hfee C accounting source hl seed world vworld
    astart vstart stage actualBit virtualBit hwa hwv hh exit hbefore exit le_rfl
  have hla := simulatorRule_legal P fee hfee C accounting source
  obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hla (seed, world) (astart + exit)
  obtain ⟨vn, _, vp⟩ := run_has_prefix input C.val .uncapped accounting source hl (seed.1, vworld) (vstart + exit)
  have hfields := simulator_prefix_state_projection input C.val .uncapped accounting actual seed _ _ ap
    source seed.1 _ _ vp (simulatorSeedDraw P fee hfee source) seed hsync
  refine ⟨exit, hBound, ?_, ?_⟩
  · rcases hExit with hh | hc
    · exact Or.inl (hfields.2.1.trans hh)
    · exact Or.inr (hfields.1.symm ▸ hc)
  · exact hsync.trans (by simpa only [Nat.min_eq_right hBound] using (hTrace 3).symm)

end PDROC
