module

public import PaperProofs.Structure.RawIncidenceCounterSafety

/-! The actual 4/8/12/17-clock pair decision of the original checker.
Every traversed counter test and rejecting HALT retains all prefix bounds;
the final branch classification is proved from the real three counters. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

theorem checker_pair_decision_safe (q : Nat) (full : List (Finset (Fin q)))
    (i j : Nat) (state : NatState) (ready : Ready full.length q i j 460 state)
    (_hi : i < full.length) (_hj : j < full.length)
    (h5bound : state.heap 5 ≤ q) (h6bound : state.heap 6 ≤ q) (h7bound : state.heap 7 ≤ q)
    (hr : RegistersBound full.length q state) :
    ∃ decision : Nat, decision ≤ 17 ∧
      (∀ count ≤ decision, SafePoint q full (natRun (rawIncidenceROM q full) checker count state)) ∧
      ((decision ≤ 12 ∧ Ready full.length q i j 540 (natRun (rawIncidenceROM q full) checker decision state)) ∨
        (natRun (rawIncidenceROM q full) checker decision state).halted = true) := by
  let rom := rawIncidenceROM q full
  have first := checker_counterTest_ready rom ⟨0, by decide⟩ ready
  have firstSafe := checker_counterTest_safe q full ⟨0, by decide⟩ state ready.pc ready.active h5bound hr
  by_cases h5 : state.heap 5 = 0
  · refine ⟨4, by decide, firstSafe, Or.inl ⟨by decide, ?_⟩⟩
    simpa only [h5, ite_true] using first.2
  · let one := natRun rom checker 4 state
    have rone : Ready full.length q i j 480 one := by simpa only [h5, ite_false] using first.2
    have hrone : RegistersBound full.length q one := (firstSafe 4 le_rfl).1
    have one6 : one.heap 6 = state.heap 6 := congrFun first.1 6
    have second := checker_counterTest_ready rom ⟨1, by decide⟩ rone
    have secondSafe := checker_counterTest_safe q full ⟨1, by decide⟩ one rone.pc rone.active
      (by simpa only [one6] using h6bound) hrone
    have safe8 := safe_prefix_add q full state 4 4 firstSafe secondSafe
    by_cases h6 : state.heap 6 = 0
    · refine ⟨8, by decide, safe8, Or.inl ⟨by decide, ?_⟩⟩
      rw [show 8 = 4 + 4 from rfl, natRun_add]
      simpa only [one6, h6, ite_true] using second.2
    · let two := natRun rom checker 4 one
      have rtwo : Ready full.length q i j 500 two := by simpa only [one6, h6, ite_false] using second.2
      have hrtwo : RegistersBound full.length q two := (secondSafe 4 le_rfl).1
      have two7 : two.heap 7 = state.heap 7 := (congrFun second.1 7).trans (congrFun first.1 7)
      have third := checker_counterTest_ready rom ⟨2, by decide⟩ rtwo
      have thirdSafe := checker_counterTest_safe q full ⟨2, by decide⟩ two rtwo.pc rtwo.active
        (by simpa only [two7] using h7bound) hrtwo
      have safe12 := safe_prefix_add q full state 4 8 firstSafe
        (safe_prefix_add q full one 4 4 secondSafe thirdSafe)
      have hrun12 : natRun rom checker 12 state = natRun rom checker 4 two := by
        rw [show 12 = (4 + 4) + 4 from rfl, natRun_add, natRun_add]
      by_cases h7 : state.heap 7 = 0
      · refine ⟨12, by decide, safe12, Or.inl ⟨by decide, ?_⟩⟩
        rw [hrun12]
        simpa only [two7, h7, ite_true] using third.2
      · let three := natRun rom checker 4 two
        have rthree : Ready full.length q i j 520 three := by simpa only [two7, h7, ite_false] using third.2
        have hrthree : RegistersBound full.length q three := (thirdSafe 4 le_rfl).1
        have rejectSafe := checker_reject_safe q full three rthree.pc rthree.active hrthree
        have safe17 := safe_prefix_add q full state 4 13 firstSafe
          (safe_prefix_add q full one 4 9 secondSafe
            (safe_prefix_add q full two 4 5 thirdSafe rejectSafe))
        refine ⟨17, by decide, safe17, Or.inr ?_⟩
        rw [show 17 = 12 + 5 from rfl, natRun_add, hrun12]
        exact (checker_reject rom three rthree.pc rthree.active).1

end PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety
