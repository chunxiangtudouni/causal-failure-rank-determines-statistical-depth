module

public import Paid.PDCompute_SolverScanKernel_037

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDMenu.ComputeFrame

theorem Header.loadSlot_execute {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (input : List Cell) (slot : ℕ) (target : Register)
    (inside : slot < headerWords) (hbase : before.register .fresh=.natural base) :
    linearExecute input (loadSlot slot target) before=some (loadSlotResult before base slot target) ∧
      (loadSlotResult before base slot target).register target=values slot := by
  refine ⟨PDLower.CalibrationCompute.loadSlot_execute input before base slot target hbase (header.live slot inside),?_⟩
  simpa only [loadSlotResult,Function.update_self] using header.value slot inside

theorem Header.loadSlot_preserves {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (slot : ℕ) (target : Register) :
    Header (loadSlotResult before base slot target) base values := header

theorem loadSlotResult_fresh (before : State) (base slot : ℕ) (target : Register)
    (different : target ≠ .fresh) :
    (loadSlotResult before base slot target).register .fresh=before.register .fresh := by
  simp [loadSlotResult,Function.update_of_ne (Ne.symm different)]

theorem loadSlotResult_frame (before : State) (base slot n k : ℕ) (target : Register) :
    Frame before (loadSlotResult before base slot target) base n k := ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩

theorem loadSlot_straight (slot : ℕ) (target : Register) : StraightCode (loadSlot slot target) := by
  intro instruction member
  simp only [loadSlot,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h <;> subst instruction <;> trivial

theorem Header.loadSlot_trace {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (program : Program) (input : List Cell) (slot : ℕ) (target : Register)
    (inside : slot < headerWords) (hbase : before.register .fresh=.natural base)
    (hfetch : FetchesCode program before.pc (loadSlot slot target)) :
    ∃ trace : List State, trace.head?=some before ∧
      trace.getLast?=some (loadSlotResult before base slot target) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 60 := by
  obtain ⟨trace,hh,hl,hchain,ht,_⟩ := linearExecute_trace_time program input (loadSlot slot target)
    (loadSlot_straight slot target) before _ hfetch (header.loadSlot_execute input slot target inside hbase).1
  exact ⟨trace,hh,hl,hchain,ht⟩

end PDCompute.Solver
