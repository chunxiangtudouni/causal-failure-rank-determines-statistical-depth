module

public import Paid.PDCompute_SolverHeaderInit_029

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDMenu.ComputeFrame

def minimumCompareCode : List Instruction :=
  loadSlot 28 .total++loadSlot 24 .value++[.ratCompare .less .index .total .value]

def minimumCompareResult (before : State) (base : ℕ) (candidate best : ℚ) : State :=
  let loaded := loadSlotResult (loadSlotResult before base 28 .total) base 24 .value
  ({loaded with pc:=loaded.pc+1}).set .index (.natural (if candidate < best then 1 else 0))

theorem minimumCompareCode_length : minimumCompareCode.length=7 := rfl

theorem minimumCompareCode_straight : StraightCode minimumCompareCode := by
  intro instruction member
  simp only [minimumCompareCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h|h))|h <;> subst instruction <;> trivial

theorem minimumCompareCode_execute (input : List Cell) (before : State) (base : ℕ) (values : ℕ → Cell)
    (candidate best : ℚ) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hc : values 28=.rational candidate) (hb : values 24=.rational best) :
    linearExecute input minimumCompareCode before=some (minimumCompareResult before base candidate best) := by
  have hcl := header.live 28 (by decide)
  have hbl := header.live 24 (by decide)
  have hcv := (header.value 28 (by decide)).trans hc
  have hbv := (header.value 24 (by decide)).trans hb
  simp [minimumCompareCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,Cell.rat?,
    hbase,hcl,hbl,hcv,hbv,Comparison.rat,minimumCompareResult,loadSlotResult]

theorem minimumCompareResult_fields (before : State) (base : ℕ) (candidate best : ℚ) :
    (minimumCompareResult before base candidate best).heap=before.heap ∧
    (minimumCompareResult before base candidate best).live=before.live ∧
    (minimumCompareResult before base candidate best).register .fresh=before.register .fresh ∧
    (minimumCompareResult before base candidate best).register .index=.natural (if candidate < best then 1 else 0) ∧
    (minimumCompareResult before base candidate best).pc=before.pc+7 ∧
    (minimumCompareResult before base candidate best).output=before.output := by
  simp [minimumCompareResult,loadSlotResult,State.set]

theorem minimumCompareResult_header (before : State) (base : ℕ) (values : ℕ → Cell)
    (candidate best : ℚ) (header : Header before base values) :
    Header (minimumCompareResult before base candidate best) base values := by
  intro slot inside
  exact header slot inside

theorem minimumCompareResult_frame (before : State) (base n k : ℕ) (candidate best : ℚ) :
    Frame before (minimumCompareResult before base candidate best) base n k := by
  exact ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩

end PDCompute.Solver
