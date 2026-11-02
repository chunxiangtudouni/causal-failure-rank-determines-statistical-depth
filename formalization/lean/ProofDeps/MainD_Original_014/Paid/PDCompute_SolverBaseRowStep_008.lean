module

public import Paid.PDCompute_SolverBaseRowCode_007
public import Paid.PDMenu_ComputeFrame_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)

def baseRowWrites : List Instruction := (baseRowBody 0).take 15

theorem baseRowWrites_length : baseRowWrites.length=15 := rfl

theorem baseRowBody_split (testPC : ℕ) : baseRowBody testPC=baseRowWrites++[.jump testPC] := rfl

theorem baseRowWrites_straight : PDMenu.ComputeFrame.StraightCode baseRowWrites := by
  simp [PDMenu.ComputeFrame.StraightCode,PDMenu.ComputeFrame.StraightInstruction,baseRowWrites,baseRowBody]

/-- Analysis description of the result of the fifteen literal writes,
pointer increments and countdown decrement. This is not a RAM primitive. -/
def baseRowWritesResult (before : State) (pointer count : ℕ) : State :=
  { before with
    register := Function.update (Function.update (Function.update before.register .value (.rational 0))
      .address (.natural (pointer+6))) .index (.natural (count-1))
    heap := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update before.heap pointer (.natural 0)) (pointer+1) (.natural 0))
      (pointer+2) (.natural 0)) (pointer+3) (.rational 0)) (pointer+4) (.rational 0)) (pointer+5) (.rational 0)
    live := insert (pointer+5) (insert (pointer+4) (insert (pointer+3) (insert (pointer+2)
      (insert (pointer+1) (insert pointer before.live)))))
    pc := before.pc+15 }

theorem baseRowWrites_execute (input : List Cell) (before : State) (pointer count : ℕ)
    (haddress : before.register .address=.natural pointer)
    (hcount : before.register .index=.natural count) (hone : before.register .flag=.natural 1) :
    linearExecute input baseRowWrites before=some (baseRowWritesResult before pointer count) := by
  simp [linearExecute,baseRowWrites,baseRowBody,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    haddress,hcount,hone,baseRowWritesResult,Nat.add_assoc]
  congr 1
  funext register
  cases register <;> simp

theorem baseRowWrites_heapList (before : State) (pointer count : ℕ) :
    HeapList (baseRowWritesResult before pointer count) pointer (denseEncodeEntry finishEntry) := by
  constructor
  · intro offset hoff
    change offset < 6 at hoff
    have hcases : offset=0 ∨ offset=1 ∨ offset=2 ∨ offset=3 ∨ offset=4 ∨ offset=5 := by omega
    rcases hcases with h|h|h|h|h|h <;> subst offset <;> simp [baseRowWritesResult]
  · simp [heapSegment,baseRowWritesResult,denseEncodeEntry,finishEntry,List.range_succ]

theorem baseRowWrites_frame (before : State) (pointer count base n k : ℕ)
    (hinside : ∀ offset < 6, pointer+offset ∈ workspace base n k) :
    Frame before (baseRowWritesResult before pointer count) base n k := by
  constructor
  · intro address hout
    have hne : ∀ offset < 6, address ≠ pointer+offset := by
      intro offset hoff he
      subst address
      exact hout (hinside offset hoff)
    simp only [baseRowWritesResult,Function.update_apply]
    rw [ite_eq_right (hne 5 (by omega)),ite_eq_right (hne 4 (by omega)),ite_eq_right (hne 3 (by omega)),
      ite_eq_right (hne 2 (by omega)),ite_eq_right (hne 1 (by omega))]
    have hzero : address ≠ pointer := by simpa only [Nat.add_zero] using hne 0 (by omega)
    rw [ite_eq_right hzero]
  · intro address hout
    have hne : ∀ offset < 6, address ≠ pointer+offset := by
      intro offset hoff he
      subst address
      exact hout (hinside offset hoff)
    have hzero : address ≠ pointer := by simpa only [Nat.add_zero] using hne 0 (by omega)
    simp only [baseRowWritesResult,Finset.mem_insert,hne 5 (by omega),hne 4 (by omega),
      hne 3 (by omega),hne 2 (by omega),hne 1 (by omega),hzero,false_or]

end PDCompute.Solver
