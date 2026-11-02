module

public import Paid.PDROC_CalibrationRow_007
public import Paid.PDROC_CalibrationRow_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- The same seven literal instructions serve initGate, zeroGate,
scatterGate and stepGate (with the indicated actual header offsets). -/
def gateCode (cursorOffset boundOffset : ℕ) : List Instruction :=
  loadSlot cursorOffset .index ++ loadSlot boundOffset .total ++
    [.natCompare .less .flag .index .total]

def gateResult (before : State) (base cursorOffset boundOffset cursor bound : ℕ) : State :=
  let cursorLoaded := loadSlotResult before base cursorOffset .index
  let boundLoaded := loadSlotResult cursorLoaded base boundOffset .total
  ({boundLoaded with pc:=boundLoaded.pc+1}).set .flag (.natural (if cursor < bound then 1 else 0))

theorem gate_execute (input : List Cell) (before : State)
    (base cursorOffset boundOffset cursor bound : ℕ)
    (fresh : before.register .fresh=.natural base)
    (cursorLive : base+cursorOffset ∈ before.live) (boundLive : base+boundOffset ∈ before.live)
    (cursorValue : before.heap (base+cursorOffset)=.natural cursor)
    (boundValue : before.heap (base+boundOffset)=.natural bound) :
    linearExecute input (gateCode cursorOffset boundOffset) before =
      some (gateResult before base cursorOffset boundOffset cursor bound) := by
  simp [gateCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
    Comparison.nat,Cell.nat?,fresh,cursorLive,boundLive,cursorValue,boundValue,
    gateResult,loadSlotResult,Nat.add_assoc]

theorem gate_fields (before : State) (base a b cursor bound : ℕ)
    (cursorValue : before.heap (base+a)=.natural cursor)
    (boundValue : before.heap (base+b)=.natural bound) :
    (gateResult before base a b cursor bound).heap=before.heap ∧
    (gateResult before base a b cursor bound).live=before.live ∧
    (gateResult before base a b cursor bound).register .fresh=before.register .fresh ∧
    (gateResult before base a b cursor bound).register .index=.natural cursor ∧
    (gateResult before base a b cursor bound).register .total=.natural bound ∧
    (gateResult before base a b cursor bound).register .flag=.natural (if cursor<bound then 1 else 0) ∧
    (gateResult before base a b cursor bound).pc=before.pc+7 ∧
    (gateResult before base a b cursor bound).output=before.output := by
  simp [gateResult,loadSlotResult,State.set,Nat.add_assoc,cursorValue,boundValue]

theorem gate_prefix_frames (region : Finset ℕ) (input : List Cell) (before : State) (a b : ℕ) :
    LinearFrames region input (gateCode a b) before := by
  apply LinearFrames.of_static
  intro instruction member state
  simp only [gateCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h|h))|h <;> subst instruction <;> trivial

theorem gate_control_execute (input : List Cell) (before : State) (base a b cursor bound origin : ℕ)
    (zero nonzero : Label) :
    (controlInstruction origin (.branch .flag zero nonzero)).execute input
      (gateResult before base a b cursor bound) =
    some {gateResult before base a b cursor bound with
      pc:=labelAddress origin (if cursor<bound then nonzero else zero)} := by
  by_cases inside : cursor<bound <;>
    simp [controlInstruction,Instruction.execute,gateResult,State.set,Cell.nat?,inside]

theorem initGate_body : (basicBlock Label.initGate).body=gateCode 7 8 := rfl
theorem zeroGate_body : (basicBlock Label.zeroGate).body=gateCode 7 8 := rfl
theorem scatterGate_body : (basicBlock Label.scatterGate).body=gateCode 7 8 := rfl
theorem stepGate_body : (basicBlock Label.stepGate).body=gateCode 6 3 := rfl

end PDROC.CalibrationRow
