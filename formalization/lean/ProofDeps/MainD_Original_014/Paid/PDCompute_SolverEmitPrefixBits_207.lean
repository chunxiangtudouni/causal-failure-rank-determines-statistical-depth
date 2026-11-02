module

public import Paid.RootD27Core_EmitLoop_005
public import Paid.PDCompute_SolverCompareBits_164
public import Paid.PDCompute_Pack_InstructionBits_058

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)
open PDROC.CalibrationRow.Operand

/-- All FIVE literal instructions of the original emitter body: actual
heap read, actual stream append, and the two real natural updates. -/
theorem emitCellCode_prefix_safe (input : List Cell) (before : State) (pointer remaining budget : ℕ) (value : Cell)
    (address : before.register .address=.natural pointer) (index : before.register .index=.natural (remaining+1))
    (live : pointer∈before.live) (payload : before.heap pointer=value) (safe : RootD27.Bits.SafeBits before budget)
    (oneBits : (.natural 1 : Cell).bits≤budget) (pointerBits : 1+natBits (pointer+1)≤budget)
    (pcBits : natBits (before.pc+5)≤budget) : PrefixSafe input RootD27.Core.emitCellCode before budget := by
  let a:=({before with pc:=before.pc+1}).set .value value
  let b : State:={a with pc:=a.pc+1,output:=a.output++[value]}
  let c:=({b with pc:=b.pc+1}).set .flag (.natural 1)
  let d:=({c with pc:=c.pc+1}).set .address (.natural (pointer+1))
  let e:=({d with pc:=d.pc+1}).set .index (.natural remaining)
  have aRun : Instruction.execute input (.load .value .address) before=some a := by
    simp [Instruction.execute,address,Cell.nat?,live,payload,a]
  have aSafe:=PDCompute.Pack.load_execute_safe input before a .value .address pointer budget safe address live
    ((natBits_mono (by omega : before.pc+1≤before.pc+5)).trans pcBits) aRun
  have bRun : Instruction.execute input (.output .value) a=some b := by simp [Instruction.execute,a,b,State.set]
  have bSafe:=PDLower.CalibrationCompute.output_execute_safe input a b .value budget aSafe
    ((natBits_mono (by change before.pc+1+1≤before.pc+5;omega)).trans pcBits) bRun
  have cRun : Instruction.execute input (.constant .flag (.natural 1)) b=some c := rfl
  have cSafe:=PDCompute.Pack.constant_execute_safe input b c .flag (.natural 1) budget bSafe oneBits
    ((natBits_mono (by change before.pc+1+1+1≤before.pc+5;omega)).trans pcBits) cRun
  have cAddress : c.register .address=.natural pointer := by simp [c,b,a,State.set,address]
  have cFlag : c.register .flag=.natural 1 := by simp [c,State.set]
  have dRun : Instruction.execute input (.natOp .add .address .address .flag) c=some d := by
    simp [Instruction.execute,cAddress,cFlag,Cell.nat?,NatOp.eval,d]
  have dSafe:=PDCompute.Pack.natOp_execute_safe input c d .add .address .address .flag pointer 1 (pointer+1) budget cSafe cAddress cFlag rfl pointerBits
    ((natBits_mono (by change before.pc+1+1+1+1≤before.pc+5;omega)).trans pcBits) dRun
  have dIndex : d.register .index=.natural (remaining+1) := by simp [d,c,b,a,State.set,index]
  have dFlag : d.register .flag=.natural 1 := by simp [d,c,State.set]
  have remainingBits : 1+natBits remaining≤budget := by
    have counted:=safe.register .index
    rw [index] at counted
    change 1+natBits (remaining+1)≤budget at counted
    exact (Nat.add_le_add_left (natBits_mono (by omega : remaining≤remaining+1)) 1).trans counted
  have subtract : NatOp.subtract.eval (remaining+1) 1=some remaining := by simp [NatOp.eval]
  have eRun : Instruction.execute input (.natOp .subtract .index .index .flag) d=some e := by
    simp [Instruction.execute,dIndex,dFlag,Cell.nat?,subtract,e]
  have eCounter : natBits (d.pc+1)≤budget := by simpa only [d,c,b,a,State.set,Nat.add_assoc] using pcBits
  have eSafe:=PDCompute.Pack.natOp_execute_safe input d e .subtract .index .index .flag (remaining+1) 1 remaining budget dSafe dIndex dFlag subtract remainingBits eCounter eRun
  exact PrefixSafe.cons input _ _ before a budget aRun safe
    (PrefixSafe.cons input _ _ a b budget bRun aSafe
      (PrefixSafe.cons input _ _ b c budget cRun bSafe
        (PrefixSafe.cons input _ _ c d budget dRun cSafe
          (PrefixSafe.cons input _ _ d e budget eRun dSafe (PrefixSafe.nil input e budget eSafe)))))

/-- Same actual one-instruction emit guard, with its true chosen PC. -/
theorem emitHeap_guard_trace_bits (program : Program) (input : List Cell) (before : State)
    (origin returnPC count budget : ℕ) (position : before.pc=origin) (index : before.register .index=.natural count)
    (fetch : FetchesCode program origin (RootD27.Core.emitHeapCode origin returnPC)) (safe : RootD27.Bits.SafeBits before budget)
    (pcBits : natBits (origin+7)≤budget) (returnBits : natBits returnPC≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤30 ∧
      after={before with pc:=if count=0 then returnPC else origin+1} ∧
      (∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let after : State:={before with pc:=if count=0 then returnPC else origin+1}
  have actual : step program input before=some after := by
    simp only [step,position,RootD27.Core.emitHeap_guard_fetch program origin returnPC fetch]
    simp [Instruction.execute,index,Cell.nat?,after]
  have execute : Instruction.execute input (.branchZero .index returnPC (origin+1)) before=some after := by
    simp [Instruction.execute,index,Cell.nat?,after]
  have afterSafe:=PDCompute.Pack.branch_execute_safe input before after .index count returnPC (origin+1) budget safe index returnBits
    ((natBits_mono (by omega : origin+1≤origin+7)).trans pcBits) execute
  refine ⟨[before,after],after,rfl,rfl,List.isChain_pair.mpr actual,time_le_length program [before,after],rfl,?_,?_⟩
  · intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst state <;> exact ⟨rfl,rfl,rfl⟩
  · intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      exact safe
    · subst state
      exact afterSafe

end PDCompute.Solver
