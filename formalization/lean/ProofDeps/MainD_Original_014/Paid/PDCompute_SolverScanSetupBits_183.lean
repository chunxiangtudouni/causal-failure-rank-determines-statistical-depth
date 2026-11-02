module

public import Paid.PDCompute_SolverLiteralFieldsBits_165
public import Paid.PDCompute_SolverFinalChoiceSetup_104
public import Paid.PDCompute_SolverScanReset_106
public import Paid.PDCompute_Nat_RuntimeSequenceBits_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame PDCompute.NatControl

theorem finalChoiceCommands_copyBound (budget : ℕ) (small : 4≤budget) :
    ∀ command∈finalChoiceCommands,CopyConstantBound budget command := by
  intro command member
  rcases List.mem_append.mp member with first|later
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at first
    rcases first with same|same <;> subst command <;> trivial
  · exact terminalFieldsCommands_copyBound true budget small command later

theorem finalChoice_trace_bits (program : Program) (input : List Cell) (before : State)
    (base n k budget : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+(headerCode finalChoiceCommands).length)≤budget)
    (fetch : FetchesCode program before.pc (headerCode finalChoiceCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤1485 ∧
      Header after base (finalChoiceValues values) ∧ after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode finalChoiceCommands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have cost : 165*(finalChoiceCommands.length+1)=1485 := rfl
  simpa only [cost] using copyConstant_trace_bits finalChoiceCommands program input before base n k budget values (finalChoiceValues values)
    finalChoiceCommands_valid header fresh (finalChoiceCommands_eval values) safe (finalChoiceCommands_copyBound budget small) addressBits pcBits fetch

theorem scanReset_evaluated_bits (values : ℕ → Cell) (source budget : ℕ) (penalty : ℚ)
    (hsource : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (initial : HeaderValueBits values budget) (small : 4≤budget) (pointerBits : 1+natBits (source+1)≤budget) :
    RuntimeEvaluatedBits budget scanResetCommands values := by
  have zeroBits : (.natural 0 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have oneBits : (.natural 1 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have penaltyBits : (.rational penalty : Cell).bits≤budget := by simpa only [hpenalty] using initial 2 (by decide)
  let a:=Function.update values 23 (.natural 0)
  let b:=Function.update a 24 (.rational penalty)
  let c:=Function.update b 25 (.natural 0)
  let d:=Function.update c 46 (.natural 1)
  let e:=Function.update d 39 (.natural (source+1))
  have ba : HeaderValueBits a budget := initial.update zeroBits
  have bb : HeaderValueBits b budget := ba.update penaltyBits
  have bc : HeaderValueBits c budget := bb.update zeroBits
  have bd : HeaderValueBits d budget := bc.update oneBits
  have be : HeaderValueBits e budget := bd.update pointerBits
  refine ⟨a,rfl,ba,b,?_,bb,c,rfl,bc,d,rfl,bd,e,?_,be,True.intro⟩
  · simp [RuntimeCommand.eval,HeaderCommand.eval,a,b,hpenalty]
  · simp [RuntimeCommand.eval,Cell.nat?,NatOp.eval,a,b,c,d,e,hsource]

/-- Real saved source+1 and cutoff initialization before the scan;
all five commands are discharged from actual original Header values. -/
theorem scanReset_trace_bits (program : Program) (input : List Cell) (before : State)
    (base source n k budget : ℕ) (values : ℕ → Cell) (penalty : ℚ)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget) (pointerBits : 1+natBits (source+1)≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+(runtimeCode scanResetCommands).length)≤budget)
    (fetch : FetchesCode program before.pc (runtimeCode scanResetCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤990 ∧
      Header after base (scanResetValues values source penalty) ∧ after.register .fresh=.natural base ∧ after.pc=before.pc+(runtimeCode scanResetCommands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have cost : 165*(scanResetCommands.length+1)=990 := rfl
  simpa only [cost] using runtimeCode_trace_bits scanResetCommands program input before base n k budget values (scanResetValues values source penalty)
    scanResetCommands_valid header fresh (scanResetCommands_eval values source penalty hsource hpenalty) safe
    (scanReset_evaluated_bits values source budget penalty hsource hpenalty (HeaderValueBits.of_safe header safe) small pointerBits) addressBits pcBits fetch

end PDCompute.Solver
