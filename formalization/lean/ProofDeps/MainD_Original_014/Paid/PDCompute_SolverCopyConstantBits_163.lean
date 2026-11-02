module

public import Paid.PDCompute_SolverSequenceBits_155

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Only fixed literal assignments and genuine live-header copies. -/
def CopyConstantBound (budget : ℕ) : HeaderCommand → Prop
  | .constant _ value => value.bits≤budget
  | .copy _ _ => True
  | .rational _ _ _ _ => False

/-- Discharge actual finite value guards for ANY original copy/literal
block. Existing header cells are copied unchanged at the same budget. -/
theorem copyConstantCommands_evaluated_bits (commands : List HeaderCommand) (values : ℕ → Cell) (budget : ℕ)
    (valid : ∀ command∈commands,command.Valid) (initial : HeaderValueBits values budget)
    (bounded : ∀ command∈commands,CopyConstantBound budget command) : HeaderEvaluatedBits budget commands values := by
  induction commands generalizing values with
  | nil => trivial
  | cons command rest ih =>
    have currentValid:=valid command (by simp)
    have currentBound:=bounded command (by simp)
    have tailValid : ∀ command∈rest,command.Valid := fun command member=>valid command (List.mem_cons_of_mem _ member)
    have tailBound : ∀ command∈rest,CopyConstantBound budget command := fun command member=>bounded command (List.mem_cons_of_mem _ member)
    cases command with
    | constant target value =>
      let next:=Function.update values target value
      have nextBits : HeaderValueBits next budget := initial.update currentBound
      exact ⟨next,rfl,nextBits,ih next tailValid nextBits tailBound⟩
    | copy source target =>
      let next:=Function.update values target (values source)
      have nextBits : HeaderValueBits next budget := initial.update (initial source currentValid.1)
      exact ⟨next,rfl,nextBits,ih next tailValid nextBits tailBound⟩
    | rational operation left right target => exact False.elim currentBound

/-- One actual canonical original copy/constant trace; all real runtime
facts are supplied by existing code realization, never an output oracle. -/
theorem copyConstant_trace_bits (commands : List HeaderCommand) (program : Program) (input : List Cell) (before : State)
    (base n k budget : ℕ) (values next : ℕ → Cell) (valid : ∀ command∈commands,command.Valid)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (evaluated : headerEval commands values=some next) (safe : RootD27.Bits.SafeBits before budget)
    (bounded : ∀ command∈commands,CopyConstantBound budget command) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+(headerCode commands).length)≤budget) (fetch : FetchesCode program before.pc (headerCode commands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤165*(commands.length+1) ∧
      Header after base next ∧ after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode commands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget :=
  headerCode_trace_bits commands program input before base n k budget values next valid header fresh evaluated safe
    (copyConstantCommands_evaluated_bits commands values budget valid (HeaderValueBits.of_safe header safe) bounded) addressBits pcBits fetch

end PDCompute.Solver
