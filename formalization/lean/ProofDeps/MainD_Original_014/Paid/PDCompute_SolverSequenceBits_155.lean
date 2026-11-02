module

public import Paid.PDCompute_SolverCommandBits_154
public import Paid.PDCompute_SolverSequenceMemory_051
public import Paid.PDCompute_Pack_TraceInvariant_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)
open PDROC.CalibrationRow.Operand

theorem HeaderValueBits.update {values : ℕ → Cell} {budget target : ℕ} {value : Cell}
    (bits : HeaderValueBits values budget) (bounded : value.bits≤budget) :
    HeaderValueBits (Function.update values target value) budget := by
  intro slot inside
  by_cases same : slot=target
  · subst slot
    simpa only [Function.update_self] using bounded
  · simpa only [Function.update_of_ne same] using bits slot inside

theorem HeaderValueBits.of_safe {before : State} {base budget : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (safe : RootD27.Bits.SafeBits before budget) : HeaderValueBits values budget := by
  intro slot inside
  have actual:=safe.heap (base+slot) (header.live slot inside)
  simpa only [header.value slot inside] using actual

/-- Finite proof-side evaluated-value bookkeeping, with NO runtime/time/
space witness. Each concrete original block must prove every scalar's
actual numerical bound; this predicate is not a new original premise. -/
def HeaderEvaluatedBits (budget : ℕ) : List HeaderCommand → (ℕ → Cell) → Prop
  | [],_ => True
  | command::rest,values => ∃ next,command.eval values=some next ∧ HeaderValueBits next budget ∧ HeaderEvaluatedBits budget rest next

theorem headerCode_prefix_safe (commands : List HeaderCommand) (input : List Cell) (before : State)
    (base budget : ℕ) (values : ℕ → Cell) (valid : ∀ command∈commands,command.Valid)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (bounded : HeaderEvaluatedBits budget commands values)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+(headerCode commands).length)≤budget) :
    PrefixSafe input (headerCode commands) before budget := by
  induction commands generalizing before values with
  | nil => exact PrefixSafe.nil input before budget safe
  | cons command rest ih =>
    obtain ⟨next,evaluated,nextBits,tailBounds⟩:=bounded
    have commandValid : command.Valid := valid command (by simp)
    obtain ⟨middle,run,middleHeader,middleFresh,middlePC,_,_⟩:=command.realize input before base 0 0 values next commandValid header fresh evaluated
    have firstPC : natBits (before.pc+command.code.length)≤budget :=
      (natBits_mono (by change before.pc+command.code.length≤before.pc+(command.code++headerCode rest).length; rw [List.length_append]; omega)).trans pcBits
    have firstSafe:=command.prefix_safe input before base budget values next commandValid header fresh evaluated safe nextBits addressBits firstPC
    have laterPC : natBits (middle.pc+(headerCode rest).length)≤budget := by
      rw [middlePC]
      simpa only [headerCode,List.flatMap_cons,List.length_append,Nat.add_assoc] using pcBits
    have laterSafe:=ih middle next (fun command member=>valid command (by simp only [List.mem_cons]; exact Or.inr member))
      middleHeader middleFresh (firstSafe.final run) tailBounds laterPC
    exact PrefixSafe.append input command.code (headerCode rest) before middle budget run firstSafe laterSafe

/-- Canonical real scalar-block trace with memory and operand bits on
the SAME witness. The concrete block supplies evaluated-value bounds,
not a machine run or postulated final resource guarantee. -/
theorem headerCode_trace_bits (commands : List HeaderCommand) (program : Program) (input : List Cell) (before : State)
    (base n k budget : ℕ) (values next : ℕ → Cell) (valid : ∀ command∈commands,command.Valid)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (evaluated : headerEval commands values=some next) (safe : RootD27.Bits.SafeBits before budget)
    (bounded : HeaderEvaluatedBits budget commands values) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+(headerCode commands).length)≤budget)
    (fetch : FetchesCode program before.pc (headerCode commands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤165*(commands.length+1) ∧
      Header after base next ∧ after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode commands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  obtain ⟨after,run,afterHeader,afterFresh,afterPC,frame,output⟩:=headerCode_realize commands input before base n k values next valid header fresh evaluated
  have prefixSafe:=headerCode_prefix_safe commands input before base budget values valid header fresh safe bounded addressBits pcBits
  obtain ⟨trace,head,last,chain,cost,invariant⟩:=PDCompute.Pack.linearExecute_trace_invariant program input (headerCode commands)
    (headerCode_straight commands) before after fetch run (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      exact ⟨headerCode_prefix_memory commands input before state base values next valid header fresh evaluated count bound executed,prefixSafe count state executed⟩)
  refine ⟨trace,after,head,last,chain,?_,afterHeader,afterFresh,afterPC,frame,output,invariant⟩
  have codeBound:=headerCode_length_le commands
  omega

end PDCompute.Solver
