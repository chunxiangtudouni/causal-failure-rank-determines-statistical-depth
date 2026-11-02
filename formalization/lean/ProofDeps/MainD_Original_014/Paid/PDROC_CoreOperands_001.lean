module

public import Paid.PDROC_D27Prepare_Assembly_006
public import Paid.RootD27Bits_SlotPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CoreOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources RootD27.Bits

def prepareBudget (P : Parameters) (fee : ℚ) : ℕ := operandBudget P fee+21

/-- Convert the actual raw invariant to ALL original stateCellBits,
including live addresses and PC, using the existing resource theorem. -/
theorem stateBounds_safe {state : State} {budget : ℕ}
    (bounds : StateBounds 64 budget state) (counter : state.pc≤pc 45) :
    SafeBits state (budget+21) := by
  apply stateCellBits_le state 64 (pc 45) (budget+21) bounds.live counter
  · intro target
    have actual := bounds.registers target
    omega
  · intro address live
    have actual := bounds.heapValues address live
    omega
  · intro value member
    have actual := bounds.outputs value member
    omega
  · have small : natBits 64=7 := by decide
    omega
  · have small : natBits (pc 45)=14 := by decide
    omega

theorem preFinal_safe (P : Parameters) (fee : ℚ) (state : State)
    (actual : PDROC.D27Prepare.Assembly.PreFinalState P fee state) :
    SafeBits state (prepareBudget P fee) :=
  stateBounds_safe actual.bounded actual.location.le

/-- The real original raw6 prefix, with its exact State/scratch/heap13,
now carries full SafeBits at EVERY fetched state of that same trace. -/
theorem raw_preFinal_safe (P : Parameters) (fee : ℚ) :
    ∃ (final : State) (trace : List State), PDROC.D27Prepare.Assembly.PreFinalState P fee final ∧
      trace.head?=some initial ∧ trace.getLast?=some final ∧
      trace.IsChain (fun before after => step PDROC.D27Prepare.Program.program (rawInput P fee) before=some after) ∧
      (∀ state∈trace,SafeBits state (prepareBudget P fee)) ∧
      (∀ state∈trace,state.output=[]) ∧ (∀ state∈trace.dropLast,state.pc<pc 45) := by
  obtain ⟨final,trace,actual,head,last,chain,_length,bounds⟩ :=
    PDROC.D27Prepare.Assembly.raw_preFinal_trace P fee
  have counters := (PDROC.D27Prepare.Prefix.chain_pc_cut PDROC.D27Prepare.Program.program (rawInput P fee)
    (pc 45) (PDROC.D27Prepare.Prefix.terminal_step_forward (rawInput P fee)) trace final chain last actual.location).1
  exact ⟨final,trace,actual,head,last,chain,
    fun state member => stateBounds_safe (bounds state member) (counters state member),
    PDROC.D27Prepare.Prefix.outputs_empty PDROC.D27Prepare.Program.program (rawInput P fee) trace final chain last actual.output,
    PDROC.D27Prepare.Prefix.preFinal_trace_pc (rawInput P fee) trace final chain last actual.location⟩

theorem prepareBudget_uniform_polynomial :
    ∃ C degree : ℕ,0<C ∧ ∀ (P : Parameters) (fee : ℚ),
      prepareBudget P fee≤C*(variableGammaSize P fee)^degree := by
  obtain ⟨C,degree,positive,bounds⟩ := common_polynomial_envelope
  exact ⟨C,degree,positive,fun P fee => (bounds P fee).2.2⟩

end PDROC.CoreOperands
