module
public import Paid.PDCompute_Pack_InstructionBits_058
public import Paid.PDCompute_Pack_TraceInvariant_055

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute)

theorem instruction_prefix_invariant (input : List Cell) (instruction : Instruction) (before : State)
    (invariant : State → Prop) (initial : invariant before)
    (preserved : ∀ after,Instruction.execute input instruction before=some after → invariant after) :
    ∀ count ≤ 1,∀ after,linearExecute input ([instruction].take count) before=some after → invariant after := by
  intro count bound after executed
  interval_cases count
  · simp only [List.take_zero,linearExecute] at executed
    have same:=Option.some.inj executed
    subst after
    exact initial
  · have run : Instruction.execute input instruction before=some after:=by simpa [linearExecute] using executed
    exact preserved after run

def constantNatPair (constantTarget : Register) (literal : ℕ) (operation : NatOp) (target left right : Register) : List Instruction:=
  [.constant constantTarget (.natural literal),.natOp operation target left right]
def constantNatFirst (before : State) (constantTarget : Register) (literal : ℕ) : State:=
  ({before with pc:=before.pc+1}).set constantTarget (.natural literal)

/-- Reusable exact two-op arithmetic prefix for tag2-tag, counter1,
source48+base. Both actual intermediate states use the SAME budget. -/
theorem constantNatPair_prefix_safe (input : List Cell) (before after : State) (constantTarget : Register) (literal : ℕ)
    (operation : NatOp) (target left right : Register) (first second result budget count : ℕ)
    (safe : SafeBits before budget) (literalBits : 1+natBits literal ≤ budget)
    (leftValue : (constantNatFirst before constantTarget literal).register left=.natural first)
    (rightValue : (constantNatFirst before constantTarget literal).register right=.natural second)
    (evaluated : operation.eval first second=some result) (resultBits : 1+natBits result ≤ budget)
    (counterBits : natBits (before.pc+2) ≤ budget) (bound : count ≤ 2)
    (executed : linearExecute input ((constantNatPair constantTarget literal operation target left right).take count) before=some after) :
    SafeBits after budget := by
  let middle:=constantNatFirst before constantTarget literal
  have firstPC : natBits (before.pc+1) ≤ budget:=(natBits_mono (by omega : before.pc+1 ≤ before.pc+2)).trans counterBits
  have middleSafe : SafeBits middle budget:=(safe.withPC (before.pc+1) firstPC).set constantTarget (.natural literal) literalBits
  have middlePC : middle.pc+1=before.pc+2:=by simp only [middle,constantNatFirst,State.set]
  have middleCounter : natBits (middle.pc+1) ≤ budget:=middlePC.symm ▸ counterBits
  have firstRun : linearExecute input [.constant constantTarget (.natural literal)] before=some middle := by
    simp [linearExecute,Instruction.execute,middle,constantNatFirst]
  have firstPrefixes:=instruction_prefix_invariant input (.constant constantTarget (.natural literal)) before (fun state=>SafeBits state budget) safe
    (fun state run=>constant_execute_safe input before state constantTarget (.natural literal) budget safe literalBits firstPC run)
  have secondPrefixes:=instruction_prefix_invariant input (.natOp operation target left right) middle (fun state=>SafeBits state budget) middleSafe
    (fun state run=>natOp_execute_safe input middle state operation target left right first second result budget middleSafe
      leftValue rightValue evaluated resultBits middleCounter run)
  have combined:=invariant_prefix_append input [.constant constantTarget (.natural literal)] [.natOp operation target left right]
    before middle firstRun (fun state=>SafeBits state budget) firstPrefixes secondPrefixes
  exact combined count bound after executed

end PDCompute.Pack
