module
public import Paid.RootD27Bits_SlotPrefix_004

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits

/-- Actual scalar instruction safety, with the same original full-state
budget. The concrete serializer proves the numerical NatOp result bounds. -/
theorem constant_execute_safe (input : List Cell) (before after : State) (target : Register) (value : Cell) (budget : ℕ)
    (safe : SafeBits before budget) (bounded : value.bits ≤ budget) (pcBits : natBits (before.pc+1) ≤ budget)
    (execute : Instruction.execute input (.constant target value) before=some after) : SafeBits after budget := by
  simp only [Instruction.execute] at execute
  have same:=Option.some.inj execute
  subst after
  exact (safe.withPC (before.pc+1) pcBits).set target value bounded

theorem load_execute_safe (input : List Cell) (before after : State) (target pointer : Register) (address budget : ℕ)
    (safe : SafeBits before budget) (hpointer : before.register pointer=.natural address) (live : address∈before.live)
    (pcBits : natBits (before.pc+1) ≤ budget)
    (execute : Instruction.execute input (.load target pointer) before=some after) : SafeBits after budget := by
  simp [Instruction.execute,hpointer,Cell.nat?,live] at execute
  subst after
  exact (safe.withPC (before.pc+1) pcBits).set target (before.heap address) (safe.heap address live)

theorem store_execute_safe (input : List Cell) (before after : State) (pointer source : Register) (address budget : ℕ)
    (safe : SafeBits before budget) (hpointer : before.register pointer=.natural address)
    (pcBits : natBits (before.pc+1) ≤ budget)
    (execute : Instruction.execute input (.store pointer source) before=some after) : SafeBits after budget := by
  simp [Instruction.execute,hpointer,Cell.nat?] at execute
  subst after
  have addressBits:=safe.register pointer
  rw [hpointer] at addressBits
  have naturalBits : natBits address ≤ budget:=by change 1+natBits address ≤ budget at addressBits;omega
  exact (safe.store address (before.register source) naturalBits (safe.register source)).withPC (before.pc+1) pcBits

theorem natOp_execute_safe (input : List Cell) (before after : State) (operation : NatOp) (target left right : Register)
    (first second result budget : ℕ) (safe : SafeBits before budget)
    (hleft : before.register left=.natural first) (hright : before.register right=.natural second)
    (evaluated : operation.eval first second=some result) (bounded : 1+natBits result ≤ budget)
    (pcBits : natBits (before.pc+1) ≤ budget)
    (execute : Instruction.execute input (.natOp operation target left right) before=some after) : SafeBits after budget := by
  simp [Instruction.execute,hleft,hright,Cell.nat?,evaluated] at execute
  subst after
  exact (safe.withPC (before.pc+1) pcBits).set target (.natural result) bounded

theorem jump_execute_safe (input : List Cell) (before after : State) (target budget : ℕ)
    (safe : SafeBits before budget) (bounded : natBits target ≤ budget)
    (execute : Instruction.execute input (.jump target) before=some after) : SafeBits after budget := by
  simp only [Instruction.execute] at execute
  have same:=Option.some.inj execute
  subst after
  exact safe.withPC target bounded

theorem branch_execute_safe (input : List Cell) (before after : State) (condition : Register) (value zeroPC nonzeroPC budget : ℕ)
    (safe : SafeBits before budget) (hvalue : before.register condition=.natural value)
    (zeroBits : natBits zeroPC ≤ budget) (nonzeroBits : natBits nonzeroPC ≤ budget)
    (execute : Instruction.execute input (.branchZero condition zeroPC nonzeroPC) before=some after) : SafeBits after budget := by
  simp [Instruction.execute,hvalue,Cell.nat?] at execute
  subst after
  apply safe.withPC
  split <;> assumption

theorem indirect_execute_safe (input : List Cell) (before after : State) (source : Register) (target budget : ℕ)
    (safe : SafeBits before budget) (hsource : before.register source=.natural target)
    (execute : Instruction.execute input (.jumpIndirect source) before=some after) : SafeBits after budget := by
  simp [Instruction.execute,hsource,Cell.nat?] at execute
  subst after
  have bounded:=safe.register source
  rw [hsource] at bounded
  apply safe.withPC target
  change 1+natBits target ≤ budget at bounded
  omega

end PDCompute.Pack
