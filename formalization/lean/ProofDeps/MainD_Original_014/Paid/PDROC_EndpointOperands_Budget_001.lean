module

public import Paid.PDROC_EndpointOperands_Base_001
public import Paid.PDROC_EndpointOperands_Math_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits RootD27.Bits

/-- A numerical envelope derived from the REAL caller carry and the
fixed intrinsic endpoint rational budget. It places no P-only bound on
arbitrary old caller registers, live values or output cells. -/
def operandBudget (P : Parameters) (carry : ℕ) : ℕ :=
  16*(carry+rationalBudget P+1)

theorem caller_natBits (before : State) (carry : ℕ) (safe : SafeBits before carry)
    (target : Register) (value : ℕ) (typed : before.register target=.natural value) :
    natBits value ≤ carry := by
  have bounded := safe.register target
  rw [typed] at bounded
  change 1+natBits value ≤ carry at bounded
  omega

theorem naturalCap_bits_of_caller (P : Parameters) (base E returnPC carry : ℕ)
    (baseBits : natBits base ≤ carry) (cacheBits : natBits E ≤ carry)
    (returnBits : natBits returnPC ≤ carry) (stopBits : natBits P.certificate.M ≤ carry) :
    natBits (naturalCap P base E returnPC) ≤ 4*carry+11 := by
  have first := natBits_add_le base E
  have second := natBits_add_le (base+E) returnPC
  have third := natBits_add_le (base+E+returnPC) (2*P.certificate.M)
  have fourth := natBits_add_le (base+E+returnPC+2*P.certificate.M) 256
  have doubled := natBits_mul_le 2 P.certificate.M
  have two : natBits 2=2 := by decide
  have fixed256 : natBits 256=9 := by decide
  rw [two] at doubled
  rw [fixed256] at fourth
  unfold naturalCap
  omega

theorem pcCap_bits_of_caller (origin returnPC carry : ℕ)
    (originBits : natBits origin ≤ carry) (returnBits : natBits returnPC ≤ carry) :
    natBits (pcCap origin returnPC) ≤ 2*carry+10 := by
  have first := natBits_add_le origin returnPC
  have second := natBits_add_le (origin+returnPC) 512
  have fixed512 : natBits 512=10 := by decide
  rw [fixed512] at second
  unfold pcCap
  omega

theorem carry_le_operandBudget (P : Parameters) (carry : ℕ) : carry ≤ operandBudget P carry := by
  dsimp only [operandBudget]
  omega

theorem rationalBudget_le_operandBudget (P : Parameters) (carry : ℕ) :
    rationalBudget P ≤ operandBudget P carry := by
  dsimp only [operandBudget]
  omega

theorem safeBits_operandBudget (P : Parameters) (before : State) (carry : ℕ)
    (callerSafe : SafeBits before carry) : SafeBits before (operandBudget P carry) :=
  safeBits_mono callerSafe (carry_le_operandBudget P carry)

/-- Every control cap follows from actual entry Cells and actual PC.
The only extra resource premise is the real caller's original SafeBits
carry, not supplied numerical/trace/initialization oracles. -/
theorem controlBudget_of_caller (P : Parameters) (origin base E returnPC carry : ℕ) (before : State)
    (callerSafe : SafeBits before carry) (position : before.pc=origin)
    (fresh : before.register .fresh=.natural base) (cache : before.register .address=.natural E)
    (ret : before.register .old=.natural returnPC) (stop : before.register .index=.natural P.certificate.M) :
    ControlBudget P origin base E returnPC (operandBudget P carry) := by
  have baseBits := caller_natBits before carry callerSafe .fresh base fresh
  have cacheBits := caller_natBits before carry callerSafe .address E cache
  have returnBits := caller_natBits before carry callerSafe .old returnPC ret
  have stopBits := caller_natBits before carry callerSafe .index P.certificate.M stop
  have originBits : natBits origin ≤ carry := by simpa only [position] using callerSafe.pc
  have naturalBits := naturalCap_bits_of_caller P base E returnPC carry baseBits cacheBits returnBits stopBits
  have pcBits := pcCap_bits_of_caller origin returnPC carry originBits returnBits
  constructor
  · dsimp only [operandBudget]
    omega
  · dsimp only [operandBudget]
    omega
  · dsimp only [operandBudget]
    omega

theorem operandBudget_of_caller (P : Parameters) (origin base E returnPC carry : ℕ) (before : State)
    (callerSafe : SafeBits before carry) (position : before.pc=origin)
    (fresh : before.register .fresh=.natural base) (cache : before.register .address=.natural E)
    (ret : before.register .old=.natural returnPC) (stop : before.register .index=.natural P.certificate.M) :
    ControlBudget P origin base E returnPC (operandBudget P carry) ∧
      rationalBudget P ≤ operandBudget P carry ∧ SafeBits before (operandBudget P carry) :=
  ⟨controlBudget_of_caller P origin base E returnPC carry before callerSafe position fresh cache ret stop,
    rationalBudget_le_operandBudget P carry,safeBits_operandBudget P before carry callerSafe⟩

end PDROC.EndpointOperands
