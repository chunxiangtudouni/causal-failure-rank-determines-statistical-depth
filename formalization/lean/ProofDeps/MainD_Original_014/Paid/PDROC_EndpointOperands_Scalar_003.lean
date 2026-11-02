module

public import Paid.PDROC_EndpointOperands_Scalar_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver RootD27.Endpoint RootD27.Bits PDROC.CalibrationRow.Operand

theorem advance_evaluated_bits (P : Parameters) (m budget : ℕ) (values : ℕ → Cell)
    (rowBound : m≤P.certificate.M+1) (oldBits : HeaderValueBits values budget)
    (power : values 7=.rational (powerRecurrence P.certificate.odds m))
    (odds : values 6=.rational P.certificate.odds) (rational : rationalBudget P≤budget) :
    HeaderEvaluatedBits budget [.rational .multiply 7 6 7] values := by
  let next := Function.update values 7
    (.rational (powerRecurrence P.certificate.odds m*P.certificate.odds))
  have nextBits : HeaderValueBits next budget :=
    oldBits.update ((rationalBounds P m rowBound).advancePower.trans rational)
  refine ⟨next,?_,nextBits,True.intro⟩
  simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,power,odds,next]

theorem advance_scalar_prefix_safe (input : List Cell) (P : Parameters)
    (origin base E returnPC m budget : ℕ) (before : State) (values : ℕ → Cell)
    (rowBound : m≤P.certificate.M+1) (header : Header before base values)
    (fresh : before.register .fresh=.natural base)
    (power : values 7=.rational (powerRecurrence P.certificate.odds m))
    (odds : values 6=.rational P.certificate.odds) (safe : SafeBits before budget)
    (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P≤budget) (position : before.pc+10≤pcCap origin returnPC) :
    PrefixSafe input (headerCode [.rational .multiply 7 6 7]) before budget := by
  apply headerCode_prefix_safe [.rational .multiply 7 6 7] input before base budget values
    (by
      intro command member
      have same : command=HeaderCommand.rational .multiply 7 6 7 := by
        simpa only [List.mem_singleton] using member
      subst command
      norm_num [HeaderCommand.Valid,headerWords]) header fresh safe
  · exact advance_evaluated_bits P m budget values rowBound (HeaderValueBits.of_safe header safe) power odds rational
  · exact ControlBudget.headerAddress P origin base E returnPC budget control
  · exact ControlBudget.pc P origin base E returnPC budget _ control position

end PDROC.EndpointOperands
