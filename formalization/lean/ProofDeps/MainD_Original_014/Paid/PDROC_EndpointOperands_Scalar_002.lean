module

public import Paid.PDROC_EndpointOperands_Scalar_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver RootD27.Endpoint RootD27.Bits PDROC.CalibrationRow.Operand

/-- The seven original row commands use the true current power/counter.
Every newly written scalar is bounded from its fixed algebraic expression;
no numerical recurrence is applied to an arbitrary old header value. -/
theorem row_evaluated_bits (P : Parameters) (m budget : ℕ) (values : ℕ → Cell)
    (rowBound : m≤P.certificate.M+1) (oldBits : HeaderValueBits values budget)
    (one : values 13=.rational 1) (two : values 14=.rational 2)
    (power : values 7=.rational (powerRecurrence P.certificate.odds m))
    (fee : values 4=.rational P.reviewFee) (row : values 18=.rational (m:ℚ))
    (denominator : values 12=.rational (2*P.certificate.gamma))
    (rational : rationalBudget P≤budget) : HeaderEvaluatedBits budget rowCommands values := by
  have numbers := rationalBounds P m rowBound
  let p := powerRecurrence P.certificate.odds m
  let err := 1/(1+p)
  let a := Function.update values 15 (.rational (1+p))
  let b := Function.update a 9 (.rational err)
  let c := Function.update b 16 (.rational (2*err))
  let d := Function.update c 16 (.rational (1-2*err))
  let e := Function.update d 18 (.rational ((m:ℚ)*(1-2*err)))
  let f := Function.update e 10 (.rational ((m:ℚ)*(1-2*err)/(2*P.certificate.gamma)))
  let g := Function.update f 11 (.rational (P.reviewFee*((m:ℚ)*(1-2*err)/(2*P.certificate.gamma))))
  have aBits : HeaderValueBits a budget := oldBits.update (numbers.powerPlusOne.trans rational)
  have bBits : HeaderValueBits b budget := aBits.update (numbers.error.trans rational)
  have cBits : HeaderValueBits c budget := bBits.update (numbers.twiceError.trans rational)
  have dBits : HeaderValueBits d budget := cBits.update (numbers.oneMinusTwiceError.trans rational)
  have eBits : HeaderValueBits e budget := dBits.update (numbers.meanNumerator.trans rational)
  have fBits : HeaderValueBits f budget := eBits.update (numbers.mean.trans rational)
  have gBits : HeaderValueBits g budget := fBits.update (numbers.charge.trans rational)
  have first : (HeaderCommand.rational .add 13 7 15).eval values=some a := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,one,power,a,p]
  have second : (HeaderCommand.rational .divide 13 15 9).eval a=some b := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,a,b,one,err,p,error_den_ne_zero P m]
  have third : (HeaderCommand.rational .multiply 14 9 16).eval b=some c := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,b,a,c,two]
  have fourth : (HeaderCommand.rational .subtract 13 16 16).eval c=some d := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,c,b,a,d,one]
  have fifth : (HeaderCommand.rational .multiply 18 16 18).eval d=some e := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,d,c,b,a,e,row]
  have sixth : (HeaderCommand.rational .divide 18 12 10).eval e=some f := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,e,d,c,b,a,f,denominator,mean_den_ne_zero P]
  have seventh : (HeaderCommand.rational .multiply 4 10 11).eval f=some g := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,f,e,d,c,b,a,g,fee]
  exact ⟨a,first,aBits,b,second,bBits,c,third,cBits,d,fourth,dBits,e,fifth,eBits,
    f,sixth,fBits,g,seventh,gBits,True.intro⟩

theorem row_scalar_prefix_safe (input : List Cell) (P : Parameters)
    (origin base E returnPC m budget : ℕ) (before : State) (values : ℕ → Cell)
    (rowBound : m≤P.certificate.M+1) (header : Header before base values)
    (fresh : before.register .fresh=.natural base)
    (one : values 13=.rational 1) (two : values 14=.rational 2)
    (power : values 7=.rational (powerRecurrence P.certificate.odds m))
    (fee : values 4=.rational P.reviewFee) (row : values 18=.rational (m:ℚ))
    (denominator : values 12=.rational (2*P.certificate.gamma))
    (safe : SafeBits before budget) (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P≤budget) (position : before.pc+70≤pcCap origin returnPC) :
    PrefixSafe input (headerCode rowCommands) before budget := by
  apply headerCode_prefix_safe rowCommands input before base budget values rowCommands_valid header fresh safe
  · exact row_evaluated_bits P m budget values rowBound (HeaderValueBits.of_safe header safe)
      one two power fee row denominator rational
  · exact ControlBudget.headerAddress P origin base E returnPC budget control
  · exact ControlBudget.pc P origin base E returnPC budget _ control
      (by simpa only [rowScalarCode_length] using position)

end PDROC.EndpointOperands
