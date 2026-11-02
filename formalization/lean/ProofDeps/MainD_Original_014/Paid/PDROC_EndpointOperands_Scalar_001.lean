module

public import Paid.PDROC_EndpointOperands_Base_001
public import Paid.PDROC_EndpointOperands_Math_001
public import Paid.PDCompute_SolverSequenceBits_155

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver RootD27.Endpoint RootD27.Bits PDROC.CalibrationRow.Operand

/-- The eight ORIGINAL initialization commands have finite evaluated-value
bounds. Untouched header cells retain their real caller bound. -/
theorem initial_evaluated_bits (P : Parameters) (budget : ℕ) (values : ℕ → Cell)
    (oldBits : HeaderValueBits values budget)
    (gamma : values 2=.rational P.certificate.gamma)
    (rational : rationalBudget P≤budget) (zero : (Cell.natural 0).bits≤budget) :
    HeaderEvaluatedBits budget initialCommands values := by
  have numbers := rationalBounds P 0 (by omega)
  let a := Function.update values 13 (.rational 1)
  let b := Function.update a 14 (.rational 2)
  let c := Function.update b 8 (.natural 0)
  let d := Function.update c 7 (.rational 1)
  let e := Function.update d 12 (.rational (2*P.certificate.gamma))
  let f := Function.update e 15 (.rational (1+2*P.certificate.gamma))
  let g := Function.update f 16 (.rational (1-2*P.certificate.gamma))
  let h := Function.update g 6 (.rational P.certificate.odds)
  have aBits : HeaderValueBits a budget := oldBits.update (numbers.one.trans rational)
  have bBits : HeaderValueBits b budget := aBits.update (numbers.two.trans rational)
  have cBits : HeaderValueBits c budget := bBits.update zero
  have dBits : HeaderValueBits d budget := cBits.update (numbers.one.trans rational)
  have eBits : HeaderValueBits e budget := dBits.update (numbers.twoGamma.trans rational)
  have fBits : HeaderValueBits f budget := eBits.update (numbers.oddsNumerator.trans rational)
  have gBits : HeaderValueBits g budget := fBits.update (numbers.oddsDenominator.trans rational)
  have hBits : HeaderValueBits h budget := gBits.update (numbers.odds.trans rational)
  have fifth : (HeaderCommand.rational .multiply 14 2 12).eval d=some e := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,d,c,b,a,e,gamma]
  have sixth : (HeaderCommand.rational .add 13 12 15).eval e=some f := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,e,d,c,b,a,f]
  have seventh : (HeaderCommand.rational .subtract 13 12 16).eval f=some g := by
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,f,e,d,c,b,a,g]
  have eighth : (HeaderCommand.rational .divide 15 16 6).eval g=some h := by
    change (HeaderCommand.rational .divide 15 16 6).eval g=
      some (Function.update g 6 (.rational ((1+2*P.certificate.gamma)/(1-2*P.certificate.gamma))))
    simp [HeaderCommand.eval,RatOp.eval,Cell.rat?,g,f,e,d,c,b,a,odds_den_ne_zero P]
  exact ⟨a,rfl,aBits,b,rfl,bBits,c,rfl,cBits,d,rfl,dBits,e,fifth,eBits,
    f,sixth,fBits,g,seventh,gBits,h,eighth,hBits,True.intro⟩

theorem initial_scalar_prefix_safe (input : List Cell) (P : Parameters)
    (origin base E returnPC budget : ℕ) (before : State) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (gamma : values 2=.rational P.certificate.gamma) (safe : SafeBits before budget)
    (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P≤budget) (position : before.pc+56≤pcCap origin returnPC) :
    PrefixSafe input (headerCode initialCommands) before budget := by
  apply headerCode_prefix_safe initialCommands input before base budget values initialCommands_valid header fresh safe
  · exact initial_evaluated_bits P budget values (HeaderValueBits.of_safe header safe) gamma rational
      (ControlBudget.nat P origin base E returnPC budget 0 control (by omega))
  · exact ControlBudget.headerAddress P origin base E returnPC budget control
  · exact ControlBudget.pc P origin base E returnPC budget _ control (by simpa only [initialScalar_length] using position)

end PDROC.EndpointOperands
