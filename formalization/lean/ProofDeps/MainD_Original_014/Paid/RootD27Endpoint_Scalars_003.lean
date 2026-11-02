module

public import Paid.RootD27Endpoint_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver

def initializedValues (values : ℕ → Cell) (gamma : ℚ) : ℕ → Cell :=
  let a:=Function.update values 13 (.rational 1)
  let b:=Function.update a 14 (.rational 2)
  let c:=Function.update b 8 (.natural 0)
  let d:=Function.update c 7 (.rational 1)
  let e:=Function.update d 12 (.rational (2*gamma))
  let f:=Function.update e 15 (.rational (1+2*gamma))
  let g:=Function.update f 16 (.rational (1-2*gamma))
  Function.update g 6 (.rational ((1+2*gamma)/(1-2*gamma)))

/-- This is the success condition of the literal four/six/ten-op scalar
expansions. The live-header and actual fetched-trace refinement is provided
by the frozen headerCode_trace theorem, not by this cell-map identity. -/
theorem initialize_eval (P : Parameters) (values : ℕ → Cell)
    (hgamma : values 2=.rational P.certificate.gamma) :
    headerEval initialCommands values=some (initializedValues values P.certificate.gamma) := by
  simp [initialCommands,headerEval,HeaderCommand.eval,initializedValues,
    Cell.rat?,RatOp.eval,hgamma,odds_den_ne_zero P]

theorem initialCommands_valid : ∀ command∈initialCommands, command.Valid := by
  intro command member
  simp only [initialCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h <;> subst command <;>
    norm_num [HeaderCommand.Valid,headerWords]

theorem initializedValues_preserves_arguments (values : ℕ → Cell) (gamma : ℚ)
    (slot : ℕ) (hslot : slot<6) : initializedValues values gamma slot=values slot := by
  have h6 : slot≠6 := by omega
  have h7 : slot≠7 := by omega
  have h8 : slot≠8 := by omega
  have h12 : slot≠12 := by omega
  have h13 : slot≠13 := by omega
  have h14 : slot≠14 := by omega
  have h15 : slot≠15 := by omega
  have h16 : slot≠16 := by omega
  simp [initializedValues,h6,h7,h8,h12,h13,h14,h15,h16]

theorem initializedValues_odds (P : Parameters) (values : ℕ → Cell) :
    initializedValues values P.certificate.gamma 6=.rational P.certificate.odds := by
  rfl

theorem initializedValues_power (values : ℕ → Cell) (gamma : ℚ) :
    initializedValues values gamma 7=.rational 1 := by
  simp [initializedValues]

theorem initializedValues_row (values : ℕ → Cell) (gamma : ℚ) :
    initializedValues values gamma 8=.natural 0 := by
  simp [initializedValues]

def rowValues (values : ℕ → Cell) (gamma fee power : ℚ) (m : ℕ) : ℕ → Cell :=
  let e:=1/(1+power)
  let a:=Function.update values 15 (.rational (1+power))
  let b:=Function.update a 9 (.rational e)
  let c:=Function.update b 16 (.rational (2*e))
  let d:=Function.update c 16 (.rational (1-2*e))
  let f:=Function.update d 18 (.rational ((m:ℚ)*(1-2*e)))
  let g:=Function.update f 10 (.rational ((m:ℚ)*(1-2*e)/(2*gamma)))
  Function.update g 11 (.rational (fee*((m:ℚ)*(1-2*e)/(2*gamma))))

theorem row_eval (gamma fee power : ℚ) (m : ℕ) (values : ℕ → Cell)
    (hone : values 13=.rational 1) (htwo : values 14=.rational 2)
    (hpower : values 7=.rational power) (hfee : values 4=.rational fee)
    (hrow : values 18=.rational (m:ℚ)) (hden : values 12=.rational (2*gamma))
    (herror : 1+power≠0) (hmean : 2*gamma≠0) :
    headerEval rowCommands values=some (rowValues values gamma fee power m) := by
  simp [rowCommands,headerEval,HeaderCommand.eval,rowValues,Cell.rat?,RatOp.eval,
    hone,htwo,hpower,hfee,hrow,hden,herror,hmean]

theorem rowCommands_valid : ∀ command∈rowCommands, command.Valid := by
  intro command member
  simp only [rowCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h <;> subst command <;>
    norm_num [HeaderCommand.Valid,headerWords]

theorem rowValues_error (values : ℕ → Cell) (gamma fee power : ℚ) (m : ℕ) :
    rowValues values gamma fee power m 9=.rational (endpointFromPower gamma fee power m).error := by
  simp [rowValues,endpointFromPower]

theorem rowValues_charge (values : ℕ → Cell) (gamma fee power : ℚ) (m : ℕ) :
    rowValues values gamma fee power m 11=.rational (endpointFromPower gamma fee power m).charge := by
  rfl

end RootD27.Endpoint
