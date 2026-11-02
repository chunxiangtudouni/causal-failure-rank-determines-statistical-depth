module

public import Paid.RootD27Endpoint_RowBody_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

/-- Values maintained by the actual cache loop, not new opcode or an
assumed answer. Entry producers and each literal body establish them. -/
structure EndpointValues (P : Parameters) (E returnPC m : ℕ) (values : ℕ → Cell) : Prop where
  cache : values 0=.natural E
  ret : values 1=.natural returnPC
  gamma : values 2=.rational P.certificate.gamma
  stop : values 3=.natural P.certificate.M
  fee : values 4=.rational P.reviewFee
  odds : values 6=.rational P.certificate.odds
  power : values 7=.rational (powerRecurrence P.certificate.odds m)
  counter : values 8=.natural m
  denominator : values 12=.rational (2*P.certificate.gamma)
  one : values 13=.rational 1
  two : values 14=.rational 2

theorem EndpointValues.initialized (P : Parameters) (E returnPC : ℕ) (values : ℕ → Cell)
    (hE : values 0=.natural E) (hret : values 1=.natural returnPC)
    (hgamma : values 2=.rational P.certificate.gamma)
    (hM : values 3=.natural P.certificate.M) (hfee : values 4=.rational P.reviewFee) :
    EndpointValues P E returnPC 0 (initializedValues values P.certificate.gamma) := by
  refine ⟨?_,?_,?_,?_,?_,initializedValues_odds P values,?_,?_,?_,?_,?_⟩
  all_goals simp [initializedValues,powerRecurrence,hE,hret,hgamma,hM,hfee]

theorem EndpointValues.body {P : Parameters} {E returnPC m : ℕ} {values : ℕ → Cell}
    (invariant : EndpointValues P E returnPC m values) :
    EndpointValues P E returnPC (m+1) (bodyValues P values m) := by
  rcases invariant with ⟨cache,ret,gamma,stop,fee,odds,power,counter,denominator,one,two⟩
  constructor <;> simp_all [bodyValues,rowValues]

/-- A real loop body preserves every saved original argument and advances
the established power/counter invariant on the same actual run. -/
theorem EndpointValues.actual_body (P : Parameters) (m : ℕ) (program : Program) (input : List Cell)
    (before : State) (base E returnPC testPC : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (invariant : EndpointValues P E returnPC m values)
    (separated : base+48≤E) (hfetch : FetchesCode program before.pc (rowBodyCode testPC)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤2235 ∧ after.pc=testPC ∧ after.register .fresh=.natural base ∧
      Header after base (bodyValues P values m) ∧
      EndpointValues P E returnPC (m+1) (bodyValues P values m) ∧
      E+1+2*m∈after.live ∧ E+2+2*m∈after.live ∧
      after.heap (E+1+2*m)=.rational (P.endpointConstant m).error ∧
      after.heap (E+2+2*m)=.rational (P.endpointConstant m).charge := by
  obtain ⟨trace,after,hh,hl,hc,ht,hp,hb,headerAfter,cells⟩:=
    rowBody_actual P m program input before base E testPC values header hbase
      invariant.cache invariant.counter invariant.one invariant.two invariant.power
      invariant.odds invariant.fee invariant.denominator separated hfetch
  exact ⟨trace,after,hh,hl,hc,ht,hp,hb,headerAfter,invariant.body,cells⟩

end RootD27.Endpoint
