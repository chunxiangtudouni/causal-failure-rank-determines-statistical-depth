module

public import Paid.RootD27Endpoint_Scalars_003
public import Paid.PDCompute_SolverSequenceMemory_051

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem initialize_scalar_actual (P : Parameters) (program : Program) (input : List Cell)
    (before : State) (base : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hgamma : values 2=.rational P.certificate.gamma)
    (hfetch : FetchesCode program before.pc (headerCode initialCommands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤1485 ∧
      Header after base (initializedValues values P.certificate.gamma) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+56 ∧
      PDCompute.Solver.Frame before after base 0 0 ∧ after.output=before.output ∧
      ∀ state∈trace, HeaderMemory before state base := by
  obtain ⟨trace,after,hh,hl,hc,ht,ha,hb,hp,hf,ho,memory⟩ :=
    headerCode_trace_memory initialCommands program input before base 0 0 values
      (initializedValues values P.certificate.gamma) initialCommands_valid header hbase
      (initialize_eval P values hgamma) hfetch
  exact ⟨trace,after,hh,hl,hc,ht,ha,hb,hp,hf,ho,memory⟩

theorem row_scalar_actual (P : Parameters) (m : ℕ) (program : Program) (input : List Cell)
    (before : State) (base : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hone : values 13=.rational 1) (htwo : values 14=.rational 2)
    (hpower : values 7=.rational (powerRecurrence P.certificate.odds m))
    (hfee : values 4=.rational P.reviewFee) (hrow : values 18=.rational (m:ℚ))
    (hden : values 12=.rational (2*P.certificate.gamma))
    (hfetch : FetchesCode program before.pc (headerCode rowCommands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤1320 ∧
      Header after base (rowValues values P.certificate.gamma P.reviewFee
        (powerRecurrence P.certificate.odds m) m) ∧
      after.heap (base+9)=.rational (P.endpointConstant m).error ∧
      after.heap (base+11)=.rational (P.endpointConstant m).charge ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+70 ∧
      PDCompute.Solver.Frame before after base 0 0 ∧ after.output=before.output ∧
      ∀ state∈trace, HeaderMemory before state base := by
  have heval:=row_eval P.certificate.gamma P.reviewFee (powerRecurrence P.certificate.odds m)
    m values hone htwo hpower hfee hrow hden (error_den_ne_zero P m) (mean_den_ne_zero P)
  obtain ⟨trace,after,hh,hl,hc,ht,ha,hb,hp,hf,ho,memory⟩ :=
    headerCode_trace_memory rowCommands program input before base 0 0 values
      (rowValues values P.certificate.gamma P.reviewFee (powerRecurrence P.certificate.odds m) m)
      rowCommands_valid header hbase heval hfetch
  refine ⟨trace,after,hh,hl,hc,ht,ha,?_,?_,hb,hp,hf,ho,memory⟩
  · have hv:=Header.value ha 9 (by decide)
    simpa only [rowValues_error,endpointFromPower_original] using hv
  · have hv:=Header.value ha 11 (by decide)
    simpa only [rowValues_charge,endpointFromPower_original] using hv

end RootD27.Endpoint
