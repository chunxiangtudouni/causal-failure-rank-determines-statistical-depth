module

public import Paid.PDROC_EndpointOperands_Entry_001
public import Paid.PDROC_EndpointOperands_Scalar_001
public import Paid.PDROC_EndpointOperands_Header_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.EndpointOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver RootD27.Endpoint RootD27.Bits PDMenu.ComputeFrame
open PDLower.CalibrationCompute

/-- The true scalar initialization trace, with its intrinsic finite SSA
budget and original HeaderMemory on ONE selected witness. -/
theorem initial_scalar_actual_sameBudget (P : Parameters) (program : Program) (input : List Cell)
    (origin base E returnPC budget : ℕ) (before : State) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (gamma : values 2=.rational P.certificate.gamma) (safe : SafeBits before budget)
    (control : ControlBudget P origin base E returnPC budget) (rational : rationalBudget P≤budget)
    (position : before.pc+56≤pcCap origin returnPC)
    (fetched : FetchesCode program before.pc (headerCode initialCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤1485 ∧
      Header after base (initializedValues values P.certificate.gamma) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+56 ∧
      PDCompute.Solver.Frame before after base 0 0 ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ SafeBits state budget := by
  exact headerCode_trace_bits initialCommands program input before base 0 0 budget values
    (initializedValues values P.certificate.gamma) initialCommands_valid header fresh
    (initialize_eval P values gamma) safe
    (initial_evaluated_bits P budget values (HeaderValueBits.of_safe header safe) gamma rational
      (ControlBudget.nat P origin base E returnPC budget 0 control (by omega)))
    (ControlBudget.headerAddress P origin base E returnPC budget control)
    (ControlBudget.pc P origin base E returnPC budget _ control position) fetched

theorem cache_header_actual_sameBudget (P : Parameters) (program : Program) (input : List Cell)
    (origin base E returnPC budget : ℕ) (before : State) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (stop : values 3=.natural P.certificate.M) (cache : values 0=.natural E)
    (safe : SafeBits before budget) (control : ControlBudget P origin base E returnPC budget)
    (separated : base+48≤E) (position : before.pc+12≤pcCap origin returnPC)
    (fetched : FetchesCode program before.pc cacheHeaderCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (cacheHeaderResult before base P.certificate.M E) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤195 ∧
      Header (cacheHeaderResult before base P.certificate.M E) base
        (Function.update values 17 (.natural (P.certificate.M+1))) ∧
      E∈(cacheHeaderResult before base P.certificate.M E).live ∧
      (cacheHeaderResult before base P.certificate.M E).heap E=.natural (P.certificate.M+1) ∧
      ∀ state∈trace,RegionMemory before state (endpointLoopRegion base E P.certificate.M) ∧
        SafeBits state budget := by
  have zeroLive : base∈before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have zeroCell : before.heap base=.natural E := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans cache
  have executed := cacheHeader_execute input before base P.certificate.M E fresh zeroLive
    (header.live 3 (by decide)) ((header.value 3 (by decide)).trans stop) zeroCell
  have prefixSafe := cache_header_prefix_safe input P origin base E returnPC budget before values
    header fresh stop cache safe control position
  obtain ⟨trace,head,last,chain,cost,prefixes⟩ := PDCompute.Pack.linearExecute_trace_invariant
    program input cacheHeaderCode cacheHeader_straight before _ fetched executed
    (fun state=>RegionMemory before state (endpointLoopRegion base E P.certificate.M) ∧ SafeBits state budget)
    (by
      intro count bound state actual
      exact ⟨cacheHeader_prefix_region input before state base P.certificate.M E values header fresh stop cache
        count (by simpa only [cacheHeaderCode_length] using bound) actual,prefixSafe count state actual⟩)
  exact ⟨trace,head,last,chain,cost,cacheHeader_header before base P.certificate.M E values header separated,
    (cacheHeader_cell before base P.certificate.M E).1,(cacheHeader_cell before base P.certificate.M E).2,prefixes⟩

end PDROC.EndpointOperands
