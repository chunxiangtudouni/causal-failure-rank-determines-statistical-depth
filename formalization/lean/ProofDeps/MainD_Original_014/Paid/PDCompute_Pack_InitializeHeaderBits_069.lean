module
public import Paid.PDCompute_Pack_CounterInitBits_063
public import Paid.PDCompute_Pack_PointerArithmeticBits_066
public import Paid.PDCompute_Pack_PointerStoresBits_068
public import Paid.PDCompute_Pack_InitializeTrace_024
public import Paid.PDCompute_Pack_BitBudget_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

theorem initializeHeader_prefix_safe (input : List Cell) (before after : State) (base n k budget count : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (safe : SafeBits before budget)
    (naturalBound : ∀ value ≤ naturalCap base n k,1+natBits value ≤ budget)
    (counter : natBits (before.pc+51) ≤ budget) (bound : count ≤ 51)
    (execute : linearExecute input (initializeHeaderCode.take count) before=some after) : SafeBits after budget := by
  let values1:=Function.update values rowRemaining (.natural (n+1))
  let values2:=counterValues values n k
  have head1 : Header (counterFirst before base n) base values1:=counterFirst_header before base n values header
  have head2 : Header (counterSecond before base n k) base values2:=counterSecond_header before base n k values header
  have base1 : (counterFirst before base n).register .fresh=.natural base:=(copyPlusOne_fresh before base 3 rowRemaining n).trans fresh
  have base2 : (counterSecond before base n k).register .fresh=.natural base:=
    (copyPlusOne_fresh (counterFirst before base n) base 4 columnsPerRow k).trans base1
  have base3 : (headerArithmetic before base n k).register .fresh=.natural base:=
    (pointerArithmetic_fields (counterSecond before base n k) base n k).2.2.2.1.trans base2
  have value4 : values1 4=.natural k:=by simpa [values1,rowRemaining] using hk
  have run1 : linearExecute input (copyPlusOneCode 3 rowRemaining) before=some (counterFirst before base n):=
    copyPlusOne_execute input before base 3 rowRemaining n values header (by decide) fresh hn
  have run2 : linearExecute input (copyPlusOneCode 4 columnsPerRow) (counterFirst before base n)=some (counterSecond before base n k):=
    copyPlusOne_execute input (counterFirst before base n) base 4 columnsPerRow k values1 head1 (by decide) base1 value4
  have run3 : linearExecute input pointerArithmeticCode (counterSecond before base n k)=some (headerArithmetic before base n k):=
    pointerArithmetic_execute input (counterSecond before base n k) base n k values2 head2 base2
      (counterValues_rows values n k) (counterValues_columns values n k)
  have address (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot) ≤ budget:=
    naturalBound _ (naturalCap_header_address base n k slot inside)
  have oneBits : 1+natBits 1 ≤ budget:=naturalBound _ (le_trans (by decide : 1 ≤ 48) (naturalCap_small base n k))
  have rowsBits:=naturalBound _ (naturalCap_rows base n k)
  have columnsBits:=naturalBound _ (naturalCap_columns base n k)
  have pcFirst : (counterFirst before base n).pc=before.pc+14:=copyPlusOne_pc before base 3 rowRemaining n
  have pcSecond : (counterSecond before base n k).pc=before.pc+28:=by
    have raw : (counterSecond before base n k).pc=(counterFirst before base n).pc+14:=
      copyPlusOne_pc (counterFirst before base n) base 4 columnsPerRow k
    omega
  have pcArithmetic : (headerArithmetic before base n k).pc=before.pc+40:=by
    have raw : (headerArithmetic before base n k).pc=(counterSecond before base n k).pc+12:=
      (pointerArithmetic_fields (counterSecond before base n k) base n k).2.2.2.2.2
    omega
  have pc1 : natBits (before.pc+14) ≤ budget:=(natBits_mono (by omega : before.pc+14 ≤ before.pc+51)).trans counter
  have pc2 : natBits ((counterFirst before base n).pc+14) ≤ budget:=by
    rw [pcFirst];exact (natBits_mono (by omega : before.pc+14+14 ≤ before.pc+51)).trans counter
  have pc3 : natBits ((counterSecond before base n k).pc+12) ≤ budget:=by
    rw [pcSecond];exact (natBits_mono (by omega : before.pc+28+12 ≤ before.pc+51)).trans counter
  have pc4 : natBits ((headerArithmetic before base n k).pc+11) ≤ budget:=by
    rw [pcArithmetic];simpa only [Nat.add_assoc] using counter
  have prefix1 : ∀ take ≤ (copyPlusOneCode 3 rowRemaining).length,∀ state,
      linearExecute input ((copyPlusOneCode 3 rowRemaining).take take) before=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact copyPlusOne_prefix_safe input before state base 3 rowRemaining n budget take values header (by decide) (by decide)
      fresh hn safe (address 3 (by decide)) (address rowRemaining (by decide)) oneBits rowsBits pc1 takeBound run
  have safe1 : SafeBits (counterFirst before base n) budget:=prefix1 _ (le_refl _) _ (by simpa only [List.take_length] using run1)
  have prefix2 : ∀ take ≤ (copyPlusOneCode 4 columnsPerRow).length,∀ state,
      linearExecute input ((copyPlusOneCode 4 columnsPerRow).take take) (counterFirst before base n)=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact copyPlusOne_prefix_safe input (counterFirst before base n) state base 4 columnsPerRow k budget take values1 head1
      (by decide) (by decide) base1 value4 safe1 (address 4 (by decide)) (address columnsPerRow (by decide)) oneBits columnsBits pc2 takeBound run
  have safe2 : SafeBits (counterSecond before base n k) budget:=prefix2 _ (le_refl _) _ (by simpa only [List.take_length] using run2)
  have prefix3 : ∀ take ≤ pointerArithmeticCode.length,∀ state,
      linearExecute input (pointerArithmeticCode.take take) (counterSecond before base n k)=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact pointerArithmetic_prefix_safe input (counterSecond before base n k) state base n k budget take values2 head2 base2
      (counterValues_rows values n k) (counterValues_columns values n k) safe2 naturalBound pc3 takeBound run
  have safe3 : SafeBits (headerArithmetic before base n k) budget:=prefix3 _ (le_refl _) _ (by simpa only [List.take_length] using run3)
  have prefix4 : ∀ take ≤ pointerStoresCode.length,∀ state,
      linearExecute input (pointerStoresCode.take take) (headerArithmetic before base n k)=some state → SafeBits state budget:=by
    intro take takeBound state run
    exact pointerStores_prefix_safe input (headerArithmetic before base n k) state base n k budget take base3 safe3 naturalBound pc4 takeBound run
  have tail:=invariant_prefix_append input pointerArithmeticCode pointerStoresCode (counterSecond before base n k)
    (headerArithmetic before base n k) run3 (fun state=>SafeBits state budget) prefix3 prefix4
  have middle:=invariant_prefix_append input (copyPlusOneCode 4 columnsPerRow) (pointerArithmeticCode++pointerStoresCode)
    (counterFirst before base n) (counterSecond before base n k) run2 (fun state=>SafeBits state budget) prefix2 tail
  have combined:=invariant_prefix_append input (copyPlusOneCode 3 rowRemaining)
    (copyPlusOneCode 4 columnsPerRow++(pointerArithmeticCode++pointerStoresCode)) before (counterFirst before base n) run1
    (fun state=>SafeBits state budget) prefix1 middle
  have allPrefixes : ∀ take ≤ initializeHeaderCode.length,∀ state,
      linearExecute input (initializeHeaderCode.take take) before=some state → SafeBits state budget:=by
    simpa only [initializeHeaderCode,List.append_assoc] using combined
  exact allPrefixes count bound after execute

theorem initializeHeader_trace_safe (program : Program) (input : List Cell) (before : State) (base n k budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (safe : SafeBits before budget)
    (naturalBound : ∀ value ≤ naturalCap base n k,1+natBits value ≤ budget)
    (counter : natBits (before.pc+51) ≤ budget) (fetched : FetchesCode program before.pc initializeHeaderCode) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (initializeHeaderResult before base n k) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 780 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  have run:=initializeHeader_run_memory input before base n k values header fresh hn hk
  obtain ⟨trace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input initializeHeaderCode
    initializeHeader_straight before _ fetched run.1 (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state executed
      have countBound : count ≤ 51:=by simpa only [initializeHeaderCode_length] using bound
      exact ⟨run.2 count bound state executed,
        initializeHeader_prefix_safe input before state base n k budget count values header fresh hn hk safe naturalBound counter countBound executed⟩)
  refine ⟨trace,hh,hl,hchain,?_,fun state member=>(invariant state member).1,fun state member=>(invariant state member).2⟩
  simpa only [initializeHeaderCode_length] using ht

/-- Original initialization needs no supplied numeric resource certificate. -/
theorem initializeHeader_trace_budget (program : Program) (input : List Cell) (before : State) (base n k origin : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (pc : before.pc=origin)
    (fetched : FetchesCode program before.pc initializeHeaderCode) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (initializeHeaderResult before base n k) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 780 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧
      (∀ state∈trace,SafeBits state (serializerBudget before n k origin)) := by
  exact initializeHeader_trace_safe program input before base n k (serializerBudget before n k origin) values header fresh hn hk
    (serializerBudget_initial before n k origin) (fun value bound=>serializerBudget_natural before base n k origin value fresh bound)
    (serializerBudget_pc before n k origin (before.pc+51) (by omega)) fetched

end PDCompute.Pack
