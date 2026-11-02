module
public import Paid.PDCompute_Pack_InitializeRun_023
public import Paid.PDCompute_Pack_PointerTrace_021

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem copyPlusOne_pc (before : State) (base source target value : ℕ) :
    (copyPlusOneResult before base source target value).pc=before.pc+14 := by
  change (addNatSlotResult (copySlotResult before base source target) base target value 1).pc=before.pc+14
  rw [(addNatSlotResult_fields (copySlotResult before base source target) base target value 1).2.2.2.1,
    (copySlotResult_fields before base source target).2.2.2.1]

theorem copyPlusOne_output (before : State) (base source target value : ℕ) :
    (copyPlusOneResult before base source target value).output=before.output :=
  (addNatSlotResult_fields (copySlotResult before base source target) base target value 1).2.2.2.2.trans
    (copySlotResult_fields before base source target).2.2.2.2

theorem initializeHeader_fields (before : State) (base n k : ℕ) :
    (initializeHeaderResult before base n k).register .fresh=before.register .fresh ∧
    (initializeHeaderResult before base n k).pc=before.pc+51 ∧
    (initializeHeaderResult before base n k).output=before.output := by
  have first:=copyPlusOne_fresh before base 3 rowRemaining n
  have second:=copyPlusOne_fresh (counterFirst before base n) base 4 columnsPerRow k
  have arithmetic:=pointerArithmetic_fields (counterSecond before base n k) base n k
  have stored:=pointerStores_fields (headerArithmetic before base n k) base (resultBase base n k) arithmetic.2.2.2.2.1
  refine ⟨stored.2.2.1.trans (arithmetic.2.2.2.1.trans (second.trans first)),?_,?_⟩
  · have pc1 : (counterFirst before base n).pc=before.pc+14 := copyPlusOne_pc before base 3 rowRemaining n
    have pc2 : (counterSecond before base n k).pc=(counterFirst before base n).pc+14 :=
      copyPlusOne_pc (counterFirst before base n) base 4 columnsPerRow k
    have pc3 : (headerArithmetic before base n k).pc=(counterSecond before base n k).pc+12 := arithmetic.2.2.2.2.2
    have pc4 : (initializeHeaderResult before base n k).pc=(headerArithmetic before base n k).pc+11 := stored.2.2.2.1
    omega
  · exact stored.2.2.2.2.trans (arithmetic.2.2.1.trans
      ((copyPlusOne_output (counterFirst before base n) base 4 columnsPerRow k).trans
        (copyPlusOne_output before base 3 rowRemaining n)))

theorem initializeHeader_straight : StraightCode initializeHeaderCode := by
  intro instruction member
  simp only [initializeHeaderCode,List.mem_append,or_assoc] at member
  rcases member with first|second|arithmetic|stored
  · exact copyPlusOne_straight 3 rowRemaining instruction first
  · exact copyPlusOne_straight 4 columnsPerRow instruction second
  · exact pointerArithmetic_straight instruction arithmetic
  · exact pointerStores_straight instruction stored

/-- Entire first51 actual instructions, with real time and EVERY state
memory footprint; full program fetches are the only code-location premise. -/
theorem initializeHeader_trace (program : Program) (input : List Cell) (before : State) (base n k : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k)
    (fetched : FetchesCode program before.pc initializeHeaderCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (initializeHeaderResult before base n k) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤780 ∧
      Header (initializeHeaderResult before base n k) base (initializeHeaderValues values base n k) ∧
      (initializeHeaderResult before base n k).register .fresh=.natural base ∧
      (initializeHeaderResult before base n k).pc=before.pc+51 ∧
      (initializeHeaderResult before base n k).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have facts:=initializeHeader_run_memory input before base n k values header hbase hn hk
  obtain ⟨trace,hh,hl,hchain,ht,memory⟩:=linearExecute_trace_memory program input initializeHeaderCode
    initializeHeader_straight before _ base fetched facts.1 facts.2
  have fields:=initializeHeader_fields before base n k
  exact ⟨trace,hh,hl,hchain,ht,initializeHeader_header before base n k values header,
    fields.1.trans hbase,fields.2.1,fields.2.2,memory⟩

end PDCompute.Pack
