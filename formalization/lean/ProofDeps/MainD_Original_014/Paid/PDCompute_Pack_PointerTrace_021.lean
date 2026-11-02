module
public import Paid.PDCompute_Pack_PointerHeader_020
public import Paid.PDCompute_SolverSmallTraceMemory_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem pointerArithmetic_straight : StraightCode pointerArithmeticCode := by
  intro instruction member
  simp only [pointerArithmeticCode,PDLower.CalibrationCompute.loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

theorem pointerArithmetic_trace (program : Program) (input : List Cell) (before : State) (base n k : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (rows : values rowRemaining=.natural (n+1)) (columns : values columnsPerRow=.natural (k+1))
    (fetched : FetchesCode program before.pc pointerArithmeticCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (pointerArithmeticResult before base n k) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤195 ∧
      Header (pointerArithmeticResult before base n k) base values ∧
      (pointerArithmeticResult before base n k).register .fresh=.natural base ∧
      (pointerArithmeticResult before base n k).register .total=.natural (resultBase base n k) ∧
      (pointerArithmeticResult before base n k).pc=before.pc+12 ∧
      (pointerArithmeticResult before base n k).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have run:=pointerArithmetic_execute input before base n k values header hbase rows columns
  obtain ⟨trace,hh,hl,hchain,ht,memory⟩:=linearExecute_trace_memory program input pointerArithmeticCode
    pointerArithmetic_straight before _ base fetched run
    (fun count _bound state execute=>pointerArithmetic_prefix_memory input before state base count execute)
  have fields:=pointerArithmetic_fields before base n k
  exact ⟨trace,hh,hl,hchain,ht,pointerArithmetic_header before base n k values header,
    fields.2.2.2.1.trans hbase,fields.2.2.2.2.1,fields.2.2.2.2.2,fields.2.2.1,memory⟩

theorem pointerStores_straight : StraightCode pointerStoresCode := by
  intro instruction member
  simp only [pointerStoresCode,sourcePointerCode,PDLower.CalibrationCompute.storeSlot,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

theorem pointerStores_trace (program : Program) (input : List Cell) (before : State) (base result : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (value : before.register .total=.natural result)
    (fetched : FetchesCode program before.pc pointerStoresCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (pointerStoresResult before base) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤180 ∧
      Header (pointerStoresResult before base) base (pointerValues values base result) ∧
      (pointerStoresResult before base).register .fresh=.natural base ∧
      (pointerStoresResult before base).pc=before.pc+11 ∧
      (pointerStoresResult before base).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have run:=pointerStores_execute input before base hbase
  obtain ⟨trace,hh,hl,hchain,ht,memory⟩:=linearExecute_trace_memory program input pointerStoresCode
    pointerStores_straight before _ base fetched run
    (fun count bound state execute=>pointerStores_prefix_memory input before state base values header hbase count bound execute)
  have fields:=pointerStores_fields before base result value
  exact ⟨trace,hh,hl,hchain,ht,pointerStores_header before base result values header value,
    fields.2.2.1.trans hbase,fields.2.2.2.1,fields.2.2.2.2,memory⟩

end PDCompute.Pack
