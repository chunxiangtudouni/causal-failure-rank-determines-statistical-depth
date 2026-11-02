module
public import Paid.PDCompute_Pack_PointerStores_010
public import Paid.PDCompute_Pack_PrefixJoin_016
public import Paid.PDCompute_SolverSmallPrefixMemory_060

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute storeSlot storeSlotResult readOnly linearReadOnly_heap)

theorem header_store_result {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (slot : ℕ) (source : Register) :
    Header (storeSlotResult before base slot source) base (Function.update values slot (before.register source)) := by
  apply Header.update header slot (before.register source) rfl
  exact Finset.subset_insert _ _

theorem sourcePointer_prefix_memory (input : List Cell) (before after : State) (base count : ℕ)
    (execute : linearExecute input (sourcePointerCode.take count) before=some after) : HeaderMemory before after base := by
  have whole : sourcePointerCode.all readOnly=true := rfl
  have safe : (sourcePointerCode.take count).all readOnly=true := by
    apply List.all_eq_true.mpr
    intro instruction member
    exact (List.all_eq_true.mp whole) instruction (List.mem_of_mem_take member)
  have unchanged:=linearReadOnly_heap input (sourcePointerCode.take count) before after safe execute
  exact HeaderMemory.of_unchanged base unchanged.1 unchanged.2.1 unchanged.2.2

/-- Prefix composition of three real header stores and the two-op
source arithmetic. Arbitrary preexisting header live cells are retained. -/
theorem pointerStores_prefix_memory (input : List Cell) (before after : State) (base : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (count : ℕ) (bound : count≤pointerStoresCode.length)
    (execute : linearExecute input (pointerStoresCode.take count) before=some after) : HeaderMemory before after base := by
  let first:=storeSlotResult before base outputStart .total
  let second:=storeSlotResult first base outputCursor .total
  let arithmetic:=sourcePointerResult second base
  let values1:=Function.update values outputStart (before.register .total)
  let values2:=Function.update values1 outputCursor (first.register .total)
  have header1 : Header first base values1 := header_store_result header outputStart .total
  have header2 : Header second base values2 := header_store_result header1 outputCursor .total
  have header3 : Header arithmetic base values2 := header2
  have base1 : first.register .fresh=.natural base := by simp [first,storeSlotResult,hbase]
  have base2 : second.register .fresh=.natural base := by simp [second,storeSlotResult,base1]
  have base3 : arithmetic.register .fresh=.natural base := by simp [arithmetic,sourcePointerResult,State.set,base2]
  have run1:=PDLower.CalibrationCompute.storeSlot_execute input before base outputStart .total hbase (by decide)
  have run2:=PDLower.CalibrationCompute.storeSlot_execute input first base outputCursor .total base1 (by decide)
  have run3:=sourcePointer_execute input second base base2
  have mem1 : ∀ count≤(storeSlot outputStart .total).length,∀ state,
      linearExecute input ((storeSlot outputStart .total).take count) before=some state → HeaderMemory before state base := by
    intro count countBound state run
    exact storeSlot_prefix_memory input before state base outputStart .total values header (by decide) hbase (by decide) count countBound run
  have mem2 : ∀ count≤(storeSlot outputCursor .total).length,∀ state,
      linearExecute input ((storeSlot outputCursor .total).take count) first=some state → HeaderMemory first state base := by
    intro count countBound state run
    exact storeSlot_prefix_memory input first state base outputCursor .total values1 header1 (by decide) base1 (by decide) count countBound run
  have mem3 : ∀ count≤sourcePointerCode.length,∀ state,
      linearExecute input (sourcePointerCode.take count) second=some state → HeaderMemory second state base := by
    intro count _countBound state run
    exact sourcePointer_prefix_memory input second state base count run
  have mem4 : ∀ count≤(storeSlot sourceCursor .total).length,∀ state,
      linearExecute input ((storeSlot sourceCursor .total).take count) arithmetic=some state → HeaderMemory arithmetic state base := by
    intro count countBound state run
    exact storeSlot_prefix_memory input arithmetic state base sourceCursor .total values2 header3 (by decide) base3 (by decide) count countBound run
  have tail:=header_prefix_append input sourcePointerCode (storeSlot sourceCursor .total) second arithmetic base run3 mem3 mem4
  have middle:=header_prefix_append input (storeSlot outputCursor .total) (sourcePointerCode++storeSlot sourceCursor .total)
    first second base run2 mem2 tail
  have joined:=header_prefix_append input (storeSlot outputStart .total)
    (storeSlot outputCursor .total++(sourcePointerCode++storeSlot sourceCursor .total)) before first base run1 mem1 middle
  have allMemory : ∀ count≤pointerStoresCode.length,∀ state,
      linearExecute input (pointerStoresCode.take count) before=some state → HeaderMemory before state base := by
    simpa only [pointerStoresCode,List.append_assoc] using joined
  exact allMemory count bound after execute

end PDCompute.Pack
