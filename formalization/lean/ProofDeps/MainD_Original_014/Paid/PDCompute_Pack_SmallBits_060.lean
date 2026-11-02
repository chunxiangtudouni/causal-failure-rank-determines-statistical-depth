module
public import Paid.PDCompute_Pack_PairBits_059
public import Paid.PDCompute_Pack_TagDifference_026
public import Paid.PDCompute_Pack_PointerStores_010

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)

theorem tagDifference_prefix_safe (input : List Cell) (before after : State) (tag budget count : ℕ)
    (safe : SafeBits before budget) (htag : before.register .value=.natural tag)
    (twoBits : 1+natBits 2 ≤ budget) (pcBits : natBits (before.pc+2) ≤ budget) (bound : count ≤ 2)
    (execute : linearExecute input (tagDifferenceCode.take count) before=some after) : SafeBits after budget := by
  have resultBits : 1+natBits (2-tag) ≤ budget := by
    have mono:=natBits_mono (Nat.sub_le 2 tag)
    omega
  exact constantNatPair_prefix_safe input before after .flag 2 .subtract .value .flag .value 2 tag (2-tag) budget count safe twoBits
    (by simp [constantNatFirst,State.set]) (by simp [constantNatFirst,State.set,htag]) rfl resultBits pcBits bound execute

theorem sourcePointer_prefix_safe (input : List Cell) (before after : State) (base budget count : ℕ)
    (safe : SafeBits before budget) (hbase : before.register .fresh=.natural base)
    (resultBits : 1+natBits (base+48) ≤ budget) (pcBits : natBits (before.pc+2) ≤ budget) (bound : count ≤ 2)
    (execute : linearExecute input (sourcePointerCode.take count) before=some after) : SafeBits after budget := by
  have literalBits : 1+natBits 48 ≤ budget := by
    have mono:=natBits_mono (by omega : 48 ≤ base+48)
    omega
  exact constantNatPair_prefix_safe input before after .total 48 .add .total .fresh .total base 48 (base+48) budget count safe literalBits
    (by simp [constantNatFirst,State.set,hbase]) (by simp [constantNatFirst,State.set]) rfl resultBits pcBits bound execute

/-- The actual six-op header copy preserves the original whole-state
budget at EVERY real prefix, including address words and prior live heap. -/
theorem copy_prefix_safe (input : List Cell) (before after : State) (base source target budget count : ℕ)
    (safe : SafeBits before budget) (hbase : before.register .fresh=.natural base) (live : base+source∈before.live)
    (sourceBits : 1+natBits (base+source) ≤ budget) (targetBits : 1+natBits (base+target) ≤ budget)
    (pcBits : natBits (before.pc+6) ≤ budget) (bound : count ≤ 6)
    (execute : linearExecute input ((copySlot source target).take count) before=some after) : SafeBits after budget := by
  let loaded:=loadSlotResult before base source .total
  have loadPC : natBits (before.pc+3) ≤ budget:=(natBits_mono (by omega : before.pc+3 ≤ before.pc+6)).trans pcBits
  have loadedSafe : SafeBits loaded budget:=loadSlotResult_safe before base source budget .total safe live sourceBits loadPC
  have loadedBase : loaded.register .fresh=.natural base:=(loadSlotResult_fresh before base source .total (by decide)).trans hbase
  have storePC : natBits (loaded.pc+3) ≤ budget:=by
    change natBits (before.pc+3+3) ≤ budget
    simpa only [Nat.add_assoc] using pcBits
  have firstRun:=PDLower.CalibrationCompute.loadSlot_execute input before base source .total hbase live
  have firstPrefixes : ∀ take ≤ (loadSlot source .total).length,∀ state,
      linearExecute input ((loadSlot source .total).take take) before=some state → SafeBits state budget := by
    intro take takeBound state run
    exact loadSlot_prefix_safe input before state base source budget take .total safe hbase live sourceBits loadPC takeBound run
  have laterPrefixes : ∀ take ≤ (storeSlot target .total).length,∀ state,
      linearExecute input ((storeSlot target .total).take take) loaded=some state → SafeBits state budget := by
    intro take takeBound state run
    exact storeSlot_prefix_safe input loaded state base target budget take .total loadedSafe loadedBase (by decide) targetBits storePC takeBound run
  have combined:=invariant_prefix_append input (loadSlot source .total) (storeSlot target .total) before loaded firstRun
    (fun state=>SafeBits state budget) firstPrefixes laterPrefixes
  exact combined count bound after execute

end PDCompute.Pack
