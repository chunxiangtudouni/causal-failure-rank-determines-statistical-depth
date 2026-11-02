module

public import Paid.RootD27Endpoint_PairStore_009
public import Paid.RootD27Endpoint_CastPrefix_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot)

def pairWriteRegion (E m : ℕ) : Finset ℕ := {E+(m*2+1),E+(m*2+1)+1}

theorem pair_region_inside_cache (E m M : ℕ) (bound : m≤M) :
    pairWriteRegion E m⊆cellRegion E (2*M+3) := by
  intro address inside
  simp only [pairWriteRegion,Finset.mem_insert,Finset.mem_singleton] at inside
  apply (mem_cellRegion_iff E (2*M+3) address).mpr
  rcases inside with first|second <;> subst address <;> omega

theorem endpoint_store_region (before : State) (address : ℕ) (value : Cell)
    (region : Finset ℕ) (inside : address∈region) :
    RegionMemory before
      {before with heap:=Function.update before.heap address value,live:=insert address before.live} region := by
  apply CellWriteMemory.region (pointer:=address) _ inside
  refine ⟨?_,Finset.Subset.refl _,Finset.subset_insert _ _,rfl⟩
  intro other different
  exact Function.update_of_ne different value before.heap

/-- Every actual prefix writes only the two actual cache addresses;
the old live workspace and output remain charged and preserved. -/
theorem pairStore_prefix_region (input : List Cell) (before after : State)
    (base E m : ℕ) (error charge : ℚ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hE : values 0=.natural E) (hm : values 8=.natural m)
    (he : values 9=.rational error) (hc : values 11=.rational charge)
    (count : ℕ) (bound : count≤20)
    (actual : linearExecute input (pairStoreCode.take count) before=some after) :
    RegionMemory before after (pairWriteRegion E m) := by
  have zeroLive : base∈before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have zeroValue : before.heap base=.natural E := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans hE
  have eightLive:=header.live 8 (by decide)
  have nineLive:=header.live 9 (by decide)
  have elevenLive:=header.live 11 (by decide)
  have eightValue:=(header.value 8 (by decide)).trans hm
  have nineValue:=(header.value 9 (by decide)).trans he
  have elevenValue:=(header.value 11 (by decide)).trans hc
  let first : State := {before with heap:=Function.update before.heap (E+(m*2+1)) (.rational error),live:=insert (E+(m*2+1)) before.live}
  have firstMemory : RegionMemory before first (pairWriteRegion E m) :=
    endpoint_store_region before _ _ _ (by simp [pairWriteRegion])
  have secondMemory := endpoint_store_region first (E+(m*2+1)+1) (.rational charge)
    (pairWriteRegion E m) (by simp [pairWriteRegion])
  interval_cases count <;>
    simp [pairStoreCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
      Cell.nat?,fresh,zeroLive,eightLive,nineLive,elevenLive,zeroValue,eightValue,
      nineValue,elevenValue,Nat.add_assoc] at actual <;>
    subst after
  all_goals
    first
    | exact RegionMemory.refl before (pairWriteRegion E m)
    | exact firstMemory
    | exact firstMemory.trans secondMemory

/-- The strengthened genuine cache-store trace carries its original
header result and every-prefix finite write region on ONE witness. -/
theorem pairStore_actual_region (program : Program) (input : List Cell) (before : State)
    (base E m : ℕ) (error charge : ℚ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hE : values 0=.natural E) (hm : values 8=.natural m)
    (he : values 9=.rational error) (hc : values 11=.rational charge)
    (separated : base+48≤E) (fetched : FetchesCode program before.pc pairStoreCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (pairStoreResult before base E m error charge) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤315 ∧ Header (pairStoreResult before base E m error charge) base values ∧
      ∀ state∈trace,RegionMemory before state (pairWriteRegion E m) := by
  have zeroLive : base∈before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have zeroValue : before.heap base=.natural E := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans hE
  have executed:=pairStore_execute input before base E m error charge fresh zeroLive
    (header.live 8 (by decide)) (header.live 9 (by decide)) (header.live 11 (by decide))
    zeroValue ((header.value 8 (by decide)).trans hm) ((header.value 9 (by decide)).trans he)
      ((header.value 11 (by decide)).trans hc)
  obtain ⟨trace,head,last,chain,cost,prefixes⟩ :=
    linearExecute_trace_time program input pairStoreCode pairStore_straight before
      (pairStoreResult before base E m error charge) fetched executed
  refine ⟨trace,head,last,chain,cost,pairStore_header before base E m error charge values header separated,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (pairStoreResult before base E m error charge) (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨count,bound,actual⟩:=prefixes state proper
    apply pairStore_prefix_region input before state base E m error charge values header fresh hE hm he hc count
    · simpa only [pairStoreCode_length] using bound.le
    · exact actual
  · have same : state=pairStoreResult before base E m error charge := List.mem_singleton.mp terminal
    subst state
    apply pairStore_prefix_region input before _ base E m error charge values header fresh hE hm he hc 20 (by omega)
    simpa only [show pairStoreCode.take 20=pairStoreCode by rw [←pairStoreCode_length,List.take_length]] using executed

end RootD27.Endpoint
