module

public import Paid.PDROC_CalibrationRow_040

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem static_prefix_heap_live (input : List Cell) (code : List Instruction) (before state : State)
    (safe : ∀ instruction∈code,∀ state,WritesWithin ∅ instruction state) (count : ℕ)
    (run : linearExecute input (code.take count) before=some state) :
    state.heap=before.heap ∧ state.live=before.live := by
  have frame := LinearFrames.of_static ∅ input code safe before count state run
  exact ⟨funext (fun address => frame.1 address (by simp)),
    Finset.ext (fun address => frame.2 address (by simp))⟩

theorem incrementSlot_heap_live (before : State) (base offset value : ℕ) :
    (incrementSlotResult before base offset value).heap=Function.update before.heap (base+offset) (.natural (value+1)) ∧
    (incrementSlotResult before base offset value).live=insert (base+offset) before.live := by
  simp [incrementSlotResult,incrementSlotLoaded,storeSlotResult,loadSlotResult]

def swapReadPreludeCode : List Instruction :=
  loadSlot 9 .old++loadSlot 10 .total++headerStorePrefixCode 9

def swapFirstCode : List Instruction :=
  incrementSlot 6++(swapReadPreludeCode++[.store .address .total])

def swapFirstResult (before : State) (base clock : ℕ) : State :=
  let incremented := incrementSlotResult before base 6 clock
  let readLoaded := loadSlotResult incremented base 9 .old
  let writeLoaded := loadSlotResult readLoaded base 10 .total
  storeSlotResult writeLoaded base 9 .total

theorem swapReadPrelude_static (region : Finset ℕ) :
    ∀ instruction∈swapReadPreludeCode,∀ state,WritesWithin region instruction state := by
  intro instruction member state
  simp only [swapReadPreludeCode,loadSlot,headerStorePrefixCode,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h|h))|(h|h) <;> subst instruction <;> trivial

theorem headerStorePrelude_static (region : Finset ℕ) (offset : ℕ) :
    ∀ instruction∈headerStorePrefixCode offset,∀ state,WritesWithin region instruction state := by
  intro instruction member state
  simp only [headerStorePrefixCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h <;> subst instruction <;> trivial

theorem swapFirst_execute (input : List Cell) (before : State) (base clock : ℕ)
    (fresh : before.register .fresh=.natural base)
    (clockLive : base+6∈before.live) (clockValue : before.heap (base+6)=.natural clock)
    (readLive : base+9∈before.live) (writeLive : base+10∈before.live) :
    linearExecute input swapFirstCode before=some (swapFirstResult before base clock) := by
  let incremented := incrementSlotResult before base 6 clock
  let readLoaded := loadSlotResult incremented base 9 .old
  let writeLoaded := loadSlotResult readLoaded base 10 .total
  have incFresh := (incrementSlot_fresh before base 6 clock).trans fresh
  have readFresh : readLoaded.register .fresh=.natural base := by
    simpa [readLoaded,loadSlotResult] using incFresh
  have writeFresh : writeLoaded.register .fresh=.natural base := by
    simpa [writeLoaded,loadSlotResult] using readFresh
  have code : swapFirstCode=incrementSlot 6++(loadSlot 9 .old++(loadSlot 10 .total++storeSlot 9 .total)) := rfl
  rw [code,linearExecute_append,incrementSlot_execute input before base 6 clock fresh clockLive clockValue,
    Option.bind_some,linearExecute_append,
    loadSlot_execute input incremented base 9 .old incFresh (Finset.mem_insert_of_mem readLive),Option.bind_some,
    linearExecute_append,
    loadSlot_execute input readLoaded base 10 .total readFresh (Finset.mem_insert_of_mem writeLive),Option.bind_some,
    storeSlot_execute input writeLoaded base 9 .total writeFresh (by decide)]
  rfl

theorem swapFirst_fields (before : State) (base clock read write : ℕ)
    (readValue : before.heap (base+9)=.natural read)
    (writeValue : before.heap (base+10)=.natural write) :
    (swapFirstResult before base clock).heap=
      Function.update (Function.update before.heap (base+6) (.natural (clock+1))) (base+9) (.natural write) ∧
    (swapFirstResult before base clock).live=insert (base+9) (insert (base+6) before.live) := by
  simp [swapFirstResult,incrementSlotResult,incrementSlotLoaded,loadSlotResult,storeSlotResult,readValue,writeValue]

/-- Exact swap prefix phases. Prefix8 changes the clock; prefix17
changes header9 while header10 still holds the old destination; prefix20
finally restores the disjoint swapped pointers. Both physical rows stay
fixed throughout, as separately certified by stepNext_prefix_row. -/
theorem stepNext_heap_live_prefix (input : List Cell) (before state : State) (base clock read write count : ℕ)
    (fresh : before.register .fresh=.natural base)
    (clockLive : base+6∈before.live) (clockValue : before.heap (base+6)=.natural clock)
    (readLive : base+9∈before.live) (writeLive : base+10∈before.live)
    (readValue : before.heap (base+9)=.natural read) (writeValue : before.heap (base+10)=.natural write)
    (bound : count≤20)
    (run : linearExecute input ((basicBlock .stepNext).body.take count) before=some state) :
    state.heap=(if count<8 then before.heap else if count<17 then
      Function.update before.heap (base+6) (.natural (clock+1)) else if count<20 then
      Function.update (Function.update before.heap (base+6) (.natural (clock+1))) (base+9) (.natural write) else
      Function.update (Function.update (Function.update before.heap (base+6) (.natural (clock+1)))
        (base+9) (.natural write)) (base+10) (.natural read)) ∧
    state.live=(if count<8 then before.live else if count<17 then insert (base+6) before.live else
      if count<20 then insert (base+9) (insert (base+6) before.live) else
      insert (base+10) (insert (base+9) (insert (base+6) before.live))) := by
  have firstCode : (basicBlock .stepNext).body=
      incrementSlot 6++(swapReadPreludeCode++[.store .address .total]++storeSlot 10 .old) := rfl
  by_cases early : count<8
  · rw [firstCode,List.take_append_of_le_length (by change count≤8; omega)] at run
    have code : incrementSlot 6=initIncrementPrefixCode 6++[.store .address .index] := rfl
    rw [code,List.take_append_of_le_length (by change count≤7; omega)] at run
    have safe : ∀ instruction∈initIncrementPrefixCode 6,∀ state,WritesWithin ∅ instruction state := by
      intro instruction member state
      simp only [initIncrementPrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with (h|h|h)|(h|h|h|h) <;> subst instruction <;> trivial
    simpa only [early,ite_true] using static_prefix_heap_live input _ before state safe count run
  · by_cases middle : count<17
    · rw [firstCode,List.take_append,List.take_of_length_le (by change 8≤count; omega),linearExecute_append,
        incrementSlot_execute input before base 6 clock fresh clockLive clockValue,Option.bind_some] at run
      rw [List.take_append_of_le_length (by change count-8≤9; omega),
        List.take_append_of_le_length (by change count-8≤8; omega)] at run
      have same := static_prefix_heap_live input swapReadPreludeCode (incrementSlotResult before base 6 clock)
        state (swapReadPrelude_static ∅) (count-8) run
      simpa only [early,ite_false,middle,ite_true] using
        And.intro (same.1.trans (incrementSlot_heap_live before base 6 clock).1)
          (same.2.trans (incrementSlot_heap_live before base 6 clock).2)
    · by_cases late : count<20
      · have code : (basicBlock .stepNext).body=swapFirstCode++storeSlot 10 .old := rfl
        rw [code,List.take_append,List.take_of_length_le (by change 17≤count; omega),linearExecute_append,
          swapFirst_execute input before base clock fresh clockLive clockValue readLive writeLive,Option.bind_some,
          headerStore_decompose,List.take_append_of_le_length (by change count-17≤2; omega)] at run
        have same := static_prefix_heap_live input (headerStorePrefixCode 10) (swapFirstResult before base clock)
          state (headerStorePrelude_static ∅ 10) (count-17) run
        have fields := swapFirst_fields before base clock read write readValue writeValue
        simpa only [early,ite_false,middle,late,ite_true] using
          And.intro (same.1.trans fields.1) (same.2.trans fields.2)
      · have equal : count=20 := by omega
        subst count
        change linearExecute input (basicBlock .stepNext).body before=some state at run
        have whole := stepNext_execute input before base clock fresh clockLive clockValue readLive writeLive
        have same := Option.some.inj (whole.symm.trans run)
        subst state
        have fields := stepNext_fields before base clock read write readValue writeValue
        simpa only [show ¬(20 : ℕ)<8 from by decide,show ¬(20 : ℕ)<17 from by decide,
          show ¬(20 : ℕ)<20 from by decide,ite_false] using And.intro fields.1 fields.2.1

end PDROC.CalibrationRow
