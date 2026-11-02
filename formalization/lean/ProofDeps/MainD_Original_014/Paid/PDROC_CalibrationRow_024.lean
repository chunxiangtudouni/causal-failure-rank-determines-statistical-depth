module

public import Paid.PDROC_CalibrationRow_015
public import Paid.PDLower_CalibrationCompute_Increment_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

def stepNextResult (before : State) (base clock : ℕ) : State :=
  let incremented := incrementSlotResult before base 6 clock
  let readLoaded := loadSlotResult incremented base 9 .old
  let writeLoaded := loadSlotResult readLoaded base 10 .total
  let readStored := storeSlotResult writeLoaded base 9 .total
  storeSlotResult readStored base 10 .old

theorem stepNext_body : (basicBlock Label.stepNext).body=
    incrementSlot 6++loadSlot 9 .old++loadSlot 10 .total++storeSlot 9 .total++storeSlot 10 .old := rfl

theorem stepNext_execute (input : List Cell) (before : State) (base clock : ℕ)
    (fresh : before.register .fresh=.natural base)
    (clockLive : base+6 ∈ before.live) (clockValue : before.heap (base+6)=.natural clock)
    (readLive : base+9 ∈ before.live) (writeLive : base+10 ∈ before.live) :
    linearExecute input (basicBlock .stepNext).body before=some (stepNextResult before base clock) := by
  let incremented := incrementSlotResult before base 6 clock
  have incFresh := (incrementSlot_fresh before base 6 clock).trans fresh
  have incReadLive : base+9 ∈ incremented.live := Finset.mem_insert_of_mem readLive
  have incWriteLive : base+10 ∈ incremented.live := Finset.mem_insert_of_mem writeLive
  let readLoaded := loadSlotResult incremented base 9 .old
  have readFresh : readLoaded.register .fresh=.natural base := by
    simpa [readLoaded,loadSlotResult] using incFresh
  let writeLoaded := loadSlotResult readLoaded base 10 .total
  have writeFresh : writeLoaded.register .fresh=.natural base := by
    simpa [writeLoaded,loadSlotResult] using readFresh
  let readStored := storeSlotResult writeLoaded base 9 .total
  have storeFresh : readStored.register .fresh=.natural base := by
    simpa [readStored,storeSlotResult] using writeFresh
  simp only [stepNext_body,List.append_assoc,linearExecute_append]
  rw [incrementSlot_execute input before base 6 clock fresh clockLive clockValue,Option.bind_some,
    loadSlot_execute input incremented base 9 .old incFresh incReadLive,Option.bind_some,
    loadSlot_execute input readLoaded base 10 .total readFresh incWriteLive,Option.bind_some,
    storeSlot_execute input writeLoaded base 9 .total writeFresh (by decide),Option.bind_some,
    storeSlot_execute input readStored base 10 .old storeFresh (by decide)]
  rfl

theorem stepNext_fields (before : State) (base clock read write : ℕ)
    (readValue : before.heap (base+9)=.natural read)
    (writeValue : before.heap (base+10)=.natural write) :
    (stepNextResult before base clock).heap=
      Function.update (Function.update (Function.update before.heap (base+6) (.natural (clock+1)))
        (base+9) (.natural write)) (base+10) (.natural read) ∧
    (stepNextResult before base clock).live=insert (base+10) (insert (base+9) (insert (base+6) before.live)) ∧
    (stepNextResult before base clock).register .fresh=before.register .fresh ∧
    (stepNextResult before base clock).pc=before.pc+20 ∧
    (stepNextResult before base clock).output=before.output := by
  simp [stepNextResult,incrementSlotResult,incrementSlotLoaded,loadSlotResult,storeSlotResult,
    readValue,writeValue,Nat.add_assoc]

theorem stepNext_slots (before : State) (base clock read write : ℕ)
    (readValue : before.heap (base+9)=.natural read)
    (writeValue : before.heap (base+10)=.natural write) :
    (stepNextResult before base clock).heap (base+6)=.natural (clock+1) ∧
    (stepNextResult before base clock).heap (base+7)=before.heap (base+7) ∧
    (stepNextResult before base clock).heap (base+9)=.natural write ∧
    (stepNextResult before base clock).heap (base+10)=.natural read := by
  simp [(stepNext_fields before base clock read write readValue writeValue).1]

theorem Buffers.swap (base M read write : ℕ) (buffers : Buffers base M read write) :
    Buffers base M write read := by
  rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩

/-- The actual swap changes only the three header words. Both physical
rows survive, so the just-computed destination becomes the next reader. -/
theorem stepNext_preserves_row (before : State) (base clock read write rowBase : ℕ)
    (readValue : before.heap (base+9)=.natural read)
    (writeValue : before.heap (base+10)=.natural write)
    (row : Array ℚ) (represented : RowAt before rowBase row) (afterHeader : base+16≤rowBase) :
    RowAt (stepNextResult before base clock) rowBase row := by
  have fields := stepNext_fields before base clock read write readValue writeValue
  constructor
  · intro i inside
    rw [fields.2.1]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (represented.live i inside)))
  · intro i inside
    rw [fields.1,Function.update_of_ne (by omega : rowBase+i≠base+10),
      Function.update_of_ne (by omega : rowBase+i≠base+9),Function.update_of_ne (by omega : rowBase+i≠base+6)]
    exact represented.value i inside

end PDROC.CalibrationRow
