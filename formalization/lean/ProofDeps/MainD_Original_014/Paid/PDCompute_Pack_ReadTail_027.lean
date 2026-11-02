module
public import Paid.PDCompute_Pack_TagDifference_026
public import Paid.PDCompute_Pack_PointerMemory_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute linearExecute_append loadSlot loadSlotResult storeSlot storeSlotResult)

def readTailCode : List Instruction :=
  storeSlot sourceCursor .old++loadSlot outputCursor .old++loadSlot entryStart .value++tagDifferenceCode
def sourceSaved (before : State) (base : ℕ) : State := storeSlotResult before base sourceCursor .old
def outputLoaded (before : State) (base : ℕ) : State := loadSlotResult (sourceSaved before base) base outputCursor .old
def tagLoaded (before : State) (base : ℕ) : State := loadSlotResult (outputLoaded before base) base entryStart .value
def readTailResult (before : State) (base tag : ℕ) : State := tagDifferenceResult (tagLoaded before base) tag
def readTailValues (values : ℕ → Cell) (source : ℕ) : ℕ → Cell := Function.update values sourceCursor (.natural source)

theorem readTailCode_length : readTailCode.length=11 := rfl

/-- Save the REAL advanced dense pointer, reload the actual output
pointer, load the actual tag and perform2-tag in original ISA operations. -/
theorem readTail_run_memory (input : List Cell) (before : State) (base source pointer tag : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hsource : before.register .old=.natural source)
    (hpointer : values outputCursor=.natural pointer) (htag : values entryStart=.natural tag) :
    linearExecute input readTailCode before=some (readTailResult before base tag) ∧
    Header (readTailResult before base tag) base (readTailValues values source) ∧
    (readTailResult before base tag).register .fresh=.natural base ∧
    (readTailResult before base tag).register .old=.natural pointer ∧
    (readTailResult before base tag).register .value=.natural (2-tag) ∧
    ∀ count≤readTailCode.length,∀ after,
      linearExecute input (readTailCode.take count) before=some after → HeaderMemory before after base := by
  have header1 : Header (sourceSaved before base) base (readTailValues values source) := by
    have h:=header_store_result header sourceCursor .old
    rw [hsource] at h
    exact h
  have header2 : Header (outputLoaded before base) base (readTailValues values source) := header1.loadSlot_preserves outputCursor .old
  have header3 : Header (tagLoaded before base) base (readTailValues values source) := header2.loadSlot_preserves entryStart .value
  have base1 : (sourceSaved before base).register .fresh=.natural base := by simp [sourceSaved,storeSlotResult,hbase]
  have base2 : (outputLoaded before base).register .fresh=.natural base :=
    (loadSlotResult_fresh (sourceSaved before base) base outputCursor .old (by decide)).trans base1
  have base3 : (tagLoaded before base).register .fresh=.natural base :=
    (loadSlotResult_fresh (outputLoaded before base) base entryStart .value (by decide)).trans base2
  have pointed : readTailValues values source outputCursor=.natural pointer := by
    simpa [readTailValues,sourceCursor,outputCursor] using hpointer
  have tagged : readTailValues values source entryStart=.natural tag := by
    simpa [readTailValues,sourceCursor,entryStart] using htag
  have old2 : (outputLoaded before base).register .old=.natural pointer :=
    (header1.loadSlot_execute input outputCursor .old (by decide) base1).2.trans pointed
  have old3 : (tagLoaded before base).register .old=.natural pointer := by
    simpa [tagLoaded,loadSlotResult] using old2
  have value3 : (tagLoaded before base).register .value=.natural tag :=
    (header2.loadSlot_execute input entryStart .value (by decide) base2).2.trans tagged
  have run1 : linearExecute input (storeSlot sourceCursor .old) before=some (sourceSaved before base) :=
    PDLower.CalibrationCompute.storeSlot_execute input before base sourceCursor .old hbase (by decide)
  have run2 : linearExecute input (loadSlot outputCursor .old) (sourceSaved before base)=some (outputLoaded before base) :=
    (header1.loadSlot_execute input outputCursor .old (by decide) base1).1
  have run3 : linearExecute input (loadSlot entryStart .value) (outputLoaded before base)=some (tagLoaded before base) :=
    (header2.loadSlot_execute input entryStart .value (by decide) base2).1
  have run4 : linearExecute input tagDifferenceCode (tagLoaded before base)=some (readTailResult before base tag) :=
    tagDifference_execute input (tagLoaded before base) tag value3
  have lastFields:=tagDifference_fields (tagLoaded before base) tag
  refine ⟨?_,header3,lastFields.1.trans base3,lastFields.2.1.trans old3,lastFields.2.2.1,?_⟩
  · simp only [readTailCode,List.append_assoc,linearExecute_append,run1,Option.bind_some,run2,run3,run4]
  · have mem1 : ∀ count≤(storeSlot sourceCursor .old).length,∀ state,
        linearExecute input ((storeSlot sourceCursor .old).take count) before=some state → HeaderMemory before state base := by
      intro count bound state execute
      exact storeSlot_prefix_memory input before state base sourceCursor .old values header (by decide) hbase (by decide) count bound execute
    have mem2 : ∀ count≤(loadSlot outputCursor .old).length,∀ state,
        linearExecute input ((loadSlot outputCursor .old).take count) (sourceSaved before base)=some state → HeaderMemory (sourceSaved before base) state base := by
      intro count bound state execute
      have unchanged:=loadSlot_prefix_memory input (sourceSaved before base) state base outputCursor .old base1
        (header1.live outputCursor (by decide)) count bound execute
      exact HeaderMemory.of_unchanged base unchanged.1 unchanged.2.1 unchanged.2.2
    have mem3 : ∀ count≤(loadSlot entryStart .value).length,∀ state,
        linearExecute input ((loadSlot entryStart .value).take count) (outputLoaded before base)=some state → HeaderMemory (outputLoaded before base) state base := by
      intro count bound state execute
      have unchanged:=loadSlot_prefix_memory input (outputLoaded before base) state base entryStart .value base2
        (header2.live entryStart (by decide)) count bound execute
      exact HeaderMemory.of_unchanged base unchanged.1 unchanged.2.1 unchanged.2.2
    have mem4 : ∀ count≤tagDifferenceCode.length,∀ state,
        linearExecute input (tagDifferenceCode.take count) (tagLoaded before base)=some state → HeaderMemory (tagLoaded before base) state base := by
      intro count _bound state execute
      exact tagDifference_prefix_memory input (tagLoaded before base) state base count execute
    have tail:=header_prefix_append input (loadSlot entryStart .value) tagDifferenceCode (outputLoaded before base)
      (tagLoaded before base) base run3 mem3 mem4
    have middle:=header_prefix_append input (loadSlot outputCursor .old) (loadSlot entryStart .value++tagDifferenceCode)
      (sourceSaved before base) (outputLoaded before base) base run2 mem2 tail
    have joined:=header_prefix_append input (storeSlot sourceCursor .old)
      (loadSlot outputCursor .old++(loadSlot entryStart .value++tagDifferenceCode)) before (sourceSaved before base) base run1 mem1 middle
    simpa only [readTailCode,List.append_assoc] using joined

end PDCompute.Pack
