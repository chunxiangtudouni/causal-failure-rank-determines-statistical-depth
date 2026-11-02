module
public import Paid.PDCompute_Pack_ReadTail_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem readTail_straight : StraightCode readTailCode := by
  intro instruction member
  simp only [readTailCode,PDLower.CalibrationCompute.storeSlot,PDLower.CalibrationCompute.loadSlot,tagDifferenceCode,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h <;> subst instruction <;> trivial

theorem readTail_pc (before : State) (base tag : ℕ) : (readTailResult before base tag).pc=before.pc+11 := rfl
theorem readTail_output (before : State) (base tag : ℕ) : (readTailResult before base tag).output=before.output := rfl

theorem readTail_trace (program : Program) (input : List Cell) (before : State) (base source pointer tag : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hsource : before.register .old=.natural source)
    (hpointer : values outputCursor=.natural pointer) (htag : values entryStart=.natural tag)
    (fetched : FetchesCode program before.pc readTailCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (readTailResult before base tag) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤180 ∧
      Header (readTailResult before base tag) base (readTailValues values source) ∧
      (readTailResult before base tag).register .fresh=.natural base ∧
      (readTailResult before base tag).register .old=.natural pointer ∧
      (readTailResult before base tag).register .value=.natural (2-tag) ∧
      (readTailResult before base tag).pc=before.pc+11 ∧ (readTailResult before base tag).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  have facts:=readTail_run_memory input before base source pointer tag values header hbase hsource hpointer htag
  obtain ⟨trace,hh,hl,hchain,ht,memory⟩:=linearExecute_trace_memory program input readTailCode readTail_straight before _ base
    fetched facts.1 facts.2.2.2.2.2
  exact ⟨trace,hh,hl,hchain,ht,facts.2.1,facts.2.2.1,facts.2.2.2.1,facts.2.2.2.2.1,
    readTail_pc before base tag,readTail_output before base tag,memory⟩

end PDCompute.Pack
