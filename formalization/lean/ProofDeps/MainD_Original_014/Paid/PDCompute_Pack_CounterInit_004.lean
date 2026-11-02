module
public import Paid.PDCompute_Pack_Code_002
public import Paid.PDCompute_SolverPrimitiveMemory_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute linearExecute_append)

def copyPlusOneCode (source target : ℕ) : List Instruction :=
  copySlot source target++addNatSlot target 1

def copyPlusOneResult (before : State) (base source target value : ℕ) : State :=
  addNatSlotResult (copySlotResult before base source target) base target value 1

theorem copyPlusOneCode_length (source target : ℕ) : (copyPlusOneCode source target).length=14 := rfl

theorem copyPlusOne_header (before : State) (base source target value : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (inside : source<headerWords) :
    Header (copyPlusOneResult before base source target value) base (Function.update values target (.natural (value+1))) := by
  have copied:=Header.copySlot header source target inside
  have incremented:=Header.addNatSlot copied target value 1
  simpa only [copyPlusOneResult,Function.update_idem] using incremented

theorem copyPlusOne_execute (input : List Cell) (before : State) (base source target value : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : source<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values source=.natural value) :
    linearExecute input (copyPlusOneCode source target) before=some (copyPlusOneResult before base source target value) := by
  let copied:=copySlotResult before base source target
  have fields:=copySlotResult_fields before base source target
  have copiedBase : copied.register .fresh=.natural base := fields.2.2.1.trans hbase
  have copiedLive : base+target∈copied.live := by rw [fields.2.1]; exact Finset.mem_insert_self _ _
  have copiedValue : copied.heap (base+target)=.natural value := by
    rw [fields.1,Function.update_self,header.value source inside,hvalue]
  have first:=copySlot_execute input before base source target hbase (header.live source inside)
  have last:=addNatSlot_execute input copied base target value 1 copiedBase copiedLive copiedValue
  rw [copyPlusOneCode,linearExecute_append,first,Option.bind_some]
  exact last

/-- Prefix composition reuses the frozen copy/header and natural-counter
memory lemmas. It never assumes disjointness of the caller's live set. -/
theorem copyPlusOne_prefix_memory (input : List Cell) (before after : State)
    (base source target value : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (sourceInside : source<headerWords) (targetInside : target<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values source=.natural value)
    (count : ℕ) (bound : count≤14)
    (execute : linearExecute input ((copyPlusOneCode source target).take count) before=some after) :
    HeaderMemory before after base := by
  have valid : (HeaderCommand.copy source target).Valid := ⟨sourceInside,targetInside⟩
  have eval : (HeaderCommand.copy source target).eval values=some (Function.update values target (values source)) := rfl
  by_cases short : count≤6
  · have cut : (copyPlusOneCode source target).take count=(copySlot source target).take count :=
      List.take_append_of_le_length short
    rw [cut] at execute
    exact (HeaderCommand.copy source target).prefix_memory input before after base values _ valid header hbase eval count short execute
  · let copied:=copySlotResult before base source target
    have first:=copySlot_execute input before base source target hbase (header.live source sourceInside)
    have cut : (copyPlusOneCode source target).take count=copySlot source target++(addNatSlot target 1).take (count-6) := by
      unfold copyPlusOneCode
      rw [List.take_append,List.take_of_length_le (by change 6≤count;omega)]
      rfl
    rw [cut,linearExecute_append,first,Option.bind_some] at execute
    have copiedHeader:=Header.copySlot header source target sourceInside
    have fields:=copySlotResult_fields before base source target
    have copiedBase : copied.register .fresh=.natural base := fields.2.2.1.trans hbase
    have firstMemory : HeaderMemory before copied base :=
      (HeaderCommand.copy source target).prefix_memory input before copied base values _ valid header hbase eval 6 (by rfl)
        (by change linearExecute input (copySlot source target) before=some copied; exact first)
    have valueCopied : (Function.update values target (values source)) target=.natural value := by
      rw [Function.update_self,hvalue]
    exact firstMemory.trans (addNatSlot_header_memory input copied after base target value 1 _ copiedHeader targetInside
      copiedBase valueCopied (count-6) (by omega) execute)

end PDCompute.Pack
