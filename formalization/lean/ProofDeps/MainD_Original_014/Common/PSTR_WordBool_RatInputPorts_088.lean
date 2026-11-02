module

public import Common.PSTR_WordBool_RatInputPaths_087

/-! Exact physical entries and exits for the reused programs. The static
role equivalences below leave arbitrary other stack contents in place. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def reverseSource (second : Bool) : RatInput.Stack := if second then 4 else 3
def reverseTarget (second : Bool) : RatInput.Stack := if second then 6 else 5
def reversePort (second : Bool) : Label := if second then .reverseDen else .reverseNum
def reverseReturn (second : Bool) : Label := if second then .den 0 else .reverseDen
def formatPort (second : Bool) : Label := if second then .den 0 else .num 0
def formatReturn (second : Bool) : Label := if second then .num 0 else .finish

def reverseCells (contents : RatInput.Stack→List Bool) (second : Bool) (word target : List Bool) : RatInput.Stack→List Bool :=
  fun slot=>if slot=reverseSource second then word else if slot=reverseTarget second then target else contents slot

def formatCells (contents : RatInput.Stack→List Bool) (second : Bool) (word left output counter : List Bool) : RatInput.Stack→List Bool :=
  fun slot=>if slot=reverseTarget second then word else if slot=14 then left else if slot=13 then output
    else if slot=12 then counter else contents slot

theorem reverse_cells_self (contents : RatInput.Stack→List Bool) (second : Bool) :
    reverseCells contents second (contents (reverseSource second)) (contents (reverseTarget second))=contents := by
  funext slot
  dsimp only [reverseCells]
  split_ifs with first second
  · rw [first]
  · rw [second]
  · rfl

theorem format_cells_self (contents : RatInput.Stack→List Bool) (second : Bool) :
    formatCells contents second (contents (reverseTarget second)) (contents 14) (contents 13) (contents 12)=contents := by
  funext slot
  dsimp only [formatCells]
  split_ifs with first second third fourth
  · rw [first]
  · rw [second]
  · rw [third]
  · rw [fourth]
  · rfl

theorem reverse_configuration (second : Bool) (contents : RatInput.Stack→List Bool)
    (point : RatOutput.Label) (context : C×RatInput.Store) (memory : WordNatIO.Store) (word target : List Bool) :
    reverseConfiguration second (RatOutput.state (StackIso.slots (reverseRoles second).symm contents) point context memory
      (contents 13) word (contents 7) target)=
    (⟨some ((if second then reverseDenLabel else reverseNumLabel) point),(context,memory),reverseCells contents second word target⟩:State C) := by
  unfold reverseConfiguration LabelMap.configuration StackIso.configuration RatOutput.state
  simp only [Option.map_some]
  congr 1
  funext slot
  cases second <;> fin_cases slot <;> rfl

theorem format_configuration (second : Bool) (contents : RatInput.Stack→List Bool)
    (point : WordNatIO.Label) (context : C×RatInput.Store) (memory : WordNatIO.Store) (word left output counter : List Bool) :
    formatConfiguration second (ContextLift.configuration context
      (WordNatIO.state (StackIso.slots (formatRoles second).symm contents) point memory word left output counter))=
    (⟨some ((if second then denLabel else numLabel) point),(context,memory),formatCells contents second word left output counter⟩:State C) := by
  unfold formatConfiguration LabelMap.configuration StackIso.configuration ContextLift.configuration WordNatIO.state
  simp only [Option.map_some]
  congr 1
  funext slot
  cases second <;> fin_cases slot <;> rfl

theorem actual_reverse (caller : Statement C) (second : Bool) (contents : RatInput.Stack→List Bool)
    (memory : Store C) :
    ∃ trace : List (State C),
      trace.head?=some ⟨some (reversePort second),memory,contents⟩ ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some ⟨some (reverseReturn second),(memory.1,(false,false)),
        reverseCells contents second [] ((contents (reverseSource second)).reverse++contents (reverseTarget second))⟩ ∧
      trace.length=(contents (reverseSource second)).length+2 := by
  let background:=StackIso.slots (reverseRoles second).symm contents
  let word:=contents (reverseSource second)
  let target:=contents (reverseTarget second)
  let trace:=RatOutput.reverseTrace background memory.1 word memory.2 (contents 13) (contents 7) target
  have path:=reverse_path caller second background memory.1 word memory.2 (contents 13) (contents 7) target
  refine ⟨trace.map (reverseConfiguration second),?_,path.2.1,?_,?_⟩
  · rw [path.1,reverse_configuration,reverse_cells_self]
    cases second <;> rfl
  · rw [path.2.2,reverse_configuration]
    cases second <;> rfl
  · rw [List.length_map,RatOutput.reverse_length]

theorem actual_format (caller : Statement C) (second : Bool) (contents : RatInput.Stack→List Bool)
    (memory : Store C) (emptyLeft : contents 14=[]) (emptyCounter : contents 12=[]) :
    ∃ trace : List (State C),
      trace.head?=some ⟨some (formatPort second),memory,contents⟩ ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some ⟨some (formatReturn second),(memory.1,(false,false)),
        formatCells contents second [] []
          (encodeNat (PSTRTMIncrement009.valueDigits (contents (reverseTarget second)))++contents 13) []⟩ ∧
      trace.length≤4*(contents (reverseTarget second)).length+11 := by
  let background:=StackIso.slots (formatRoles second).symm contents
  let word:=contents (reverseTarget second)
  obtain ⟨trace,first,chain,last,count,_contexts,_bounds,_frames⟩:=
    WordNatIO.actual_caller_format .halt memory.1 background memory.2 word (contents 13)
  have path:=format_path caller second trace _ _ first chain last rfl
  refine ⟨trace.map (formatConfiguration second),?_,path.2.1,?_,?_⟩
  · have same:=format_cells_self contents second
    rw [emptyLeft,emptyCounter] at same
    rw [path.1,format_configuration,same]
    cases second <;> rfl
  · rw [path.2.2,format_configuration]
    cases second <;> rfl
  · simpa only [List.length_map] using count

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Encoder
