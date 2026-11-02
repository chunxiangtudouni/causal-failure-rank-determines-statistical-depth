module

public import Paid.PDLower_CalibrationCompute_HeapList_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- A proof-side description of the sixteen REAL heap cells. It is not
an ISA instruction, a supplied output, or an extra paper qualification. -/
structure Header where
  returnPC : ℕ
  endpoints : ℕ
  M : ℕ
  Q : ℕ
  gamma : ℚ
  level : ℕ
  clock : ℕ
  cursor : ℕ
  width : ℕ
  readBase : ℕ
  writeBase : ℕ
  q : ℚ
  outputCursor : ℕ

def Header.cells (header : Header) : List Cell :=
  [.natural header.returnPC,.natural header.endpoints,.natural header.M,.natural header.Q,.rational header.gamma,
   .natural header.level,.natural header.clock,.natural header.cursor,.natural header.width,
   .natural header.readBase,.natural header.writeBase,.rational header.q,
   .rational (1/2-header.gamma),.rational (1/2+header.gamma),.natural 0,.natural header.outputCursor]

@[simp] theorem Header.cells_length (header : Header) : header.cells.length = 16 := rfl

def Header.At (header : Header) (state : State) (base : ℕ) : Prop := HeapList state base header.cells

def Header.initial (base endpoints returnPC M Q : ℕ) (gamma : ℚ) : Header :=
  ⟨returnPC,endpoints,M,Q,gamma,1,0,0,0,firstRow base,secondRow base M,0,resultBase base M+1⟩

theorem Header.set_level (header : Header) (level : ℕ) :
    header.cells.set 5 (.natural level) = ({header with level := level}).cells := rfl
theorem Header.set_clock (header : Header) (clock : ℕ) :
    header.cells.set 6 (.natural clock) = ({header with clock := clock}).cells := rfl
theorem Header.set_cursor (header : Header) (cursor : ℕ) :
    header.cells.set 7 (.natural cursor) = ({header with cursor := cursor}).cells := rfl
theorem Header.set_width (header : Header) (width : ℕ) :
    header.cells.set 8 (.natural width) = ({header with width := width}).cells := rfl
theorem Header.set_readBase (header : Header) (readBase : ℕ) :
    header.cells.set 9 (.natural readBase) = ({header with readBase := readBase}).cells := rfl
theorem Header.set_writeBase (header : Header) (writeBase : ℕ) :
    header.cells.set 10 (.natural writeBase) = ({header with writeBase := writeBase}).cells := rfl
theorem Header.set_q (header : Header) (q : ℚ) :
    header.cells.set 11 (.rational q) = ({header with q := q}).cells := rfl
theorem Header.set_outputCursor (header : Header) (cursor : ℕ) :
    header.cells.set 15 (.natural cursor) = ({header with outputCursor := cursor}).cells := rfl

theorem Header.At.lookup {header : Header} {state : State} {base offset : ℕ} {value : Cell}
    (represented : header.At state base) (lookup : header.cells[offset]? = some value) :
    state.heap (base+offset) = value ∧ base+offset ∈ state.live := by
  obtain ⟨inside,eq⟩ := List.getElem?_eq_some_iff.mp lookup
  exact ⟨(HeapList.value represented offset inside).trans eq,represented.1 offset inside⟩

theorem Header.At.load {header : Header} {state : State} {base offset : ℕ} {value : Cell}
    (represented : header.At state base) (input : List Cell) (fresh : state.register .fresh = .natural base)
    (lookup : header.cells[offset]? = some value) (target : Register) :
    ∃ after,linearExecute input (loadSlot offset target) state = some after ∧
      after.register target = value ∧ header.At after base := by
  obtain ⟨correct,live⟩ := represented.lookup lookup
  refine ⟨loadSlotResult state base offset target,loadSlot_execute input state base offset target fresh live,?_,?_⟩
  · simpa [loadSlotResult] using correct
  · simpa only [Header.At,HeapList,heapSegment,loadSlotResult] using represented

theorem Header.At.store {header : Header} {state : State} {base : ℕ}
    (represented : header.At state base) (input : List Cell) (fresh : state.register .fresh = .natural base)
    (offset : ℕ) (inside : offset < 16) (source : Register) (safe : source ≠ .address)
    (value : Cell) (sourceValue : state.register source = value) (updated : Header)
    (updatedCells : header.cells.set offset value = updated.cells) :
    ∃ after,linearExecute input (storeSlot offset source) state = some after ∧
      updated.At after base ∧ Frame state after base header.M := by
  have bound : offset < header.cells.length := by simpa only [Header.cells_length] using inside
  have newCells : header.cells.set offset (state.register source) = updated.cells := by rw [sourceValue,updatedCells]
  refine ⟨storeSlotResult state base offset source,storeSlot_execute input state base offset source fresh safe,?_,?_⟩
  · simpa only [Header.At,HeapList,heapSegment,storeSlotResult,writeCell,newCells] using
      HeapList.write represented offset bound (state.register source)
  · exact storeSlot_frame state base offset source header.M (by rw [workspaceSize_linear]; omega)

end PDLower.CalibrationCompute
