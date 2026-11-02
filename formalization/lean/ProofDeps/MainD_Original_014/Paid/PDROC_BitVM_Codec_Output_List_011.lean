module

public import Paid.PDROC_BitVM_Codec_Output_List_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PaperProofs.Common.Native.PSTRWordBool

/-- First really clear the arbitrary remaining native padding. At the
first actual empty pop, push the final TRUE on reverse output. Two genuine
drains then restore byte order and prepend the bare count word. -/
def flushProgram (label : CountLabel) : CountStatement :=
  if label = 0 then
    .pop 0 countCapture
      (.branch (fun store => store.2.isSome) (.goto (fun _ => 0))
        (.push 1 (fun _ => true) (.goto (fun _ => 1))))
  else if label = 1 then flowCode 1 1 (.goto (fun _ => 2))
  else if label = 2 then flowCode 3 2 .halt else .halt

def flushBefore (padding bytes header : List Bool) (store : CountStore) : CountState :=
  ⟨some 0, store, emitSlots padding bytes.reverse [] header.reverse⟩

def flushOutput (bytes header : List Bool) (old : BoolOnStacks.Store 51) : CountState :=
  ⟨some 1, (old, none), emitSlots [] (true :: bytes.reverse) [] header.reverse⟩

def flushHeader (bytes header : List Bool) (old : BoolOnStacks.Store 51) : CountState :=
  ⟨some 2, (old, none), emitSlots (bytes ++ [true]) [] [] header.reverse⟩

def flushAfter (bytes header : List Bool) (old : BoolOnStacks.Store 51) : CountState :=
  ⟨none, (old, none), emitSlots (header ++ bytes ++ [true]) [] [] []⟩

theorem flush_clear_cons (bit : Bool) (padding bytes header : List Bool) (store : CountStore) :
    TM2.step flushProgram (flushBefore (bit :: padding) bytes header store) =
      some (flushBefore padding bytes header (store.1, some bit)) := by
  change (some ⟨some 0, (store.1, some bit), Function.update
    (emitSlots (bit :: padding) bytes.reverse [] header.reverse) 0 padding⟩ : Option CountState) = _
  have same : Function.update (emitSlots (bit :: padding) bytes.reverse [] header.reverse) 0 padding =
      emitSlots padding bytes.reverse [] header.reverse := by
    funext role
    fin_cases role <;> simp [emitSlots]
  rw [same]
  rfl

theorem flush_clear_nil (bytes header : List Bool) (store : CountStore) :
    TM2.step flushProgram (flushBefore [] bytes header store) =
      some (flushOutput bytes header store.1) := by
  change (some ⟨some 1, (store.1, none), Function.update (Function.update
    (emitSlots [] bytes.reverse [] header.reverse) 0 []) 1 (true :: bytes.reverse)⟩ : Option CountState) = _
  have same : Function.update (Function.update
      (emitSlots [] bytes.reverse [] header.reverse) 0 []) 1 (true :: bytes.reverse) =
      emitSlots [] (true :: bytes.reverse) [] header.reverse := by
    funext role
    fin_cases role <;> simp [emitSlots]
  rw [same]
  rfl

def flushClearTrace : List Bool → List Bool → List Bool → CountStore → List CountState
  | [], bytes, header, store => [flushBefore [] bytes header store, flushOutput bytes header store.1]
  | bit :: padding, bytes, header, store =>
      flushBefore (bit :: padding) bytes header store ::
        flushClearTrace padding bytes header (store.1, some bit)

theorem flushClear_head (padding bytes header : List Bool) (store : CountStore) :
    (flushClearTrace padding bytes header store).head? = some (flushBefore padding bytes header store) := by
  cases padding <;> rfl

theorem flushClear_last (padding bytes header : List Bool) (store : CountStore) :
    (flushClearTrace padding bytes header store).getLast? = some (flushOutput bytes header store.1) := by
  induction padding generalizing store with
  | nil => rfl
  | cons bit padding ih => rw [flushClearTrace, List.getLast?_cons, ih]; rfl

theorem flushClear_length (padding bytes header : List Bool) (store : CountStore) :
    (flushClearTrace padding bytes header store).length = padding.length + 2 := by
  induction padding generalizing store with
  | nil => rfl
  | cons bit padding ih => simp only [flushClearTrace, List.length_cons, ih]

theorem flushClear_chain (padding bytes header : List Bool) (store : CountStore) :
    (flushClearTrace padding bytes header store).IsChain
      (fun a b => TM2.step flushProgram a = some b) := by
  induction padding generalizing store with
  | nil => exact List.isChain_cons_cons.mpr ⟨flush_clear_nil bytes header store, List.isChain_singleton _⟩
  | cons bit padding ih =>
    apply List.IsChain.cons (ih (store.1, some bit))
    intro after member
    rw [flushClear_head] at member
    have same : after = flushBefore padding bytes header (store.1, some bit) :=
      (Option.mem_some_iff.mp member).symm
    subst after
    exact flush_clear_cons bit padding bytes header store

def flushOutputTrace (bytes header : List Bool) (old : BoolOnStacks.Store 51) : List CountState :=
  flowTrace 1 1 (.goto (fun _ => 2))
    (fun role => if role = 3 then header.reverse else []) (true :: bytes.reverse) [] (old, none)

def flushHeaderTrace (bytes header : List Bool) (old : BoolOnStacks.Store 51) : List CountState :=
  flowTrace 3 2 .halt (fun _ => []) header.reverse (bytes ++ [true]) (old, none)

theorem flushOutput_head (bytes header : List Bool) (old : BoolOnStacks.Store 51) :
    (flushOutputTrace bytes header old).head? = some (flushOutput bytes header old) := by
  rw [flushOutputTrace, flow_head]
  apply congrArg some
  have same : flowSlots 1 (true :: bytes.reverse) []
      (fun role => if role = 3 then header.reverse else []) =
      emitSlots [] (true :: bytes.reverse) [] header.reverse := by
    funext role
    fin_cases role <;> simp [flowSlots, emitSlots]
  change (⟨some 1, (old, none), _⟩ : CountState) = _
  rw [same]
  rfl

theorem flushOutput_last (bytes header : List Bool) (old : BoolOnStacks.Store 51) :
    (flushOutputTrace bytes header old).getLast? = some (flushHeader bytes header old) := by
  rw [flushOutputTrace, flow_last]
  simp only [List.reverse_cons, List.reverse_reverse, List.append_nil, TM2.stepAux]
  apply congrArg some
  have same : flowSlots 1 [] (bytes ++ [true])
      (fun role => if role = 3 then header.reverse else []) =
      emitSlots (bytes ++ [true]) [] [] header.reverse := by
    funext role
    fin_cases role <;> simp [flowSlots, emitSlots]
  rw [same]
  rfl

theorem flushHeader_head (bytes header : List Bool) (old : BoolOnStacks.Store 51) :
    (flushHeaderTrace bytes header old).head? = some (flushHeader bytes header old) := by
  rw [flushHeaderTrace, flow_head]
  apply congrArg some
  have same : flowSlots 3 header.reverse (bytes ++ [true]) (fun _ => []) =
      emitSlots (bytes ++ [true]) [] [] header.reverse := by
    funext role
    fin_cases role <;> simp [flowSlots, emitSlots]
  change (⟨some 2, (old, none), _⟩ : CountState) = _
  rw [same]
  rfl

theorem flushHeader_last (bytes header : List Bool) (old : BoolOnStacks.Store 51) :
    (flushHeaderTrace bytes header old).getLast? = some (flushAfter bytes header old) := by
  rw [flushHeaderTrace, flow_last]
  simp only [List.reverse_reverse, TM2.stepAux]
  apply congrArg some
  have same : flowSlots 3 [] (header ++ (bytes ++ [true])) (fun _ => []) =
      emitSlots (header ++ bytes ++ [true]) [] [] [] := by
    funext role
    fin_cases role <;> simp [flowSlots, emitSlots, List.append_assoc]
  rw [same]
  rfl

def flushTrace (padding bytes header : List Bool) (store : CountStore) : List CountState :=
  (flushClearTrace padding bytes header store ++ (flushOutputTrace bytes header store.1).tail) ++
    (flushHeaderTrace bytes header store.1).tail

/-- Actual variable-byte output assembly. Header and bytes are PROOF
descriptions of the physical reverse stacks. The machine reads neither
host lists nor a numeric count and really clears all prior padding. -/
theorem flush_runs (padding bytes header : List Bool) (store : CountStore) :
    ∃ run : List CountState,
      run.head? = some (flushBefore padding bytes header store) ∧
      run.IsChain (fun a b => TM2.step flushProgram a = some b) ∧
      run.getLast? = some (flushAfter bytes header store.1) ∧
      TM2.step flushProgram (flushAfter bytes header store.1) = none ∧
      run.length = padding.length + bytes.length + header.length + 5 ∧
      (flushAfter bytes header store.1).stk 0 = header ++ bytes ++ [true] ∧
      (flushAfter bytes header store.1).stk 1 = [] ∧
      (flushAfter bytes header store.1).stk 2 = [] ∧
      (flushAfter bytes header store.1).stk 3 = [] := by
  have left := PDROC.BitVM.Log.TwoStack.join_chain
    (flushClearTrace padding bytes header store) (flushOutputTrace bytes header store.1)
    (flushOutput bytes header store.1) (flushClear_chain padding bytes header store)
    (flow_chain flushProgram 1 (by decide) 1 (.goto (fun _ => 2)) rfl _ _ _ _)
    (flushClear_last padding bytes header store) (flushOutput_head bytes header store.1)
  have leftLast : (flushClearTrace padding bytes header store ++
      (flushOutputTrace bytes header store.1).tail).getLast? =
      some (flushHeader bytes header store.1) := by
    have notOne : (flushOutputTrace bytes header store.1).length ≠ 1 := by
      simp only [flushOutputTrace, flow_length, List.length_cons, List.length_reverse]
      omega
    simp only [List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      flushOutput_last, Option.some_or]
  have actual := PDROC.BitVM.Log.TwoStack.join_chain _ _ (flushHeader bytes header store.1)
    left (flow_chain flushProgram 3 (by decide) 2 .halt rfl _ _ _ _) leftLast
      (flushHeader_head bytes header store.1)
  refine ⟨flushTrace padding bytes header store, ?_, actual, ?_, rfl, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [flushTrace, List.head?_append, flushClear_head, Option.some_or]
  · have notOne : (flushHeaderTrace bytes header store.1).length ≠ 1 := by
      simp only [flushHeaderTrace, flow_length, List.length_reverse]
      omega
    simp only [flushTrace, List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
      flushHeader_last, Option.some_or]
  · simp only [flushTrace, List.length_append, List.length_tail, flushClear_length,
      flushOutputTrace, flushHeaderTrace, flow_length, List.length_cons, List.length_reverse]
    omega

end PDROC.BitVM.Codec.OutputList
