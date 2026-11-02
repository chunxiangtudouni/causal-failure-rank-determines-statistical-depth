module

public import Paid.PDROC_BitVM_Codec_Output_List_009
public import Paid.PDROC_BitVM_Codec_Output_List_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing

abbrev CleanLabel := Fin 2
abbrev CleanState := TM2.Cfg (fun _ : EmitStack => Bool) CleanLabel CountStore

/-- ListBlank blankness is never used as physical emptiness: this real
loop pops the native LEFT work stack until its actual finite end. -/
def cleanProgram (label : CleanLabel) : TM2.Stmt (fun _ : EmitStack => Bool) CleanLabel CountStore :=
  if label = 0 then .pop 2 countCapture
    (.branch (fun store => store.2.isSome) (.goto (fun _ => 0)) .halt) else .halt

def cleanBefore (right output left header : List Bool) (store : CountStore) : CleanState :=
  ⟨some 0, store, emitSlots right output left header⟩

def cleanAfter (right output header : List Bool) (store : CountStore) : CleanState :=
  ⟨none, (store.1, none), emitSlots right output [] header⟩

theorem clean_cons (bit : Bool) (left right output header : List Bool) (store : CountStore) :
    TM2.step cleanProgram (cleanBefore right output (bit :: left) header store) =
      some (cleanBefore right output left header (store.1, some bit)) := by
  change (some ⟨some 0, (store.1, some bit), Function.update
    (emitSlots right output (bit :: left) header) 2 left⟩ : Option CleanState) = _
  have same : Function.update (emitSlots right output (bit :: left) header) 2 left =
      emitSlots right output left header := by
    funext role
    fin_cases role <;> simp [emitSlots]
  rw [same]
  rfl

theorem clean_nil (right output header : List Bool) (store : CountStore) :
    TM2.step cleanProgram (cleanBefore right output [] header store) =
      some (cleanAfter right output header store) := by
  change (some ⟨none, (store.1, none), Function.update (emitSlots right output [] header) 2 []⟩ :
    Option CleanState) = _
  have same : Function.update (emitSlots right output [] header) 2 [] = emitSlots right output [] header := by
    funext role
    fin_cases role <;> simp [emitSlots]
  rw [same]
  rfl

def cleanTrace (right output header : List Bool) : List Bool → CountStore → List CleanState
  | [], store => [cleanBefore right output [] header store, cleanAfter right output header store]
  | bit :: left, store => cleanBefore right output (bit :: left) header store ::
      cleanTrace right output header left (store.1, some bit)

theorem clean_head (left right output header : List Bool) (store : CountStore) :
    (cleanTrace right output header left store).head? = some (cleanBefore right output left header store) := by
  cases left <;> rfl

theorem clean_last (left right output header : List Bool) (store : CountStore) :
    (cleanTrace right output header left store).getLast? = some (cleanAfter right output header store) := by
  induction left generalizing store with
  | nil => rfl
  | cons bit left ih => rw [cleanTrace, List.getLast?_cons, ih]; rfl

theorem clean_length (left right output header : List Bool) (store : CountStore) :
    (cleanTrace right output header left store).length = left.length + 2 := by
  induction left generalizing store with
  | nil => rfl
  | cons bit left ih => simp only [cleanTrace, List.length_cons, ih]

theorem clean_chain (left right output header : List Bool) (store : CountStore) :
    (cleanTrace right output header left store).IsChain (fun a b => TM2.step cleanProgram a = some b) := by
  induction left generalizing store with
  | nil => exact List.isChain_cons_cons.mpr ⟨clean_nil right output header store, List.isChain_singleton _⟩
  | cons bit left ih =>
    apply List.IsChain.cons (ih (store.1, some bit))
    intro after member
    rw [clean_head] at member
    have same : after = cleanBefore right output left header (store.1, some bit) :=
      (Option.mem_some_iff.mp member).symm
    subst after
    exact clean_cons bit left right output header store

abbrev FinalLabel := Fin 18
abbrev FinalStore := CountStore × Unit
abbrev FinalState := TM2.Cfg (fun _ : EmitStack => Bool) FinalLabel FinalStore
abbrev FinalStatement := TM2.Stmt (fun _ : EmitStack => Bool) FinalLabel FinalStore

def countLabels (label : CountLabel) : FinalLabel := ⟨label.val, by omega⟩
def cleanLabels (label : CleanLabel) : FinalLabel := ⟨4 + label.val, by omega⟩
def readLabels (label : ReadLabel) : FinalLabel := ⟨6 + label.val, by omega⟩
def flushLabels (label : CountLabel) : FinalLabel := ⟨11 + label.val, by omega⟩
def preCleanLabels (label : CleanLabel) : FinalLabel := ⟨16 + label.val, by omega⟩

/-- ONE fixed finalizer. Each component HALT is translated into an actual
goto by the checked Native.Inline syntax. No host stage dispatch occurs:
these are finitely many fixed control labels before every input. -/
def finalProgram (label : FinalLabel) : FinalStatement :=
  if count : label.val < 4 then
    PDROC.BitVM.Native.Inline.statement countLabels 4 (countProgram ⟨label.val, count⟩)
  else if clean : label.val < 6 then
    PDROC.BitVM.Native.Inline.statement cleanLabels 6 (cleanProgram ⟨label.val - 4, by omega⟩)
  else if read : label.val < 11 then
    PDROC.BitVM.Native.Inline.statement readLabels 11 (readerProgram ⟨label.val - 6, by omega⟩)
  else if flush : label.val < 15 then
    PDROC.BitVM.Native.Inline.statement flushLabels 15 (flushProgram ⟨label.val - 11, by omega⟩)
  else if label.val = 15 then .halt
  else PDROC.BitVM.Native.Inline.statement preCleanLabels 2
    (cleanProgram ⟨label.val - 16, by omega⟩)

theorem final_count_agrees (label : CountLabel) :
    finalProgram (countLabels label) =
      PDROC.BitVM.Native.Inline.statement countLabels 4 (countProgram label) := by
  fin_cases label <;> rfl

theorem final_clean_agrees (label : CleanLabel) :
    finalProgram (cleanLabels label) =
      PDROC.BitVM.Native.Inline.statement cleanLabels 6 (cleanProgram label) := by
  fin_cases label <;> rfl

theorem final_read_agrees (label : ReadLabel) :
    finalProgram (readLabels label) =
      PDROC.BitVM.Native.Inline.statement readLabels 11 (readerProgram label) := by
  fin_cases label <;> rfl

theorem final_flush_agrees (label : CountLabel) :
    finalProgram (flushLabels label) =
      PDROC.BitVM.Native.Inline.statement flushLabels 15 (flushProgram label) := by
  fin_cases label <;> rfl

theorem final_preClean_agrees (label : CleanLabel) :
    finalProgram (preCleanLabels label) =
      PDROC.BitVM.Native.Inline.statement preCleanLabels 2 (cleanProgram label) := by
  fin_cases label <;> rfl

end PDROC.BitVM.Codec.OutputList
