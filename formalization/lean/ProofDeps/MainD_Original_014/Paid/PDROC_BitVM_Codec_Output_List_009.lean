module

public import Paid.PDROC_BitVM_Codec_Output_List_008
public import Paid.PDROC_BitVM_Log_Header_005
public import Paid.PDROC_BitVM_Native_StoreTrace_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

abbrev ReadLabel := Fin 5
abbrev ReadState := TM2.Cfg (fun _ : EmitStack => Bool) ReadLabel CountStore
abbrev ReadLocalStore := Option Bool × BoolOnStacks.Store 51
abbrev ReadLocalState := TM2.Cfg (fun _ : EmitStack => Bool) ReadLabel ReadLocalStore
abbrev ReadLocalStatement := TM2.Stmt (fun _ : EmitStack => Bool) ReadLabel ReadLocalStore

def readerRoles : PDROC.BitVM.Log.Header.Stack ↪ EmitStack :=
  ⟨fun role => if role = 0 then 0 else if role = 1 then 2 else 3, by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all⟩

def readerLabels : PDROC.BitVM.Log.Header.Label → ReadLabel :=
  fun label => ⟨label.val, Nat.lt_trans label.isLt (by decide)⟩

def readerCaller (label : ReadLabel) : ReadLocalStatement :=
  if small : label.val < 4 then
    PDROC.BitVM.Native.Inline.statement readerLabels 4
      (PDROC.BitVM.Native.Lift.statement readerRoles
        (PDROC.BitVM.Log.Header.program ⟨label.val, small⟩))
  else .halt

/-- The existing actual Nat reader with a fixed finite store swap.
Its archive is the whole BARE Nat word, without a natural Cell tag. -/
def readerProgram : ReadLabel → TM2.Stmt (fun _ : EmitStack => Bool) ReadLabel CountStore :=
  PDROC.BitVM.Native.StoreIso.machine (Equiv.prodComm _ _) readerCaller

def readerBefore (value : ℕ) (suffix output : List Bool) (store : CountStore) : ReadState :=
  ⟨some 0, store, emitSlots (encodeNat value ++ suffix) output [] []⟩

def readerAfter (value : ℕ) (suffix output : List Bool) (old : BoolOnStacks.Store 51) : ReadState :=
  ⟨none, (old, none), emitSlots suffix output [] (encodeNat value).reverse⟩

theorem readerCaller_agrees (label : PDROC.BitVM.Log.Header.Label) :
    readerCaller (readerLabels label) =
      PDROC.BitVM.Native.Inline.statement readerLabels 4
        (PDROC.BitVM.Native.Lift.machine readerRoles PDROC.BitVM.Log.Header.program label) := by
  fin_cases label <;> rfl

/-- Genuine self-delimiting extraction from the PHYSICAL prefix proved in
008. Arbitrary trailing padding is left on role0 and must really be cleared
later. The reverse output remains unchanged, and the width ticks end empty. -/
theorem reader_runs (value : ℕ) (suffix output : List Bool) (store : CountStore) :
    ∃ run : List ReadState,
      run.head? = some (readerBefore value suffix output store) ∧
      run.IsChain (fun a b => TM2.step readerProgram a = some b) ∧
      run.getLast? = some (readerAfter value suffix output store.1) ∧
      TM2.step readerProgram (readerAfter value suffix output store.1) = none ∧
      run.length = 2 * natBits value + 5 ∧
      (readerAfter value suffix output store.1).stk 0 = suffix ∧
      (readerAfter value suffix output store.1).stk 1 = output ∧
      (readerAfter value suffix output store.1).stk 2 = [] ∧
      (readerAfter value suffix output store.1).stk 3 = (encodeNat value).reverse := by
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceSize, _input, _ticks, _archive⟩ :=
    PDROC.BitVM.Log.Header.officialNat_runs value suffix [] store.2
  simp only [PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral] at sourceHead sourceLast
  let start : TM2.Cfg (fun _ : EmitStack => Bool) PDROC.BitVM.Log.Header.Label (Option Bool) :=
    ⟨some 0, store.2, emitSlots (encodeNat value ++ suffix) output [] []⟩
  let final : PDROC.BitVM.Log.Header.State :=
    PDROC.BitVM.Log.Header.state none none suffix [] (encodeNat value).reverse
  have entry : PDROC.BitVM.Native.Lift.cfg readerRoles start =
      PDROC.BitVM.Log.Header.state (some 0) store.2 (encodeNat value ++ suffix) [] [] := by
    have same : PDROC.BitVM.Native.Lift.slots readerRoles
        (emitSlots (encodeNat value ++ suffix) output [] []) =
          PDROC.BitVM.Log.Header.slots (encodeNat value ++ suffix) [] [] := by
      funext role
      fin_cases role <;> rfl
    change (⟨some 0, store.2, _⟩ : PDROC.BitVM.Log.Header.State) = _
    rw [same]
    rfl
  have sourceLast' : source.getLast? = some final := by
    simpa only [List.append_nil, final] using sourceLast
  have sourceHalt' : TM2.step PDROC.BitVM.Log.Header.program final = none := rfl
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq := Option.some.inj sourceHead
    change first = _ at firstEq
    subst first
    obtain ⟨posts, localFinal, length, chain, last, represented, frame⟩ :=
      PDROC.BitVM.Native.Lift.path readerRoles PDROC.BitVM.Log.Header.program start
        (PDROC.BitVM.Log.Header.state (some 0) store.2 (encodeNat value ++ suffix) [] [])
        final rest entry sourceChain sourceLast'
    have halted : TM2.step
        (PDROC.BitVM.Native.Lift.machine readerRoles PDROC.BitVM.Log.Header.program) localFinal = none := by
      apply PDROC.BitVM.Native.Lift.halt_project readerRoles PDROC.BitVM.Log.Header.program
      rw [represented]
      exact sourceHalt'
    have data : localFinal.stk = emitSlots suffix output [] (encodeNat value).reverse := by
      funext role
      fin_cases role
      · exact congrArg (fun state : PDROC.BitVM.Log.Header.State => state.stk 0) represented
      · exact frame 1 (by intro role; fin_cases role <;> decide)
      · exact congrArg (fun state : PDROC.BitVM.Log.Header.State => state.stk 1) represented
      · exact congrArg (fun state : PDROC.BitVM.Log.Header.State => state.stk 2) represented
    have localStore : localFinal.var = none :=
      congrArg (fun state : PDROC.BitVM.Log.Header.State => state.var) represented
    obtain ⟨readerTrace, middle, head, actual, middleLast, returned, middleData, middleStore, size⟩ :=
      PDROC.BitVM.Native.Inline.actual_return_trace readerLabels 4
        (PDROC.BitVM.Native.Lift.machine readerRoles PDROC.BitVM.Log.Header.program)
        readerCaller readerCaller_agrees (start :: posts) start localFinal store.1 rfl chain last halted
    let stopped : ReadLocalState :=
      ⟨none, (none, store.1), emitSlots suffix output [] (encodeNat value).reverse⟩
    have middleEq : middle =
        (⟨some 4, (none, store.1), emitSlots suffix output [] (encodeNat value).reverse⟩ :
          ReadLocalState) := by
      rcases middle with ⟨label, finiteStore, contents⟩
      change label = some 4 at returned
      change finiteStore = (localFinal.var, store.1) at middleStore
      change contents = localFinal.stk at middleData
      rw [localStore] at middleStore
      subst label
      subst finiteStore
      rw [middleData, data]
    have edge : TM2.step readerCaller middle = some stopped := by
      rw [middleEq]
      rfl
    have pair : [middle, stopped].IsChain (fun a b => TM2.step readerCaller a = some b) :=
      List.isChain_cons_cons.mpr ⟨edge, List.isChain_singleton _⟩
    have joined := PDROC.BitVM.Log.TwoStack.join_chain readerTrace [middle, stopped] middle
      actual pair middleLast rfl
    have localHead : (readerTrace ++ [stopped]).head? =
        some (PDROC.BitVM.Native.Inline.cfg readerLabels 4 store.1 start) := by
      simp only [List.head?_append, head, Option.some_or]
    obtain ⟨run, after, first, real, finalLast, halt, _label, _store, finalData, realSize⟩ :=
      PDROC.BitVM.Native.StoreIso.actual_trace (Equiv.prodComm _ _) readerCaller
        (readerTrace ++ [stopped]) (PDROC.BitVM.Native.Inline.cfg readerLabels 4 store.1 start)
        stopped localHead joined (List.getLast?_append_cons readerTrace stopped []) rfl
    have afterEq : after = readerAfter value suffix output store.1 := by
      rcases after with ⟨label, finiteStore, contents⟩
      change label = none at _label
      change finiteStore = (store.1, none) at _store
      subst label
      subst finiteStore
      change contents = emitSlots suffix output [] (encodeNat value).reverse at finalData
      rw [finalData]
      rfl
    rw [afterEq] at finalLast halt
    refine ⟨run, first, real, finalLast, halt, ?_, rfl, rfl, rfl, rfl⟩
    simp only [realSize, List.length_append, size, List.length_cons, List.length_nil, length]
    change rest.length + 1 = 2 * natBits value + 4 at sourceSize
    omega

end PDROC.BitVM.Codec.OutputList
