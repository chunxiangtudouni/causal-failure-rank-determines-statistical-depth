module

public import Paid.PDROC_BitVM_Codec_RatMarshal_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.RatMarshal

open Turing PDROC.BitVM.Native
open PaperProofs.Paid.Computation

theorem three_selected (embed : Fin 3 ↪ Stack) (contents : Stack → List Bool)
    (a b c : List Bool) (at0 : contents (embed 0) = a)
    (at1 : contents (embed 1) = b) (at2 : contents (embed 2) = c) :
    Lift.slots embed contents = PDROC.BitVM.Log.TwoStack.threeStacks a b c := by
  funext role
  fin_cases role
  · exact at0
  · exact at1
  · exact at2

theorem source_not_right (source : Register) :
    PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source ≠ 0 := by
  intro same
  have values := congrArg Fin.val same
  have bounds := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot_bounds source
  change (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source).val = 0 at values
  omega

/-- The full physical source Cell is copied BEFORE either destination is
cleared. Only the real 0/24 entry work roles are empty; no other old slot
is constrained. The original complete source bytes are restored. -/
theorem copy_call (source : Register) (num den : Fin 7) (different : num ≠ den)
    (contents : Stack → List Bool) (word : List Bool)
    (sourceWord : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) = word)
    (rightEmpty : contents 0 = []) (leftEmpty : contents 24 = []) :
    ∃ path : Trace (program source num den different)
      (⟨some 1, (none, false), contents⟩ : State)
      (⟨some 4, (none, false), Function.update contents 0 word⟩ : State),
      path.states.length = 2 * word.length + 3 := by
  obtain ⟨run, head, chain, last, _halt, time, _source, _target, _scratch⟩ := Copy.copy_runs word []
  simp only [List.append_nil] at last
  have beforeData := three_selected (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source)
    contents word [] [] sourceWord rightEmpty leftEmpty
  have afterData : Lift.slots (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source)
      (Function.update contents 0 word) = PDROC.BitVM.Log.TwoStack.threeStacks word word [] := by
    apply three_selected
    · change (Function.update contents 0 word)
        (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) = word
      rw [Function.update_of_ne (source_not_right source)]
      exact sourceWord
    · exact Function.update_self _ _ _
    · change (Function.update contents 0 word) 24 = []
      rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 0)]
      exact leftEmpty
  obtain ⟨path, length⟩ := call_three (PDROC.BitVM.Kernel.NatMarshalGlobal.embedding source)
    Copy.program (program source num den different) copyLabels 4
    (copy_agrees source num den different)
    (Copy.state (some 0) none word [] []) (Copy.state none none word word [])
    run head chain last rfl contents (Function.update contents 0 word) false beforeData afterData
    (by
      intro other outside
      exact Function.update_of_ne (outside 1) _ _)
  exact ⟨path, length.trans time⟩

/-- Reuse the already checked literal local clear projection, rather than
reprove a clear loop. The machine equality to Clear006 is definitional. -/
theorem clear_call (caller : Label → Statement) (start finish : Label) (temp : Fin 7)
    (agrees : ∀ label : Unit, caller start = Inline.statement (fun _ : Unit => start) finish
      (Lift.machine (NatWriter.Global.embedding (tempSlot temp) (temp_not_right temp) (temp_not_left temp))
        (NatWriter.clearProgram 2) label))
    (contents : Stack → List Bool) (sign : Bool) :
    ∃ path : Trace caller (⟨some start, (none, sign), contents⟩ : State)
      (⟨some finish, (none, sign), Function.update contents (tempSlot temp) []⟩ : State),
      path.states.length = (contents (tempSlot temp)).length + 2 := by
  let embed := NatWriter.Global.embedding (tempSlot temp) (temp_not_right temp) (temp_not_left temp)
  let localContents := Lift.slots embed contents
  obtain ⟨run, head, chain, last, _halt, time, _frame⟩ := NatWriter.clear_runs 2 localContents none
  have afterData : Lift.slots embed (Function.update contents (tempSlot temp) []) =
      Function.update localContents 2 [] := by
    exact Lift.slots_update embed contents 2 []
  obtain ⟨path, length⟩ := call_three embed (NatWriter.clearProgram 2) caller
    (fun _ : Unit => start) finish agrees
    (⟨some (), none, localContents⟩ : NatWriter.ClearState)
    (⟨none, none, Function.update localContents 2 []⟩ : NatWriter.ClearState)
    run head chain last rfl contents (Function.update contents (tempSlot temp) []) sign rfl afterData
    (by
      intro other outside
      exact Function.update_of_ne (outside 2) _ _)
  exact ⟨path, length.trans time⟩

/-- An actual Header scan, with its real target width ticks consumed and
the full original Nat word reversed into native LEFT. -/
theorem header_call (caller : Label → Statement)
    (labels : PDROC.BitVM.Log.Header.Label → Label) (finish : Label) (temp : Fin 7)
    (agrees : ∀ label, caller (labels label) = Inline.statement labels finish
      (Lift.machine (headerEmbedding temp) PDROC.BitVM.Log.Header.program label))
    (contents : Stack → List Bool) (value : ℕ) (suffix : List Bool) (sign : Bool)
    (input : contents 0 = encodeNatBits value ++ suffix)
    (ticks : contents (tempSlot temp) = []) (archive : contents 24 = []) :
    ∃ path : Trace caller (⟨some (labels 0), (none, sign), contents⟩ : State)
      (⟨some finish, (none, sign), Function.update (Function.update contents 0 suffix)
        24 (encodeNatBits value).reverse⟩ : State),
      path.states.length = 2 * PaperProofs.Paid.Parameters.natBits value + 4 := by
  obtain ⟨run, head, chain, last, _halt, time, _input, _ticks, _archive⟩ :=
    PDROC.BitVM.Log.Header.officialNat_runs value suffix [] none
  simp only [List.append_nil] at last
  have beforeData := three_selected (headerEmbedding temp) contents
    (encodeNatBits value ++ suffix) [] [] input ticks archive
  have afterData : Lift.slots (headerEmbedding temp)
      (Function.update (Function.update contents 0 suffix) 24 (encodeNatBits value).reverse) =
        PDROC.BitVM.Log.TwoStack.threeStacks suffix [] (encodeNatBits value).reverse := by
    change Lift.slots (headerEmbedding temp)
      (Function.update (Function.update contents ((headerEmbedding temp) 0) suffix)
        ((headerEmbedding temp) 2) (encodeNatBits value).reverse) = _
    rw [Lift.slots_update, Lift.slots_update, beforeData,
      PDROC.BitVM.Native.Copy.update_first, PDROC.BitVM.Native.Copy.update_third]
  obtain ⟨path, length⟩ := call_three (headerEmbedding temp) PDROC.BitVM.Log.Header.program
    caller labels finish agrees
    (PDROC.BitVM.Log.Header.state (some 0) none (encodeNatBits value ++ suffix) [] [])
    (PDROC.BitVM.Log.Header.state none none suffix [] (encodeNatBits value).reverse)
    run head chain last rfl contents
    (Function.update (Function.update contents 0 suffix) 24 (encodeNatBits value).reverse)
    sign beforeData afterData
    (by
      intro other outside
      have not24 : other ≠ (24 : Stack) := outside 2
      have not0 : other ≠ (0 : Stack) := outside 0
      rw [Function.update_of_ne not24, Function.update_of_ne not0])
  exact ⟨path, length.trans time⟩

/-- Existing real drain plus actual FALSE Cell tag. The unused selected
role is genuinely empty, not merely a logically blank Tape. -/
theorem drain_call (caller : Label → Statement) (start finish : Label)
    (embed : NatWriter.Stack ↪ Stack)
    (agrees : ∀ label : Unit, caller start = Inline.statement (fun _ : Unit => start) finish
      (Lift.machine embed NatWriter.drainProgram label))
    (contents : Stack → List Bool) (word : List Bool) (sign : Bool)
    (unused : contents (embed 0) = []) (archive : contents (embed 1) = word)
    (target : contents (embed 2) = []) :
    ∃ path : Trace caller (⟨some start, (none, sign), contents⟩ : State)
      (⟨some finish, (none, sign), Function.update (Function.update contents (embed 1) [])
        (embed 2) (false :: word.reverse)⟩ : State),
      path.states.length = word.length + 2 := by
  let run := NatWriter.drainTrace word [] none
  have last := NatWriter.drain_last word [] none
  simp only [List.append_nil] at last
  have beforeData := three_selected embed contents [] word [] unused archive target
  have afterData : Lift.slots embed
      (Function.update (Function.update contents (embed 1) []) (embed 2) (false :: word.reverse)) =
        PDROC.BitVM.Log.TwoStack.threeStacks [] [] (false :: word.reverse) := by
    rw [Lift.slots_update, Lift.slots_update, beforeData,
      PDROC.BitVM.Native.Copy.update_second, PDROC.BitVM.Native.Copy.update_third]
  obtain ⟨path, length⟩ := call_three embed NatWriter.drainProgram caller
    (fun _ : Unit => start) finish agrees
    (NatWriter.drainState (some ()) none word []) (NatWriter.drainState none none [] (false :: word.reverse))
    run (NatWriter.drain_head word [] none) (NatWriter.drain_chain word [] none) last rfl contents
    (Function.update (Function.update contents (embed 1) []) (embed 2) (false :: word.reverse))
    sign beforeData afterData
    (by
      intro other outside
      rw [Function.update_of_ne (outside 2), Function.update_of_ne (outside 1)])
  exact ⟨path, length.trans (NatWriter.drain_length word [] none)⟩

end PDROC.BitVM.Codec.RatMarshal
