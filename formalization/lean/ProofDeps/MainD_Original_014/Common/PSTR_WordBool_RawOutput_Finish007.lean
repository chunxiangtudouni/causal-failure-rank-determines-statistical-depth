module

public import Common.PSTR_WordBool_RawOutput_Erase006

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

def finishSeekCfg (west east : List Bool) : State :=
  ⟨some 10, (), (seekCfg false west east []).Tape⟩

theorem finish_pair_step (bit : Bool) (later east : List Bool) :
    Edge (finishSeekCfg (bit :: later) east) (finishSeekCfg later (bit :: east)) := by
  cases later <;>
    simp [Edge,finishSeekCfg,seekCfg,cfg,sourceMachine,TM1.step,TM1.stepAux,
      readBit,mv,jump,Function.iterate_succ_apply,Tape.mk₂,
      PSTRTMRawNat010.leftBlocks,PSTRTMIncrement009.blocks]

theorem finish_empty (east : List Bool) : Edge (finishSeekCfg [] east) (finishCfg east) := by
  change some (TM1.stepAux (mv 1 .right .halt) ()
    (Tape.mk₂ [] (false :: (PSTRTMIncrement009.blocks east ++ [false,false] ++ [])))) = _
  simp only [mv,Function.iterate_one,TM1.stepAux,Tape.mk₂,Tape.move_right_mk',
    ListBlank.head_mk,ListBlank.tail_mk,List.headI_cons,List.tail_cons,ListBlank.cons_mk]
  have right : ListBlank.mk (PSTRTMIncrement009.blocks east ++ [false,false] ++ [])=
      ListBlank.mk (PSTRTMIncrement009.blocks east) := by
    simpa using blank_append_zeros (PSTRTMIncrement009.blocks east) 2
  simp only [List.append_nil] at right ⊢
  rw [PSTRTMRawNat010.blank_single_false,right]
  rfl

theorem finish_seek (west east : List Bool) :
    ∃ rest : List State, (finishSeekCfg west east :: rest).IsChain Edge ∧
      (finishSeekCfg west east :: rest).getLast?=some (finishCfg (west.reverse ++ east)) ∧
      rest.length=west.length+1 := by
  induction west generalizing east with
  | nil => exact ⟨[finishCfg east], List.isChain_cons_cons.mpr ⟨finish_empty east,.singleton _⟩,rfl,rfl⟩
  | cons bit later ih =>
    obtain ⟨rest,chain,last,clock⟩ := ih (bit :: east)
    refine ⟨finishSeekCfg later (bit :: east) :: rest,
      List.isChain_cons_cons.mpr ⟨finish_pair_step bit later east,chain⟩,?_,?_⟩
    · simpa [List.reverse_cons,List.append_assoc] using last
    · simp only [List.length_cons,clock]

theorem find_output (bits : List Bool) :
    Edge (cfg 9 (workLeft bits) []) (finishSeekCfg bits.reverse []) := by
  rw [workLeft,blocks_reverse]
  cases h : bits.reverse <;>
    simp [Edge,finishSeekCfg,seekCfg,cfg,sourceMachine,TM1.step,TM1.stepAux,
      mv,jump,Function.iterate_succ_apply,Tape.mk₂,
      PSTRTMRawNat010.leftBlocks,PSTRTMIncrement009.blocks]

/-- Actual final seek through all TRUE flags, followed by RIGHT1 and real
HALT. Only genuinely erased/default FALSE tail cells are normalized. -/
theorem finish_all (bits : List Bool) :
    ∃ rest : List State, (cfg 9 (workLeft bits) [] :: rest).IsChain Edge ∧
      (cfg 9 (workLeft bits) [] :: rest).getLast?=some (finishCfg bits) ∧
      rest.length=bits.length+2 := by
  obtain ⟨rest,chain,last,clock⟩ := finish_seek bits.reverse []
  refine ⟨finishSeekCfg bits.reverse [] :: rest,
    List.isChain_cons_cons.mpr ⟨find_output bits,chain⟩,?_,?_⟩
  · simpa using last
  · simp only [List.length_cons,clock,List.length_reverse]

end PaperProofs.Common.Native.PSTRWordBool.RawOutput.Extract
