module
public import Structure.RootB23_Threshold_OutputArithmetic_Pair_002
public import Structure.RootB23_Threshold_ReturnHeadroom_031

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.OutputArithmetic.OddsFields
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def gap : List Bool := [false,false,true,false,true,true,false,false,true,false,true,true,false,false,true,false]

def literalCode : Machine 48 := PSTRTMPrepend022.prefixMachine gap

private theorem owned_prefix (bits left right : List Bool) :
    BoundedRun (PSTRTMPrepend022.prefixMachine bits)
      (Tape.mk₂ (List.replicate bits.length false ++ left) right)
      ⟨PSTRTMPrepend022.prefixStates bits,by omega⟩ (Tape.mk₂ left (bits ++ right)) (3 * bits.length + 1) := by
  induction bits generalizing left right with
  | nil =>
    refine ⟨[⟨0,Tape.mk₂ left right⟩],⟨rfl,.singleton _,rfl,?_⟩,by rfl⟩
    rfl
  | cons bit later ih =>
    have before := ih (false :: left) right
    have room : List.replicate later.length false ++ false :: left =
        List.replicate (bit :: later).length false ++ left := by
      simp only [List.length_cons,List.replicate_add,List.replicate_one,
        List.append_assoc,List.cons_append,List.nil_append]
    rw [room] at before
    have after := PA17TMRatArithmeticPrefix5060.literal_bit_bounded bit left (later ++ right)
    have joined := before.seq after
    have port : PSTRTMSeq005.rightLabel (a := PSTRTMPrepend022.prefixStates later) (2 : Fin 3) =
        (⟨PSTRTMPrepend022.prefixStates (bit :: later),by omega⟩ : Fin (PSTRTMPrepend022.prefixStates (bit :: later) + 1)) := by
      apply Fin.ext
      simp only [PSTRTMSeq005.rightLabel,PSTRTMPrepend022.prefixStates,
        show (2 : Fin 3).val = 2 by decide]
    rw [port] at joined
    exact joined.mono (by simp only [List.length_cons]; omega)

theorem literal_bounded (left right : List Bool) :
    BoundedRun literalCode (Tape.mk₂ (List.replicate 16 false ++ left) right) 48
      (Tape.mk₂ left (gap ++ right)) 49 := owned_prefix gap left right

def twelveCode : Machine 359 := PSTRTMSeq005.seqMachine ReturnHeadroom.code ReturnHeadroom.fourCode

def fourteenCode : Machine 419 := PSTRTMSeq005.seqMachine twelveCode ReturnHeadroom.twoCode

theorem fourteen_bounded (archive digits : List Bool) :
    BoundedRun fourteenCode (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks digits)) 419
      (Tape.mk₂ (List.replicate 15 false ++ archive) (PSTRTMIncrement009.blocks digits))
      (140 * digits.length + 336) := by
  have eight := ReturnHeadroom.bounded archive digits
  have four := ReturnHeadroom.four_bounded (List.replicate 8 false ++ archive) digits
  have two := ReturnHeadroom.two_bounded (List.replicate 12 false ++ archive) digits
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] at eight four two ⊢
  exact ((eight.seq four).seq two).mono (by omega)

end RootB23.Threshold.OutputArithmetic.OddsFields
