module
public import Structure.RootB23_Threshold_FinalSerialize_Pass_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FinalSerialize.Control
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def footerMidCode : Machine 4 := PSTRTMSeq005.seqMachine Uncapped.Steps.twoRightCode
  (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def footerCode : Machine 7 := PSTRTMSeq005.seqMachine footerMidCode PSTRTMThresholdDenPrepare141.twoLeftMachine

theorem footer_bounded (left suffix : List Bool) :
    BoundedRun footerCode (Tape.mk₂ left (false :: false :: true :: suffix)) 7
      (Tape.mk₂ left (false :: false :: false :: suffix)) 8 := by
  have forward : BoundedRun Uncapped.Steps.twoRightCode
      (Tape.mk₂ left (false :: false :: true :: suffix)) 2
      (Tape.mk₂ (false :: false :: left) (true :: suffix)) 3 :=
    ⟨Uncapped.Steps.twoRightTrace left false false (true :: suffix),
      Uncapped.Steps.twoRight_runsFrom _ _ _ _,by rfl⟩
  have erased : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
      (Tape.mk₂ (false :: false :: left) (true :: suffix)) 1
      (Tape.mk₂ (false :: false :: left) (false :: suffix)) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true false _ suffix,
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
  have backward : BoundedRun PSTRTMThresholdDenPrepare141.twoLeftMachine
      (Tape.mk₂ (false :: false :: left) (false :: suffix)) 2
      (Tape.mk₂ left (false :: false :: false :: suffix)) 3 :=
    ⟨PSTRTMThresholdDenPrepare141.twoLeftTrace false false left (false :: suffix),
      PSTRTMThresholdDenPrepare141.twoLeft_runsFrom _ _ _ _,by rfl⟩
  have actual := (forward.seq erased).seq backward
  have port : PSTRTMSeq005.rightLabel (a := 4) (2 : Fin 3) = (7 : Fin 8) := by decide
  rw [port] at actual
  exact actual

def clearMidCap (n : Nat) : Nat := Pass.walkCap n+7+1
def clearCap (n : Nat) : Nat := clearMidCap n+Pass.backCap n+1
def clearCode (n : Nat) : Machine (clearCap n) := PSTRTMSeq005.seqMachine (a := clearMidCap n) (b := Pass.backCap n)
  (PSTRTMSeq005.seqMachine (a := Pass.walkCap n) (b := 7) (Pass.walkCode n) footerCode) (Pass.backCode n)

theorem clear_port (n : Nat) : PSTRTMSeq005.rightLabel (a := Pass.walkCap n+7+1) (maxLabel (Pass.backCap n)) =
    maxLabel (clearCap n) := by
  apply Fin.ext
  change (Pass.walkCap n+7+1)+1+Pass.backCap n = (Pass.walkCap n+7+1)+Pass.backCap n+1
  omega

/-- The sole existing far TRUE is really cleared, without reading or
moving any suffix cell. The fixed field passes then return to B DATA. -/
theorem clear_bounded (archive head : List Bool) (rest : List (List Bool)) (suffix : List Bool) :
    BoundedRun (clearCode rest.length) (Tape.mk₂ (false :: archive) (word head rest (true :: suffix)))
      (maxLabel (clearCap rest.length))
      (Tape.mk₂ (false :: archive) (word head rest (false :: suffix)))
      (4*width head rest+18*(rest.length+1)+8) := by
  have walked := Pass.walk_bounded (false :: archive) head rest (true :: suffix)
  have cleared := footer_bounded (endLeft (false :: archive) head rest) suffix
  have returned := Pass.back_bounded archive head rest (false :: suffix)
  have actual := (walked.seq cleared).seq returned
  rw [clear_port] at actual
  exact actual.mono (by omega)

def nineCode : Machine 158 := clearCode 8

def enteredCode : Machine 5 := PSTRTMSeq005.seqMachine Uncapped.Walk.code Uncapped.Steps.twoRightCode
def clampedCode : Machine 7 := PSTRTMSeq005.seqMachine enteredCode
  (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def entryCode : Machine 10 := PSTRTMSeq005.seqMachine clampedCode Uncapped.Steps.twoRightCode

def bArchive (archive digits : List Bool) : List Bool :=
  false :: false :: (PSTRTMRawNat010.leftBlocks digits.reverse ++ false :: archive)

theorem entry_bounded (archive digits tail : List Bool) :
    BoundedRun entryCode
      (Tape.mk₂ (false :: archive) (PSTRTMIncrement009.blocks digits ++ marker tail)) 10
      (Tape.mk₂ (false :: false :: bArchive archive digits) tail) (2*digits.length+11) := by
  let passed := PSTRTMRawNat010.leftBlocks digits.reverse ++ false :: archive
  have walked := Pass.walk_one (false :: archive) digits (true :: false :: tail)
  have moved : BoundedRun Uncapped.Steps.twoRightCode (Tape.mk₂ passed (marker tail)) 2
      (Tape.mk₂ (false :: false :: passed) (true :: false :: tail)) 3 :=
    ⟨Uncapped.Steps.twoRightTrace passed false false (true :: false :: tail),
      Uncapped.Steps.twoRight_runsFrom _ _ _ _,by rfl⟩
  have erased : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
      (Tape.mk₂ (false :: false :: passed) (true :: false :: tail)) 1
      (Tape.mk₂ (false :: false :: passed) (false :: false :: tail)) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true false _ (false :: tail),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
  have entered : BoundedRun Uncapped.Steps.twoRightCode
      (Tape.mk₂ (false :: false :: passed) (false :: false :: tail)) 2
      (Tape.mk₂ (false :: false :: false :: false :: passed) tail) 3 :=
    ⟨Uncapped.Steps.twoRightTrace _ false false tail,Uncapped.Steps.twoRight_runsFrom _ _ _ _,by rfl⟩
  have actual := ((walked.seq moved).seq erased).seq entered
  have port : PSTRTMSeq005.rightLabel (a := 7) (2 : Fin 3) = (10 : Fin 11) := by decide
  rw [port] at actual
  exact actual.mono (by omega)

def headerCode : Machine 21 := PSTRTMPrepend022.prefixMachine (encodeNat 5)

private theorem owned_prefix (bits left right : List Bool) :
    BoundedRun (PSTRTMPrepend022.prefixMachine bits)
      (Tape.mk₂ (List.replicate bits.length false ++ left) right)
      ⟨PSTRTMPrepend022.prefixStates bits,by omega⟩ (Tape.mk₂ left (bits ++ right)) (3*bits.length+1) := by
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
    have actual := before.seq after
    have port : PSTRTMSeq005.rightLabel (a := PSTRTMPrepend022.prefixStates later) (2 : Fin 3) =
        (⟨PSTRTMPrepend022.prefixStates (bit :: later),by omega⟩ : Fin (PSTRTMPrepend022.prefixStates (bit :: later)+1)) := by
      apply Fin.ext
      simp only [PSTRTMSeq005.rightLabel,PSTRTMPrepend022.prefixStates,show (2 : Fin 3).val=2 by decide]
    rw [port] at actual
    exact actual.mono (by simp only [List.length_cons];omega)

theorem header_bounded (archive right : List Bool) :
    BoundedRun headerCode (Tape.mk₂ (List.replicate 7 false ++ archive) right) 21
      (Tape.mk₂ archive (encodeNat 5 ++ right)) 22 := owned_prefix (encodeNat 5) archive right

end RootB23.Threshold.FinalSerialize.Control
