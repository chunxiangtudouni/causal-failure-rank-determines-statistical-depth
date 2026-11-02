module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038e

/-! A real SOURCE rewind and LSB write. The cache bit occupies an actual
extra control row, preserving every old carry bit. A preceding actual038
read port must select this row; no bit is an executable machine argument. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticAllocatePass023 (pushField)

def seenPhase (p : Nat) (memory : Fin (p+1)) (bit : Bool) : Fin (2*p+2) :=
  ⟨2*memory.val+(if bit then 1 else 0),by have hm:=memory.isLt;cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩

def seenBit {p : Nat} (phase : Fin (2*p+2)) : Bool := phase.val%2==1

theorem seenPhase_carry (p : Nat) (memory : Fin (p+1)) (bit : Bool) :
    (seenPhase p memory bit).val/2=memory.val := by
  cases bit <;> simp only [seenPhase,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem seenBit_eq (p : Nat) (memory : Fin (p+1)) (bit : Bool) : seenBit (seenPhase p memory bit)=bit := by
  have hm : (seenPhase p memory bit).val%2=(if bit then 1 else 0) := by
    cases bit <;> simp only [seenPhase,Bool.false_eq_true,ite_false,ite_true] <;> omega
  unfold seenBit
  rw [hm]
  cases bit <;> rfl

def sourceRestoreRow {p : Nat} (phase : Fin (2*p+2)) : Machine 7 :=
  PSTRTMSeq005.seqMachine (a:=5) (b:=1) PA17TMRatArithmeticParse002.fieldBackMachine
    (PA17TMRatArithmeticAllocate013.setMarkerMachine (seenBit phase))

def sourceRestoreRows (p : Nat) : Fin (2*p+2) → Machine 7 := fun phase => sourceRestoreRow phase
def sourceRestorePorts (p : Nat) : Fin (2*p+2) → Fin 8 → Option (Fin (2*p+2) × Fin 8) := fun _ _ => none
def sourceRestoreFamily (p : Nat) : Machine (totalStates (2*p+1) 7) :=
  blockMachine (sourceRestoreRows p) (sourceRestorePorts p)

theorem sourceRestore_row_bounded {p : Nat} (phase : Fin (2*p+2)) (archive tail suffix : List Bool) :
    BoundedRun (sourceRestoreRow phase)
      (Tape.mk₂ (pushField (false::archive) (false::tail)) suffix) 7
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (seenBit phase::tail)++false::suffix))
      (2*(false::tail).length+7) := by
  have hb : BoundedRun PA17TMRatArithmeticParse002.fieldBackMachine
      (Tape.mk₂ (pushField (false::archive) (false::tail)) suffix) 5
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (false::tail)++false::suffix))
      (2*(false::tail).length+5) :=
    ⟨PA17TMRatArithmeticParse002.fieldBackTrace archive (false::tail) suffix,
      PA17TMRatArithmeticParse002.fieldBack_runsFrom archive (false::tail) suffix,
      by rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]⟩
  have hs : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine (seenBit phase))
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (false::tail)++false::suffix)) 1
      (Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (seenBit phase::tail)++false::suffix)) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false (seenBit phase) (false::archive)
        (true::(PSTRTMIncrement009.blocks tail++false::suffix)),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom false (seenBit phase) (false::archive)
        (true::(PSTRTMIncrement009.blocks tail++false::suffix)),by rfl⟩
  exact (hb.seq hs).mono (by omega)

/-- SOURCE payload and every frame cell are physically restored. The
new cache observation remains in the row together with the old carry. -/
theorem sourceRestore_contract (p : Nat) (memory : Fin (p+1)) (bit : Bool)
    (archive tail suffix : List Bool) (inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (sourceRestoreFamily p)
      (blockCfg (seenPhase p memory bit)
        (⟨0,Tape.mk₂ (pushField (false::archive) (false::tail)) suffix⟩ : MachineState 7)) trace
      (blockCfg (seenPhase p memory bit)
        (⟨7,Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks (bit::tail)++false::suffix)⟩ : MachineState 7)) ∧
      trace.length≤2*(false::tail).length+7 ∧
      ∀ k, visitedSpace (sourceRestoreFamily p) inputLength (trace.take k) ≤
        inputLength+4*(false::tail).length+15 := by
  obtain ⟨trace,hr,hl⟩ := sourceRestore_row_bounded (seenPhase p memory bit) archive tail suffix
  rw [seenBit_eq] at hr
  have hb := block_runsFrom (sourceRestoreRows p) (sourceRestorePorts p) (seenPhase p memory bit) _ _ trace hr rfl
  refine ⟨trace.map (blockCfg (seenPhase p memory bit)),hb,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k
    have hs := PSTRTMTrace002.visitedSpace_le (sourceRestoreFamily p) inputLength
      ((trace.map (blockCfg (seenPhase p memory bit))).take k)
    have hk : ((trace.map (blockCfg (seenPhase p memory bit))).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

theorem passedLeft_blocks (left digits : List Bool) :
    PA17TMRatArithmeticFarLoad031.passedLeft left digits=PSTRTMRawNat010.leftBlocks digits.reverse++left := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [PA17TMRatArithmeticFarLoad031.passedLeft,ih,PSTRTMRawNat010.leftBlocks,
      List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
