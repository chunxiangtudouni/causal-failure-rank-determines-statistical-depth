module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038q
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038n

/-! Header-entry original-field loader with an existing nonempty cache
bank. The original saved LSB is the actual014 incoming finite-control row;
all rows are compiled before input. No SourceCorrect or head oracle is an
extra caller premise. Both plain and actual shared-B geometry are covered. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticFarLoad031

def originalBankNavCopyCap (j : Nat) (kind : Destination) : Nat := 16+originalBankCopyCap j kind+1
def originalBankRowCap (j : Nat) (kind : Destination) : Nat := originalBankNavCopyCap j kind+1+1
def originalBankNavCopyMachine (field : SourceField) (j : Nat) (kind : Destination) :
    Machine (originalBankNavCopyCap j kind) :=
  PSTRTMSeq005.seqMachine (a:=16) (b:=originalBankCopyCap j kind)
    (sourceNavigation field) (originalBankCopyMachine (sourceRoute field) j kind)
def originalBankRowMachine (memory : Nat) (field : SourceField) (j : Nat) (kind : Destination) :
    Machine (originalBankRowCap j kind) :=
  PSTRTMSeq005.seqMachine (a:=originalBankNavCopyCap j kind) (b:=1)
    (originalBankNavCopyMachine field j kind)
    (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit (sourceSlot field)))
def originalBankRowPort (j : Nat) (kind : Destination) : Fin (originalBankRowCap j kind+1) :=
  PSTRTMSeq005.rightLabel (a:=originalBankNavCopyCap j kind) 1
def originalBankRowFee (field : SourceField) (kind : Destination) (j gap : Nat) (first : RecordSpec)
    (records : List RecordSpec) (nxTail dxTail nyTail dyTail a : List Bool) : Nat :=
  navigationFee nxTail dxTail nyTail+
    originalBankCopyFee kind (sourceCost field dxTail nyTail dyTail) j gap first records
      (sourceTail field nxTail dxTail nyTail dyTail) a+2

def originalBankRowTime (field : SourceField) (kind : Destination) (j gap : Nat) (first : RecordSpec)
    (records : List RecordSpec) (nxTail dxTail nyTail dyTail a : List Bool) : Nat :=
  navigationFee nxTail dxTail nyTail+
    originalBankCopyTime kind (sourceCost field dxTail nyTail dyTail) j gap first records
      (sourceTail field nxTail dxTail nyTail dyTail) a+2

theorem original_bank_row_fee_le (field : SourceField) (kind : Destination) (j gap : Nat) (first : RecordSpec)
    (records : List RecordSpec) (nxTail dxTail nyTail dyTail a : List Bool) :
    originalBankRowFee field kind j gap first records nxTail dxTail nyTail dyTail a≤
      originalBankRowTime field kind j gap first records nxTail dxTail nyTail dyTail a := by
  have h := original_bank_copy_fee_le kind (sourceCost field dxTail nyTail dyTail) j gap first records
    (sourceTail field nxTail dxTail nyTail dyTail) a
  unfold originalBankRowFee originalBankRowTime
  omega

theorem original_bank_row_bounded (memory : Nat) (field : SourceField) (j : Nat) (kind : Destination)
    (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail a : List Bool) (gap : Nat) :
    BoundedRun (originalBankRowMachine memory field j kind)
      (PA17TMRatArithmeticMul047.sourceHeaderTape sx counter nxTail dxTail nyTail dyTail
        (bankTail (first::records) (copyWork kind gap a []))) (originalBankRowPort j kind)
      (Tape.mk₂ (destinationLeft kind
        (bankLeftAny false (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) (first::records)) a gap true)
        (PA17TMRatArithmeticCopy006.workspace
          (memory.testBit (sourceSlot field)::sourceTail field nxTail dxTail nyTail dyTail)))
      (originalBankRowFee field kind j gap first records nxTail dxTail nyTail dyTail a) := by
  let tail := sourceTail field nxTail dxTail nyTail dyTail
  let outputLeft := destinationLeft kind
    (bankLeftAny false (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) (first::records)) a gap true
  have hn := PA17TMRatArithmeticMul047.source_navigation_with_suffix_bounded field sx counter
    nxTail dxTail nyTail dyTail (bankTail (first::records) (copyWork kind gap a []))
  have hc := original_bank_copy_bounded (sourceRoute field) (sourceContext field dxTail nyTail dyTail)
    (sourceFinish field dxTail nyTail dyTail) (sourceCost field dxTail nyTail dyTail)
    (source_correct field dxTail nyTail dyTail) j first records hj kind
    (sourceArchive field sx counter nxTail dxTail nyTail) tail a gap
  rw [source_finish_global] at hc
  have hw : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit (sourceSlot field)))
      (Tape.mk₂ outputLeft (PA17TMRatArithmeticCopy006.workspace (false::tail))) 1
      (Tape.mk₂ outputLeft
        (PA17TMRatArithmeticCopy006.workspace (memory.testBit (sourceSlot field)::tail))) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false (memory.testBit (sourceSlot field)) outputLeft
        (true::(PSTRTMIncrement009.blocks tail++[false,false])),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom false (memory.testBit (sourceSlot field)) outputLeft
        (true::(PSTRTMIncrement009.blocks tail++[false,false])),by rfl⟩
  have result := (hn.seq hc).seq hw
  simpa only [originalBankRowMachine,originalBankNavCopyMachine,originalBankRowPort,
    originalBankRowCap,originalBankNavCopyCap,originalBankRowFee,tail,outputLeft] using result

def originalBankRows (p : Nat) (field : SourceField) (j : Nat) (kind : Destination) :
    Fin (p+1) → Machine (originalBankRowCap j kind) := fun memory => originalBankRowMachine memory.val field j kind
def originalBankPorts (p j : Nat) (kind : Destination) :
    Fin (p+1) → Fin (originalBankRowCap j kind+1) →
      Option (Fin (p+1) × Fin (originalBankRowCap j kind+1)) := fun _ _ => none
def originalBankLoader (p : Nat) (field : SourceField) (j : Nat) (kind : Destination) :
    Machine (totalStates p (originalBankRowCap j kind)) :=
  blockMachine (originalBankRows p field j kind) (originalBankPorts p j kind)

/-- Every old32/64carry bit is retained. The old original footer is
physically FALSE at the output, all source clamps/flags and existing
records/A are unchanged; the only restored datum is DEST firstDATA. -/
theorem original_bank_loader_contract (p : Nat) (memory : Fin (p+1)) (field : SourceField)
    (j : Nat) (kind : Destination) (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail a : List Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalBankLoader p field j kind)
      (blockCfg memory (⟨0,PA17TMRatArithmeticMul047.sourceHeaderTape sx counter nxTail dxTail nyTail dyTail
        (bankTail (first::records) (copyWork kind gap a []))⟩ : MachineState (originalBankRowCap j kind))) trace
      (blockCfg memory (⟨originalBankRowPort j kind,Tape.mk₂
        (destinationLeft kind
          (bankLeftAny false (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) (first::records)) a gap true)
        (PA17TMRatArithmeticCopy006.workspace
          (memory.val.testBit (sourceSlot field)::sourceTail field nxTail dxTail nyTail dyTail))⟩ :
          MachineState (originalBankRowCap j kind))) ∧
      trace.length≤originalBankRowFee field kind j gap first records nxTail dxTail nyTail dyTail a ∧
      ∀ k, visitedSpace (originalBankLoader p field j kind) inputLength (trace.take k) ≤
        inputLength+2*originalBankRowFee field kind j gap first records nxTail dxTail nyTail dyTail a+1 := by
  obtain ⟨trace,hr,hl⟩ := original_bank_row_bounded memory.val field j kind first records hj sx counter
    nxTail dxTail nyTail dyTail a gap
  have hb := block_runsFrom (originalBankRows p field j kind) (originalBankPorts p j kind) memory _ _ trace hr rfl
  refine ⟨trace.map (blockCfg memory),hb,?_,?_⟩
  · simpa only [List.length_map] using hl
  · intro k
    have hs := PSTRTMTrace002.visitedSpace_le (originalBankLoader p field j kind) inputLength
      ((trace.map (blockCfg memory)).take k)
    have hk : ((trace.map (blockCfg memory)).take k).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

theorem original_bank_carry_preserved (p : Nat) (memory : Fin (p+1)) (j : Nat) (kind : Destination) :
    phaseOf (label memory (originalBankRowPort j kind))=memory := phaseOf_label _ _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
