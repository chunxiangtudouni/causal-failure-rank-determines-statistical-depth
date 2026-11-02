module
public import Structure.PA17_TM_RatArithmetic_PairInput_050a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticMul047
attribute [local implicit_reducible] sharedLoopCap sharedBeforeCap sharedCopyCap

theorem globalSourceLeft_footer (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) :
    globalSourceLeft sx counter nxTail dxTail nyTail dyTail=
      PA17TMRatArithmeticReturnHome037.footerLeft sx counter
        (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) := rfl

theorem sourceBank_widthBank (nxTail dxTail nyTail dyTail suffix : List Bool) :
    sourceBank nxTail dxTail nyTail dyTail suffix=
      bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) suffix := by
  simp only [sourceBank,fieldWord,PA17TMRatArithmeticFarLoad031.nxContext,
    PA17TMRatArithmeticFarLoad031.dxContext,bank,nxStream,List.append_assoc,
    List.cons_append,List.nil_append]

/-- This equality uses only a descriptor FALSE at the genuine right blank
tail. The A END and the physical future B first DATA stay at their cells. -/
theorem shared_empty_tape (sx : Bool) (counter nxTail dxTail nyTail dyTail first : List Bool) (gap : Nat) :
    Tape.mk₂ counter (prefixRight sx (bank (false::nxTail) (false::dxTail)
      (false::nyTail) (false::dyTail) (PA17TMRatArithmeticFarLoad031.workSuffix gap first)))=
      sourceHeaderTape sx counter nxTail dxTail nyTail dyTail
        (PA17TMRatArithmeticPairExcursion041.workSuffix gap first []) := by
  rw [←PA17TMRatArithmeticPairEncode017.tape_trailing_false counter
    (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
      (PA17TMRatArithmeticFarLoad031.workSuffix gap first)))]
  congr 1
  simp only [sourceBank_widthBank,prefixRight,bank,nxStream,
    PA17TMRatArithmeticFarLoad031.workSuffix,PA17TMRatArithmeticPairExcursion041.workSuffix,
    PA17TMRatArithmeticCopy006.workspace,PSTRTMIncrement009.blocks,List.flatMap_nil,
    List.append_assoc,List.cons_append,List.nil_append]

theorem firstRow_bounded (field : SourceField) (memory : Nat) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    BoundedRun (firstRow field memory) (headerTape sx counter nxTail dxTail nyTail dyTail gap) 478
      (sourceHeaderTape sx counter nxTail dxTail nyTail dyTail
        (PA17TMRatArithmeticPairExcursion041.workSuffix gap
          (restoredDigits field memory nxTail dxTail nyTail dyTail) []))
      (firstFee field nxTail dxTail nyTail dyTail gap) := by
  have load := restoreRow_bounded (sourceNavigation field) (sourceRoute field)
    (sourceContext field dxTail nyTail dyTail) (sourceFinish field dxTail nyTail dyTail)
    (sourceCost field dxTail nyTail dyTail) (source_correct field dxTail nyTail dyTail)
    (sourceSlot field) memory (headerTape sx counter nxTail dxTail nyTail dyTail gap)
    (sourcePort field) (navigationFee nxTail dxTail nyTail)
    (sourceArchive field sx counter nxTail dxTail nyTail)
    (sourceTail field nxTail dxTail nyTail dyTail) gap
    (source_navigation_bounded field sx counter nxTail dxTail nyTail dyTail gap)
  rw [source_finish_global] at load
  have home := PA17TMRatArithmeticWorkHome046.original_work_home_bounded sx counter
    (false::nxTail) (false::dxTail) (false::nyTail) dyTail gap
    (PA17TMRatArithmeticCopy006.workspace (restoredDigits field memory nxTail dxTail nyTail dyTail))
  rw [←globalSourceLeft_footer] at home
  change BoundedRun PA17TMRatArithmeticWorkHome046.originalHomeMachine
    (Tape.mk₂ (PA17TMRatArithmeticFarLoad031.destinationLeft gap
      (globalSourceLeft sx counter nxTail dxTail nyTail dyTail))
      (PA17TMRatArithmeticCopy006.workspace (restoredDigits field memory nxTail dxTail nyTail dyTail))) 42
    (Tape.mk₂ counter (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
      (PA17TMRatArithmeticFarLoad031.workSuffix gap (restoredDigits field memory nxTail dxTail nyTail dyTail)))))
    (gap+2*PA17TMRatArithmeticWidth018.bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)+41) at home
  rw [shared_empty_tape] at home
  have combined := load.seq home
  simpa [firstRow,firstFee,PA17TMRatArithmeticFarLoad031.destinationLeft,restoredDigits,
    PA17TMRatArithmeticFarLoad031.bankWidth,PA17TMRatArithmeticWidth018.bankWidth,
    PSTRTMSeq005.rightLabel] using combined

theorem secondRow_bounded (field : SourceField) (memory : Nat) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail first : List Bool) (gap : Nat) :
    BoundedRun (secondRow field memory)
      (sourceHeaderTape sx counter nxTail dxTail nyTail dyTail
        (PA17TMRatArithmeticPairExcursion041.workSuffix gap first [])) 482
      (Tape.mk₂
        (PA17TMRatArithmeticPairExcursion041.destinationLeft (secondRoute field) gap
          (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) first)
        (PA17TMRatArithmeticCopy006.workspace (restoredDigits field memory nxTail dxTail nyTail dyTail)))
      (secondFee field nxTail dxTail nyTail dyTail first gap) := by
  have nav := source_navigation_with_suffix_bounded field sx counter nxTail dxTail nyTail dyTail
    (PA17TMRatArithmeticPairExcursion041.workSuffix gap first [])
  have copy := shared_copy_bounded (secondRoute field) (sourceContext field dxTail nyTail dyTail)
    (sourceFinish field dxTail nyTail dyTail) (sourceCost field dxTail nyTail dyTail) gap
    (sourceArchive field sx counter nxTail dxTail nyTail)
    (false::sourceTail field nxTail dxTail nyTail dyTail) first
    (original_source_route_correct field dxTail nyTail dyTail) rfl
  rw [source_finish_global] at copy
  have inputEq : PA17TMRatArithmeticPairExcursion041.sourceWord (secondRoute field)
      (sourceContext field dxTail nyTail dyTail) (false::sourceTail field nxTail dxTail nyTail dyTail)
      (PA17TMRatArithmeticPairExcursion041.workSuffix gap first [])=
      fieldWord (sourceContext field dxTail nyTail dyTail)
        (false::sourceTail field nxTail dxTail nyTail dyTail)
        (PA17TMRatArithmeticPairExcursion041.workSuffix gap first []) := rfl
  rw [inputEq] at copy
  let left := PA17TMRatArithmeticPairExcursion041.destinationLeft (secondRoute field) gap
    (globalSourceLeft sx counter nxTail dxTail nyTail dyTail) first
  have write : BoundedRun
      (PA17TMRatArithmeticAllocate013.setMarkerMachine (memory.testBit (sourceSlot field)))
      (Tape.mk₂ left (PA17TMRatArithmeticCopy006.workspace
        (false::sourceTail field nxTail dxTail nyTail dyTail))) 1
      (Tape.mk₂ left (PA17TMRatArithmeticCopy006.workspace
        (restoredDigits field memory nxTail dxTail nyTail dyTail))) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false (memory.testBit (sourceSlot field)) left
        (true::(PSTRTMIncrement009.blocks (sourceTail field nxTail dxTail nyTail dyTail)++[false,false])),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom false (memory.testBit (sourceSlot field)) left
        (true::(PSTRTMIncrement009.blocks (sourceTail field nxTail dxTail nyTail dyTail)++[false,false])),by rfl⟩
  have combined := (nav.seq copy).seq write
  change BoundedRun (s:=482) (secondRow field memory) _ (482 : Fin 483) _ _ at combined
  exact combined

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050
