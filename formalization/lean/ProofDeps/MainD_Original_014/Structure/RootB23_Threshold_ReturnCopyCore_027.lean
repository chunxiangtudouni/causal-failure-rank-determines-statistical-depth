module
public import Structure.RootB23_Threshold_ReturnRoute_026
public import Structure.RootB23_Threshold_RoutedLoop_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnCopy
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031

/-! The old RoutedCopy006 interface has capacity100, smaller than this
actual cap-scratch/rat-inverse/B route. These fixed192-row instances reuse
the SAME readMark, appendStart, OWN initializer and physical gap kernels.
Only the control bindings are enlarged; no value enters any code table. -/

theorem out_bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x)
    (left : ℕ) (sourceLeft digits suffix : List Bool) :
    BoundedRun (ReturnRoute.out capped)
      (Tape.mk₂ sourceLeft (RoutedCopy.fieldWord (ReturnRoute.context capped x y q left) digits suffix))
      (ReturnRoute.outPort capped) (Tape.mk₂ (ReturnRoute.finish capped x y q left sourceLeft digits) (false::suffix))
      (2*digits.length+ReturnRoute.cost capped x y q left) := by
  cases capped with
  | false=>exact bounded_pad (by decide : 83≤192) (ReturnRoute.outFalse_bounded x y q nonnegative left sourceLeft digits suffix)
  | true=>exact bounded_pad (by decide : 113≤192) (ReturnRoute.outTrue_bounded x y q nonnegative left sourceLeft digits suffix)

theorem back_bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (left : ℕ) (archive digits suffix : List Bool) :
    BoundedRun (ReturnRoute.back capped)
      (Tape.mk₂ (ReturnRoute.finish capped x y q left (false::archive) digits) (false::suffix))
      (ReturnRoute.backPort capped)
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnRoute.context capped x y q left) digits suffix))
      (2*digits.length+ReturnRoute.cost capped x y q left) := by
  cases capped with
  | false=>
    exact bounded_pad (by decide : 133≤192)
      (ReturnRoute.backFalse_bounded x y q nonnegative qNonnegative left archive digits suffix)
  | true=>exact bounded_pad (by decide : 168≤192) (ReturnRoute.backTrue_bounded x y q nonnegative left archive digits suffix)

def outSetMachine (capped : Bool) : Machine 194 :=
  PSTRTMSeq005.seqMachine (ReturnRoute.out capped) (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
def outDestMachine (capped : Bool) : Machine 199 := PSTRTMSeq005.seqMachine (outSetMachine capped) toDestMachine
def outAppendMachine (capped bit : Bool) : Machine 258 := PSTRTMSeq005.seqMachine (outDestMachine capped) (appendStartMachine bit)
def outBackMachine (capped bit : Bool) : Machine 262 := PSTRTMSeq005.seqMachine (outAppendMachine capped bit) backFromGuardMachine
def outClearMachine (capped bit : Bool) : Machine 264 :=
  PSTRTMSeq005.seqMachine (outBackMachine capped bit) (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def outReturnMachine (capped bit : Bool) : Machine 457 := PSTRTMSeq005.seqMachine (outClearMachine capped bit) (ReturnRoute.back capped)
def excursionMachine (capped bit : Bool) : Machine 461 :=
  PSTRTMSeq005.seqMachine (outReturnMachine capped bit) PA17TMRatArithmeticAllocatePass023.restoreBackMachine

theorem excursion_bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (credit : ℕ) (left later copied : List Bool) (bit : Bool) (gap : ℕ) :
    BoundedRun (excursionMachine capped bit)
      (Tape.mk₂ (false::bit::left)
        (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) later (workSuffix gap copied))) 461
      (Tape.mk₂ (true::bit::left)
        (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) later (workSuffix gap (copied++[bit]))))
      (4*later.length+2*ReturnRoute.cost capped x y q credit+2*gap+4*copied.length+32) := by
  let archive:=ReturnRoute.finish capped x y q credit (false::bit::left) later
  have ho:=out_bounded capped x y q nonnegative credit (false::bit::left) later (workSuffix gap copied)
  have ht : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ archive (false::workSuffix gap copied)) 1
      (Tape.mk₂ archive (true::workSuffix gap copied)) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true archive (workSuffix gap copied),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
  have hd:=toDest_bounded gap archive true (PA17TMRatArithmeticCopy006.workspace copied)
  have ha:=appendStart_bounded bit (true::(List.replicate gap false++true::archive)) copied
  have hb:=backFromGuard_bounded gap archive (PA17TMRatArithmeticCopy006.workspace (copied++[bit]))
  have hf : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
      (Tape.mk₂ archive (true::workSuffix gap (copied++[bit]))) 1
      (Tape.mk₂ archive (false::workSuffix gap (copied++[bit]))) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true false archive (workSuffix gap (copied++[bit])),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
  have hr:=back_bounded capped x y q nonnegative qNonnegative credit (bit::left) later (workSuffix gap (copied++[bit]))
  have hs : BoundedRun PA17TMRatArithmeticAllocatePass023.restoreBackMachine
      (Tape.mk₂ (false::bit::left)
        (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) later (workSuffix gap (copied++[bit])))) 3
      (Tape.mk₂ (true::bit::left)
        (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) later (workSuffix gap (copied++[bit])))) 4 :=
    ⟨PA17TMRatArithmeticAllocatePass023.restoreBackTrace (bit::left) _,
      PA17TMRatArithmeticAllocatePass023.restoreBack_runsFrom _ _,by rfl⟩
  have actual:=((((((ho.seq ht).seq hd).seq ha).seq hb).seq hf).seq hr).seq hs
  exact actual.mono (by omega)

def readerMachine : Machine 461 := padMachine (by decide : 277≤461) RoutedCopy.readerMachine
def readerPort (bit : Bool) : Fin 462 := if bit then 8 else 5
theorem reader_data_bounded (left : List Bool) (bit : Bool) (suffix : List Bool) :
    BoundedRun readerMachine (Tape.mk₂ left (bit::true::suffix)) (readerPort bit)
      (Tape.mk₂ (false::bit::left) suffix) 5 := by
  have actual:=bounded_pad (by decide : 277≤461) (RoutedCopy.reader_data_bounded left bit suffix)
  cases bit <;> exact actual
theorem reader_eof_bounded (left suffix : List Bool) :
    BoundedRun readerMachine (Tape.mk₂ left (false::false::suffix)) 3
      (Tape.mk₂ (false::left) (false::suffix)) 3 :=
  bounded_pad (by decide : 277≤461) (RoutedCopy.reader_eof_bounded left suffix)

end RootB23.Threshold.ReturnCopy
