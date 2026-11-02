module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031f

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.RoutedCopy
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031

structure Route where
  out : Machine 100
  back : Machine 100
  outPort : Fin 101
  backPort : Fin 101

def fieldWord (context digits suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::(context++false::suffix)

/-- This is a trace specification, not an executable width/context input.
`finish` is the actual archive at the original footer after the route. -/
structure RouteCorrect (route : Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat) : Prop where
  end_false : context.headD false=false
  finish_cons : ∀ left bit later, finish (true::bit::left) later=finish left (bit::later)
  out_run : ∀ left later suffix,
    BoundedRun route.out (Tape.mk₂ left (fieldWord context later suffix)) route.outPort
      (Tape.mk₂ (finish left later) (false::suffix)) (2*later.length+cost)
  back_run : ∀ archive later suffix,
    BoundedRun route.back (Tape.mk₂ (finish (false::archive) later) (false::suffix)) route.backPort
      (Tape.mk₂ (false::archive) (fieldWord context later suffix)) (2*later.length+cost)

def outSetMachine (route : Route) : Machine 102 :=
  PSTRTMSeq005.seqMachine route.out (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
def outDestMachine (route : Route) : Machine 107 :=
  PSTRTMSeq005.seqMachine (outSetMachine route) toDestMachine
def outAppendMachine (route : Route) (bit : Bool) : Machine 166 :=
  PSTRTMSeq005.seqMachine (outDestMachine route) (appendStartMachine bit)
def outBackMachine (route : Route) (bit : Bool) : Machine 170 :=
  PSTRTMSeq005.seqMachine (outAppendMachine route bit) backFromGuardMachine
def outClearMachine (route : Route) (bit : Bool) : Machine 172 :=
  PSTRTMSeq005.seqMachine (outBackMachine route bit) (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def outReturnMachine (route : Route) (bit : Bool) : Machine 273 :=
  PSTRTMSeq005.seqMachine (outClearMachine route bit) route.back
def excursionMachine (route : Route) (bit : Bool) : Machine 277 :=
  PSTRTMSeq005.seqMachine (outReturnMachine route bit) PA17TMRatArithmeticAllocatePass023.restoreBackMachine

theorem excursion_bounded (route : Route) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost)
    (left later copied : List Bool) (bit : Bool) (gap : Nat) :
    BoundedRun (excursionMachine route bit)
      (Tape.mk₂ (false::bit::left) (fieldWord context later (workSuffix gap copied))) 277
      (Tape.mk₂ (true::bit::left) (fieldWord context later (workSuffix gap (copied++[bit]))))
      (4*later.length+2*cost+2*gap+4*copied.length+32) := by
  let archive := finish (false::bit::left) later
  have ho := routes.out_run (false::bit::left) later (workSuffix gap copied)
  have ht : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ archive (false::workSuffix gap copied)) 1
      (Tape.mk₂ archive (true::workSuffix gap copied)) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace false true archive (workSuffix gap copied),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom false true archive (workSuffix gap copied),by rfl⟩
  have hd := toDest_bounded gap archive true (PA17TMRatArithmeticCopy006.workspace copied)
  have ha := appendStart_bounded bit (true::(List.replicate gap false++true::archive)) copied
  have hb := backFromGuard_bounded gap archive (PA17TMRatArithmeticCopy006.workspace (copied++[bit]))
  have hf : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
      (Tape.mk₂ archive (true::workSuffix gap (copied++[bit]))) 1
      (Tape.mk₂ archive (false::workSuffix gap (copied++[bit]))) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true false archive (workSuffix gap (copied++[bit])),
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom true false archive (workSuffix gap (copied++[bit])),by rfl⟩
  have hr := routes.back_run (bit::left) later (workSuffix gap (copied++[bit]))
  have hs : BoundedRun PA17TMRatArithmeticAllocatePass023.restoreBackMachine
      (Tape.mk₂ (false::bit::left) (fieldWord context later (workSuffix gap (copied++[bit])))) 3
      (Tape.mk₂ (true::bit::left) (fieldWord context later (workSuffix gap (copied++[bit])))) 4 :=
    ⟨PA17TMRatArithmeticAllocatePass023.restoreBackTrace (bit::left)
        (fieldWord context later (workSuffix gap (copied++[bit]))),
      PA17TMRatArithmeticAllocatePass023.restoreBack_runsFrom (bit::left)
        (fieldWord context later (workSuffix gap (copied++[bit]))),by rfl⟩
  have h := ((((((ho.seq ht).seq hd).seq ha).seq hb).seq hf).seq hr).seq hs
  exact h.mono (by omega)


end RootB23.Threshold.RoutedCopy
