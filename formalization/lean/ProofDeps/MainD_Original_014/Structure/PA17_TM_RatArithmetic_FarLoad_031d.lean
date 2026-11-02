module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031c

/-! A paid far-field excursion. The route code is fixed independently of
all field widths. Context and finish below describe whole tapes only.
The original following fields are read by the frozen023 routes, never
treated as a zero gap or cleared to manufacture one. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

def appendStartMachine (bit : Bool) : Machine 58 := fun q symbol =>
  if q.val=0 then some
    (PA17TMRatArithmeticBankCopy024.oldLabel (PA17TMRatArithmeticCopy006.workData bit),.write symbol)
  else appendMachine q symbol

def appendStartTrace (bit : Bool) (left copied : List Bool) : List (MachineState 58) :=
  ⟨0,Tape.mk₂ (false::left) (PA17TMRatArithmeticCopy006.workspace copied)⟩ ::
    appendTrace bit left copied

theorem appendStart_bounded (bit : Bool) (left copied : List Bool) :
    BoundedRun (appendStartMachine bit)
      (Tape.mk₂ (false::left) (PA17TMRatArithmeticCopy006.workspace copied)) 36
      (Tape.mk₂ left (false::PA17TMRatArithmeticCopy006.workspace (copied++[bit])))
      (4*copied.length+15) := by
  have hr := append_runsFrom bit left copied
  have he (s : MachineState 58) (hs : s ∈ appendTrace bit left copied) :
      TM0.step (appendStartMachine bit) s = TM0.step appendMachine s := by
    have hb := appendTrace_labels bit left copied s hs
    have hn : s.q.val≠0 := by omega
    cases s with
    | mk q tape => simp only [TM0.step,appendStartMachine,ite_eq_right hn]
  refine ⟨appendStartTrace bit left copied,⟨rfl,?_,?_,?_⟩,?_⟩
  · apply List.IsChain.cons
    · apply List.IsChain.imp_of_mem_imp _ hr.2.1
      intro a b ha _ hab
      rw [he a ha]
      exact hab
    · intro s hs
      rw [hr.1] at hs
      simp only [Option.mem_some_iff] at hs
      subst s
      simp [TM0.step,appendStartMachine,PA17TMRatArithmeticBankCopy024.state,
        PA17TMRatArithmeticCopy006.workData,PA17TMRatArithmeticBankCopy024.oldLabel,
        PSTRTMSeq005.leftLabel,Tape.write_self]
  · change ([(⟨0,Tape.mk₂ (false::left) (PA17TMRatArithmeticCopy006.workspace copied)⟩ : MachineState 58)] ++
      appendTrace bit left copied).getLast? = _
    rw [List.getLast?_append,hr.2.2.1]
    rfl
  · simp [TM0.step,appendStartMachine,appendMachine,Tape.mk₂]
  · rw [appendStartTrace,List.length_cons,appendTrace_length]

/-- Executable route tables and their fixed local HALT ports. -/
structure FarRoute where
  out : Machine 10
  back : Machine 26
  outPort : Fin 11
  backPort : Fin 27

def fieldWord (context digits suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::(context++false::suffix)

/-- This is a trace specification, not an executable width/context input.
`finish` is the actual archive at the original footer after the route. -/
structure RouteCorrect (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat) : Prop where
  end_false : context.headD false=false
  finish_cons : ∀ left bit later, finish (true::bit::left) later=finish left (bit::later)
  out_run : ∀ left later suffix,
    BoundedRun route.out (Tape.mk₂ left (fieldWord context later suffix)) route.outPort
      (Tape.mk₂ (finish left later) (false::suffix)) (2*later.length+cost)
  back_run : ∀ archive later suffix,
    BoundedRun route.back (Tape.mk₂ (finish (false::archive) later) (false::suffix)) route.backPort
      (Tape.mk₂ (false::archive) (fieldWord context later suffix)) (2*later.length+cost)

def workSuffix (gap : Nat) (copied : List Bool) : List Bool :=
  List.replicate gap false++true::false::PA17TMRatArithmeticCopy006.workspace copied

def outSetMachine (route : FarRoute) : Machine 12 :=
  PSTRTMSeq005.seqMachine route.out (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
def outDestMachine (route : FarRoute) : Machine 17 :=
  PSTRTMSeq005.seqMachine (outSetMachine route) toDestMachine
def outAppendMachine (route : FarRoute) (bit : Bool) : Machine 76 :=
  PSTRTMSeq005.seqMachine (outDestMachine route) (appendStartMachine bit)
def outBackMachine (route : FarRoute) (bit : Bool) : Machine 80 :=
  PSTRTMSeq005.seqMachine (outAppendMachine route bit) backFromGuardMachine
def outClearMachine (route : FarRoute) (bit : Bool) : Machine 82 :=
  PSTRTMSeq005.seqMachine (outBackMachine route bit) (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def outReturnMachine (route : FarRoute) (bit : Bool) : Machine 109 :=
  PSTRTMSeq005.seqMachine (outClearMachine route bit) route.back
def excursionMachine (route : FarRoute) (bit : Bool) : Machine 113 :=
  PSTRTMSeq005.seqMachine (outReturnMachine route bit) PA17TMRatArithmeticAllocatePass023.restoreBackMachine

theorem excursion_bounded (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost)
    (left later copied : List Bool) (bit : Bool) (gap : Nat) :
    BoundedRun (excursionMachine route bit)
      (Tape.mk₂ (false::bit::left) (fieldWord context later (workSuffix gap copied))) 113
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

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
