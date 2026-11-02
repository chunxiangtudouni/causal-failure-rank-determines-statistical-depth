module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031d

/-! One fixed read/branch/return loop. The executable finite control reads
each DATA bit and branches to a compiled FALSE/TRUE excursion. Lists and
lengths occur only in the finite actual trace and its specification. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

def readerMachine : Machine 113 := padMachine (by decide : 8≤113) readMarkMachine

def readerPort (bit : Bool) : Fin 114 := if bit then 8 else 5

theorem reader_data_bounded (left : List Bool) (bit : Bool) (suffix : List Bool) :
    BoundedRun readerMachine (Tape.mk₂ left (bit::true::suffix)) (readerPort bit)
      (Tape.mk₂ (false::bit::left) suffix) 5 := by
  have h := pad_runsFrom (by decide : 8≤113) readMarkMachine _ _ _ (readMark_runsFrom left bit suffix)
  refine ⟨(readMarkTrace left bit suffix).map (padCfg (by decide : 8≤113)),?_,?_⟩
  · cases bit <;> exact h
  · rw [List.length_map,readMarkTrace_length]

theorem reader_eof_bounded (left suffix : List Bool) :
    BoundedRun readerMachine (Tape.mk₂ left (false::false::suffix)) 3
      (Tape.mk₂ (false::left) (false::suffix)) 3 := by
  have h := pad_runsFrom (by decide : 8≤113) readMarkMachine _ _ _ (eof_runsFrom left suffix)
  exact ⟨(eofTrace left suffix).map (padCfg (by decide : 8≤113)),h,
    by rw [List.length_map,eofTrace_length]⟩

def loopRows (route : FarRoute) (phase : Fin 3) : Machine 113 :=
  if phase.val=0 then readerMachine else excursionMachine route (phase.val==2)

def loopPorts (phase : Fin 3) (localLabel : Fin 114) : Option (Fin 3 × Fin 114) :=
  if phase.val=0 then
    if localLabel.val=5 then some (1,0)
    else if localLabel.val=8 then some (2,0) else none
  else if localLabel.val=113 then some (0,0) else none

def loopMachine (route : FarRoute) : Machine (totalStates 2 113) := blockMachine (loopRows route) loopPorts

theorem block_zero_three (tape : Tape Bool) :
    blockCfg (p:=2) (s:=113) 0 (⟨3,tape⟩ : MachineState 113)=
      (⟨3,tape⟩ : MachineState (totalStates 2 113)) := by
  have hq : label (p:=2) (s:=113) (0 : Fin 3) (3 : Fin 114)=
      (3 : Fin (totalStates 2 113+1)) := by decide
  change (⟨label (p:=2) (s:=113) 0 3,tape⟩ : MachineState (totalStates 2 113))=⟨3,tape⟩
  rw [hq]

def passedLeft : List Bool → List Bool → List Bool
  | left, [] => left
  | left, bit::later => passedLeft (true::bit::left) later

def loopFee (cost gap : Nat) : List Bool → List Bool → Nat
  | _, [] => 3
  | copied, bit::later => 5+(4*later.length+2*cost+2*gap+4*copied.length+32)+
      loopFee cost gap (copied++[bit]) later

theorem context_false (context suffix : List Bool) (h : context.headD false=false) :
    context++false::suffix=false::(context++false::suffix).tail := by
  cases context with
  | nil => rfl
  | cons bit later =>
    have hb : bit=false := h
    subst bit
    rfl

theorem loop_bounded (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost)
    (digits left copied : List Bool) (gap : Nat) :
    BoundedRun (loopMachine route)
      (Tape.mk₂ left (fieldWord context digits (workSuffix gap copied))) 3
      (Tape.mk₂ (false::passedLeft left digits)
        (context++false::workSuffix gap (copied++digits)))
      (loopFee cost gap copied digits) := by
  induction digits generalizing left copied with
  | nil =>
    have hc := context_false context (workSuffix gap copied) routes.end_false
    have hr := reader_eof_bounded left ((context++false::workSuffix gap copied).tail)
    rw [← hc] at hr
    obtain ⟨trace,hr,hl⟩ := hr
    have hb := block_runsFrom (loopRows route) loopPorts 0 _ _ trace hr (by rfl)
    refine ⟨trace.map (blockCfg (p:=2) (s:=113) (0 : Fin 3)),?_,?_⟩
    · simpa only [blockCfg_zero,block_zero_three,loopMachine,fieldWord,PSTRTMIncrement009.blocks,List.flatMap_nil,
        List.nil_append,List.append_nil,passedLeft] using hb
    · change (trace.map (blockCfg (p:=2) (s:=113) (0 : Fin 3))).length≤3
      simpa only [List.length_map] using hl
  | cons bit later ih =>
    let suffix := fieldWord context later (workSuffix gap copied)
    obtain ⟨tr,hr,hlr⟩ := reader_data_bounded left bit suffix
    have hre : PSTRTMSeq005.RunsFrom (loopRows route 0) ⟨0,Tape.mk₂ left (bit::true::suffix)⟩
        tr ⟨readerPort bit,Tape.mk₂ (false::bit::left) suffix⟩ := hr
    obtain ⟨te,he,hle⟩ := excursion_bounded route context finish cost routes left later copied bit gap
    have hee : PSTRTMSeq005.RunsFrom (loopRows route (PA17TMRatArithmeticBookmark014.readPort bit))
        ⟨0,Tape.mk₂ (false::bit::left) suffix⟩ te
        ⟨113,Tape.mk₂ (true::bit::left) (fieldWord context later (workSuffix gap (copied++[bit])))⟩ := by
      cases bit <;> exact he
    obtain ⟨ti,hi,hli⟩ := ih (true::bit::left) (copied++[bit])
    have hs := segment_append (loopMachine route) _ _ _ _ _ _
      (block_segment (loopRows route) loopPorts 0 _ _ tr hre)
      (block_segment (loopRows route) loopPorts (PA17TMRatArithmeticBookmark014.readPort bit) _ _ te hee)
      (block_transfer (loopRows route) loopPorts 0 _
        (PA17TMRatArithmeticBookmark014.readPort bit,0) hre.2.2.2 (by cases bit <;> rfl))
    have hs' := segment_append (loopMachine route) _ _ _ _ _ _ hs
      ⟨hi.1,hi.2.1,hi.2.2.1⟩
      (block_transfer (loopRows route) loopPorts (PA17TMRatArithmeticBookmark014.readPort bit) _
        (0,0) hee.2.2.2 (by cases bit <;> rfl))
    refine ⟨(tr.map (blockCfg (p:=2) (s:=113) (0 : Fin 3))++
      te.map (blockCfg (p:=2) (s:=113) (PA17TMRatArithmeticBookmark014.readPort bit)))++ti,?_,?_⟩
    · have h := segment_runsFrom _ _ _ _ hs' hi.2.2.2
      simpa only [blockCfg_zero,suffix,fieldWord,PSTRTMIncrement009.blocks,List.flatMap_cons,
        List.cons_append,List.nil_append,List.append_assoc,List.singleton_append,passedLeft] using h
    · simp only [List.length_append,List.length_map,loopFee]
      omega

theorem passedLeft_finish (route : FarRoute) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : RouteCorrect route context finish cost) (left digits : List Bool) :
    finish (passedLeft left digits) []=finish left digits := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    rw [passedLeft,ih,routes.finish_cons]

theorem loopFee_le (cost gap : Nat) (copied digits : List Bool) :
    loopFee cost gap copied digits ≤
      digits.length*(4*(digits.length+copied.length)+2*cost+2*gap+37)+3 := by
  induction digits generalizing copied with
  | nil => simp [loopFee]
  | cons bit later ih =>
    have hi := ih (copied++[bit])
    simp only [List.length_append,List.length_singleton] at hi
    simp only [loopFee,List.length_cons]
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
