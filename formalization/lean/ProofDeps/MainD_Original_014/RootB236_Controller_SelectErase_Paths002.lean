module
public import RootB236_Controller_SelectErase_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.SelectErase
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

structure Path (first last : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some first
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  tail : trace.getLast?=some last
  time : trace.length≤budget

namespace Path
variable {a b c : State C} {s t : Nat}
def trans (front : Path a b s) (back : Path b c t) : Path a c (s+t) := by
  have shape : b::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.head
    rw [same];rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head];rfl
  · exact NativeTrace.join_chain _ _ _ front.tail front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.tail).trans (shape.symm ▸ back.tail)
  · have sizes:=congrArg List.length shape
    have h1:=front.time;have h2:=back.time
    simp only [List.length_cons] at sizes
    simp only [List.length_append]
    omega
def weaken (path : Path a b s) (bound : s≤t) : Path a b t :=
  ⟨path.trace,path.head,path.chain,path.tail,path.time.trans bound⟩
end Path

def frame (bg : Stack → List Bool) (candidate tool cursor parked room : List Bool) : Stack → List Bool :=
  bank bg candidate [] tool cursor parked [] room []

theorem archive_state (bg : Stack → List Bool) (candidate tool cursor parked room input backup scratch : List Bool)
    (point : MaskArchive.Label) (memory : Store C) :
    LabelMap.configuration archiveLabels
      (MaskArchive.Public.physicalState 4 8 (frame bg candidate tool cursor parked room) point memory input backup scratch)=
    state bg (archiveLabels point) memory candidate input tool cursor parked backup room scratch := by
  unfold LabelMap.configuration MaskArchive.Public.physicalState MaskArchive.Public.physicalBank state frame bank
  congr 1
  funext slot;fin_cases slot <;> rfl

theorem restore_state (mapping : MaskArchive.Label → Label) (bg : Stack → List Bool)
    (candidate tool cursor parked room input backup scratch : List Bool) (point : MaskArchive.Label) (memory : Store C) :
    LabelMap.configuration mapping
      (MaskArchive.Public.physicalState 8 4 (frame bg candidate tool cursor parked room) point memory input backup scratch)=
    state bg (mapping point) memory candidate backup tool cursor parked input room scratch := by
  unfold LabelMap.configuration MaskArchive.Public.physicalState MaskArchive.Public.physicalBank state frame bank
  congr 1
  funext slot;fin_cases slot <;> rfl

theorem archive_path (bg : Stack → List Bool) (memory : Store C) (eligible remaining old5 : List Bool) :
    Nonempty (Path (initial bg memory eligible remaining old5)
      (state bg (.candidate (.inl 0)) (memory.1,true,true) eligible remaining old5 [] []
        remaining.reverse (ControllerCandidate.unary eligible.length) []) (2*remaining.length+4)) := by
  let oldBg:=frame bg eligible old5 [] [] (ControllerCandidate.unary eligible.length)
  obtain ⟨run,facts,first,last⟩:=MaskArchive.Public.archive4To8_actual (.halt : MaskArchive.Statement C) oldBg memory remaining
  refine ⟨⟨run.map (LabelMap.configuration archiveLabels),?_,?_,?_,?_⟩⟩
  · rw [List.head?_map,first,Option.map_some,archive_state];rfl
  · apply LabelMap.chain_configuration_on archiveLabels (MaskArchive.Public.archive4To8 .halt) source run facts.chain
    intro current member point selected
    exact archive_agrees .halt .halt point (fun same => (facts.proper current member).1 (same ▸ selected))
  · rw [List.getLast?_map,last,Option.map_some,archive_state];rfl
  · rw [List.length_map,facts.count]

theorem candidate_first (bg : Stack → List Bool) (eligible remaining old5 : List Bool) (memory : Store C) :
    LabelMap.configuration candidateLabels
      (ControllerCandidate.inContext memory.1 (ControllerCandidate.andEmbed
        (Bitwise.state (bank bg eligible remaining old5 [] [] remaining.reverse
          (ControllerCandidate.unary eligible.length) []) 0 memory.2 eligible remaining []
            (ControllerCandidate.unary eligible.length) [])))=
      state bg (.candidate (.inl 0)) memory eligible remaining old5 [] [] remaining.reverse
        (ControllerCandidate.unary eligible.length) [] := by
  unfold LabelMap.configuration ControllerCandidate.inContext ContextLift.configuration ControllerCandidate.andEmbed
    Bitwise.state Bitwise.cells state bank
  congr 1
  funext slot;fin_cases slot <;> rfl

theorem candidate_final (bg : Stack → List Bool) (eligible remaining old5 bits tool cursor : List Bool)
    (point : ControllerCandidate.ScanLabel) (memory : Store C) :
    LabelMap.configuration candidateLabels (ControllerCandidate.inContext memory.1
      (ControllerCandidate.scanEmbed (ControllerCandidate.state
        (ControllerCandidate.scanBackground (bank bg eligible remaining old5 [] [] remaining.reverse
          (ControllerCandidate.unary eligible.length) []) eligible.length) point memory.2 bits tool cursor [])))=
      state bg (candidateLabels (.inr point)) memory bits [] tool cursor [] remaining.reverse
        (ControllerCandidate.unary eligible.length) [] := by
  unfold LabelMap.configuration ControllerCandidate.inContext ContextLift.configuration ControllerCandidate.scanEmbed
    ControllerCandidate.state ControllerCandidate.cells ControllerCandidate.scanBackground Bitwise.cells state bank
  congr 1
  funext slot;fin_cases slot <;> rfl

def andBits (eligible remaining : List Bool) : List Bool := Bitwise.outputs false (eligible.zip remaining)

theorem candidate_path (bg : Stack → List Bool) (memory : Store C) (eligible remaining old5 : List Bool)
    (same : eligible.length=remaining.length) :
    ∃ (scanFinal : ControllerCandidate.ScanState) (final : State C),
      ControllerCandidate.Outcome
        (ControllerCandidate.scanBackground (bank bg eligible remaining old5 [] [] remaining.reverse
          (ControllerCandidate.unary eligible.length) []) eligible.length) (andBits eligible remaining) 0 scanFinal ∧
      final=LabelMap.configuration candidateLabels (ControllerCandidate.inContext memory.1 (ControllerCandidate.scanEmbed scanFinal)) ∧
      Nonempty (Path (state bg (.candidate (.inl 0)) memory eligible remaining old5 [] [] remaining.reverse
        (ControllerCandidate.unary eligible.length) []) final (12*(old5.length+eligible.length+1))) := by
  let oldBg:=bank bg eligible remaining old5 [] [] remaining.reverse (ControllerCandidate.unary eligible.length) []
  obtain ⟨run,oldFinal,first,chain,last,time,⟨scanFinal,outcome,returned⟩,_bounds,_counts,_internal,_charge⟩:=
    ControllerCandidate.actual_first_masks memory.1 oldBg memory.2 eligible remaining same rfl
  have active : oldFinal.l≠none := by
    rw [returned]
    rcases outcome with ⟨skip,tail,shape,ended⟩ | ⟨shape,ended⟩ <;> rw [ended] <;>
      simp [ControllerCandidate.inContext,ContextLift.configuration,ControllerCandidate.scanEmbed,
        LabelMap.configuration,ControllerCandidate.state]
  have noFound:=ControllerCandidate.no_early_halt_port (ControllerCandidate.withContext C) (.inr .found) rfl run oldFinal chain last active
  have noEmpty:=ControllerCandidate.no_early_halt_port (ControllerCandidate.withContext C) (.inr .empty) rfl run oldFinal chain last active
  let final:=LabelMap.configuration candidateLabels oldFinal
  refine ⟨scanFinal,final,outcome,congrArg (LabelMap.configuration candidateLabels) returned,⟨?_,?_,?_,?_,?_⟩⟩
  · exact run.map (LabelMap.configuration candidateLabels)
  · rw [List.head?_map,first,Option.map_some,candidate_first]
  · apply LabelMap.chain_configuration_on candidateLabels (ControllerCandidate.withContext C) source run chain
    intro current member point selected
    exact candidate_agrees .halt .halt point (fun same => noFound current member (same ▸ selected))
      (fun same => noEmpty current member (same ▸ selected))
  · rw [List.getLast?_map,last,Option.map_some]
  · simpa only [List.length_map,show oldBg 5=old5 from rfl] using time

theorem restore_found_path (bg : Stack → List Bool) (memory : Store C) (candidate remaining tool cursor room : List Bool) :
    Nonempty (Path (state bg (.restoreFound .boot) memory candidate [] tool cursor [] remaining.reverse room [])
      (state bg (.erase 0) (memory.1,true,true) candidate remaining tool cursor [] remaining.reverse room [])
      (2*remaining.length+4)) := by
  let oldBg:=frame bg candidate tool cursor [] room
  obtain ⟨run,facts,first,last⟩:=MaskArchive.Public.restore8To4_actual (.halt : MaskArchive.Statement C) oldBg memory remaining
  refine ⟨⟨run.map (LabelMap.configuration foundRestoreLabels),?_,?_,?_,?_⟩⟩
  · rw [List.head?_map,first,Option.map_some,restore_state];rfl
  · apply LabelMap.chain_configuration_on foundRestoreLabels (MaskArchive.Public.restore8To4 .halt) source run facts.chain
    intro current member point selected
    exact found_restore_agrees .halt .halt point (fun same => (facts.proper current member).1 (same ▸ selected))
  · rw [List.getLast?_map,last,Option.map_some,restore_state];rfl
  · rw [List.length_map,facts.count,List.length_reverse]

theorem restore_empty_path (bg : Stack → List Bool) (memory : Store C) (remaining cursor room : List Bool) :
    Nonempty (Path (state bg (.restoreEmpty .boot) memory [] [] [] cursor [] remaining.reverse room [])
      (state bg .empty (memory.1,true,true) [] remaining [] cursor [] remaining.reverse room [])
      (2*remaining.length+4)) := by
  let oldBg:=frame bg [] [] cursor [] room
  obtain ⟨run,facts,first,last⟩:=MaskArchive.Public.restore8To4_actual (.halt : MaskArchive.Statement C) oldBg memory remaining
  refine ⟨⟨run.map (LabelMap.configuration emptyRestoreLabels),?_,?_,?_,?_⟩⟩
  · rw [List.head?_map,first,Option.map_some,restore_state];rfl
  · apply LabelMap.chain_configuration_on emptyRestoreLabels (MaskArchive.Public.restore8To4 .halt) source run facts.chain
    intro current member point selected
    exact empty_restore_agrees .halt .halt point (fun same => (facts.proper current member).1 (same ▸ selected))
  · rw [List.getLast?_map,last,Option.map_some,restore_state];rfl
  · rw [List.length_map,facts.count,List.length_reverse]

def eraseMask (mask : List Bool) (tool : Nat) : List Bool := mask.take tool++false::mask.drop (tool+1)

theorem erase_state (bg : Stack → List Bool) (candidate cursor archive room mask tool parked : List Bool)
    (point : ErasePort.Label) (memory : Store C) :
    LabelMap.configuration eraseLabels (ErasePort.state
      (bank bg candidate [] [] cursor [] archive room []) point memory mask tool parked)=
      state bg (eraseLabels point) memory candidate mask tool cursor parked archive room [] := by
  unfold LabelMap.configuration ErasePort.state Erase.cells state bank
  congr 1
  funext slot;fin_cases slot <;> rfl

theorem erase_path (bg : Stack → List Bool) (memory : Store C) (candidate remaining cursor room : List Bool)
    (tool : Nat) (inside : tool<remaining.length) :
    Nonempty (Path (state bg (.erase 0) memory candidate remaining (ControllerCandidate.unary tool) cursor [] remaining.reverse room [])
      (state bg .found (memory.1,false,false) candidate (eraseMask remaining tool)
        (ControllerCandidate.unary tool) cursor [] remaining.reverse room []) (2*tool+3)) := by
  let front:=remaining.take tool
  let suffix:=remaining.drop (tool+1)
  have represented : remaining=front++remaining[tool]::suffix := by
    rw [←List.drop_eq_getElem_cons inside,List.take_append_drop]
  have position : front.length=tool := by rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt inside)]
  let oldBg:=bank bg candidate [] [] cursor [] remaining.reverse room []
  obtain ⟨run,final,facts,_clock,_charge⟩:=ErasePort.Public.actual (.halt : ErasePort.Statement C)
    oldBg memory.1 memory.2.1 memory.2.2 front remaining[tool] suffix
  refine ⟨⟨run.map (LabelMap.configuration eraseLabels),?_,?_,?_,?_⟩⟩
  · rw [List.head?_map,facts.first,Option.map_some,erase_state,position,←represented];rfl
  · apply LabelMap.chain_configuration_on eraseLabels (ErasePort.program .halt) source run facts.chain
    intro current member point selected
    exact erase_agrees .halt .halt point (fun same => facts.no_early current member (same ▸ selected))
  · rw [List.getLast?_map,facts.last,facts.contents,Option.map_some,erase_state,position];rfl
  · rw [List.length_map,facts.time,position]

end RootB236.Controller.SelectErase
