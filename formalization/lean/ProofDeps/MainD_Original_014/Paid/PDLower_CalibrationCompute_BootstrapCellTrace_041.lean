module

public import Paid.PDLower_CalibrationCompute_BootstrapCell_040
public import Paid.PDMenu_ComputeFrame_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem bootstrapCopy_straight : PDMenu.ComputeFrame.StraightCode bootstrapCopyBody := by
  intro instruction member
  simp only [bootstrapCopyBody,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq|eq|eq|eq|eq|eq <;> subst instruction <;> trivial

theorem bootstrapCopy_trace (input : List Cell) (before : State) (source destination remaining : ℕ) (value : Cell)
    (position : before.pc=mainStart+13)
    (old : before.register .old=.natural source) (address : before.register .address=.natural destination)
    (flag : before.register .flag=.natural remaining) (data : input[source]?=some value) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some {bootstrapCopyResult before source destination remaining value with pc:=mainStart+12} ∧
      trace.IsChain (fun first later => step calibrate input first=some later) ∧ time calibrate trace≤120 := by
  let middle := bootstrapCopyResult before source destination remaining value
  let after : State := {middle with pc:=mainStart+12}
  have fetch : PDMenu.ComputeFrame.FetchesCode calibrate before.pc bootstrapCopyBody := by
    intro offset inside
    rw [position]
    exact calibrate_bootstrapCopy_fetch offset inside
  obtain ⟨body,head,last,length,chain,_prefix⟩ :=
    PDMenu.ComputeFrame.linearExecute_trace calibrate input bootstrapCopyBody bootstrapCopy_straight before middle fetch
      (bootstrapCopy_execute input before source destination remaining value old address flag data)
  have jumped : step calibrate input middle=some after := by
    have pc : middle.pc=mainStart+19 := by dsimp [middle,bootstrapCopyResult]; omega
    have fetched : calibrate[middle.pc]?=some (.jump (mainStart+12)) := by
      rw [pc,calibrate_bootstrap_fetch]
      rfl
    simp only [step,fetched,Instruction.execute]
    rfl
  have actual := PDMenu.ComputeFrame.chain_append_control calibrate input body middle after chain last jumped
  refine ⟨body++[after],?_,?_,actual.1,?_⟩
  · cases body with
    | nil => cases head
    | cons first rest => exact head
  · simp only [List.getLast?_append_cons,List.getLast?_singleton,after,middle]
  · have cost := PDMenu.ComputeFrame.time_le_length calibrate body
    have size : body.length=7 := length
    exact actual.2.trans (by omega)

end PDLower.CalibrationCompute
