module

public import Paid.RootD27Core_RuntimeSolverCall_041
public import Paid.RootD27Core_HeapCopy_034
public import Paid.PDCompute_SolverHeaderResources_140
public import Paid.PDCompute_Pack_BitBudget_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver
open PaperProofs.Paid.Parameters
open RootD27.Bits

/-- A bound on actual incoming live cells/registers plus the fixed
header producer. It is a proof bound, never a runtime input or fuel. -/
noncomputable def coreHeaderBudget (before : State) : ℕ :=
  PDCompute.Pack.initialBits before+natBits (before.pc+39)+16

/-- Real fresh13, the original37-op header producer, then real fresh0.
All48 core header cells are genuinely live; the original prepared13 is
preserved. Old scratch and output are retained and counted throughout. -/
theorem core_header_initialize_actual (P : Parameters) (fee : ℚ) (input : List Cell)
    (program : Program) (before : State)
    (prepared : HeapList before 0 (preparedInput P fee))
    (startFetch : program[before.pc]?=some (.constant .fresh (.natural 13)))
    (prologueFetch : FetchesCode program (before.pc+1) solverPrologue)
    (leadFetch : FetchesCode program (before.pc+17) RootD27.Endpoint.paddingLeadCode)
    (loopFetch : FetchesCode program (before.pc+20) (baseRowCode (before.pc+20)))
    (endFetch : program[before.pc+38]?=some (.constant .fresh (.natural 0))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤2520 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ HeapList after 0 (preparedInput P fee) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+39 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+48 ∧
      (∀ state∈trace,RegionMemory before state (cellRegion 13 48) ∧
        SafeBits state (coreHeaderBudget before) ∧ before.pc≤state.pc ∧ state.pc≤before.pc+39) := by
  let budget:=coreHeaderBudget before
  let entered : State:={(before.set .fresh (.natural 13)) with pc:=before.pc+1}
  have initialSafe : SafeBits before budget :=
    PDCompute.Pack.safeBits_mono (PDCompute.Pack.initialBits_safe before) (by unfold budget coreHeaderBudget;omega)
  have small13 : (.natural 13 : Cell).bits≤budget := by
    have small : (.natural 13 : Cell).bits≤16:=by decide
    unfold budget coreHeaderBudget
    omega
  have small0 : (.natural 0 : Cell).bits≤budget := by
    have small : (.natural 0 : Cell).bits≤16:=by decide
    unfold budget coreHeaderBudget
    omega
  have addressBits : 1+natBits (13+headerWords)≤budget := by
    have small : 1+natBits (13+headerWords)≤16:=by decide
    unfold budget coreHeaderBudget
    omega
  have zeroBits : (.rational 0 : Cell).bits≤budget := by
    have small : (.rational 0 : Cell).bits≤16:=by decide
    unfold budget coreHeaderBudget
    omega
  have pcBits : natBits (before.pc+39)≤budget:=by unfold budget coreHeaderBudget;omega
  have entryPC : natBits (before.pc+1)≤budget :=
    (PDROC.DataBits.natBits_mono (by omega : before.pc+1≤before.pc+39)).trans pcBits
  have entrySafe : SafeBits entered budget:=(initialSafe.set .fresh (.natural 13) small13).withPC _ entryPC
  have start : step program input before=some entered := by
    simp only [step,startFetch]
    rfl
  have startChain : [before,entered].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_pair.mpr start
  have startTime : time program [before,entered]≤30:=time_le_length program [before,entered]
  have leadLocated : FetchesCode program ((before.pc+1)+16) RootD27.Endpoint.paddingLeadCode := by
    simpa only [Nat.add_assoc] using leadFetch
  have loopLocated : FetchesCode program ((before.pc+1)+19) (baseRowCode ((before.pc+1)+19)) := by
    simpa only [Nat.add_assoc] using loopFetch
  have headerPC : natBits ((before.pc+1)+37)≤budget :=
    (PDROC.DataBits.natBits_mono (by omega : (before.pc+1)+37≤before.pc+39)).trans pcBits
  obtain ⟨body,middle,bh,bl,bc,bt,header,_fresh,middlePC,_frame,_output,resources,_proper⟩:=
    solver_header_initialization_resources program input (before.pc+1) entered 13 0 0 budget
      rfl rfl entrySafe addressBits zeroBits headerPC prologueFetch leadLocated loopLocated
  have joined:=joinTrace_spec program input [before,entered] body before entered middle 30 2460
    rfl rfl bh bl startChain bc startTime bt
  have middleMemory : RegionMemory before middle (cellRegion 13 48):=
    (resources middle (List.mem_of_getLast? bl)).1
  have middleSafe : SafeBits middle budget:=(resources middle (List.mem_of_getLast? bl)).2.1
  let after : State:={(middle.set .fresh (.natural 0)) with pc:=middle.pc+1}
  have endLocated : program[middle.pc]?=some (.constant .fresh (.natural 0)) := by
    have pc : middle.pc=before.pc+38:=by omega
    rw [pc]
    exact endFetch
  have finish : step program input middle=some after := by
    simp only [step,endLocated]
    rfl
  have afterPC : after.pc=before.pc+39:=by change middle.pc+1=before.pc+39;omega
  have afterSafe : SafeBits after budget := by
    apply (middleSafe.set .fresh (.natural 0) small0).withPC
    change natBits after.pc≤budget
    rw [afterPC]
    exact pcBits
  have allMemory : ∀ state∈joinTrace [before,entered] body,
      RegionMemory before state (cellRegion 13 48) ∧ SafeBits state budget ∧
        before.pc≤state.pc ∧ state.pc≤before.pc+39 := by
    intro state member
    rcases joinTrace_member member with initialMember|bodyMember
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at initialMember
      rcases initialMember with same|same
      · subst state
        exact ⟨.refl before _,initialSafe,by omega⟩
      · subst state
        exact ⟨.refl before _,entrySafe,by change before.pc≤before.pc+1 ∧ before.pc+1≤before.pc+39;omega⟩
    · have info:=resources state bodyMember
      exact ⟨info.1,info.2.1,by omega⟩
  have finalMemory : RegionMemory before after (cellRegion 13 48):=middleMemory
  have retained : HeapList after 0 (preparedInput P fee) := by
    apply finalMemory.heapList prepared
    intro offset inside
    change offset<13 at inside
    rw [mem_cellRegion_iff]
    omega
  have coreHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    refine ⟨?_,by simp only [Nat.zero_add]⟩
    simp only [Nat.zero_add]
    by_cases old : slot<13
    · simpa only [Nat.zero_add] using retained.1 slot (by change slot<13;exact old)
    · have localSlot : slot-13<headerWords:=by unfold headerWords at *;omega
      have live:=(header (slot-13) localSlot).1
      have address : 13+(slot-13)=slot:=by omega
      rw [address] at live
      exact live
  have appended:=chain_append_control program input (joinTrace [before,entered] body) middle after
    joined.2.2.1 joined.2.1 finish
  have nonempty : joinTrace [before,entered] body≠[] := by
    intro empty
    have head:=joined.1
    simp only [empty,List.head?_nil,reduceCtorEq] at head
  have all : ∀ state∈joinTrace [before,entered] body++[after],
      RegionMemory before state (cellRegion 13 48) ∧ SafeBits state budget ∧
        before.pc≤state.pc ∧ state.pc≤before.pc+39 := by
    intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact allMemory state earlier
    · have same : state=after:=List.mem_singleton.mp last
      subst state
      exact ⟨finalMemory,afterSafe,by rw [afterPC];omega⟩
  refine ⟨joinTrace [before,entered] body++[after],after,?_,by simp,appended.1,
    appended.2.trans (by omega),coreHeader,retained,rfl,afterPC,finalMemory.2.2.2,?_,all⟩
  · simpa only [List.head?_append_of_ne_nil _ nonempty] using joined.1
  · apply PDLower.CalibrationCompute.peakCells_le_of_forall
    intro state member
    exact heapCopy_region_cells 13 48 (all state member).1

end RootD27.Core
