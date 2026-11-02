module

public import Paid.PDCompute_SolverPrologueResources_127
public import Paid.RootD27Endpoint_Padding_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

/-- SAME original four-op padding setup, including its shared flag1
opcode. Every prefix keeps heap/live/output and the SAME bit budget. -/
theorem paddingLead_prefix_resources (input : List Cell) (before after : State) (base budget count : ℕ)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (pcBits : natBits (before.pc+4) ≤ budget)
    (bound : count ≤ 4) (executed : linearExecute input (RootD27.Endpoint.paddingLeadCode.take count) before=some after) :
    RegionMemory before after (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits after budget := by
  have localAddress : 1+natBits (base+6) ≤ budget := by
    have mono:=natBits_mono (by unfold headerWords; omega : base+6 ≤ base+headerWords)
    omega
  have counter3 : natBits (before.pc+3) ≤ budget := (natBits_mono (by omega : before.pc+3 ≤ before.pc+4)).trans pcBits
  have sevenBits : (.natural 7 : Cell).bits ≤ budget := by
    have mono:=natBits_mono (by unfold headerWords; omega : 7 ≤ base+headerWords)
    change 1+natBits 7 ≤ budget
    omega
  have oneBits : (.natural 1 : Cell).bits ≤ budget := by
    have mono:=natBits_mono (by unfold headerWords; omega : 1 ≤ base+headerWords)
    change 1+natBits 1 ≤ budget
    omega
  have firstSafe:=RootD27.Bits.addressOne_safe before base 6 budget safe localAddress counter3
  have secondSafe:=RootD27.Bits.addressTwo_safe before base 6 budget safe localAddress counter3
  have thirdSafe:=(secondSafe.withPC (before.pc+3) counter3).set .index (.natural 7) sevenBits
  have fourthSafe:=(thirdSafe.withPC (before.pc+4) pcBits).set .flag (.natural 1) oneBits
  interval_cases count <;>
    simp [RootD27.Endpoint.paddingLeadCode,RootD27.Endpoint.paddingSetup,linearExecute,Instruction.execute,State.set,
      NatOp.eval,Cell.nat?,fresh,Nat.add_assoc] at executed <;> subst after
  · exact ⟨RegionMemory.refl before _,safe⟩
  · exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,by simpa [RootD27.Bits.addressOne,State.set] using firstSafe⟩
  · exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,by simpa [RootD27.Bits.addressTwo,RootD27.Bits.addressOne,State.set] using secondSafe⟩
  · exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,by simpa [RootD27.Bits.addressTwo,RootD27.Bits.addressOne,State.set] using thirdSafe⟩
  · exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,by simpa [RootD27.Bits.addressTwo,RootD27.Bits.addressOne,State.set] using fourthSafe⟩

theorem paddingLead_trace_resources (program : Program) (input : List Cell) (before : State) (base budget : ℕ)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (pcBits : natBits (before.pc+4) ≤ budget)
    (fetch : FetchesCode program before.pc RootD27.Endpoint.paddingLeadCode) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (RootD27.Endpoint.paddingLeadResult before base) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 75 ∧
      ∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits state budget ∧
        before.pc ≤ state.pc ∧ state.pc ≤ before.pc+4 := by
  have execute:=RootD27.Endpoint.paddingLead_execute input before base fresh
  obtain ⟨trace,head,last,chain,timeBound,prefixes,pcRange⟩:=linearExecute_trace_closedPC program input RootD27.Endpoint.paddingLeadCode
    RootD27.Endpoint.paddingLead_straight before _ fetch execute
  refine ⟨trace,head,last,chain,timeBound,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (RootD27.Endpoint.paddingLeadResult before base) (by rw [last]; simp)
  have represented : ∃ count ≤ 4,linearExecute input (RootD27.Endpoint.paddingLeadCode.take count) before=some state := by
    rw [← split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,run⟩:=prefixes state proper
      exact ⟨count,Nat.le_of_lt bound,run⟩
    · have same : state=RootD27.Endpoint.paddingLeadResult before base := List.mem_singleton.mp terminal
      subst state
      exact ⟨4,le_refl _,execute⟩
  obtain ⟨count,bound,run⟩:=represented
  have resources:=paddingLead_prefix_resources input before state base budget count fresh safe addressBits pcBits bound run
  exact ⟨resources.1,resources.2,pcRange state member⟩

end PDCompute.Solver
