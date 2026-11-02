module

public import Paid.PDCompute_SolverPaddingLoop_138
public import Paid.PDCompute_SolverPaddingLead_139
public import Paid.PDCompute_SolverArguments_017
public import Paid.PDCompute_SolverHeaderInit_029

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDMenu.ComputeFrame

/-- The SAME original37-op producer and ONE real witness now carry
functional Header, arbitrary oldlive frame, EVERY-prefix memory/bits,
and proper-prefix PC interval. No prefilling/freshness shortcut. -/
theorem solver_header_initialization_resources (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (base n k budget : ℕ) (hpc : before.pc=origin) (fresh : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+headerWords) ≤ budget)
    (zeroBits : (.rational 0 : Cell).bits ≤ budget) (pcBits : natBits (origin+37) ≤ budget)
    (prologueFetch : FetchesCode program before.pc solverPrologue)
    (leadFetch : FetchesCode program (origin+16) RootD27.Endpoint.paddingLeadCode)
    (loopFetch : FetchesCode program (origin+19) (baseRowCode (origin+19))) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 2460 ∧
      Header after base (initializedHeaderValues (solverPrologueResult before base) base) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+37 ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits state budget ∧
        origin ≤ state.pc ∧ state.pc ≤ origin+37) ∧
      ∀ state ∈ trace.dropLast,origin ≤ state.pc ∧ state.pc < origin+37 := by
  let middle:=solverPrologueResult before base
  let started:=RootD27.Endpoint.paddingLeadResult middle base
  let after:=baseRowLoopResult (origin+19) 7 started (base+6)
  have prologuePC : natBits (before.pc+16) ≤ budget := (natBits_mono (by omega : before.pc+16 ≤ origin+37)).trans pcBits
  obtain ⟨prologue,prologueHead,prologueLast,prologueChain,prologueTime,prologueResources⟩:=
    solverPrologue_trace_resources program input before base budget fresh safe addressBits prologuePC prologueFetch
  have middleFresh : middle.register .fresh=.natural base := (solverPrologue_base before base).trans fresh
  have middleAt : middle.pc=origin+16 := (solverPrologue_pc before base).trans (congrArg (·+16) hpc)
  have middleSafe:=(prologueResources middle (List.mem_of_getLast? prologueLast)).2.1
  have leadPC : natBits (middle.pc+4) ≤ budget := (natBits_mono (by rw [middleAt]; omega : middle.pc+4 ≤ origin+37)).trans pcBits
  have leadLocated : FetchesCode program middle.pc RootD27.Endpoint.paddingLeadCode := by rw [middleAt]; exact leadFetch
  obtain ⟨lead,leadHead,leadLast,leadChain,leadTime,leadResources⟩:=
    paddingLead_trace_resources program input middle base budget middleFresh middleSafe addressBits leadPC leadLocated
  have startedSafe:=(leadResources started (List.mem_of_getLast? leadLast)).2.1
  have fields:=RootD27.Endpoint.paddingLead_registers middle base
  have startedAt : started.pc=(origin+19)+1 := by
    change middle.pc+4=(origin+19)+1
    rw [middleAt]
  have loopPC : natBits ((origin+19)+18) ≤ budget := by simpa only [Nat.add_assoc] using pcBits
  obtain ⟨loop,loopHead,loopLast,loopChain,loopTime,loopResources,loopProper⟩:=baseRowLoop_trace_resources program input (origin+19)
    loopFetch base budget 7 started (base+6) startedAt fields.2.1 fields.2.2.1 fields.2.2.2 startedSafe (by omega)
      (by unfold headerWords; omega) addressBits zeroBits loopPC
  have firstLive : ∀ slot < 6,base+slot ∈ started.live := by
    intro slot inside
    exact (solverPrologue_arguments before base).1 slot inside
  have finalHeader : Header after base (initializedHeaderValues middle base) :=
    baseRowLoopResult_header (origin+19) started base firstLive
  have finalFresh : after.register .fresh=.natural base :=
    (baseRowLoopResult_unchanged_register (origin+19) 7 started (base+6) .fresh (by decide) (by decide) (by decide)).trans
      (fields.1.trans middleFresh)
  have finalPC : after.pc=origin+37 := by
    simpa only [Nat.add_assoc] using baseRowLoopResult_pc (origin+19) 7 started (base+6)
  have firstJoin:=joinTrace_spec program input prologue lead before middle started 255 75
    prologueHead prologueLast leadHead leadLast prologueChain leadChain prologueTime leadTime
  have firstMemory:=RegionMemory.join_trace prologue lead before middle _ prologueLast
    (fun state member => (prologueResources state member).1) (fun state member => (leadResources state member).1)
  have prologueFacts : ∀ state ∈ prologue,RootD27.Bits.SafeBits state budget ∧ origin ≤ state.pc ∧ state.pc < origin+37 := by
    intro state member
    have info:=prologueResources state member
    exact ⟨info.2.1,by omega⟩
  have leadFacts : ∀ state ∈ lead,RootD27.Bits.SafeBits state budget ∧ origin ≤ state.pc ∧ state.pc < origin+37 := by
    intro state member
    have info:=leadResources state member
    exact ⟨info.2.1,by omega⟩
  have firstFacts:=solverJoinTrace_all prologue lead middle
    (fun state => RootD27.Bits.SafeBits state budget ∧ origin ≤ state.pc ∧ state.pc < origin+37) prologueLast prologueFacts leadFacts
  have joined:=joinTrace_spec program input (joinTrace prologue lead) loop before started after 330 2130
    firstJoin.1 firstJoin.2.1 loopHead loopLast firstJoin.2.2.1 loopChain firstJoin.2.2.2 loopTime
  have allMemory:=RegionMemory.join_trace (joinTrace prologue lead) loop before started _ firstJoin.2.1 firstMemory
    (fun state member => (loopResources state member).1)
  have allFacts:=solverJoinTrace_all (joinTrace prologue lead) loop started
    (fun state => RootD27.Bits.SafeBits state budget ∧ origin ≤ state.pc ∧ state.pc ≤ origin+37) firstJoin.2.1
    (fun state member => ⟨(firstFacts state member).1,(firstFacts state member).2.1,(firstFacts state member).2.2.le⟩)
    (by
      intro state member
      have info:=loopResources state member
      exact ⟨info.2.1,by omega⟩)
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  refine ⟨joinTrace (joinTrace prologue lead) loop,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    finalHeader,finalFresh,finalPC,finalMemory.frame (headerRegion_subset_workspace base n k),finalMemory.2.2.2,?_,?_⟩
  · exact fun state member => ⟨allMemory state member,allFacts state member⟩
  · apply solverJoinTrace_proper (joinTrace prologue lead) loop started
      (fun state => origin ≤ state.pc ∧ state.pc < origin+37) firstJoin.2.1 loopHead
    · exact fun state member => (firstFacts state member).2
    · intro state member
      have interval:=loopProper state member
      omega

end PDCompute.Solver
