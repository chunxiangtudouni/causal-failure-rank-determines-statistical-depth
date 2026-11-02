module

public import Paid.PDCompute_SolverPaddingBody_137
public import Paid.PDCompute_SolverBaseRowResult_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDMenu.ComputeFrame

theorem solverJoinTrace_all (first later : List State) (middle : State) (property : State → Prop)
    (last : first.getLast?=some middle) (left : ∀ state ∈ first,property state) (right : ∀ state ∈ later,property state) :
    ∀ state ∈ joinTrace first later,property state := by
  have split:=List.dropLast_append_getLast? middle (by rw [last]; simp)
  intro state member
  rcases List.mem_append.mp member with proper|laterMember
  · apply left state
    rw [← split]
    exact List.mem_append.mpr (Or.inl proper)
  · exact right state laterMember

theorem solverJoinTrace_proper (first later : List State) (middle : State) (property : State → Prop)
    (last : first.getLast?=some middle) (head : later.head?=some middle)
    (left : ∀ state ∈ first,property state) (right : ∀ state ∈ later.dropLast,property state) :
    ∀ state ∈ (joinTrace first later).dropLast,property state := by
  have split:=List.dropLast_append_getLast? middle (by rw [last]; simp)
  cases later with
  | nil => simp at head
  | cons firstState rest =>
    intro state member
    change state ∈ (first.dropLast++firstState::rest).dropLast at member
    rw [List.dropLast_append_cons] at member
    rcases List.mem_append.mp member with proper|laterMember
    · apply left state
      rw [← split]
      exact List.mem_append.mpr (Or.inl proper)
    · exact right state laterMember

/-- SAME original counted padding loop and EXACT recursive result.
Header-region memory, SAME bit budget and PC metadata are attached to
ONE real trace, including the final proper-prefix interval. -/
theorem baseRowLoop_trace_resources (program : Program) (input : List Cell) (origin : ℕ)
    (fetch : FetchesCode program origin (baseRowCode origin)) (base budget count : ℕ) (before : State) (pointer : ℕ)
    (hpc : before.pc=origin+1) (address : before.register .address=.natural pointer)
    (current : before.register .index=.natural count) (one : before.register .flag=.natural 1)
    (safe : RootD27.Bits.SafeBits before budget) (lower : base ≤ pointer) (room : pointer+6*count ≤ base+headerWords)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (zeroBits : (.rational 0 : Cell).bits ≤ budget)
    (pcBits : natBits (origin+18) ≤ budget) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (baseRowLoopResult origin count before pointer) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 300*count+30 ∧
      (∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits state budget ∧
        origin ≤ state.pc ∧ state.pc ≤ origin+18) ∧
      ∀ state ∈ trace.dropLast,origin ≤ state.pc ∧ state.pc < origin+18 := by
  induction count generalizing before pointer with
  | zero =>
    let final : State:={before with pc:=origin+18}
    have branchFetch : program[before.pc]?=some (.branchZero .index (origin+18) (origin+2)) := by
      rw [hpc]
      exact fetch 1 (by rw [baseRowCode_length]; omega)
    have control : step program input before=some final := by simp [step,branchFetch,Instruction.execute,current,Cell.nat?,final]
    have finalSafe:=safe.withPC (origin+18) pcBits
    refine ⟨[before,final],rfl,rfl,List.isChain_pair.mpr control,?_,?_,?_⟩
    · simpa using time_le_length program [before,final]
    · intro state member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with same|same
      · subst state
        exact ⟨RegionMemory.refl before _,safe,by omega⟩
      · subst state
        exact ⟨RegionMemory.of_unchanged _ rfl rfl rfl,finalSafe,by change origin ≤ origin+18 ∧ origin+18 ≤ origin+18; omega⟩
    · intro state member
      have same : state=before := by simpa using member
      subst state
      omega
  | succ count ih =>
    let start : State:={before with pc:=origin+2}
    let returned : State:={baseRowWritesResult start pointer (count+1) with pc:=origin+1}
    let guardTrace:=[before,start]
    have branchFetch : program[before.pc]?=some (.branchZero .index (origin+18) (origin+2)) := by
      rw [hpc]
      exact fetch 1 (by rw [baseRowCode_length]; omega)
    have control : step program input before=some start := by simp [step,branchFetch,Instruction.execute,current,Cell.nat?,start]
    have guardChain : guardTrace.IsChain (fun first later => step program input first=some later) := List.isChain_pair.mpr control
    have guardTime : time program guardTrace ≤ 30 := by simpa [guardTrace] using time_le_length program [before,start]
    have startSafe : RootD27.Bits.SafeBits start budget := safe.withPC (origin+2) ((natBits_mono (by omega : origin+2 ≤ origin+18)).trans pcBits)
    have guardMemory : ∀ state ∈ guardTrace,RegionMemory before state (cellRegion base headerWords) := by
      intro state member
      simp only [guardTrace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with same|same <;> subst state
      · exact RegionMemory.refl before _
      · exact RegionMemory.of_unchanged _ rfl rfl rfl
    have guardFacts : ∀ state ∈ guardTrace,RootD27.Bits.SafeBits state budget ∧ origin ≤ state.pc ∧ state.pc < origin+18 := by
      intro state member
      simp only [guardTrace,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with same|same
      · subst state
        exact ⟨safe,by omega⟩
      · subst state
        exact ⟨startSafe,by change origin ≤ origin+2 ∧ origin+2 < origin+18; omega⟩
    obtain ⟨body,bodyHead,bodyLast,bodyChain,bodyTime,bodyResources⟩:=baseRowBody_trace_resources program input origin fetch start
      base pointer (count+1) budget rfl address current one startSafe lower (by omega) addressBits zeroBits pcBits
    have returnedFacts:=bodyResources returned (List.mem_of_getLast? bodyLast)
    have nextAddress : returned.register .address=.natural (pointer+6) := by simp [returned,baseRowWritesResult]
    have nextIndex : returned.register .index=.natural count := by simp [returned,baseRowWritesResult]
    have nextOne : returned.register .flag=.natural 1 := by simp [returned,baseRowWritesResult,start,one]
    obtain ⟨later,laterHead,laterLast,laterChain,laterTime,laterResources,laterProper⟩:=
      ih (before:=returned) (pointer:=pointer+6) rfl nextAddress nextIndex nextOne returnedFacts.2.1 (by omega) (by omega)
    have firstJoin:=joinTrace_spec program input guardTrace body before start returned 30 255 rfl rfl bodyHead bodyLast
      guardChain bodyChain guardTime bodyTime
    have firstMemory:=RegionMemory.join_trace guardTrace body before start _ rfl guardMemory
      (fun state member => (bodyResources state member).1)
    have firstFacts:=solverJoinTrace_all guardTrace body start
      (fun state => RootD27.Bits.SafeBits state budget ∧ origin ≤ state.pc ∧ state.pc < origin+18) rfl guardFacts
      (fun state member => (bodyResources state member).2)
    have finalJoin:=joinTrace_spec program input (joinTrace guardTrace body) later before returned
      (baseRowLoopResult origin count returned (pointer+6)) 285 (300*count+30) firstJoin.1 firstJoin.2.1 laterHead laterLast
      firstJoin.2.2.1 laterChain firstJoin.2.2.2 laterTime
    have allMemory:=RegionMemory.join_trace (joinTrace guardTrace body) later before returned _ firstJoin.2.1 firstMemory
      (fun state member => (laterResources state member).1)
    have allFacts:=solverJoinTrace_all (joinTrace guardTrace body) later returned
      (fun state => RootD27.Bits.SafeBits state budget ∧ origin ≤ state.pc ∧ state.pc ≤ origin+18) firstJoin.2.1
      (fun state member => ⟨(firstFacts state member).1,(firstFacts state member).2.1,(firstFacts state member).2.2.le⟩)
      (fun state member => (laterResources state member).2)
    refine ⟨joinTrace (joinTrace guardTrace body) later,finalJoin.1,finalJoin.2.1,finalJoin.2.2.1,?_,?_,?_⟩
    · calc
        _ ≤ 285+(300*count+30) := finalJoin.2.2.2
        _ = 300*count+315 := by ring
        _ ≤ 300*count+330 := Nat.add_le_add_left (by decide : 315 ≤ 330) _
        _ = _ := by ring
    · exact fun state member => ⟨allMemory state member,allFacts state member⟩
    · exact solverJoinTrace_proper (joinTrace guardTrace body) later returned
        (fun state => origin ≤ state.pc ∧ state.pc < origin+18) firstJoin.2.1 laterHead
        (fun state member => (firstFacts state member).2) laterProper

end PDCompute.Solver
