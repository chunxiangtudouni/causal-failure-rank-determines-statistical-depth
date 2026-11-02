module

public import Paid.PDCompute_CorePreludePC_Row_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDCompute.CorePreludePC

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute

attribute [local irreducible] kernel

/-- The original functional segment, retaining time and lower PC on ONE trace. -/
def ScopedSegment (origin : ℕ) (input : List Cell) (before after : State) (budget : ℕ) : Prop :=
  ∃ states : List State,states.head?=some before ∧ states.getLast?=some after ∧
    states.IsChain (fun first later=>step (locatedBlock origin (kernel origin)) input first=some later) ∧
    time (locatedBlock origin (kernel origin)) states≤budget ∧
    ∀ state∈states,origin+1≤state.pc

theorem ScopedSegment.trans {origin : ℕ} {input : List Cell} {before middle after : State} {first later : ℕ}
    (earlier : ScopedSegment origin input before middle first)
    (following : ScopedSegment origin input middle after later) :
    ScopedSegment origin input before after (first+later) := by
  obtain ⟨left,lh,ll,lc,lt,lp⟩:=earlier
  obtain ⟨right,rh,rl,rc,rt,rp⟩:=following
  exact ⟨joinTrace left right,joinTrace_head left right before middle lh ll rh,
    joinTrace_last left right after rl,joinTrace_chain _ _ left right middle lc rc ll rh,
    (joinTrace_time_le _ left right middle ll).trans (Nat.add_le_add lt rt),
    PDCompute.Pack.joinTrace_invariant left right _ lp rp⟩

theorem ScopedSegment.mono {origin : ℕ} {input : List Cell} {before after : State} {first later : ℕ}
    (actual : ScopedSegment origin input before after first) (bound : first≤later) :
    ScopedSegment origin input before after later := by
  obtain ⟨states,head,last,chain,cost,lower⟩:=actual
  exact ⟨states,head,last,chain,cost.trans bound,lower⟩

theorem scoped_block (origin : ℕ) (label : Label) (input : List Cell)
    (before middle after : State) (position : before.pc=labelAddress origin label)
    (executed : linearExecute input (basicBlock label).body before=some middle)
    (controlled : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (bodyLow : origin+1≤labelAddress origin label) (afterLow : origin+1≤after.pc) :
    ScopedSegment origin input before after (15*((basicBlock label).body.length+1)+15) := by
  obtain ⟨body,head,last,_length,chain,middlePC,cost,prefixes⟩:=
    kernel_body_trace origin label input before middle position executed
  have bodyLower : ∀ state∈body,origin+1≤state.pc := by
    intro state member
    have split:=List.dropLast_append_getLast? middle (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,_inside,run⟩:=prefixes state proper
      exact prefix_after_enter origin input label before state count (by rw [position];exact bodyLow) run
    · have same:=List.mem_singleton.mp terminal
      subst state
      omega
  have next : step (locatedBlock origin (kernel origin)) input middle=some after := by
    rw [kernel_control_step origin label input middle middlePC]
    exact controlled
  have joined:=chain_append_control (locatedBlock origin (kernel origin)) input body middle after chain last next
  have nonempty : body≠[]:=by intro empty;rw [empty] at head;cases head
  refine ⟨body++[after],?_,by simp,joined.1,joined.2.trans (by omega),?_⟩
  · simpa only [List.head?_append_of_ne_nil body nonempty] using head
  · intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact bodyLower state earlier
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact afterLow

theorem scoped_go (origin : ℕ) (label target : Label) (input : List Cell) (before middle : State)
    (position : before.pc=labelAddress origin label)
    (run : linearExecute input (basicBlock label).body before=some middle)
    (control : (basicBlock label).control=.go target)
    (notEnter : label≠.enter := by decide) (targetNotEnter : target≠.enter := by decide) :
    ScopedSegment origin input before {middle with pc:=labelAddress origin target}
      (15*((basicBlock label).body.length+1)+15) := by
  apply scoped_block origin label input before middle _ position run _
    (label_after_enter origin label notEnter) (label_after_enter origin target targetNotEnter)
  simp only [control,controlInstruction,Instruction.execute]
  rfl

theorem scoped_branch (origin : ℕ) (label zero nonzero : Label) (input : List Cell)
    (before middle : State) (condition : Prop) [Decidable condition]
    (position : before.pc=labelAddress origin label)
    (run : linearExecute input (basicBlock label).body before=some middle)
    (control : (basicBlock label).control=.branch .flag zero nonzero)
    (flag : middle.register .flag=.natural (if condition then 1 else 0))
    (notEnter : label≠.enter := by decide) (zeroNotEnter : zero≠.enter := by decide)
    (nonzeroNotEnter : nonzero≠.enter := by decide) :
    ScopedSegment origin input before {middle with pc:=labelAddress origin (if condition then nonzero else zero)}
      (15*((basicBlock label).body.length+1)+15) := by
  exact scoped_block origin label input before middle _ position run (by
      by_cases decision : condition <;>
        simp [control,controlInstruction,Instruction.execute,flag,decision,Cell.nat?])
    (label_after_enter origin label notEnter)
    (by split <;> exact label_after_enter origin _ (by assumption))

/-- The actual bounded prefix summation loop. Its invariant relates the
stored accumulator to the original array prefix; the supplied row is the
already computed row, and no successful summation run is assumed. -/
theorem sumLoop_pc (origin : ℕ) (input : List Cell) (base : ℕ) (row : Array ℚ) (remaining : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .sumGate)
    (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (fresh : before.register .fresh=.natural base)
    (readOutside : base+16 ≤ header.readBase) (rowSize : header.level < row.size)
    (count : header.level=header.cursor+remaining)
    (qValue : header.q=rowPrefixSum row header.cursor) :
    ∃ after : State,
      ScopedSegment origin input before after (465*remaining+135) ∧
      after.pc=labelAddress origin .sumFinish ∧
      ({header with cursor:=header.level,q:=rowPrefixSum row header.level}).At after base ∧
      RowAt after header.readBase row ∧ after.register .fresh=.natural base ∧ after.output=before.output ∧ PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before after := by
  have budget : 15*((basicBlock .sumGate).body.length+1)+15=135 := by decide
  induction remaining generalizing before header with
  | zero =>
    have cursorEq : header.cursor=header.level := by omega
    let middle := sumGateResult before base header.cursor header.level
    let after : State := {middle with pc:=labelAddress origin .sumFinish}
    have run : ScopedSegment origin input before after 135 := by
      simpa only [middle,after,cursorEq,lt_self_iff_false,ite_false,budget] using
        scoped_branch origin .sumGate .sumFinish .sumCell input before middle
          (header.cursor < header.level) position (sumGate_execute input before base header represented fresh)
          rfl (by simp [middle,sumGateResult])
    have finalHeader : {header with cursor:=header.level,q:=rowPrefixSum row header.level}=header := by
      have qEq : rowPrefixSum row header.level=header.q := by rw [←cursorEq,←qValue]
      have pairEq : (header.level,rowPrefixSum row header.level)=(header.cursor,header.q) :=
        Prod.ext cursorEq.symm qEq
      exact congrArg (fun pair : ℕ×ℚ => {header with cursor:=pair.1,q:=pair.2}) pairEq
    refine ⟨after,?_,rfl,?_,?_,?_,rfl,?_⟩
    · simpa using run
    · rw [finalHeader]
      exact represented
    · exact ⟨rowAt.live,rowAt.value⟩
    · exact (sumGate_fresh before base header.cursor header.level).trans fresh
    · exact PDMenu.ComputeFrame.MemoryFrame.refl (sumRegion base) before
  | succ remaining ih =>
    have below : header.cursor<header.level := by omega
    have inside : header.cursor<row.size := by omega
    let middle := sumGateResult before base header.cursor header.level
    let entered : State := {middle with pc:=labelAddress origin .sumCell}
    have hEntered : header.At entered base := represented
    have rEntered : RowAt entered header.readBase row := ⟨rowAt.live,rowAt.value⟩
    have fEntered : entered.register .fresh=.natural base :=
      (sumGate_fresh before base header.cursor header.level).trans fresh
    have iEntered : entered.register .index=.natural header.cursor := sumGate_index before base header represented
    have gate : ScopedSegment origin input before entered 135 := by
      simpa only [middle,entered,ite_eq_left below,budget] using
        scoped_branch origin .sumGate .sumFinish .sumCell input before middle
          (header.cursor < header.level) position (sumGate_execute input before base header represented fresh)
          rfl (by simp [middle,sumGateResult])
    let computed := sumCellResult entered base header.readBase header.cursor header.q (row.getD header.cursor 0)
    let nextState : State := {computed with pc:=labelAddress origin .sumGate}
    let nextHeader : Header := {header with cursor:=header.cursor+1,q:=header.q+row.getD header.cursor 0}
    have cell : ScopedSegment origin input entered nextState 330 :=
      scoped_go origin .sumCell .sumGate input entered computed rfl
        (sumCell_execute input entered base header row hEntered rEntered inside fEntered iEntered) rfl
    have nextRepresented : nextHeader.At nextState base := sumCell_header row hEntered
    have computedRow := sumCell_row row rEntered readOutside
    have nextRow : RowAt nextState nextHeader.readBase row := ⟨computedRow.live,computedRow.value⟩
    have nextFresh : nextState.register .fresh=.natural base :=
      (sumCell_fresh entered base header.readBase header.cursor header.q (row.getD header.cursor 0)).trans fEntered
    have nextCount : nextHeader.level=nextHeader.cursor+remaining := by dsimp [nextHeader]; omega
    have nextQ : nextHeader.q=rowPrefixSum row nextHeader.cursor := by
      change header.q+row.getD header.cursor 0=rowPrefixSum row (header.cursor+1)
      rw [rowPrefixSum_succ,qValue]
    obtain ⟨after,later,last,finalHeader,finalRow,finalFresh,finalOutput,finalMemory⟩ := ih nextState nextHeader rfl
      nextRepresented nextRow nextFresh readOutside rowSize nextCount nextQ
    refine ⟨after,((gate.trans cell).trans later).mono (by omega),last,?_,finalRow,finalFresh,?_,?_⟩
    · exact finalHeader
    · exact finalOutput
    · have current : PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before nextState :=
        sumCell_memoryFrame entered base header.readBase header.cursor header.q (row.getD header.cursor 0)
      exact current.trans finalMemory

/-- Complete ACTUAL summation phase, including zero initialization,
every prefix iteration, the final center cell's half contribution and
the real jump to the weight block. -/
theorem sumPhase_pc (origin : ℕ) (input : List Cell) (base : ℕ) (row : Array ℚ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .sumStart)
    (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (fresh : before.register .fresh=.natural base)
    (outside : base+16≤header.readBase) (rowSize : header.level<row.size) :
    ∃ after : State,
      ScopedSegment origin input before after (1000*(header.level+1)) ∧
      after.pc=labelAddress origin .weight ∧
      ({header with
        cursor:=header.level
        q:=rowPrefixSum row header.level+row.getD header.level 0*(1/2)}).At after base ∧
      after.register .fresh=.natural base ∧ after.output=before.output ∧ PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before after := by
  let first : State := {sumStartResult before base with pc:=labelAddress origin .sumGate}
  let firstHeader : Header := {header with q:=0,cursor:=0}
  have start : ScopedSegment origin input before first 150 :=
    scoped_go origin .sumStart .sumGate input before (sumStartResult before base) position
      (sumStart_execute input before base fresh) rfl
  have firstRepresented : firstHeader.At first base := sumStart_header represented
  have initializedRow := sumStart_rowStrong row rowAt outside
  have firstRow : RowAt first firstHeader.readBase row := ⟨initializedRow.live,initializedRow.value⟩
  have firstFresh : first.register .fresh=.natural base := by
    simpa [first,sumStartResult,constantSlot_fresh] using fresh
  obtain ⟨last,loop,atFinish,lastHeader,lastRow,lastFresh,lastOutput,loopMemory⟩ :=
    sumLoop_pc origin input base row header.level first firstHeader rfl firstRepresented firstRow firstFresh outside rowSize
      (by simp [firstHeader]) (by simp [firstHeader,rowPrefixSum_zero])
  let summedHeader : Header := {header with cursor:=header.level,q:=rowPrefixSum row header.level}
  let completed := sumFinishResult last base header.readBase header.level (rowPrefixSum row header.level)
    (row.getD header.level 0)
  let after : State := {completed with pc:=labelAddress origin .weight}
  have complete : ScopedSegment origin input last after 285 :=
    scoped_go origin .sumFinish .weight input last completed atFinish
      (sumFinish_execute input last base summedHeader row lastHeader lastRow rowSize lastFresh) rfl
  refine ⟨after,((start.trans loop).trans complete).mono (by omega),rfl,?_,?_,?_,?_⟩
  · exact sumFinish_header row lastHeader
  · simpa [after,completed,sumFinishResult,storeSlotResult,sumFinishLeadResult,loadSlotResult] using lastFresh
  · exact lastOutput
  · have initialized : PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before first := by
      have one := constantSlotResult_memoryFrame (sumRegion base) before base 11 (.rational 0) (by simp [sumRegion])
      have two := constantSlotResult_memoryFrame (sumRegion base) (constantSlotResult before base 11 (.rational 0))
        base 7 (.natural 0) (by simp [sumRegion])
      exact one.trans two
    have finished : PDMenu.ComputeFrame.MemoryFrame (sumRegion base) last after :=
      sumFinish_memoryFrame last base header.readBase header.level (rowPrefixSum row header.level) (row.getD header.level 0)
    exact (initialized.trans loopMemory).trans finished


end PDCompute.CorePreludePC
