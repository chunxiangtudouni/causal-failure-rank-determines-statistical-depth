module

public import Paid.PDCompute_SolverEmitCellBits_208

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame RootD27.Core

/-- COMPLETE original fixed seven-op output loop. ACTUAL live original
cells are loaded/emitted, real counters and backedges run, and every
output prefix carries the SAME complete-state numerical budget. -/
theorem emitHeap_trace_resources (program : Program) (input : List Cell) (origin returnPC budget : ℕ)
    (fetched : FetchesCode program origin (emitHeapCode origin returnPC))
    (cells : List Cell) (before : State) (pointer : ℕ)
    (position : before.pc=origin) (address : before.register .address=.natural pointer)
    (index : before.register .index=.natural cells.length) (stored : PDLower.CalibrationCompute.HeapList before pointer cells)
    (safe : RootD27.Bits.SafeBits before budget) (oneBits : (.natural 1 : Cell).bits≤budget)
    (pointerBits : 1+natBits (pointer+cells.length)≤budget) (pcBits : natBits (origin+7)≤budget) (returnBits : natBits returnPC≤budget) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤135*cells.length+30 ∧ after.pc=returnPC ∧
      after.register .address=.natural (pointer+cells.length) ∧ after.register .index=.natural 0 ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++cells ∧
      (∀ state∈trace,EmittedPrefix before cells state) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  induction cells generalizing before pointer with
  | nil =>
    obtain ⟨trace,after,head,last,chain,cost,afterEq,memory,bounded⟩:=
      emitHeap_guard_trace_bits program input before origin returnPC 0 budget position index fetched safe pcBits returnBits
    have eq : after={before with pc:=returnPC} := by simpa using afterEq
    refine ⟨trace,after,head,last,chain,cost,?_,?_,?_,?_,?_,?_,?_,bounded⟩
    · rw [eq]
    · simpa [eq] using address
    · simpa [eq] using index
    · rw [eq]
    · rw [eq]
    · simp only [eq,List.append_nil]
    · intro state member
      have unchanged:=memory state member
      exact ⟨unchanged.1,unchanged.2.1,[],[],rfl,by simpa only [List.append_nil] using unchanged.2.2⟩
  | cons value tail ih =>
    have index' : before.register .index=.natural (tail.length+1) := index
    obtain ⟨guardTrace,tested,gh,gl,gc,gt,testedEq,guardMemory,guardSafe⟩:=
      emitHeap_guard_trace_bits program input before origin returnPC (tail.length+1) budget position index' fetched safe pcBits returnBits
    have guardEq : tested={before with pc:=origin+1} := by simpa using testedEq
    have guardFinal:=guardMemory tested (RootD27.Endpoint.trace_last_member guardTrace tested gl)
    have testedPosition : tested.pc=origin+1 := by rw [guardEq]
    have testedAddress : tested.register .address=.natural pointer := by simpa only [guardEq] using address
    have testedIndex : tested.register .index=.natural (tail.length+1) := by simpa only [guardEq] using index'
    have headLive : pointer∈tested.live := by
      rw [guardFinal.2.1]
      simpa only [Nat.add_zero] using stored.1 0 (by simp)
    have headValue : tested.heap pointer=value := by
      rw [guardFinal.1]
      have lookup:=PDLower.CalibrationCompute.HeapList.value stored 0 (by simp)
      rw [List.getElem_cons_zero] at lookup
      simpa only [Nat.add_zero] using lookup
    obtain ⟨bodyTrace,middle,bh,bl,bc,bt,bodyPC,bodyAddress,bodyIndex,bodyHeap,bodyLive,bodyOutput,bodyMemory,bodySafe⟩:=
      emitCell_trace_resources program input tested origin returnPC pointer tail.length budget value testedPosition
        testedAddress testedIndex headLive headValue fetched (guardSafe tested (List.mem_of_getLast? gl)) oneBits
        ((Nat.add_le_add_left (natBits_mono (by simp only [List.length_cons];omega : pointer+1≤pointer+(value::tail).length)) 1).trans pointerBits) pcBits
    have middleHeap : middle.heap=before.heap := bodyHeap.trans guardFinal.1
    have middleLive : middle.live=before.live := bodyLive.trans guardFinal.2.1
    have tailStored : PDLower.CalibrationCompute.HeapList middle (pointer+1) tail := by
      apply PDLower.CalibrationCompute.HeapList.of_values
      · intro offset inside
        rw [middleLive]
        have shift : pointer+1+offset=pointer+(offset+1) := by omega
        rw [shift]
        exact stored.1 (offset+1) (by simp only [List.length_cons];omega)
      · intro offset inside
        rw [middleHeap]
        have shift : pointer+1+offset=pointer+(offset+1) := by omega
        rw [shift]
        have lookup:=PDLower.CalibrationCompute.HeapList.value stored (offset+1) (by simp only [List.length_cons];omega)
        rw [List.getElem_cons_succ] at lookup
        exact lookup
    have tailPointerBits : 1+natBits (pointer+1+tail.length)≤budget := by
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 tail.length] using pointerBits
    obtain ⟨later,after,lh,ll,lc,lt,afterPC,afterAddress,afterIndex,afterHeap,afterLive,afterOutput,laterPrefixes,laterSafe⟩:=
      ih middle (pointer+1) bodyPC bodyAddress bodyIndex tailStored (bodySafe middle (List.mem_of_getLast? bl)) tailPointerBits
    have first:=joinTrace_spec program input guardTrace bodyTrace before tested middle
      30 105 gh gl bh bl gc bc gt bt
    have joined:=joinTrace_spec program input (joinTrace guardTrace bodyTrace) later before middle after
      135 (135*tail.length+30) first.1 first.2.1 lh ll first.2.2.1 lc first.2.2.2 lt
    refine ⟨joinTrace (joinTrace guardTrace bodyTrace) later,after,joined.1,joined.2.1,joined.2.2.1,
      ?_,afterPC,?_,afterIndex,afterHeap.trans middleHeap,afterLive.trans middleLive,?_,?_,
      PDCompute.Pack.joinTrace_invariant (joinTrace guardTrace bodyTrace) later (fun state=>RootD27.Bits.SafeBits state budget)
        (PDCompute.Pack.joinTrace_invariant guardTrace bodyTrace (fun state=>RootD27.Bits.SafeBits state budget) guardSafe bodySafe) laterSafe⟩
    · exact joined.2.2.2.trans_eq (emitBudget_succ tail.length)
    · exact afterAddress.trans (congrArg Cell.natural (by simp only [List.length_cons];omega))
    · rw [afterOutput,bodyOutput,guardFinal.2.2,List.append_assoc]
      rfl
    · intro state member
      rcases joinTrace_member member with early|subsequent
      · rcases joinTrace_member early with guarding|body
        · have unchanged:=guardMemory state guarding
          exact ⟨unchanged.1,unchanged.2.1,[],value::tail,rfl,
            by simpa only [List.append_nil] using unchanged.2.2⟩
        · have changed:=bodyMemory state body
          refine ⟨changed.1.trans guardFinal.1,changed.2.1.trans guardFinal.2.1,?_⟩
          rcases changed.2.2 with noOutput|oneOutput
          · exact ⟨[],value::tail,rfl,by simpa only [List.append_nil] using noOutput.trans guardFinal.2.2⟩
          · exact ⟨[value],tail,rfl,by rw [oneOutput,guardFinal.2.2]⟩
      · obtain ⟨heap,live,written,pending,decomposition,output⟩:=laterPrefixes state subsequent
        refine ⟨heap.trans middleHeap,live.trans middleLive,value::written,pending,?_,?_⟩
        · simp only [List.cons_append,decomposition]
        · rw [output,bodyOutput,guardFinal.2.2,List.append_assoc]
          rfl


end PDCompute.Solver
