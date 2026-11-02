module

public import Paid.RootD27Core_EmitCellTrace_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

def EmittedPrefix (before : State) (cells : List Cell) (state : State) : Prop :=
  state.heap=before.heap ∧ state.live=before.live ∧
    ∃ written pending : List Cell,cells=written++pending ∧ state.output=before.output++written

theorem joinTrace_member {first later : List State} {state : State}
    (member : state∈joinTrace first later) : state∈first ∨ state∈later := by
  rcases List.mem_append.mp member with prior|subsequent
  · exact Or.inl (List.mem_of_mem_dropLast prior)
  · exact Or.inr subsequent

theorem emitBudget_succ (n : ℕ) : 135+(135*n+30)=135*(n+1)+30 := by
  rw [Nat.mul_succ]
  ac_rfl

/-- A fixed seven-instruction physical loop emits every cell of an
ACTUALLY live heap list. Every trace prefix preserves all heap/live cells
and has output equal to an exact original-list prefix. -/
theorem emitHeap_actual (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (fetched : FetchesCode program origin (emitHeapCode origin returnPC))
    (cells : List Cell) (before : State) (pointer : ℕ)
    (position : before.pc=origin) (address : before.register .address=.natural pointer)
    (index : before.register .index=.natural cells.length) (stored : HeapList before pointer cells) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤135*cells.length+30 ∧ after.pc=returnPC ∧
      after.register .address=.natural (pointer+cells.length) ∧ after.register .index=.natural 0 ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++cells ∧
      ∀ state∈trace,EmittedPrefix before cells state := by
  induction cells generalizing before pointer with
  | nil =>
    obtain ⟨trace,after,head,last,chain,cost,afterEq,memory⟩:=
      emitHeap_guard_actual program input before origin returnPC 0 position index fetched
    have eq : after={before with pc:=returnPC} := by simpa using afterEq
    refine ⟨trace,after,head,last,chain,cost,?_,?_,?_,?_,?_,?_,?_⟩
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
    obtain ⟨guardTrace,tested,gh,gl,gc,gt,testedEq,guardMemory⟩:=
      emitHeap_guard_actual program input before origin returnPC (tail.length+1) position index' fetched
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
    obtain ⟨bodyTrace,middle,bh,bl,bc,bt,bodyPC,bodyAddress,bodyIndex,bodyHeap,bodyLive,bodyOutput,bodyMemory⟩:=
      emitCell_actual program input tested origin returnPC pointer tail.length value testedPosition
        testedAddress testedIndex headLive headValue fetched
    have middleHeap : middle.heap=before.heap := bodyHeap.trans guardFinal.1
    have middleLive : middle.live=before.live := bodyLive.trans guardFinal.2.1
    have tailStored : HeapList middle (pointer+1) tail := by
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
    obtain ⟨later,after,lh,ll,lc,lt,afterPC,afterAddress,afterIndex,afterHeap,afterLive,afterOutput,laterPrefixes⟩:=
      ih middle (pointer+1) bodyPC bodyAddress bodyIndex tailStored
    have first:=joinTrace_spec program input guardTrace bodyTrace before tested middle
      30 105 gh gl bh bl gc bc gt bt
    have joined:=joinTrace_spec program input (joinTrace guardTrace bodyTrace) later before middle after
      135 (135*tail.length+30) first.1 first.2.1 lh ll first.2.2.1 lc first.2.2.2 lt
    refine ⟨joinTrace (joinTrace guardTrace bodyTrace) later,after,joined.1,joined.2.1,joined.2.2.1,
      ?_,afterPC,?_,afterIndex,afterHeap.trans middleHeap,afterLive.trans middleLive,?_,?_⟩
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

end RootD27.Core
