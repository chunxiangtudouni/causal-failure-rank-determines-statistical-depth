module

public import Paid.PDROC_BitVM_Kernel_Reset_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.Reset

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

def entry (stage : ℕ) : Label :=
  if bound : stage<32 then clearLabel ⟨stage,bound⟩ else .inr ()

def tailContents (stage : ℕ) (contents : Stack → List Bool) : Stack → List Bool :=
  fun role=>if readonly role then contents role else if role.val<stage then contents role else word role

theorem word_length (slot : Stack) : (word slot).length ≤ 4 := by
  cases reg : isRegister slot
  · simp only [word,reg,Bool.false_eq_true,↓reduceIte,List.length_nil];omega
  · change (if isRegister slot then encodeCellBits (.natural 0) else []).length ≤ 4
    rw [reg]
    change 4 ≤ 4
    exact Nat.le_refl _

theorem after_frame (slot other : Stack) (contents : Stack → List Bool) (store : Option Bool)
    (different : other ≠ slot) : (after slot contents store).stk other=contents other := by
  cases read : readonly slot <;> simp only [after,read,Bool.false_eq_true,
    ↓reduceIte,Function.update_of_ne different]

theorem after_bound (slot : Stack) (contents : Stack → List Bool) (store : Option Bool) (initial : ℕ)
    (bounded : ∀ role,(contents role).length ≤ initial+4) :
    ∀ role,((after slot contents store).stk role).length ≤ initial+4 := by
  intro role
  by_cases same : role=slot
  · subst role
    cases read : readonly slot
    · simp only [after,read,Bool.false_eq_true,↓reduceIte,Function.update_self]
      exact (word_length slot).trans (by omega)
    · simpa only [after,read,↓reduceIte] using bounded slot
  · rw [after_frame slot role contents store same]
    exact bounded role

theorem tailContents_phase (slot : Stack) (contents : Stack → List Bool) (store : Option Bool) :
    tailContents (slot.val+1) (after slot contents store).stk=tailContents slot.val contents := by
  funext role
  by_cases same : role=slot
  · subst role
    cases read : readonly slot
    · simp only [tailContents,after,read,Bool.false_eq_true,↓reduceIte,Function.update_self,
        Nat.lt_succ_self,Nat.lt_irrefl]
    · simp only [tailContents,after,read,↓reduceIte]
  · have unequal : role.val ≠ slot.val := fun eq=>same (Fin.ext eq)
    have equalTests : (role.val<slot.val+1) ↔ role.val<slot.val := by omega
    simp only [tailContents,after_frame slot role contents store same,equalTests]

theorem after_entry (slot : Stack) (contents : Stack → List Bool) (store : Option Bool) :
    after slot contents store=
      (⟨some (entry (slot.val+1)),((after slot contents store).var.1,()),
        (after slot contents store).stk⟩ : State) := by
  cases read : readonly slot <;> simp only [after,read,Bool.false_eq_true,
    ↓reduceIte,nextLabel,entry]

/-- The entire fixed32-role reset loop. The bound is derived from actual
entry stack lengths and the actual same path, with no supplied workspace,
padding or trace. It is valid after the real six/13-cell bank mount. -/
theorem tail_runs (remaining : ℕ) : ∀ (stage : ℕ),stage+remaining=32 → 
    ∀ (contents : Stack → List Bool) (store : Option Bool) (initial : ℕ),
      (∀ role,(contents role).length ≤ initial+4) → 
      ∃ (run : List State) (lastState : State),
        run.head?=some (⟨some (entry stage),(store,()),contents⟩ : State) ∧ 
        run.IsChain (fun a b=>TM2.step program a=some b) ∧ run.getLast?=some lastState ∧ 
        TM2.step program lastState=none ∧ lastState.stk=tailContents stage contents ∧ 
        run.length ≤ remaining*(initial+7)+2 := by
  induction remaining with
  | zero =>
    intro stage total contents store initial _bounded
    have same : stage=32 := by omega
    subst stage
    let first : State := ⟨some (.inr ()),(store,()),contents⟩
    let final : State := ⟨none,(store,()),contents⟩
    refine ⟨[first,final],final,rfl,
      List.isChain_cons_cons.mpr ⟨rfl,List.isChain_singleton _⟩,rfl,rfl,?_,?_⟩
    · funext role
      simp only [final,tailContents,role.isLt,↓reduceIte]
      split <;> rfl
    · change 2 ≤ 0*(initial+7)+2
      omega
  | succ remaining ih =>
    intro stage total contents store initial bounded
    have valid : stage<32 := by omega
    let slot : Stack := ⟨stage,valid⟩
    obtain ⟨first,firstHead,firstChain,firstLast,firstBound⟩ := phase_runs slot contents store
    have nextTotal : (stage+1)+remaining=32 := by omega
    obtain ⟨second,final,secondHead,secondChain,secondLast,halt,finalData,secondBound⟩ :=
      ih (stage+1) nextTotal (after slot contents store).stk (after slot contents store).var.1 initial
        (after_bound slot contents store initial bounded)
    have boundary : after slot contents store=
        (⟨some (entry (stage+1)),((after slot contents store).var.1,()),
          (after slot contents store).stk⟩ : State) := after_entry slot contents store
    rw [←boundary] at secondHead
    have firstHead' : first.head?=some (⟨some (entry stage),(store,()),contents⟩ : State) := by
      simpa only [entry,valid,↓reduceDIte,before,slot] using firstHead
    cases second with
    | nil => simp only [List.head?_nil,reduceCtorEq] at secondHead
    | cons start rest =>
      have same : start=after slot contents store := Option.some.inj secondHead
      subst start
      refine ⟨first++rest,final,?_,
        PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain first
          (after slot contents store) rest firstLast firstChain secondChain,
        (PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_last first
          (after slot contents store) rest firstLast).trans secondLast,halt,?_,?_⟩
      · simp only [List.head?_append,firstHead',Option.some_or]
      · exact finalData.trans (tailContents_phase slot contents store)
      · have phaseSize : first.length ≤ initial+7 := firstBound.trans (by have h:=bounded slot;omega)
        simp only [List.length_append,List.length_cons] at secondBound ⊢
        rw [Nat.succ_mul]
        omega

theorem reset_runs (contents : Stack → List Bool) (store : Option Bool) :
    ∃ (run : List State) (lastState : State),
      run.head?=some (⟨some (clearLabel 0),(store,()),contents⟩ : State) ∧ 
      run.IsChain (fun a b=>TM2.step program a=some b) ∧ run.getLast?=some lastState ∧ 
      TM2.step program lastState=none ∧ 
      (∀ role,readonly role=true → lastState.stk role=contents role) ∧ 
      (∀ role,readonly role=false → lastState.stk role=word role) ∧ 
      run.length ≤ 32*((∑ role : Stack,(contents role).length)+7)+2 := by
  let initial := ∑ role : Stack,(contents role).length
  have bounded : ∀ role,(contents role).length ≤ initial+4 := by
    intro role
    have h := Finset.single_le_sum (s := (Finset.univ : Finset Stack))
      (f := fun index : Stack=>(contents index).length) (a := role)
      (fun index _=>Nat.zero_le ((contents index).length)) (Finset.mem_univ role)
    change (contents role).length ≤ initial at h
    omega
  obtain ⟨run,lastState,head,chain,last,halt,data,bound⟩ := tail_runs 32 0 rfl contents store initial bounded
  refine ⟨run,lastState,head,chain,last,halt,?_,?_,bound⟩
  · intro role read
    rw [data]
    simp only [tailContents,read,↓reduceIte]
  · intro role read
    rw [data]
    simp only [tailContents,read,Bool.false_eq_true,↓reduceIte,Nat.not_lt_zero]

/-- Original RAM.initial is physically established after each real bank
mount, including prepare-to-core reuse of a nonempty old workspace. -/
theorem initial_ram_runs (contents : Stack → List Bool) (store : Option Bool) :
    ∃ (run : List State) (lastState : State),
      run.head?=some (⟨some (clearLabel 0),(store,()),contents⟩ : State) ∧ 
      run.IsChain (fun a b=>TM2.step program a=some b) ∧ run.getLast?=some lastState ∧ 
      TM2.step program lastState=none ∧ RegistersRepresent PaperProofs.Paid.Computation.initial lastState ∧ 
      (∀ role,readonly role=true → lastState.stk role=contents role) ∧ 
      (∀ role,role=0 ∨ 21 ≤ role.val → lastState.stk role=[]) ∧ 
      run.length ≤ 32*((∑ role : Stack,(contents role).length)+7)+2 := by
  obtain ⟨run,lastState,head,chain,last,halt,bank,writable,bound⟩ := reset_runs contents store
  refine ⟨run,lastState,head,chain,last,halt,?_,bank,?_,bound⟩
  · intro reg
    have read : readonly (registerSlot reg)=false := by cases reg <;> decide
    have canonical : word (registerSlot reg)=encodeCellBits (.natural 0) := by cases reg <;> rfl
    exact (writable (registerSlot reg) read).trans canonical
  · intro role nonRegister
    rcases nonRegister with zero | large
    · subst role
      exact writable 0 (by decide)
    · have read : readonly role=false := by simp only [readonly,decide_eq_false_iff_not];omega
      have notReg : isRegister role=false := by simp only [isRegister,decide_eq_false_iff_not];omega
      rw [writable role read]
      simp only [word,notReg,Bool.false_eq_true,↓reduceIte]

end PDROC.BitVM.Kernel.Reset
