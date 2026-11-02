module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsPaths_083

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem build_shared (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (.build 0)) (source : before.stk 3=NatField.packet number tail)
    (scratch : before.stk 4=[]) :
    buildCfg (RootB234.RuntimeCounter.Builder.atState countRoles before.stk 0
      ((packetIso C).symm before.var).1 ((packetIso C).symm before.var).2
      (NatField.packet number tail) [] (before.stk 10) (before.stk 11))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.build 0) at active
    subst point
    change (⟨some (.build 0),packetIso C ((packetIso C).symm memory),
      RootB234.RuntimeCounter.Builder.Public.physicalBank 3 slots _ _ _ _⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> simp_all [RootB234.RuntimeCounter.Builder.Public.physicalBank]

theorem actual_build (caller : Statement C) (before : State C) (number : Nat) (tail : List Bool)
    (active : before.l=some (.build 0)) (source : before.stk 3=NatField.packet number tail)
    (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some .clearCount ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (PSTRTMNatValue017.rawPayload number) ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,slot≠4→slot≠10→slot≠11→final.stk slot=before.stk slot) ∧
      run.trace.length≤(before.stk 10).length+(before.stk 11).length+
        2*(PSTRTMNatValue017.rawPayload number).length+14 := by
  let registers := (packetIso C).symm before.var
  obtain ⟨trace,facts⟩ := RootB234.RuntimeCounter.Builder.at_actual countRoles false
    before.stk registers.1 registers.2 number tail (before.stk 10) (before.stk 11)
  let final := RootB234.RuntimeCounter.Builder.Public.finalState countRoles false before.stk registers.1 number tail
  have path := single_port_path (packetIso C) buildLabel _ caller 5 rfl trace _ final
    facts.first facts.chain facts.last rfl
    (by intro point different; simp only [buildLabel,different,ite_false,program])
  let run : Segment caller before (buildCfg final) :=
    ⟨trace.map buildCfg,path.1.trans (congrArg some (build_shared before number tail active source scratch)),
      path.2.1,path.2.2⟩
  refine ⟨buildCfg final,run,rfl,?_,rfl,rfl,rfl,?_,?_⟩
  · change registers.1.2.2=before.var.2.2
    rfl
  · intro slot n4 n10 n11
    change RootB234.RuntimeCounter.Builder.Public.physicalBank 3 before.stk _ _ _ _ slot=before.stk slot
    by_cases s3 : slot=3
    · subst slot
      exact source.symm
    · simp only [RootB234.RuntimeCounter.Builder.Public.physicalBank,s3,n4,n10,n11,ite_false]
  · simpa only [run,List.length_map] using facts.count

def clearState (bank : RatInput.Stack → List Bool) (point : Label) (memory : Store C)
    (cells : List Bool) : State C := ⟨some point,memory,Function.update bank 3 cells⟩

theorem clear_bit (caller : Statement C) (bank : RatInput.Stack → List Bool) (memory : Store C)
    (bit : Bool) (cells : List Bool) :
    TM2.step (program caller) (clearState bank .clearCount memory (bit::cells))=
      some (clearState bank .clearCount (capture memory (some bit)) cells) := by
  simp [clearState,program,TM2.step,TM2.stepAux,capture,present,Function.update_self,Function.update_idem]

theorem clear_end (caller : Statement C) (bank : RatInput.Stack → List Bool) (memory : Store C) :
    TM2.step (program caller) (clearState bank .clearCount memory [])=
      some (clearState bank (.round 0) (capture memory none) []) := by
  simp [clearState,program,TM2.step,TM2.stepAux,capture,present,Function.update_self,Function.update_idem]

def clearPath (caller : Statement C) (bank : RatInput.Stack → List Bool) (memory : Store C)
    (cells : List Bool) : Segment caller (clearState bank .clearCount memory cells)
      (clearState bank (.round 0) (capture memory none) []) := by
  induction cells generalizing memory with
  | nil =>
    exact ⟨[clearState bank .clearCount memory [],clearState bank (.round 0) (capture memory none) []],rfl,
      List.isChain_cons_cons.mpr ⟨clear_end caller bank memory,List.isChain_singleton _⟩,rfl⟩
  | cons bit cells ih =>
    let next := clearState bank .clearCount (capture memory (some bit)) cells
    let edge : Segment caller (clearState bank .clearCount memory (bit::cells)) next :=
      ⟨[clearState bank .clearCount memory (bit::cells),next],rfl,
        List.isChain_cons_cons.mpr ⟨clear_bit caller bank memory bit cells,List.isChain_singleton _⟩,rfl⟩
    exact edge.append (ih (capture memory (some bit)))

theorem actual_clear (caller : Statement C) (before : State C) (active : before.l=some .clearCount) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some (.round 0) ∧ final.var.2.2=before.var.2.2 ∧ final.stk 3=[] ∧
      ∀ slot,slot≠3→final.stk slot=before.stk slot := by
  have shared : clearState before.stk .clearCount before.var (before.stk 3)=before := by
    unfold clearState
    rw [Function.update_eq_self,←active]
  let result := clearPath caller before.stk before.var (before.stk 3)
  let run : Segment caller before (clearState before.stk (.round 0) (capture before.var none) []) :=
    ⟨result.trace,result.first.trans (congrArg some shared),result.chain,result.last⟩
  refine ⟨_,run,rfl,rfl,?_,?_⟩
  · rfl
  · intro slot untouched
    exact Function.update_of_ne untouched _ _

end B23_4_RatWordPrep.WordFields
