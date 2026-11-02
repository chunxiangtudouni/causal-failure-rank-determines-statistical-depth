module

public import B23_4_RatWordPrep_SeqCmp_WordCode_010

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp.Word

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PSTRWordVM

variable {C : Type*}

structure Segment (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget

def Segment.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Segment caller before middle A) (back : Segment caller middle final B) :
    Segment caller before final (A+B) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a := front.count
    have b := back.count
    simp only [List.length_append,List.length_tail]
    omega

theorem front_path (caller : Statement C) (trace : List (SeqCmp.State C))
    (before final : SeqCmp.State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (SeqCmp.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map frontCfg).head?=some (frontCfg before) ∧
    (trace.map frontCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map frontCfg).getLast?=some (frontCfg final) := by
  have proper := NativeMulLink.no_early_halt_port (SeqCmp.program .halt) .done rfl trace final chain last active
  have mapped := LabelMap.actual_path_on frontLabel (SeqCmp.program .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_front caller point (by intro same; subst point; exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem map_path (caller : Statement C) (trace : List (SeqCmp.State C))
    (before final : SeqCmp.State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (SeqCmp.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .emit) :
    (trace.map mapCfg).head?=some (mapCfg before) ∧
    (trace.map mapCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map mapCfg).getLast?=some (mapCfg final) := by
  have proper := no_early_emit trace final chain last active
  have mapped := LabelMap.actual_path_on mapLabel (SeqCmp.program .halt) (program caller)
    trace before final first chain last (by
      intro current member point selected
      exact program_map caller point (by intro same; subst point; exact proper current member selected))
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem output_path (caller : Statement C) (trace : List (WordOutput.State (OutputContext C)))
    (before final : WordOutput.State (OutputContext C)) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (WordOutput.program .halt) a=some b))
    (last : trace.getLast?=some final) (active : final.l=some .done) :
    (trace.map outputCfg).head?=some (outputCfg before) ∧
    (trace.map outputCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (trace.map outputCfg).getLast?=some (outputCfg final) := by
  let old := WordOutput.program (C := OutputContext C) .halt
  let isoProgram := StoreIso.machine (outputIso C) old
  have iso := StoreIso.actual_path_on (outputIso C) old isoProgram trace before final first chain last
    (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port isoProgram .done rfl _ _ iso.2.1 iso.2.2.1 active
  have mapped := LabelMap.actual_path_on outputLabel isoProgram (program caller)
    _ _ _ iso.1 iso.2.1 iso.2.2.1 (by
      intro current member point selected
      exact program_output caller point (by intro same; subst point; exact proper current member selected))
  have maps : (trace.map (StoreIso.configuration (outputIso C))).map (LabelMap.configuration outputLabel)=
      trace.map outputCfg := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

def or_path (caller : Statement C) (memory : Store C) (contents : RatInput.Stack → List Bool)
    (lower upper : Bool) :
    Segment caller
      ⟨some .orFirst,memory,Function.update contents 3 [lower,upper]⟩
      ⟨some (.mapRound (.pair true (.collect 0))),recordOr (record false memory (some lower)) (some upper),
        Function.update contents 3 []⟩ 3 := by
  let before : State C := ⟨some .orFirst,memory,Function.update contents 3 [lower,upper]⟩
  let middle : State C := ⟨some .orSecond,record false memory (some lower),Function.update contents 3 [upper]⟩
  let final : State C := ⟨some (.mapRound (.pair true (.collect 0))),recordOr middle.var (some upper),Function.update contents 3 []⟩
  refine ⟨[before,middle,final],rfl,?_,rfl,Nat.le_refl _⟩
  exact List.isChain_cons_cons.mpr ⟨first_or caller memory contents lower upper,
    List.isChain_cons_cons.mpr ⟨second_or caller middle.var contents upper,List.isChain_singleton _⟩⟩

theorem output_shared (background : RatInput.Stack → List Bool) (before : SeqCmp.State C)
    (r : Rat) (tail scratch : List Bool) (active : before.l=some .emit)
    (contents : before.stk=RatPair.Link.initial background (RatInput.Encoder.packet r tail) scratch) :
    let memory := (outputIso C).symm before.var
    outputCfg (WordOutput.entry (RatPair.Link.clean background) memory.1.1.1 memory.1.1.2.1 memory.1.1.2.2
      memory.1.2 memory.2 r tail scratch)=mapCfg before := by
  cases before with
  | mk position memory cells =>
    change position=some .emit at active
    subst position
    change (⟨some (.serialize (.collect (.collect 0))),outputIso C ((outputIso C).symm memory),_⟩ : State C)=
      ⟨some (.serialize (.collect (.collect 0))),memory,cells⟩
    rw [Equiv.apply_symm_apply]
    congr 1
    exact (output_entry_stacks background ((outputIso C).symm memory) r tail scratch).trans contents.symm

end B23_4_RatWordPrep.SeqCmp.Word
