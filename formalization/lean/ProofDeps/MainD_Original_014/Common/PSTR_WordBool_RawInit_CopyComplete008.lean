module

public import Common.PSTR_WordBool_RawInit_CopyLoop007

/-! Full finite86-control copier on the actual parsed outer-header layout.
The unread head bit is read by code, held in finite control and restored.
Two far-left zero cells are ListBlank equalities of the original initial
blank tape, never a new caller qualification. The final tape retains both
the unchanged work digits and their actual far-left read-only copy. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMRawNat010 PSTRTMIncrement009 PSTRTMSeq005

def coreInitial (digits tail : List Bool) : MachineState 41 :=
  coreState 0 ((false :: bank digits) ++ [false,false]) (false :: tail)

def coreTrace (digits tail : List Bool) : List (MachineState 41) :=
  [coreInitial digits tail,
   coreState 1 (bank digits ++ [false,false]) (false :: false :: tail)] ++
    loopTrace digits.reverse [] tail

theorem core_head (digits tail : List Bool) :
    (coreTrace digits tail).head? = some (coreInitial digits tail) := rfl

theorem core_last (digits tail : List Bool) :
    (coreTrace digits tail).getLast? = some (coreFinal digits tail) := by
  have app := List.getLast?_append
    (l := [coreInitial digits tail, coreState 1 (bank digits ++ [false,false]) (false :: false :: tail)])
    (l' := loopTrace digits.reverse [] tail)
  rw [loop_last, Option.some_or] at app
  simpa only [coreTrace, List.reverse_reverse, List.append_nil] using app

theorem core_length (digits tail : List Bool) :
    (coreTrace digits tail).length = 4 * digits.length^2 + 16 * digits.length + 5 := by
  simp only [coreTrace, List.length_append, List.length_cons, List.length_nil,
    loop_length, List.length_reverse]
  ring

theorem core_chain (digits tail : List Bool) :
    (coreTrace digits tail).IsChain
      (fun before after => TM0.step coreMachine before = some after) := by
  change ([coreInitial digits tail,
    coreState 1 (bank digits ++ [false,false]) (false :: false :: tail)] ++
      loopTrace digits.reverse [] tail).IsChain _
  apply List.IsChain.append
  · apply List.isChain_cons_cons.mpr
    refine ⟨?_, .singleton _⟩
    simp [coreInitial, coreState, TM0.step, coreMachine, Tape.mk₂]
  · exact loop_chain digits.reverse [] tail
  · intro before beforeLast after afterHead
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
    simp only [loop_head, Option.mem_some_iff] at afterHead
    subst before
    subst after
    cases shape : digits.reverse <;>
      simp [loopStart, bank, shape, workRight, blocks, leftBlocks, coreState,
        TM0.step, coreMachine, Tape.mk₂]

theorem core_runsFrom (digits tail : List Bool) :
    RunsFrom coreMachine (coreInitial digits tail) (coreTrace digits tail) (coreFinal digits tail) :=
  ⟨core_head digits tail, core_chain digits tail, core_last digits tail, core_final_halt digits tail⟩

theorem tape_pad (left right : List Bool) :
    Tape.mk₂ (left ++ [false,false]) right = Tape.mk₂ left right := by
  have pad : ListBlank.mk (left ++ [false,false]) = ListBlank.mk left := by
    calc
      ListBlank.mk (left ++ [false,false]) =
          ListBlank.mk ((left ++ [false]) ++ [false]) := by simp only [List.append_assoc, List.cons_append, List.nil_append]
      _ = ListBlank.mk left := (blank_append_false (left ++ [false])).trans (blank_append_false left)
  change Tape.mk' (ListBlank.mk (left ++ [false,false])) (ListBlank.mk right) =
    Tape.mk' (ListBlank.mk left) (ListBlank.mk right)
  rw [pad]

def copyInitial (digits : List Bool) (originalHead : Bool) (tail : List Bool) : MachineState 85 :=
  state 0 (false :: bank digits) (originalHead :: tail)

def copyFinal (digits : List Bool) (originalHead : Bool) (tail : List Bool) : MachineState 85 :=
  state 85 (false :: (bank digits ++ false :: false :: bank digits)) (originalHead :: tail)

private theorem lifted_initial_eq (digits tail : List Bool) (originalHead : Bool) :
    bodyCfg originalHead (coreInitial digits tail) =
      state (bodyLabel originalHead 0) (false :: bank digits) (false :: tail) := by
  change (⟨bodyLabel originalHead 0,
    Tape.mk₂ ((false :: bank digits) ++ [false,false]) (false :: tail)⟩ : MachineState 85) = _
  exact congrArg (fun tape : Tape Bool => (⟨bodyLabel originalHead 0, tape⟩ : MachineState 85))
    (tape_pad (false :: bank digits) (false :: tail))

def copyTrace (digits : List Bool) (originalHead : Bool) (tail : List Bool) : List (MachineState 85) :=
  [copyInitial digits originalHead tail] ++
    (coreTrace digits tail).map (bodyCfg originalHead) ++ [copyFinal digits originalHead tail]

theorem copy_head (digits : List Bool) (originalHead : Bool) (tail : List Bool) :
    (copyTrace digits originalHead tail).head? = some (copyInitial digits originalHead tail) := rfl

theorem copy_last (digits : List Bool) (originalHead : Bool) (tail : List Bool) :
    (copyTrace digits originalHead tail).getLast? = some (copyFinal digits originalHead tail) := by
  have app := List.getLast?_append
    (l := [copyInitial digits originalHead tail] ++ (coreTrace digits tail).map (bodyCfg originalHead))
    (l' := [copyFinal digits originalHead tail])
  rw [List.getLast?_singleton, Option.some_or] at app
  exact app

theorem copy_length (digits : List Bool) (originalHead : Bool) (tail : List Bool) :
    (copyTrace digits originalHead tail).length = 4 * digits.length^2 + 16 * digits.length + 7 := by
  simp only [copyTrace, List.length_append, List.length_cons, List.length_nil,
    List.length_map, core_length]
  omega

theorem copy_chain (digits : List Bool) (originalHead : Bool) (tail : List Bool) :
    (copyTrace digits originalHead tail).IsChain
      (fun before after => TM0.step machine before = some after) := by
  let body := (coreTrace digits tail).map (bodyCfg originalHead)
  have firstBody : body.head? = some (bodyCfg originalHead (coreInitial digits tail)) := by
    simp only [body, List.head?_map, core_head, Option.map_some]
  have lastBody : body.getLast? = some (bodyCfg originalHead (coreFinal digits tail)) := by
    simp only [body, List.getLast?_map, core_last, Option.map_some]
  have mapped : body.IsChain (fun before after => TM0.step machine before = some after) := by
    apply (List.isChain_map _).mpr
    exact (core_chain digits tail).imp (fun before after edge => by rw [body_step, edge])
  have prefixChain : ([copyInitial digits originalHead tail] ++ body).IsChain
      (fun before after => TM0.step machine before = some after) := by
    apply List.IsChain.append (.singleton _) mapped
    intro before beforeLast after afterHead
    simp only [List.getLast?_singleton, Option.mem_some_iff] at beforeLast
    simp only [firstBody, Option.mem_some_iff] at afterHead
    subst before
    subst after
    simpa only [copyInitial, lifted_initial_eq] using
      capture_step (false :: bank digits) tail originalHead
  have lastPrefix : ([copyInitial digits originalHead tail] ++ body).getLast? =
      some (bodyCfg originalHead (coreFinal digits tail)) := by
    have app := List.getLast?_append (l := [copyInitial digits originalHead tail]) (l' := body)
    rw [lastBody, Option.some_or] at app
    exact app
  change (([copyInitial digits originalHead tail] ++ body) ++ [copyFinal digits originalHead tail]).IsChain _
  apply List.IsChain.append prefixChain (.singleton _)
  intro before beforeLast after afterHead
  simp only [lastPrefix, Option.mem_some_iff] at beforeLast
  simp only [List.head?_singleton, Option.mem_some_iff] at afterHead
  subst before
  subst after
  have returned := body_step originalHead (coreFinal digits tail)
  rw [core_final_halt] at returned
  simpa [copyFinal, coreFinal, coreState, state, Tape.mk₂] using returned

theorem copy_runsFrom (digits : List Bool) (originalHead : Bool) (tail : List Bool) :
    RunsFrom machine (copyInitial digits originalHead tail) (copyTrace digits originalHead tail)
      (copyFinal digits originalHead tail) :=
  ⟨copy_head digits originalHead tail, copy_chain digits originalHead tail,
    copy_last digits originalHead tail, final_halt _ _⟩

theorem actual (digits : List Bool) (originalHead : Bool) (tail : List Bool) (inputLength : Nat) :
    ∃ trace, RunsFrom machine (copyInitial digits originalHead tail) trace (copyFinal digits originalHead tail) ∧
      trace.length ≤ 64 * (digits.length + 1)^2 ∧
      ∀ clock, visitedSpace machine inputLength (trace.take clock) ≤
        inputLength + 128 * (digits.length + 1)^2 + 1 := by
  have time : (copyTrace digits originalHead tail).length ≤ 64 * (digits.length + 1)^2 := by
    rw [copy_length]
    nlinarith [Nat.zero_le (digits.length^2)]
  refine ⟨copyTrace digits originalHead tail, copy_runsFrom digits originalHead tail, time, ?_⟩
  intro clock
  have space := PSTRTMTrace002.visitedSpace_le machine inputLength
    ((copyTrace digits originalHead tail).take clock)
  have short : ((copyTrace digits originalHead tail).take clock).length ≤
      (copyTrace digits originalHead tail).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.HeaderCopy
