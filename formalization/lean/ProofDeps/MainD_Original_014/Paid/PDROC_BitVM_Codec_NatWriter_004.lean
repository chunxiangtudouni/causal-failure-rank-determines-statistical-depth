module

public import Paid.PDROC_BitVM_Codec_NatWriter_003
public import Paid.PDROC_BitVM_Common_Occupancy_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Codec.NatWriter

open Turing PaperProofs.Common.Native.RationalControllerComputation

theorem finite_labels_support {Λ σ : Type*} [Fintype Λ] [Inhabited Λ]
    (machine : Λ → TM2.Stmt Alphabet Λ σ) :
    TM2.Supports machine Finset.univ := by
  have every : ∀ code : TM2.Stmt Alphabet Λ σ,
      TM2.SupportsStmt Finset.univ code := by
    intro code
    induction code with
    | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
    | branch _ _ _ yes no => exact ⟨yes, no⟩
    | goto _ => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact ⟨Finset.mem_univ _, fun label _ => every (machine label)⟩

def before (right left target : List Bool) (store : Option Bool) : State :=
  PDROC.BitVM.Native.Inline.cfg (fun _ : Unit => 0) 1 ()
    (PDROC.BitVM.Kernel.NatResult.before right left target store)

def finish (state : State) : State := ⟨none, state.var, state.stk⟩

theorem halt_edge (state : State) (position : state.l = some 9) :
    TM2.step program state = some (finish state) := by
  rcases state with ⟨label, store, contents⟩
  change label = some 9 at position
  subst label
  rfl

/-- This Nat is the proof description of the ALREADY computed native
right half-tape. The code reads and writes actual Bool data, including
zero's real materialized FALSE bits. No answer or prepared workspace is
an extra runtime input. LEFT and target can be arbitrary old lists. -/
theorem build (value : ℕ) (right left target : List Bool) (store : Option Bool)
    (representation : ListBlank.mk right = ListBlank.mk (encodeNat value)) :
    ∃ (after : State) (path : Path (before right left target store) after),
      after.l = none ∧ after.stk = PDROC.BitVM.Log.TwoStack.threeStacks [] []
        (PaperProofs.Paid.Computation.encodeCellBits (.natural value)) ∧
      path.states.length ≤ 32 * (right.length + left.length + target.length + 1) := by
  obtain ⟨padding, physical⟩ := PDROC.BitVM.Kernel.NatResult.canonical_prefix value right representation
  let material := PDROC.BitVM.Kernel.NatResult.padded right
  obtain ⟨materialRun, materialHead, materialChain, materialLast, materialHalt,
    materialSize, _leftFrame, _targetFrame⟩ := PDROC.BitVM.Kernel.NatResult.runs right left target store
  obtain ⟨run0, end0, head0, chain0, last0, return0, data0, var0, size0⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace (fun _ : Unit => 0) 1
      PDROC.BitVM.Kernel.NatResult.program program materialize_agrees materialRun
      (PDROC.BitVM.Kernel.NatResult.before right left target store)
      (PDROC.BitVM.Kernel.NatResult.after right left target) ()
      materialHead materialChain materialLast materialHalt
  let contents1 := PDROC.BitVM.Log.TwoStack.threeStacks material left target
  let start1 : ClearState := ⟨some (), none, contents1⟩
  let final1 : ClearState := ⟨none, none, Function.update contents1 1 []⟩
  obtain ⟨clearL, clearLHead, clearLChain, clearLLast, clearLHalt, clearLSize, _clearLFrame⟩ :=
    clear_runs 1 contents1 none
  obtain ⟨run1, end1, head1, chain1, last1, return1, data1, var1, size1⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace (fun _ : Unit => 1) 2 (clearProgram 1)
      program left_agrees clearL start1 final1 () clearLHead clearLChain clearLLast clearLHalt
  have boundary1 : end0 = PDROC.BitVM.Native.Inline.cfg (fun _ : Unit => 1) 2 () start1 := by
    apply state_eq
    · exact return0
    · exact var0
    · exact data0
  let contents2 := PDROC.BitVM.Log.TwoStack.threeStacks material [] target
  let start2 : ClearState := ⟨some (), none, contents2⟩
  let final2 : ClearState := ⟨none, none, Function.update contents2 2 []⟩
  obtain ⟨clearT, clearTHead, clearTChain, clearTLast, clearTHalt, clearTSize, _clearTFrame⟩ :=
    clear_runs 2 contents2 none
  obtain ⟨run2, end2, head2, chain2, last2, return2, data2, var2, size2⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace (fun _ : Unit => 2) 3 (clearProgram 2)
      program target_agrees clearT start2 final2 () clearTHead clearTChain clearTLast clearTHalt
  have boundary2 : end1 = PDROC.BitVM.Native.Inline.cfg (fun _ : Unit => 2) 3 () start2 := by
    apply state_eq
    · exact return1
    · exact var1
    · change end1.stk = PDROC.BitVM.Log.TwoStack.threeStacks material [] target
      simpa only [final1, contents1, PDROC.BitVM.Native.Copy.update_second] using data1
  obtain ⟨header, headerHead, headerChain, headerLast, headerHalt, headerSize⟩ :=
    header_runs value padding
  obtain ⟨run3, end3, head3, chain3, last3, return3, data3, var3, size3⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace headerLabels 7
      (PDROC.BitVM.Native.Lift.machine headerRoles PDROC.BitVM.Log.Header.program)
      program header_agrees header (headerBefore value padding) (headerAfter value padding) ()
      headerHead headerChain headerLast headerHalt
  have boundary3 : end2 = PDROC.BitVM.Native.Inline.cfg headerLabels 7 () (headerBefore value padding) := by
    apply state_eq
    · exact return2
    · exact var2
    · change end2.stk = PDROC.BitVM.Log.TwoStack.threeStacks (encodeNat value ++ padding) [] []
      simpa only [final2, contents2, PDROC.BitVM.Native.Copy.update_third, material,
        physical] using data2
  let contents4 := PDROC.BitVM.Log.TwoStack.threeStacks padding (encodeNat value).reverse []
  let start4 : ClearState := ⟨some (), none, contents4⟩
  let final4 : ClearState := ⟨none, none, Function.update contents4 0 []⟩
  obtain ⟨clearR, clearRHead, clearRChain, clearRLast, clearRHalt, clearRSize, _clearRFrame⟩ :=
    clear_runs 0 contents4 none
  obtain ⟨run4, end4, head4, chain4, last4, return4, data4, var4, size4⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace (fun _ : Unit => 7) 8 (clearProgram 0)
      program right_agrees clearR start4 final4 () clearRHead clearRChain clearRLast clearRHalt
  have boundary4 : end3 = PDROC.BitVM.Native.Inline.cfg (fun _ : Unit => 7) 8 () start4 := by
    apply state_eq
    · exact return3
    · exact var3
    · exact data3
  let drainStart := drainState (some ()) none (encodeNat value).reverse []
  let drainFinal := drainState none none [] (false :: encodeNat value)
  have drainLast : (drainTrace (encodeNat value).reverse [] none).getLast? = some drainFinal := by
    simpa only [List.reverse_reverse, List.append_nil, drainFinal] using
      drain_last (encodeNat value).reverse [] none
  obtain ⟨run5, end5, head5, chain5, last5, return5, data5, var5, size5⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace (fun _ : Unit => 8) 9 drainProgram
      program drain_agrees (drainTrace (encodeNat value).reverse [] none) drainStart drainFinal ()
      (drain_head _ _ _) (drain_chain _ _ _) drainLast rfl
  have boundary5 : end4 = PDROC.BitVM.Native.Inline.cfg (fun _ : Unit => 8) 9 () drainStart := by
    apply state_eq
    · exact return4
    · exact var4
    · change end4.stk = PDROC.BitVM.Log.TwoStack.threeStacks [] (encodeNat value).reverse []
      simpa only [final4, contents4, PDROC.BitVM.Native.Copy.update_first] using data4
  let part0 : Path (before right left target store) end0 := ⟨run0, head0, chain0, last0⟩
  let part1 : Path end0 end1 := ⟨run1, by rw [boundary1]; exact head1, chain1, last1⟩
  let part2 : Path end1 end2 := ⟨run2, by rw [boundary2]; exact head2, chain2, last2⟩
  let part3 : Path end2 end3 := ⟨run3, by rw [boundary3]; exact head3, chain3, last3⟩
  let part4 : Path end3 end4 := ⟨run4, by rw [boundary4]; exact head4, chain4, last4⟩
  let part5 : Path end4 end5 := ⟨run5, by rw [boundary5]; exact head5, chain5, last5⟩
  let part6 : Path end5 (finish end5) :=
    ⟨[end5, finish end5], rfl,
      List.isChain_cons_cons.mpr ⟨halt_edge end5 return5, List.isChain_singleton _⟩, rfl⟩
  let combined := (((((part0.append part1).append part2).append part3).append part4).append part5).append part6
  have total : combined.states.length ≤ run0.length + run1.length + run2.length + run3.length +
      run4.length + run5.length + 2 := by
    have one := part0.append_length part1
    have two := (part0.append part1).append_length part2
    have three := ((part0.append part1).append part2).append_length part3
    have four := (((part0.append part1).append part2).append part3).append_length part4
    have five := ((((part0.append part1).append part2).append part3).append part4).append_length part5
    have six := (((((part0.append part1).append part2).append part3).append part4).append part5).append_length part6
    dsimp only [part0, part1, part2, part3, part4, part5, part6] at one two three four five six
    simp only [List.length_cons, List.length_nil] at six
    dsimp only [combined, part0, part1, part2, part3, part4, part5, part6]
    omega
  have paddedSize : material.length ≤ right.length + 3 := by
    dsimp only [material]
    cases right with
    | nil => decide
    | cons a rest =>
      cases rest with
      | nil => change 3 ≤ 4; decide
      | cons b rest =>
        cases rest with
        | nil => change 3 ≤ 5; decide
        | cons c rest => simp only [PDROC.BitVM.Kernel.NatResult.padded, List.length_cons]; omega
  have wordSize : (encodeNat value).length = 2 * natBits value + 1 := by
    simp [encodeNat]
    omega
  have physicalSize := congrArg List.length physical
  simp only [List.length_append] at physicalSize
  change material.length = (encodeNat value).length + padding.length at physicalSize
  rw [wordSize] at physicalSize
  have bounded : combined.states.length ≤ 32 * (right.length + left.length + target.length + 1) := by
    rw [size0, materialSize, size1, clearLSize, size2, clearTSize, size3, headerSize,
      size4, clearRSize, size5, drain_length, List.length_reverse] at total
    change _ ≤ 2 + (left.length + 2) + (target.length + 2) + (2 * natBits value + 4) +
      (padding.length + 2) + ((encodeNat value).length + 2) + 2 at total
    omega
  refine ⟨finish end5, combined, rfl, ?_, bounded⟩
  simpa only [finish, drainFinal, drainState, PaperProofs.Paid.Computation.encodeCellBits,
    PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral] using data5

def initialSize (right left target : List Bool) : ℕ := right.length + left.length + target.length

def spaceCoefficient : ℕ := 32 * PDROC.BitVM.Common.sourcePushCap program Finset.univ + 1

/-- Same actual whole writer trace, exact Nat Cell and ALL-state occupied
stack envelope. Bounds are linear in existing physical input lengths. -/
theorem runs (value : ℕ) (right left target : List Bool) (store : Option Bool)
    (representation : ListBlank.mk right = ListBlank.mk (encodeNat value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (before right left target store) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.stk 0 = [] ∧ after.stk 1 = [] ∧
      after.stk 2 = PaperProofs.Paid.Computation.encodeCellBits (.natural value) ∧
      run.length ≤ 32 * (initialSize right left target + 1) ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤
        spaceCoefficient * (initialSize right left target + 1) := by
  obtain ⟨after, path, halted, finalData, time⟩ := build value right left target store representation
  have stopped : TM2.step program after = none := by
    rcases after with ⟨label, finiteStore, contents⟩
    change label = none at halted
    subst label
    rfl
  refine ⟨path.states, after, path.first, path.actual, path.last, stopped, ?_, ?_, ?_, time, ?_⟩
  · rw [finalData]
    rfl
  · rw [finalData]
    rfl
  · rw [finalData]
    rfl
  · have supported : TM2.Supports program Finset.univ :=
      finite_labels_support program
    cases states : path.states with
    | nil =>
      have impossible := path.first
      simp only [states, List.head?_nil, reduceCtorEq] at impossible
    | cons start rest =>
      have first : start = before right left target store := by
        have first := path.first
        rw [states] at first
        exact Option.some.inj first
      have initial : ∀ role, (start.stk role).length ≤ initialSize right left target := by
        rw [first]
        intro role
        fin_cases role <;> simp [before, PDROC.BitVM.Native.Inline.cfg,
          PDROC.BitVM.Kernel.NatResult.before, PDROC.BitVM.Log.TwoStack.threeStacks, initialSize] <;> omega
      have actual := PDROC.BitVM.Common.source_path_occupancy program Finset.univ supported start rest
        (initialSize right left target) (by rw [first]; exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _))
        initial (by rw [← states]; exact path.actual)
      intro state member role
      have bounded := (actual state member).2 role
      have length : rest.length ≤ 32 * (initialSize right left target + 1) := by
        rw [states] at time
        simp only [List.length_cons] at time
        exact Nat.le_trans (by omega) time
      have enlarged := bounded.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)
      dsimp only [spaceCoefficient]
      nlinarith

end PDROC.BitVM.Codec.NatWriter
