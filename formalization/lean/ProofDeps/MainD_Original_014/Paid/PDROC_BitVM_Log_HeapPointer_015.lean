module

public import Paid.PDROC_BitVM_Log_HeapPointer_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Log.HeapPointer

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

/-- The existing genuine Nat marshaller is selected once and lifted into
the real register/query/scratch roles. Arbitrary other31 stack data carry. -/
theorem source_runs (pointer : Register) (value : ℕ) (contents : Stack → List Bool) (saved : Option Bool)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value))
    (scratch : contents 24 = []) :
    ∃ (run : List SourceState) (after : SourceState),
      run.head? = some (⟨some 0, (saved, ()), contents⟩ : SourceState) ∧
      run.IsChain (fun a b => TM2.step (sourceProgram pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (sourceProgram pointer) after = none ∧
      after.l = none ∧ after.var = (none, ()) ∧
      after.stk = Function.update contents 26 (encodeNatBits value ++ contents 26) ∧
      run.length = 2 * (encodeNatBits value).length + 5 := by
  obtain ⟨source, sourceHead, sourceChain, sourceLast, sourceHalt, sourceLength,
    sourceRegister, sourceQuery, sourceScratch⟩ :=
    Kernel.NatMarshal.official_nat_runs value (contents 26) saved
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = Kernel.NatMarshal.before (encodeNatBits value) (contents 26) saved :=
      Option.some.inj sourceHead
    subst first
    let before : SourceState := ⟨some 0, (saved, ()), contents⟩
    obtain ⟨posts, final, length, chain, last, projected, frame⟩ :=
      Lift.path (embedding pointer) Kernel.NatMarshal.program before
        (Kernel.NatMarshal.before (encodeNatBits value) (contents 26) saved)
        (Kernel.NatMarshal.final (encodeNatBits value) (contents 26)) rest
        (initial_projection pointer value contents saved register scratch) sourceChain sourceLast
    have halt : TM2.step (sourceProgram pointer) final = none := by
      apply Lift.halt_project
      rw [projected]
      exact sourceHalt
    have done : final.l = none := congrArg (fun current : Kernel.NatMarshal.State => current.l) projected
    have savedEq : final.var = (none, ()) := congrArg (fun current : Kernel.NatMarshal.State => current.var) projected
    have localData (index : Fin 3) : final.stk (embedding pointer index) =
        (Kernel.NatMarshal.final (encodeNatBits value) (contents 26)).stk index :=
      congrArg (fun current : Kernel.NatMarshal.State => current.stk index) projected
    have data : final.stk = Function.update contents 26 (encodeNatBits value ++ contents 26) := by
      funext index
      by_cases query : index = 26
      · subst index
        simpa [embedding, Kernel.NatMarshal.final, TwoStack.threeStacks] using localData 1
      · rw [Function.update_of_ne query]
        by_cases sourceSlot : index = registerSlot pointer
        · subst index
          exact (localData 0).trans register.symm
        · by_cases scratchSlot : index = 24
          · subst index
            exact (localData 2).trans scratch.symm
          · exact frame index (by
              intro localIndex
              fin_cases localIndex
              · exact sourceSlot
              · exact query
              · exact scratchSlot)
    refine ⟨before :: posts, final, rfl, chain, last, halt, done, savedEq, data, ?_⟩
    simp only [List.length_cons] at sourceLength ⊢
    omega

/-- One path peeks the real Nat Cell tag, performs the real read/copy/restore
and returns a typed-success flag. Old query bytes remain its real suffix.
Scratch24 is produced empty by the caller's separate genuine clear phase. -/
theorem natural_runs (pointer : Register) (value : ℕ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.natural value))
    (scratch : contents 24 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some 0) store contents) ∧
      run.IsChain (fun a b => TM2.step (program pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer) after = none ∧
      after.l = none ∧ after.var = setTyped ((none, ()), store.2) true ∧
      after.stk = Function.update contents 26 (encodeNatBits value ++ contents 26) ∧
      run.length = 2 * (encodeNatBits value).length + 7 := by
  rcases store with ⟨⟨saved, marker⟩, extra⟩
  cases marker
  let original : Store := ((saved, ()), extra)
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceVar, sourceData, sourceLength⟩ :=
    source_runs pointer value contents (some false) register scratch
  obtain ⟨returned, after, head, chain, last, returnedLabel, data, storeEq, length⟩ :=
    Inline.actual_return_trace marshalLabel 6 (sourceProgram pointer) (program pointer)
      (marshal_agrees pointer) source
      (⟨some 0, (some false, ()), contents⟩ : SourceState)
      sourceFinal extra sourceHead sourceChain sourceLast sourceHalt
  let finalContents := Function.update contents 26 (encodeNatBits value ++ contents 26)
  have finalVar : after.var = ((none, ()), extra) := by rw [storeEq, sourceVar]
  have finalData : after.stk = finalContents := data.trans sourceData
  have afterEq : after = state (some 6) ((none, ()), extra) finalContents := by
    rcases after with ⟨label, vars, current⟩
    change label = some 6 at returnedLabel
    change vars = ((none, ()), extra) at finalVar
    change current = finalContents at finalData
    subst label; subst vars; subst current
    rfl
  have entry : returned.head? = some (state (some (marshalLabel 0)) (saveTag original (some false)) contents) := by
    exact head
  have fieldHead : (contents (registerSlot pointer)).head? = some false := by rw [register]; rfl
  let frontTrace := state (some 0) original contents :: returned
  have frontHead : frontTrace.head? = some (state (some 0) original contents) := rfl
  have frontChain : frontTrace.IsChain (fun a b => TM2.step (program pointer) a = some b) := by
    apply List.IsChain.cons chain
    intro next member
    rw [entry] at member
    have equal := Option.mem_some_iff.mp member
    subst next
    exact guard_nat pointer contents original fieldHead
  have frontLast : frontTrace.getLast? = some (state (some 6) ((none, ()), extra) finalContents) := by
    simp only [frontTrace, List.getLast?_cons, last, afterEq, Option.getD_some]
  let final := state none (setTyped ((none, ()), extra) true) finalContents
  let run := frontTrace ++ [final]
  have actual : run.IsChain (fun a b => TM2.step (program pointer) a = some b) := by
    apply frontChain.append (List.isChain_singleton _)
    intro old ho next hn
    simp only [frontLast, Option.mem_some_iff] at ho
    simp only [List.head?_cons, Option.mem_some_iff] at hn
    subst old; subst next
    exact success_step pointer finalContents ((none, ()), extra)
  refine ⟨run, final, ?_, actual, List.getLast?_append_cons frontTrace final [], rfl, rfl, rfl, rfl, ?_⟩
  · change (frontTrace ++ [final]).head? = some (state (some 0) original contents)
    simp only [List.head?_append, frontHead, Option.some_or]
  · simp only [run, frontTrace, List.length_append, List.length_cons, List.length_nil]
    omega

/-- Rational pointers take a true failure route, with every physical stack
unchanged. The guard does not pop or damage the actual register Cell. -/
theorem rational_runs (pointer : Register) (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (register : contents (registerSlot pointer) = encodeCellBits (.rational value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some 0) store contents) ∧
      run.IsChain (fun a b => TM2.step (program pointer) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer) after = none ∧
      after.l = none ∧ after.var = setTyped (saveTag store (some true)) false ∧
      after.stk = contents ∧ run.length = 3 := by
  let rejected := state (some 7) (saveTag store (some true)) contents
  let final := state none (setTyped (saveTag store (some true)) false) contents
  have fieldHead : (contents (registerSlot pointer)).head? = some true := by rw [register]; rfl
  refine ⟨[state (some 0) store contents, rejected, final], final, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨guard_rat pointer contents store fieldHead, ?_⟩
  exact List.isChain_cons_cons.mpr ⟨invalid_step pointer contents (saveTag store (some true)), List.isChain_singleton _⟩

end PDROC.BitVM.Log.HeapPointer
