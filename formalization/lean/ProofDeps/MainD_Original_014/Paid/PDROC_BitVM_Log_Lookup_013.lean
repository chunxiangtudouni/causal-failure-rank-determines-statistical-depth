module

public import Paid.PDROC_BitVM_Log_Lookup_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Log.Lookup

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! The fixed whole-VM roles are embedded using the parent lifting library.
No new generic lifting/store machinery and no input-dependent stack types. -/

def heapWorkEmbed : Stack ↪ Fin 32 where
  toFun := fun index => if index = 0 then 21 else if index = 1 then 24
    else if index = 2 then 25 else if index = 3 then 26 else if index = 4 then 27
    else if index = 5 then 28 else 29
  inj' := by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all

abbrev WideState := TM2.Cfg (fun _ : Fin 32 => Bool) Label Store
def wideProgram := Native.Lift.machine heapWorkEmbed program

theorem wide_supports : TM2.Supports wideProgram (Finset.univ : Finset Label) :=
  Native.Lift.supports heapWorkEmbed program (Finset.univ : Finset Label) supports

/-- The ONE chosen local query path is lifted to the fixed32-stack caller.
The remaining25 stacks preserve arbitrary existing Bool data exactly. The
representation premise specifies actual input stacks, never a run oracle. -/
theorem wide_lookup_runs (events : List HeapEvent) (query : ℕ) (result : List Bool)
    (store : Store) (before : WideState)
    (representation : Native.Lift.cfg heapWorkEmbed before =
      state (some gateLabel) store (encodeHistory events) [] (encodeNatBits query) result) :
    ∃ (run : List WideState) (after : WideState),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step wideProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step wideProgram after = none ∧
      after.l = none ∧
      Native.Lift.slots heapWorkEmbed after.stk = slots (encodeHistory events) [] (encodeNatBits query)
        (valueBytes (lookup events query) ++ result) ∧
      (Query.equality after.var.1 && Query.recordTag after.var.1) = (lookup events query).isSome ∧
      (∀ index : Fin 32, (∀ localIndex, heapWorkEmbed localIndex ≠ index) → after.stk index = before.stk index) ∧
      run.length ≤ 100 * (events.length + 1) * ((encodeHistory events).length + 1) := by
  obtain ⟨source, sourceFinal, sourceHead, sourceChain, sourceLast, sourceHalt,
    sourceDone, sourceData, sourceFlag, sourceLength⟩ :=
    chronological_lookup_runs events query result store
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at sourceHead
  | cons first rest =>
    have firstEq : first = state (some gateLabel) store (encodeHistory events) [] (encodeNatBits query) result :=
      Option.some.inj sourceHead
    subst first
    obtain ⟨posts, final, length, chain, last, projected, frame⟩ :=
      Native.Lift.path heapWorkEmbed program before
        (state (some gateLabel) store (encodeHistory events) [] (encodeNatBits query) result)
        sourceFinal rest representation sourceChain sourceLast
    have actualHalt : TM2.step wideProgram final = none := by
      apply Native.Lift.halt_project
      rw [projected]
      exact sourceHalt
    have done : final.l = none :=
      (congrArg (fun current : State => current.l) projected).trans sourceDone
    have data : Native.Lift.slots heapWorkEmbed final.stk =
        slots (encodeHistory events) [] (encodeNatBits query) (valueBytes (lookup events query) ++ result) :=
      (congrArg (fun current : State => current.stk) projected).trans sourceData
    have finalStore : final.var = sourceFinal.var := congrArg (fun current : State => current.var) projected
    refine ⟨before :: posts, final, rfl, chain, last, actualHalt, done, data, ?_, ?_, ?_⟩
    · rw [finalStore]; exact sourceFlag
    · intro index outside
      exact frame index (fun localIndex => Ne.symm (outside localIndex))
    · simp only [List.length_cons] at sourceLength ⊢
      omega

/-- The role list is fixed before the input. Parent frame theorem protects
all non-work stacks, including registers/output/ticks/raw/nativeRight. -/
theorem heapWorkEmbed_not_readonly (index : Fin 32) (low : index.val ≤ 20) :
    ∀ localIndex, heapWorkEmbed localIndex ≠ index := by
  intro localIndex
  fin_cases localIndex <;> simp only [heapWorkEmbed]
  all_goals intro same; have := congrArg Fin.val same; norm_num at this; omega

end PDROC.BitVM.Log.Lookup
