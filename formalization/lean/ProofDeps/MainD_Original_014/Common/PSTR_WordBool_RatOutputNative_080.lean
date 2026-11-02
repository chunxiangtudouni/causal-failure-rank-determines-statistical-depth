module

public import Common.PSTR_WordBool_RatOutputLink_079

/-! The SAME073 actual RawSub path followed by its actual original-codec
reader and finite cleanup. Output premises are obtained internally from
the whole Tape; the original caller supplies no new result property. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatOutput.Link

open Turing PSTRWordVM RationalControllerComputation
open PA17TMRatArithmeticAddSubController075 PA17TMRatArithmeticAddSubFull079 PA17TMRatArithmeticParse002

variable {C : Type*}

theorem mass_self (contents : RatOutput.Stack → List Bool) :
    RatOutput.outside contents+(contents 13).length+(contents 14).length+(contents 7).length+(contents 15).length =
      RatOutput.occupied contents := by
  have mass := RatOutput.occupied_state contents 0 () (false,false)
    (contents 13) (contents 14) (contents 7) (contents 15)
  change RatOutput.occupied (RatOutput.cells contents (contents 13) (contents 14) (contents 7) (contents 15)) = _ at mass
  rw [cells_self] at mass
  exact mass.symm

theorem point_mass (contents : RatOutput.Stack → List Bool) (point : RatOutput.Stack) :
    (contents point).length ≤ RatOutput.occupied contents :=
  Finset.single_le_sum (f:=fun other : RatOutput.Stack => (contents other).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ point)

def budget (background : RatOutput.Stack → List Bool) (p : Rat) : Nat :=
  IsolatedRat.outside background + IsolatedRat.rawBudget p

theorem actual_prior_output (caller : Statement C controllerCap) (context : C) (readerMemory : RatOutput.Store)
    (nativeMemory : BoolOnStacks.Store controllerCap) (background : RatOutput.Stack → List Bool) (p : Rat) :
    ∃ (trace : List (State C controllerCap)) (final : State C controllerCap),
      trace.head? = some (nativeConfiguration (IsolatedRat.entry (context,readerMemory) nativeMemory background
        (encode [.rational 1,.rational p]))) ∧
      trace.IsChain (fun a b => TM2.step (program subMachine caller) a = some b) ∧
      trace.getLast? = some final ∧ final.l = some 10 ∧ final.var.1.1 = context ∧
      final.stk 13 = [] ∧ final.stk 14 = [] ∧ final.stk 7 = background 7 ∧
      final.stk 15 = PSTRSymbolicRatExport.packet (sign (1-p)) (numeratorDigits (1-p)) (denominatorDigits (1-p)) (background 15) ∧
      (∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 15 → final.stk slot = background slot) ∧
      trace.length ≤ 4*budget background p+20 ∧
      (∀ current ∈ trace, current.var.1.1 = context ∧
        (∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
        RatOutput.occupied current.stk ≤ budget background p+8) ∧
      ∀ current ∈ trace.dropLast, current.l ≠ some 10 := by
  obtain ⟨native,rawFinal,nHead,nChain,nLast,nActive,nTape,nCount,nBounds,_nProper,_nInternal⟩ :=
    IsolatedRat.actual_prior_complement (.halt : IsolatedRat.Statement (C × RatOutput.Store) controllerCap)
      (context,readerMemory) nativeMemory background p
  have finalBound := nBounds rawFinal (List.mem_of_getLast? nLast)
  have finalContext : rawFinal.var.1.1 = context := congrArg Prod.fst finalBound.1
  have nativeMass : RatOutput.occupied rawFinal.stk ≤ budget background p := finalBound.2.2
  have sameRight : ListBlank.mk (rawFinal.stk 13) = ListBlank.mk (encode [.rational (1-p)]) := by
    have tape := congrArg Tape.right₀ nTape
    simpa only [IsolatedRat.represented,Tape.mk₁,Tape.mk₂,Tape.mk'_right₀] using tape
  let rBefore := RatOutput.state rawFinal.stk 0 (rawFinal.var.1.1,rawFinal.var.2) rawFinal.var.1.2
    (rawFinal.stk 13) (rawFinal.stk 14) (rawFinal.stk 7) (rawFinal.stk 15)
  let result := PSTRSymbolicRatExport.packet (sign (1-p)) (numeratorDigits (1-p)) (denominatorDigits (1-p)) (rawFinal.stk 15)
  let rFinal := RatOutput.state rawFinal.stk 8 (rawFinal.var.1.1,rawFinal.var.2) (false,false) [] [] (rawFinal.stk 7) result
  obtain ⟨reader,rHead,rChain,rLast,rCount,rBounds⟩ := RatOutput.actual_singleton_reader
    (.halt : RatOutput.Statement (C × BoolOnStacks.Store controllerCap)) rawFinal.stk
    (rawFinal.var.1.1,rawFinal.var.2) rawFinal.var.1.2 (1-p)
    (rawFinal.stk 13) (rawFinal.stk 14) (rawFinal.stk 7) (rawFinal.stk 15) sameRight
  have readHead : reader.head? = some rBefore := rHead
  have readLast : reader.getLast? = some rFinal := rLast
  have shared : readerConfiguration rBefore = nativeConfiguration rawFinal := shared_configuration rawFinal nActive
  have linkedN := native_path subMachine caller native _ rawFinal nHead nChain nLast nActive
  have linkedR := reader_path subMachine caller reader rBefore rFinal readHead rChain readLast rfl
  have decomposed : nativeConfiguration rawFinal :: (reader.map readerConfiguration).tail = reader.map readerConfiguration := by
    have head : (reader.map readerConfiguration).head? = some (nativeConfiguration rawFinal) :=
      linkedR.1.trans (congrArg some shared)
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp head
    rw [same]
    rfl
  let trace := native.map nativeConfiguration ++ (reader.map readerConfiguration).tail
  have actual : ∀ finish : Statement C controllerCap,
      trace.IsChain (fun a b => TM2.step (program subMachine finish) a = some b) := by
    intro finish
    have front := native_path subMachine finish native _ rawFinal nHead nChain nLast nActive
    have back := reader_path subMachine finish reader rBefore rFinal readHead rChain readLast rfl
    exact NativeTrace.join_chain _ _ _ front.2.2 front.2.1 (decomposed.symm ▸ back.2.1)
  have last : trace.getLast? = some (readerConfiguration rFinal) :=
    (NativeTrace.join_last _ _ _ linkedN.2.2).trans (decomposed.symm ▸ linkedR.2.2)
  have active : (readerConfiguration rFinal).l = some 10 := rfl
  have frames : ∀ current ∈ trace, current.var.1.1 = context ∧
      (∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
      RatOutput.occupied current.stk ≤ budget background p+8 := by
    intro current member
    rcases List.mem_append.mp member with front | back
    · obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp front
      have source := nBounds old oldMember
      refine ⟨congrArg Prod.fst source.1,?_,?_⟩
      · intro slot notR notL _notC _notT
        exact source.2.1 slot notR notL
      · exact source.2.2.trans (Nat.le_add_right _ _)
    · obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp (List.mem_of_mem_tail back)
      have source := rBounds old oldMember
      refine ⟨(congrArg Prod.fst source.1).trans finalContext,?_,?_⟩
      · intro slot notR notL notC notT
        exact (source.2.1 slot notR notL notC notT).trans (finalBound.2.1 slot notR notL)
      · have mass := source.2.2
        rw [mass_self] at mass
        exact mass.trans (Nat.add_le_add_right nativeMass 8)
  refine ⟨trace,readerConfiguration rFinal,?_,actual caller,last,active,finalContext,rfl,rfl,?_,?_,?_,?_,frames,
    NativeMulLink.no_early_halt_port (program subMachine .halt) 10 rfl trace _ (actual .halt) last active⟩
  · rw [List.head?_append,linkedN.1]
    rfl
  · exact finalBound.2.1 7 (by decide) (by decide)
  · exact congrArg (PSTRSymbolicRatExport.packet (sign (1-p)) (numeratorDigits (1-p)) (denominatorDigits (1-p)))
      (finalBound.2.1 15 (by decide) (by decide))
  · intro slot notR notL notT
    by_cases atC : slot = 7
    · subst slot
      exact finalBound.2.1 7 (by decide) (by decide)
    · change RatOutput.cells rawFinal.stk [] [] (rawFinal.stk 7) result slot = background slot
      simp only [RatOutput.cells,notR,notL,atC,notT,ite_false]
      exact finalBound.2.1 slot notR notL
  · have rightSize := (point_mass rawFinal.stk 13).trans nativeMass
    have leftSize := (point_mass rawFinal.stk 14).trans nativeMass
    have readSize := rCount
    have nativeSize := nCount
    have base : IsolatedRat.rawBudget p ≤ budget background p := Nat.le_add_left _ _
    dsimp only [trace]
    simp only [List.length_append,List.length_map,List.length_tail]
    omega

end PaperProofs.Common.Native.PSTRWordBool.RatOutput.Link
