module

public import RootB234_PrepExponent_GlobalArithmetic035
public import PSTR_WordBool_RatCmp_Run_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM PA17TMRatArithmeticParse002
open RootL01.SymbolicSource
variable {C : Type*}

theorem reader_bank (background : Stack → List Bool) (cache exponent input result : List Bool) :
    RatCmp.Reader.cells (bank background cache exponent [] [] [] []) input result=
      bank background cache exponent input [] [] result := by
  funext slot
  fin_cases slot <;> rfl

theorem reader_state (background : Stack → List Bool) (cache exponent : List Bool) (point : RatCmp.Reader.Label)
    (context : Arithmetic.ReaderContext (PacketUnary.Store C)) (flags : RatCmp.Reader.Store) (input result : List Bool) :
    LabelMap.configuration readerLabel (StoreIso.configuration (readerIso C)
      (RatCmp.Reader.state (bank background cache exponent [] [] [] []) point context flags input result))=
      state (readerLabel point) (readerIso C (context,flags)) (bank background cache exponent input [] [] result) := by
  unfold LabelMap.configuration StoreIso.configuration RatCmp.Reader.state state
  rw [reader_bank]
  rfl

theorem reader_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (value : Rat) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.reader 0) memory (bank background cache exponent (RatInput.Encoder.packet value []) [] [] []))
      (state .branch afterMemory (bank background cache exponent [] [] [] [decide (value≤0)]))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧ afterMemory.2=memory.2 ∧
      part.trace.length ≤ RatInput.Encoder.fieldSize value+5 := by
  let m := (readerIso C).symm memory
  let flags : RatCmp.Reader.Store := (sign value,RatCmp.Reader.anyTrue (numeratorDigits value),false)
  let afterMemory := readerIso C (m.1,flags)
  obtain ⟨run,first,chain,last,count,_contexts⟩ := RatCmp.Reader.actual_packet .halt
    (bank background cache exponent [] [] [] []) m.1 m.2 (sign value)
    (numeratorDigits value) (denominatorDigits value) [] []
  have path := store_label_path (readerIso C) readerLabel (RatCmp.Reader.program .halt) caller 4 rfl
    run _ _ first chain last rfl (by intro point different;simp only [readerLabel,different,ite_false,program])
  have vars : readerIso C (m.1,m.2)=memory := Equiv.apply_symm_apply (readerIso C) memory
  have firstState := reader_state background cache exponent 0 m.1 m.2 (RatInput.Encoder.packet value []) []
  rw [vars] at firstState
  have bit : (sign value || !RatCmp.Reader.anyTrue (numeratorDigits value))=decide (value≤0) :=
    RatCmp.Reader.decision_nonpos value
  have lastState := reader_state background cache exponent 4 m.1 flags []
    [sign value || !RatCmp.Reader.anyTrue (numeratorDigits value)]
  have startName : readerLabel 0=.reader 0 := rfl
  have endName : readerLabel 4=.branch := rfl
  rw [startName] at firstState
  rw [endName] at lastState
  have endpoint : state .branch (readerIso C (m.1,flags))
      (bank background cache exponent [] [] [] [sign value || !RatCmp.Reader.anyTrue (numeratorDigits value)])=
      state .branch afterMemory (bank background cache exponent [] [] [] [decide (value≤0)]) := by rw [bit]
  refine ⟨afterMemory,⟨run.map (fun current => LabelMap.configuration readerLabel (StoreIso.configuration (readerIso C) current)),
    path.1.trans (congrArg some firstState),path.2.1,path.2.2.trans (congrArg some (lastState.trans endpoint))⟩,?_,?_,?_⟩
  · have same : QLoop.rootContext afterMemory=QLoop.rootContext (readerIso C (m.1,m.2)) := rfl
    exact same.trans (congrArg QLoop.rootContext vars)
  · have same : afterMemory.2=(readerIso C (m.1,m.2)).2 := rfl
    exact same.trans (congrArg Prod.snd vars)
  · simpa only [List.length_map,RatInput.Encoder.fieldSize] using count

theorem reader_compare_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache exponent : List Bool) (x y : Rat) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.reader 0) memory (bank background cache exponent (RatInput.Encoder.packet (x-y) []) [] [] []))
      (state .branch afterMemory (bank background cache exponent [] [] [] [decide (x≤y)]))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧ afterMemory.2=memory.2 ∧
      part.trace.length ≤ RatInput.Encoder.fieldSize (x-y)+5 := by
  obtain ⟨afterMemory,part,context,flags,count⟩ := reader_actual caller background memory cache exponent (x-y)
  have endpoint : state .branch afterMemory (bank background cache exponent [] [] [] [decide (x-y≤0)])=
      state .branch afterMemory (bank background cache exponent [] [] [] [decide (x≤y)]) := by simp only [sub_nonpos]
  exact ⟨afterMemory,⟨part.trace,part.first,part.chain,part.last.trans (congrArg some endpoint)⟩,context,flags,count⟩

theorem increment_bank (background : Stack → List Bool) (cache source : List Bool) :
    NatIncrement.bank (bank background cache [] [] [] [] []) source []=bank background cache source [] [] [] [] := by
  funext slot
  fin_cases slot <;> rfl

theorem increment_state (background : Stack → List Bool) (cache source : List Bool)
    (point : NatIncrement.Label) (memory : Store C) :
    LabelMap.configuration incrementLabel
      (NatIncrement.state (bank background cache [] [] [] [] []) point memory.1 memory.2 source [])=
      state (incrementLabel point) memory (bank background cache source [] [] [] []) := by
  unfold LabelMap.configuration NatIncrement.state state
  rw [increment_bank]
  rfl

theorem increment_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache : List Bool) (number : Nat) :
    ∃ part : Segment caller
      (state (.increment 0) memory (bank background cache (B23_4_RatWordPrep.NatField.packet number []) [] [] [] []))
      (state (.packet .compareCopyY 0) (memory.1,false,false)
        (bank background cache (B23_4_RatWordPrep.NatField.packet (number+1) []) [] [] [] [])),
      part.trace.length ≤ 3*(PSTRTMNatValue017.rawPayload number).length+3 := by
  obtain ⟨run,first,chain,last,count⟩ := NatIncrement.actual_natural .halt
    (bank background cache [] [] [] [] []) memory.1 memory.2 number []
  have path := label_path incrementLabel (NatIncrement.program .halt) caller 4 rfl run _ _ first chain last rfl
    (by intro point different;simp only [incrementLabel,different,ite_false,program])
  have firstState := increment_state background cache (B23_4_RatWordPrep.NatField.packet number []) 0 memory
  have lastState := increment_state background cache (B23_4_RatWordPrep.NatField.packet (number+1) []) 4 (memory.1,false,false)
  have startName : incrementLabel 0=.increment 0 := rfl
  have endName : incrementLabel 4=.packet .compareCopyY 0 := rfl
  rw [startName] at firstState
  rw [endName] at lastState
  exact ⟨⟨run.map (LabelMap.configuration incrementLabel),path.1.trans (congrArg some firstState),
    path.2.1,path.2.2.trans (congrArg some lastState)⟩,by simpa only [List.length_map] using count⟩

theorem bank_update3 (background : Stack → List Bool) (cache exponent input left right result next : List Bool) :
    Function.update (bank background cache exponent input left right result) 3 next=
      bank background cache exponent input left right next := by
  funext slot
  fin_cases slot <;> rfl

theorem branch_step (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache exponent input : List Bool) (bit : Bool) :
    TM2.step (program caller) (state .branch memory (bank background cache exponent input [] [] [bit]))=
      some (state (if bit then .packet .stopDropY 0 else .packet .repeatCopyY 0) (memory.1,true,bit)
        (bank background cache exponent input [] [] [])) := by
  cases bit with
  | false =>
    change some (state (.packet .repeatCopyY 0) (memory.1,true,false)
      (Function.update (bank background cache exponent input [] [] [false]) 3 []))=_
    rw [bank_update3,ite_eq_right (by decide : ¬((false : Bool)=true))]
  | true =>
    change some (state (.packet .stopDropY 0) (memory.1,true,true)
      (Function.update (bank background cache exponent input [] [] [true]) 3 []))=_
    rw [bank_update3,ite_eq_left (rfl : (true : Bool)=true)]

end RootB234.PrepExponent.Global
