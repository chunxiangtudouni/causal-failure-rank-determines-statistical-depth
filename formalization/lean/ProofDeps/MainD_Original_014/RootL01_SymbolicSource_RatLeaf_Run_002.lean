module

public import RootL01_SymbolicSource_RatLeaf_Code_001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.RatLeaf

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation

variable {C : Type*}

abbrev bank := RatInput.Encoder.bank

theorem collect_configuration (background : Bank) (point : RatInput.Label)
    (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch numRev denRev numerator denominator raw left counter : List Bool) :
    collectConfiguration (RatInput.state (bank background [] [] [] [] numerator denominator [] left counter)
      point (context,formatter) memory source scratch numRev denRev raw) =
    (⟨some (collectLabel point),((context,memory),formatter),
      bank background source scratch numRev denRev numerator denominator raw left counter⟩ : State C) := by
  unfold collectConfiguration LabelMap.configuration StoreIso.configuration RatInput.state
  simp only [Option.map_some]
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem actual_collect_bank (caller : Statement C) (background : Bank) (context : C)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (negative : Bool)
    (num den source scratch output : List Bool) :
    ∃ trace : List (State C),
      trace.head? = some ⟨some (.collect 0),((context,memory),formatter),
        bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] [] [] output [] []⟩ ∧
      trace.IsChain (fun a b => TM2.step (program caller) a = some b) ∧
      trace.getLast? = some ⟨some (.collect 4),
        ((context,(PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)),formatter),
        bank background (PSTRSymbolicRatExport.packet negative num den source) scratch num.reverse den.reverse [] []
          (true :: output) [] []⟩ ∧
      trace.length ≤ 3*(num.length+den.length)+11 := by
  let background' := bank background [] [] [] [] [] [] [] [] []
  obtain ⟨trace,first,chain,last,count,_stable⟩ := RatInput.actual_collect .halt background'
    (context,formatter) memory negative num den source scratch [] [] output
  have path := collect_path caller trace _ _ first chain last rfl
  refine ⟨trace.map collectConfiguration,?_,path.2.1,?_,?_⟩
  · rw [path.1,collect_configuration]
    rfl
  · simp only [List.append_nil] at path
    rw [path.2.2,collect_configuration]
    rfl
  · simpa only [List.length_map] using count

theorem actual_reverse (caller : Statement C) (second : Bool) (contents : Bank) (memory : Store C) :
    ∃ trace : List (State C),
      trace.head? = some ⟨some (RatInput.Encoder.reversePort second),memory,contents⟩ ∧
      trace.IsChain (fun a b => TM2.step (program caller) a = some b) ∧
      trace.getLast? = some ⟨some (RatInput.Encoder.reverseReturn second),(memory.1,(false,false)),
        RatInput.Encoder.reverseCells contents second []
          ((contents (RatInput.Encoder.reverseSource second)).reverse ++ contents (RatInput.Encoder.reverseTarget second))⟩ ∧
      trace.length = (contents (RatInput.Encoder.reverseSource second)).length+2 := by
  let background := StackIso.slots (reverseRoles second).symm contents
  let word := contents (RatInput.Encoder.reverseSource second)
  let target := contents (RatInput.Encoder.reverseTarget second)
  let trace := RatOutput.reverseTrace background memory.1 word memory.2 (contents 13) (contents 7) target
  have path := reverse_path caller second background memory.1 word memory.2 (contents 13) (contents 7) target
  refine ⟨trace.map (reverseConfiguration second),?_,path.2.1,?_,?_⟩
  · rw [path.1]
    simp only [reverseConfiguration,background,reverseRoles]
    rw [RatInput.Encoder.reverse_configuration,RatInput.Encoder.reverse_cells_self]
    cases second <;> rfl
  · rw [path.2.2]
    simp only [reverseConfiguration,background,reverseRoles]
    rw [RatInput.Encoder.reverse_configuration]
    cases second <;> rfl
  · rw [List.length_map,RatOutput.reverse_length]

theorem actual_format (caller : Statement C) (second : Bool) (contents : Bank) (memory : Store C)
    (emptyLeft : contents 14 = []) (emptyCounter : contents 12 = []) :
    ∃ trace : List (State C),
      trace.head? = some ⟨some (RatInput.Encoder.formatPort second),memory,contents⟩ ∧
      trace.IsChain (fun a b => TM2.step (program caller) a = some b) ∧
      trace.getLast? = some ⟨some (RatInput.Encoder.formatReturn second),(memory.1,(false,false)),
        RatInput.Encoder.formatCells contents second [] []
          (encodeNat (PSTRTMIncrement009.valueDigits (contents (RatInput.Encoder.reverseTarget second))) ++ contents 13) []⟩ ∧
      trace.length ≤ 4*(contents (RatInput.Encoder.reverseTarget second)).length+11 := by
  let background := StackIso.slots (formatRoles second).symm contents
  let word := contents (RatInput.Encoder.reverseTarget second)
  obtain ⟨trace,first,chain,last,count,_contexts,_bounds,_frames⟩ :=
    WordNatIO.actual_caller_format .halt memory.1 background memory.2 word (contents 13)
  have path := format_path caller second trace _ _ first chain last rfl
  refine ⟨trace.map (formatConfiguration second),?_,path.2.1,?_,?_⟩
  · have same := RatInput.Encoder.format_cells_self contents second
    rw [emptyLeft,emptyCounter] at same
    rw [path.1]
    simp only [formatConfiguration,background,formatRoles]
    rw [RatInput.Encoder.format_configuration,same]
    cases second <;> rfl
  · rw [path.2.2]
    simp only [formatConfiguration,background,formatRoles]
    rw [RatInput.Encoder.format_configuration]
    cases second <;> rfl
  · simpa only [List.length_map] using count

structure Path (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head? = some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a = some b)
  last : trace.getLast? = some final
  count : trace.length ≤ budget

def Path.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Path caller before middle A) (back : Path caller middle final B) : Path caller before final (A+B-1) := by
  have shape : middle :: back.trace.tail = back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]; rfl
  have size := congrArg List.length shape
  simp only [List.length_cons] at size
  refine ⟨front.trace ++ back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a := front.count; have b := back.count
    simp only [List.length_append]
    omega

theorem actual_fields (caller : Statement C) (background : Bank) (context : C)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (negative : Bool)
    (num den source scratch output : List Bool) :
    ∃ trace : List (State C),
      trace.head? = some ⟨some (.collect 0),((context,memory),formatter),
        bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] [] [] output [] []⟩ ∧
      trace.IsChain (fun a b => TM2.step (program caller) a = some b) ∧
      trace.getLast? = some ⟨some .done,
        ((context,(PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)),(false,false)),
        bank background (PSTRSymbolicRatExport.packet negative num den source) scratch [] [] [] []
          (leafPrefix ++ true :: negative :: (encodeNat (PSTRTMIncrement009.valueDigits num) ++
            encodeNat (PSTRTMIncrement009.valueDigits den) ++ output)) [] []⟩ ∧
      trace.length ≤ 8*(num.length+den.length)+35 := by
  let packet := PSTRSymbolicRatExport.packet negative num den source
  let rat : RatInput.Store := (PSTRSymbolicNaturalExport.finalBit (RatOutput.outputLeft negative num den) false,true,negative)
  let encN := encodeNat (PSTRTMIncrement009.valueDigits num)
  let encD := encodeNat (PSTRTMIncrement009.valueDigits den)
  let b0 := bank background packet scratch [] [] [] [] output [] []
  let marked := bank background packet scratch num.reverse den.reverse [] [] (true :: output) [] []
  let b1 := bank background packet scratch num.reverse den.reverse [] [] output [] []
  let b2 := bank background packet scratch [] den.reverse num [] output [] []
  let b3 := bank background packet scratch [] [] num den output [] []
  let b4 := bank background packet scratch [] [] num [] (encD ++ output) [] []
  let b5 := bank background packet scratch [] [] [] [] (encN ++ encD ++ output) [] []
  let b6 := bank background packet scratch [] [] [] [] (leafPrefix ++ true :: negative :: (encN ++ encD ++ output)) [] []
  let s0 : State C := ⟨some (.collect 0),((context,memory),formatter),b0⟩
  let atMark : State C := ⟨some (.collect 4),((context,rat),formatter),marked⟩
  let s1 : State C := ⟨some .reverseNum,((context,rat),formatter),b1⟩
  let s2 : State C := ⟨some .reverseDen,((context,rat),(false,false)),b2⟩
  let s3 : State C := ⟨some (.den 0),((context,rat),(false,false)),b3⟩
  let s4 : State C := ⟨some (.num 0),((context,rat),(false,false)),b4⟩
  let s5 : State C := ⟨some .finish,((context,rat),(false,false)),b5⟩
  let s6 : State C := ⟨some .done,((context,rat),(false,false)),b6⟩
  obtain ⟨t0,h0,c0,l0,n0⟩ := actual_collect_bank caller background context memory formatter negative num den source scratch output
  let p0 : Path caller s0 atMark (3*(num.length+den.length)+11) := ⟨t0,h0,c0,l0,n0⟩
  have strip : TM2.step (program caller) atMark = some s1 := by
    have step := strip_step caller ((context,rat),formatter) marked output rfl
    rw [RatInput.Encoder.bank_update_raw] at step
    exact step
  let ps : Path caller atMark s1 2 :=
    ⟨[atMark,s1],rfl,List.isChain_cons_cons.mpr ⟨strip,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  obtain ⟨t1,h1,c1,l1,n1⟩ := actual_reverse caller false b1 ((context,rat),formatter)
  have last1 : t1.getLast? = some s2 := by
    simpa [b1,s2,b2,RatInput.Encoder.reverse_num_bank,RatInput.Encoder.reverseSource,
      RatInput.Encoder.reverseTarget,RatInput.Encoder.reverseReturn,bank,RatInput.Encoder.bank,
      List.reverse_reverse,List.append_nil] using l1
  let p1 : Path caller s1 s2 (num.length+2) := ⟨t1,h1,c1,last1,by
    simpa [b1,RatInput.Encoder.reverseSource,bank,RatInput.Encoder.bank] using n1.le⟩
  obtain ⟨t2,h2,c2,l2,n2⟩ := actual_reverse caller true b2 ((context,rat),(false,false))
  have last2 : t2.getLast? = some s3 := by
    simpa [b2,s3,b3,RatInput.Encoder.reverse_den_bank,RatInput.Encoder.reverseSource,
      RatInput.Encoder.reverseTarget,RatInput.Encoder.reverseReturn,bank,RatInput.Encoder.bank,
      List.reverse_reverse,List.append_nil] using l2
  let p2 : Path caller s2 s3 (den.length+2) := ⟨t2,h2,c2,last2,by
    simpa [b2,RatInput.Encoder.reverseSource,bank,RatInput.Encoder.bank] using n2.le⟩
  obtain ⟨t3,h3,c3,l3,n3⟩ := actual_format caller true b3 ((context,rat),(false,false)) rfl rfl
  have last3 : t3.getLast? = some s4 := by
    simpa [b3,s4,b4,encD,RatInput.Encoder.format_den_bank,RatInput.Encoder.reverseTarget,
      RatInput.Encoder.formatReturn,bank,RatInput.Encoder.bank] using l3
  let p3 : Path caller s3 s4 (4*den.length+11) := ⟨t3,h3,c3,last3,by
    simpa [b3,RatInput.Encoder.reverseTarget,bank,RatInput.Encoder.bank] using n3⟩
  obtain ⟨t4,h4,c4,l4,n4⟩ := actual_format caller false b4 ((context,rat),(false,false)) rfl rfl
  have last4 : t4.getLast? = some s5 := by
    simpa [b4,s5,b5,encN,RatInput.Encoder.format_num_bank,RatInput.Encoder.reverseTarget,
      RatInput.Encoder.formatReturn,bank,RatInput.Encoder.bank,List.append_assoc] using l4
  let p4 : Path caller s4 s5 (4*num.length+11) := ⟨t4,h4,c4,last4,by
    simpa [b4,RatInput.Encoder.reverseTarget,bank,RatInput.Encoder.bank] using n4⟩
  have finish : TM2.step (program caller) s5 = some s6 := by
    simpa [s5,s6,b5,b6,RatInput.Encoder.bank_update_raw,bank,RatInput.Encoder.bank,
      PSTRSymbolicNaturalExport.positive,rat] using finish_step caller ((context,rat),(false,false)) b5
  let p5 : Path caller s5 s6 2 :=
    ⟨[s5,s6],rfl,List.isChain_cons_cons.mpr ⟨finish,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  let whole := (((((p0.append ps).append p1).append p2).append p3).append p4).append p5
  exact ⟨whole.trace,whole.head,whole.chain,whole.last,by have count := whole.count; omega⟩

def entry (background : Bank) (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (p : Rat) (tail scratch output : List Bool) : State C :=
  ⟨some (.collect 0),((context,memory),formatter),
    bank background (RatInput.Encoder.packet p tail) scratch [] [] [] [] output [] []⟩

def leafBits (p : Rat) : List Bool := (PaperProofs.Common.Native.CompactPrice.encodeExpr
  (.rational p)).flatMap encodeDatum

theorem leafBits_exact (p : Rat) :
    leafBits p = encodeDatum (.natural 0) ++ encodeDatum (.rational p) := by
  simp only [leafBits,PaperProofs.Common.Native.CompactPrice.encodeExpr,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem actual_rational_leaf (caller : Statement C) (background : Bank) (context : C)
    (memory : RatInput.Store) (formatter : WordNatIO.Store) (p : Rat) (tail scratch output : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head? = some (entry background context memory formatter p tail scratch output) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a = some b) ∧
      trace.getLast? = some final ∧ final.l = some .done ∧ final.var.1.1 = context ∧
      final.stk = bank background (RatInput.Encoder.packet p tail) scratch [] [] [] []
        (leafBits p ++ output) [] [] ∧
      trace.length ≤ 8*RatInput.Encoder.fieldSize p+35 := by
  obtain ⟨trace,first,chain,last,count⟩ := actual_fields caller background context memory formatter
    (PA17TMRatArithmeticParse002.sign p) (PA17TMRatArithmeticParse002.numeratorDigits p)
    (PA17TMRatArithmeticParse002.denominatorDigits p) tail scratch output
  refine ⟨trace,_,first,chain,last,rfl,rfl,?_,count⟩
  have encoded : leafPrefix ++ true :: PA17TMRatArithmeticParse002.sign p ::
      (encodeNat (PSTRTMIncrement009.valueDigits (PA17TMRatArithmeticParse002.numeratorDigits p)) ++
        encodeNat (PSTRTMIncrement009.valueDigits (PA17TMRatArithmeticParse002.denominatorDigits p)) ++ output) =
      leafBits p ++ output := by
    rw [PA17TMRatArithmeticParse002.numeratorDigits_value,PA17TMRatArithmeticParse002.denominatorDigits_value]
    simp only [leafBits_exact,leafPrefix,encodeDatum,PA17TMRatArithmeticParse002.sign,
      List.append_assoc,List.cons_append,List.nil_append]
  rw [encoded]
  rfl

end RootL01.SymbolicSource.RatLeaf


