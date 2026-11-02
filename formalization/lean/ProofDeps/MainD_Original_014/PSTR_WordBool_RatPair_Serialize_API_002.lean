module

public import PSTR_WordBool_RatPair_Serialize_Resources_002

/-! Actual four-field serializer with its same-trace linear resources.
The source is fixed before all signs/lists, and the Rat instance is ALL x,y. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def fieldSize2 (nx dx ny dy : List Bool) : Nat := nx.length+dx.length+ny.length+dy.length

def space2 (background : RatInput.Stack → List Bool) (nx dx ny dy : List Bool) : Nat :=
  outside2 background+(background 7).length+(background 15).length+161*fieldSize2 nx dx ny dy+1920

structure Facts2 (caller : Statement C) (background : RatInput.Stack → List Bool)
    (context : C) (negativeX negativeY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (nx dx ny dy : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head? = some (entry background context negativeX negativeY memory formatter nx dx ny dy)
  chain : trace.IsChain (fun a b => TM2.step (program2 caller) a = some b)
  last : trace.getLast? = some final
  active : final.l = some .done
  context_eq : final.var.1.1 = (context,negativeX,negativeY)
  contents : final.stk = bank background [] [] [] [] [] [] (output2 negativeX negativeY nx dx ny dy) [] []
  time : trace.length ≤ 5*fieldSize2 nx dx ny dy+60
  boundaries : ∀ current∈trace,
    (∀ slot,(current.stk slot).length ≤ space2 background nx dx ny dy) ∧
    RatInput.occupied current.stk ≤ 16*space2 background nx dx ny dy ∧
    ∀ slot,¬Work2 slot → current.stk slot = background slot
  proper : ∀ current∈trace.dropLast, current.l ≠ some .done ∧
    ∀ point,current.l = some point →
      (∀ node∈AuxWorkspace.nodes (program2 caller point) current.var current.stk,
        (∀ slot,(node.2 slot).length ≤ space2 background nx dx ny dy+32) ∧
        ∀ slot,¬Work2 slot → node.2 slot = background slot) ∧
      ScannerStatement.clock (program2 caller point) current.var current.stk ≤
        64*(space2 background nx dx ny dy+33)

theorem actual_fields_resources2 (caller : Statement C) (background : RatInput.Stack → List Bool)
    (context : C) (negativeX negativeY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (nx dx ny dy : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      Facts2 caller background context negativeX negativeY memory formatter nx dx ny dy trace final := by
  obtain ⟨trace,first,chain,last,count⟩ :=
    actual_fields2 .halt background context negativeX negativeY memory formatter nx dx ny dy
  let before := entry background context negativeX negativeY memory formatter nx dx ny dy
  let final : State C := ⟨some .done,
    (((context,negativeX,negativeY),(memory.1,memory.2.1,negativeX)),(false,false)),
    bank background [] [] [] [] [] [] (output2 negativeX negativeY nx dx ny dy) [] []⟩
  have proper := NativeMulLink.no_early_halt_port (program2 .halt) .done rfl trace final chain last rfl
  have mass : RatInput.occupied before.stk =
      outside2 background+(background 7).length+(background 15).length+fieldSize2 nx dx ny dy := by
    dsimp only [before,entry]
    rw [occupied_bank2]
    simp only [List.length_reverse,List.length_nil,Nat.add_zero]
    dsimp only [fieldSize2]
    omega
  have frames : ∀ slot,¬Work2 slot → before.stk slot = background slot := by
    intro slot untouched
    exact bank_frame2 _ _ _ _ _ _ _ _ _ _ slot untouched
  have bounds := trace_resources2 trace before background (RatInput.occupied before.stk) first chain
    (RatInput.Encoder.point_mass before.stk) frames
  have linear : RatInput.occupied before.stk+32*trace.length ≤ space2 background nx dx ny dy := by
    rw [mass]
    change trace.length ≤ 5*fieldSize2 nx dx ny dy+60 at count
    dsimp only [space2]
    omega
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length ≤ space2 background nx dx ny dy :=
    fun current member slot => ((bounds current member).1 slot).trans linear
  refine ⟨trace,final,{
    first := first
    chain := chain_caller2 caller trace chain proper
    last := last
    active := rfl
    context_eq := rfl
    contents := rfl
    time := count
    boundaries := ?_
    proper := ?_ }⟩
  · intro current member
    exact ⟨bounded current member,
      RatInput.Encoder.occupied_bound current.stk _ (bounded current member),
      (bounds current member).2⟩
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have notDone : point ≠ .done := by intro same;subst point;exact proper current member selected
    rw [program_proper2 caller point notDone]
    have internal := internal_resources2 current point _ (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,internal.2⟩
    intro node nodeMember
    have nodeFacts := internal.1 node nodeMember
    refine ⟨nodeFacts.1,?_⟩
    intro slot untouched
    exact (nodeFacts.2 slot untouched).trans ((bounds current (List.mem_of_mem_dropLast member)).2 slot untouched)

theorem output_original2 (x y : Rat) :
    output2 (PA17TMRatArithmeticParse002.sign x) (PA17TMRatArithmeticParse002.sign y)
      (PA17TMRatArithmeticParse002.numeratorDigits x) (PA17TMRatArithmeticParse002.denominatorDigits x)
      (PA17TMRatArithmeticParse002.numeratorDigits y) (PA17TMRatArithmeticParse002.denominatorDigits y) =
      encode [.rational x,.rational y] := by
  unfold output2 datumBits fields
  rw [PA17TMRatArithmeticParse002.numeratorDigits_value,PA17TMRatArithmeticParse002.denominatorDigits_value,
    PA17TMRatArithmeticParse002.numeratorDigits_value,PA17TMRatArithmeticParse002.denominatorDigits_value]
  simp only [encode,encodeDatum,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.append_assoc,List.cons_append,List.nil_append,PA17TMRatArithmeticParse002.sign]

theorem actual_rats2 (caller : Statement C) (background : RatInput.Stack → List Bool)
    (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store) (x y : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      Facts2 caller background context (PA17TMRatArithmeticParse002.sign x) (PA17TMRatArithmeticParse002.sign y)
        memory formatter (PA17TMRatArithmeticParse002.numeratorDigits x) (PA17TMRatArithmeticParse002.denominatorDigits x)
        (PA17TMRatArithmeticParse002.numeratorDigits y) (PA17TMRatArithmeticParse002.denominatorDigits y) trace final ∧
      final.stk 13 = encode [.rational x,.rational y] := by
  obtain ⟨trace,final,facts⟩ := actual_fields_resources2 caller background context
    (PA17TMRatArithmeticParse002.sign x) (PA17TMRatArithmeticParse002.sign y) memory formatter
    (PA17TMRatArithmeticParse002.numeratorDigits x) (PA17TMRatArithmeticParse002.denominatorDigits x)
    (PA17TMRatArithmeticParse002.numeratorDigits y) (PA17TMRatArithmeticParse002.denominatorDigits y)
  refine ⟨trace,final,facts,?_⟩
  rw [facts.contents]
  change output2 _ _ _ _ _ _ = _
  exact output_original2 x y

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer

#print axioms PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer.actual_fields2
#print axioms PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer.actual_fields_resources2
#print axioms PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer.output_original2
#print axioms PaperProofs.Common.Native.PSTRWordBool.RatPair.Serializer.actual_rats2
