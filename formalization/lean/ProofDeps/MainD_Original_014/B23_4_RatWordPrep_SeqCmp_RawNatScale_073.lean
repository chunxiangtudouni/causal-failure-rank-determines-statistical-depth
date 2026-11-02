module

public import B23_4_RatWordPrep_SeqCmp_RawNatResources_072

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawNat

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMRatArithmeticParse002

variable {C : Type*}

def inputScale (background : RatInput.Stack → List Bool) (number : Nat) : Nat :=
  RatInput.occupied background+(PSTRTMNatValue017.rawPayload number).length+1
def coefficient : Nat := 65536
def degree : Nat := 2

theorem coefficient_pos : 0<coefficient := by decide
theorem degree_eq_two : degree=2 := rfl
theorem inputScale_pos (background : RatInput.Stack → List Bool) (number : Nat) : 1 ≤ inputScale background number := by
  unfold inputScale
  omega

theorem linear_square (n : Nat) (positive : 1≤n) : n≤n^2 := by
  have bound := Nat.pow_le_pow_right positive (show 1≤2 by decide)
  simpa only [pow_one] using bound

theorem time_le (background : RatInput.Stack → List Bool) (number : Nat) : time number≤32*(inputScale background number)^2 := by
  have localTime : time number ≤ 32*((PSTRTMNatValue017.rawPayload number).length+1)^2 := by
    dsimp only [time]
    nlinarith [Nat.zero_le ((PSTRTMNatValue017.rawPayload number).length^2)]
  have scale : (PSTRTMNatValue017.rawPayload number).length+1 ≤ inputScale background number := by unfold inputScale; omega
  exact localTime.trans (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left scale 2))

theorem space_le (background : RatInput.Stack → List Bool) (number : Nat) : space background number≤513*(inputScale background number)^2 := by
  have time := time_le background number
  have linear := linear_square _ (inputScale_pos background number)
  have mass : RatInput.occupied background ≤ inputScale background number := by unfold inputScale; omega
  dsimp only [space]
  nlinarith only [time,linear,mass]

theorem unified_bounds (background : RatInput.Stack → List Bool) (number : Nat) :
    let n := inputScale background number
    time number≤coefficient*n^degree ∧ 16*space background number≤coefficient*n^degree ∧
    space background number+16≤coefficient*n^degree ∧ 32*(space background number+17)≤coefficient*n^degree := by
  dsimp only
  have time := time_le background number
  have space := space_le background number
  have linear := linear_square _ (inputScale_pos background number)
  have one := inputScale_pos background number
  dsimp only [coefficient,degree]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

structure Facts (source : Label → Statement C) (background : RatInput.Stack → List Bool)
    (memory : Store C) (number : Nat) (suffix : List Bool) (trace : List (State C)) (final parsed : State C) : Prop where
  first : trace.head?=some (⟨some .boot,memory,background⟩ : State C)
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final
  parsed_member : parsed∈trace
  active : final.l=some .done
  context_eq : final.var.1.1=memory.1.1
  contents : final.stk=Function.update parsed.stk 15 (NatField.packet number (background 15))
  parserTape : Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))=Tape.mk₂
    (false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::true::background 1)) (suffix++[true])
  scratch : parsed.stk 7=background 7
  target : parsed.stk 15=background 15
  time : trace.length≤coefficient*(inputScale background number)^degree
  boundaries : ∀ current∈trace,current.var.1.1=memory.1.1 ∧
    (∀ slot,(current.stk slot).length≤coefficient*(inputScale background number)^degree) ∧
    RatInput.occupied current.stk≤coefficient*(inputScale background number)^degree ∧
    ∀ slot,¬Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        node.1.1.1=memory.1.1 ∧ (∀ slot,(node.2 slot).length≤coefficient*(inputScale background number)^degree) ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤coefficient*(inputScale background number)^degree

theorem actual_polynomial_current (background : RatInput.Stack → List Bool) (memory : Store C)
    (number : Nat) (suffix : List Bool)
    (right : ListBlank.mk (background 0)=ListBlank.mk (encodeDatum (.natural number)++suffix++[true])) :
    ∃ trace final parsed,Facts (program .halt) background memory number suffix trace final parsed := by
  obtain ⟨trace,final,parsed,first,chain,last,member,active,context,contents,tape,scratch,target,count,boundaries,proper⟩ :=
    actual_current_bounded background memory number suffix right
  have caps := unified_bounds background number
  refine ⟨trace,final,parsed,⟨first,chain,last,member,active,context,contents,tape,scratch,target,count.trans caps.1,?_,?_⟩⟩
  · intro current present
    have bound := boundaries current present
    exact ⟨bound.1,fun slot => (bound.2.1 slot).trans
      ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1),bound.2.2.1.trans caps.2.1,bound.2.2.2⟩
  · intro current present
    refine ⟨(proper current present).1,?_⟩
    intro point selected
    have bound := (proper current present).2 point selected
    exact ⟨fun node inside => ⟨(bound.1 node inside).1,
      fun slot => ((bound.1 node inside).2.1 slot).trans caps.2.2.1,(bound.1 node inside).2.2⟩,
      bound.2.trans caps.2.2.2⟩

theorem inputScale_le_mass (background : RatInput.Stack → List Bool) (number : Nat) (suffix : List Bool)
    (right : ListBlank.mk (background 0)=ListBlank.mk (encodeDatum (.natural number)++suffix++[true])) :
    inputScale background number ≤ 2*(RatInput.occupied background+1) := by
  obtain ⟨tail,shape⟩:=PSTRSymbolicNaturalExport.finite_marked_prefix
    (encodeDatum (.natural number)++suffix) [] (background 0)
    (by simpa only [List.append_assoc,List.singleton_append,List.append_nil] using right)
  have length:=congrArg List.length shape
  simp only [List.length_append,List.length_cons,encodeDatum,PSTRTMLength004.encodeNat_length] at length
  have field : (PSTRTMNatValue017.rawPayload number).length ≤ (background 0).length := by
    simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
    omega
  have mass:=RatInput.Encoder.point_mass background 0
  dsimp only [inputScale]
  omega

end B23_4_RatWordPrep.RawNat
