module
public import RootB234_RatPacketTransport_Code001

/-! One real packet path, including both 00 guards and the temporary4 EOF.
No tail cells are read as packet data and no original input tail is erased. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.RatPacketTransport
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMRawNat010
variable {C : Type*}

structure Path (code : Label → Statement C) (first last : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some first
  chain : trace.IsChain (fun a b => TM2.step code a=some b)
  tail : trace.getLast?=some last
  time : trace.length≤budget

namespace Path
variable {code : Label → Statement C} {a b c : State C} {s t : Nat}

def edge (step : TM2.step code a=some b) : Path code a b 2 :=
  ⟨[a,b],rfl,List.isChain_cons_cons.mpr ⟨step,.singleton _⟩,rfl,by rfl⟩

def trans (front : Path code a b s) (back : Path code b c t) : Path code a c (s+t) := by
  have shape : b::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.head
    rw [same];rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head];rfl
  · exact NativeTrace.join_chain _ _ _ front.tail front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.tail).trans (shape.symm ▸ back.tail)
  · have sizes:=congrArg List.length shape
    have first:=front.time
    have second:=back.time
    simp only [List.length_cons] at sizes
    simp only [List.length_append]
    omega

def weaken (path : Path code a b s) (room : s≤t) : Path code a b t :=
  ⟨path.trace,path.head,path.chain,path.tail,path.time.trans room⟩
end Path

def packet (negative : Bool) (num den tail : List Bool) : List Bool :=
  PSTRSymbolicRatExport.packet negative num den tail

theorem packet_append (negative : Bool) (num den tail : List Bool) :
    packet negative num den tail=packet negative num den []++tail := by
  simp [packet,PSTRSymbolicRatExport.packet,List.append_assoc]

def parse (copy : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (negative : Bool) (num den source target : List Bool) :
    Path (program copy caller)
      (state background 0 context memory (packet negative num den source) [] target)
      (state background 3 context (true,false) source (packet negative num den []).reverse target)
      (num.length+den.length+6) := by
  let old:=oldBackground background target
  let denSource:=leftBlocks den++false::false::source
  let hpark:=[negative,true]
  let npark:=RatDrop.fieldCopied true num hpark
  let dpark:=RatDrop.fieldCopied true den npark
  let a:=state background 0 context memory (packet negative num den source) [] target
  let b:=state background 1 context (true,negative) (leftBlocks num++false::false::denSource) hpark target
  let c:=state background 2 context (true,false) denSource npark target
  let d:=state background 3 context (true,false) source dpark target
  have oldEdge:=RatDrop.header_step (.halt : RatDrop.Statement C) true 0 1 rfl old context memory negative
    (leftBlocks num++false::false::denSource) []
  have mapped:=StackIso.step_configuration_on roles (RatDrop.program (.halt : RatDrop.Statement C))
    (program copy caller) (RatDrop.state old 0 context memory (packet negative num den source) [])
    (by intro q selected; have same : q=0:=Option.some.inj selected.symm;subst q;exact program_parse copy caller 0 (by decide))
  have ab : TM2.step (program copy caller) a=some b := by
    rw [show RatDrop.state old 0 context memory (packet negative num den source) []=
      RatDrop.state old 0 context memory (true::negative::(leftBlocks num++false::false::denSource)) [] by rfl,
      oldEdge] at mapped
    simpa [old,renamed_state,a,b,hpark,packet,PSTRSymbolicRatExport.packet,denSource] using mapped
  let numTrace:=(RatDrop.fieldTrace true old context 1 2 num (true,negative) denSource hpark).map
    (StackIso.configuration roles)
  let denTrace:=(RatDrop.fieldTrace true old context 2 3 den (true,false) source npark).map
    (StackIso.configuration roles)
  have first : Path (program copy caller) b c (num.length+2) :=
    ⟨numTrace,by simp only [numTrace,List.head?_map,RatDrop.field_head,Option.map_some,old,renamed_state];rfl,
      field_chain copy caller old context 1 2 (by decide) rfl num (true,negative) denSource hpark,
      by simp only [numTrace,List.getLast?_map,RatDrop.field_last,Option.map_some,old,renamed_state];rfl,
      by simp only [numTrace,List.length_map,RatDrop.field_length];rfl⟩
  have second : Path (program copy caller) c d (den.length+2) :=
    ⟨denTrace,by simp only [denTrace,List.head?_map,RatDrop.field_head,Option.map_some,old,renamed_state];rfl,
      field_chain copy caller old context 2 3 (by decide) rfl den (true,false) source npark,
      by simp only [denTrace,List.getLast?_map,RatDrop.field_last,Option.map_some,old,renamed_state];rfl,
      by simp only [denTrace,List.length_map,RatDrop.field_length];rfl⟩
  have same : dpark=(packet negative num den []).reverse := by
    simpa only [dpark,npark,hpark,packet,ite_true,List.append_nil] using RatDrop.copied_packet true negative num den []
  have result:=((Path.edge ab).trans first).trans second
  dsimp only [d] at result
  rw [same] at result
  exact result.weaken (by omega)

def reverseTrace (copy : Bool) (background : Stack → List Bool) (context : C) :
    List Bool → RatOutput.Store → List Bool → List Bool → List (State C)
  | [],memory,source,target =>
      [state background 3 context memory source [] target,state background 4 context (false,false) source [] target]
  | bit::later,memory,source,target =>
      state background 3 context memory source (bit::later) target::
      reverseTrace copy background context later (true,bit) (if copy then bit::source else source) (bit::target)

theorem reverse_head (copy : Bool) (background : Stack → List Bool) (context : C)
    (word : List Bool) (memory : RatOutput.Store) (source target : List Bool) :
    (reverseTrace copy background context word memory source target).head?=
      some (state background 3 context memory source word target) := by cases word <;> rfl

theorem reverse_nonempty (copy : Bool) (background : Stack → List Bool) (context : C)
    (word : List Bool) (memory : RatOutput.Store) (source target : List Bool) :
    reverseTrace copy background context word memory source target≠[] := by cases word <;> simp [reverseTrace]

theorem reverse_last (copy : Bool) (background : Stack → List Bool) (context : C)
    (word : List Bool) (memory : RatOutput.Store) (source target : List Bool) :
    (reverseTrace copy background context word memory source target).getLast?=
      some (state background 4 context (false,false) (if copy then word.reverse++source else source) []
        (word.reverse++target)) := by
  induction word generalizing memory source target with
  | nil => cases copy <;> rfl
  | cons bit later ih =>
    rw [reverseTrace,List.getLast?_cons_of_ne_nil (reverse_nonempty _ _ _ _ _ _ _),ih]
    cases copy <;> simp [List.reverse_cons,List.append_assoc]

theorem reverse_length (copy : Bool) (background : Stack → List Bool) (context : C)
    (word : List Bool) (memory : RatOutput.Store) (source target : List Bool) :
    (reverseTrace copy background context word memory source target).length=word.length+2 := by
  induction word generalizing memory source target with
  | nil => rfl
  | cons bit later ih => simp only [reverseTrace,List.length_cons,ih]

theorem reverse_chain (copy : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (word : List Bool) (memory : RatOutput.Store) (source target : List Bool) :
    (reverseTrace copy background context word memory source target).IsChain
      (fun a b => TM2.step (program copy caller) a=some b) := by
  induction word generalizing memory source target with
  | nil => exact List.isChain_cons_cons.mpr ⟨reverse_end copy caller background context memory source target,.singleton _⟩
  | cons bit later ih =>
    apply List.IsChain.cons (ih (true,bit) (if copy then bit::source else source) (bit::target))
    intro next selected
    rw [reverse_head] at selected
    have same : next=_ := (Option.mem_some_iff.mp selected).symm
    subst next
    exact reverse_bit copy caller background context memory bit source later target

def fields (copy : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (negative : Bool) (num den source target : List Bool) :
    Path (program copy caller)
      (state background 0 context memory (packet negative num den source) [] target)
      (state background 4 context (false,false) (if copy then packet negative num den source else source) []
        (packet negative num den target)) (3*(num.length+den.length)+14) := by
  have front:=parse copy caller background context memory negative num den source target
  let word:=(packet negative num den []).reverse
  let trace:=reverseTrace copy background context word (true,false) source target
  have back : Path (program copy caller)
      (state background 3 context (true,false) source word target)
      (state background 4 context (false,false) (if copy then packet negative num den source else source) []
        (packet negative num den target)) (word.length+2) :=
    ⟨trace,reverse_head _ _ _ _ _ _ _,reverse_chain _ _ _ _ _ _ _ _,by
      rw [reverse_last]
      simp only [word,List.reverse_reverse,←packet_append],
      by rw [reverse_length]⟩
  have result:=front.trans back
  have length : word.length=2*(num.length+den.length)+6 := by
    simp only [word,List.length_reverse,packet,RatDrop.packet_length,List.length_nil,Nat.add_zero]
  exact result.weaken (by rw [length];omega)

theorem actual (copy : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (x : Rat) (source target : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (state background 0 context memory (RatInput.Encoder.packet x source) [] target) ∧
      trace.IsChain (fun a b => TM2.step (program copy caller) a=some b) ∧
      trace.getLast?=some (state background 4 context (false,false)
        (if copy then RatInput.Encoder.packet x source else source) [] (RatInput.Encoder.packet x target)) ∧
      trace.length≤3*RatInput.Encoder.fieldSize x+14 := by
  let path:=fields copy caller background context memory (PA17TMRatArithmeticParse002.sign x)
    (PA17TMRatArithmeticParse002.numeratorDigits x) (PA17TMRatArithmeticParse002.denominatorDigits x) source target
  exact ⟨path.trace,path.head,path.chain,path.tail,path.time⟩

end RootB234.RatPacketTransport
