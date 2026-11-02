module
public import RootB234_RuntimeCounter_Builder_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.RuntimeCounter.Builder
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMRawNat010
variable {C : Type*}

def clear10Trace (background : Stack → List Bool) (context : C) (source temporary leftguard : List Bool) :
    List Bool → RatOutput.Store → List (State C)
  | [],memory => [state background 0 context memory source temporary [] leftguard,
      state background 6 context (false,false) source temporary [] leftguard]
  | bit::later,memory => state background 0 context memory source temporary (bit::later) leftguard::
      clear10Trace background context source temporary leftguard later (true,bit)

def clear11Trace (background : Stack → List Bool) (context : C) (source temporary counter : List Bool) :
    List Bool → RatOutput.Store → List (State C)
  | [],memory => [state background 6 context memory source temporary counter [],
      state background 7 context (false,false) source temporary counter []]
  | bit::later,memory => state background 6 context memory source temporary counter (bit::later)::
      clear11Trace background context source temporary counter later (true,bit)

theorem clear10_head (background : Stack → List Bool) (context : C) (source temporary leftguard old : List Bool)
    (memory : RatOutput.Store) : (clear10Trace background context source temporary leftguard old memory).head?=
      some (state background 0 context memory source temporary old leftguard) := by cases old <;> rfl
theorem clear11_head (background : Stack → List Bool) (context : C) (source temporary counter old : List Bool)
    (memory : RatOutput.Store) : (clear11Trace background context source temporary counter old memory).head?=
      some (state background 6 context memory source temporary counter old) := by cases old <;> rfl

theorem clear10_last (background : Stack → List Bool) (context : C) (source temporary leftguard old : List Bool)
    (memory : RatOutput.Store) : (clear10Trace background context source temporary leftguard old memory).getLast?=
      some (state background 6 context (false,false) source temporary [] leftguard) := by
  induction old generalizing memory with
  | nil => rfl
  | cons bit later ih =>
    rw [clear10Trace,List.getLast?_cons_of_ne_nil (by cases later <;> simp [clear10Trace]),ih]
theorem clear11_last (background : Stack → List Bool) (context : C) (source temporary counter old : List Bool)
    (memory : RatOutput.Store) : (clear11Trace background context source temporary counter old memory).getLast?=
      some (state background 7 context (false,false) source temporary counter []) := by
  induction old generalizing memory with
  | nil => rfl
  | cons bit later ih =>
    rw [clear11Trace,List.getLast?_cons_of_ne_nil (by cases later <;> simp [clear11Trace]),ih]

theorem clear10_length (background : Stack → List Bool) (context : C) (source temporary leftguard old : List Bool)
    (memory : RatOutput.Store) : (clear10Trace background context source temporary leftguard old memory).length=old.length+2 := by
  induction old generalizing memory with
  | nil => rfl
  | cons bit later ih => simp only [clear10Trace,List.length_cons,ih]
theorem clear11_length (background : Stack → List Bool) (context : C) (source temporary counter old : List Bool)
    (memory : RatOutput.Store) : (clear11Trace background context source temporary counter old memory).length=old.length+2 := by
  induction old generalizing memory with
  | nil => rfl
  | cons bit later ih => simp only [clear11Trace,List.length_cons,ih]

theorem clear10_chain (doubled : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (source temporary leftguard old : List Bool) (memory : RatOutput.Store) :
    (clear10Trace background context source temporary leftguard old memory).IsChain
      (fun a b => TM2.step (program doubled caller) a=some b) := by
  induction old generalizing memory with
  | nil => exact List.isChain_cons_cons.mpr ⟨clear10_end _ _ _ _ _ _ _ _,.singleton _⟩
  | cons bit later ih =>
    apply List.IsChain.cons (ih (true,bit))
    intro after selected
    rw [clear10_head] at selected
    have same : after=_ := (Option.mem_some_iff.mp selected).symm
    subst after
    exact clear10_bit _ _ _ _ _ _ _ _ _ _
theorem clear11_chain (doubled : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (source temporary counter old : List Bool) (memory : RatOutput.Store) :
    (clear11Trace background context source temporary counter old memory).IsChain
      (fun a b => TM2.step (program doubled caller) a=some b) := by
  induction old generalizing memory with
  | nil => exact List.isChain_cons_cons.mpr ⟨clear11_end _ _ _ _ _ _ _ _,.singleton _⟩
  | cons bit later ih =>
    apply List.IsChain.cons (ih (true,bit))
    intro after selected
    rw [clear11_head] at selected
    have same : after=_ := (Option.mem_some_iff.mp selected).symm
    subst after
    exact clear11_bit _ _ _ _ _ _ _ _ _ _

def reverseTrace (background : Stack → List Bool) (context : C) :
    List Bool → RatOutput.Store → List Bool → List Bool → List Bool → List (State C)
  | [],memory,source,counter,leftguard =>
      [state background 3 context memory source [] counter leftguard,
        state background 4 context (false,false) source [] counter leftguard]
  | bit::later,memory,source,counter,leftguard =>
      state background 3 context memory source (PSTRTMIncrement009.blocks (bit::later)) counter leftguard::
      reverseTrace background context later (true,true) (true::bit::source) (bit::true::counter) leftguard

theorem reverse_head (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : RatOutput.Store) (source counter leftguard : List Bool) :
    (reverseTrace background context digits memory source counter leftguard).head?=
      some (state background 3 context memory source (PSTRTMIncrement009.blocks digits) counter leftguard) := by
  cases digits <;> rfl

theorem reverse_nonempty (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : RatOutput.Store) (source counter leftguard : List Bool) :
    reverseTrace background context digits memory source counter leftguard≠[] := by cases digits <;> simp [reverseTrace]

theorem leftBlocks_append (a b : List Bool) : leftBlocks (a++b)=leftBlocks a++leftBlocks b := by
  simp only [leftBlocks,List.flatMap_append]
theorem blocks_append (a b : List Bool) : PSTRTMIncrement009.blocks (a++b)=
    PSTRTMIncrement009.blocks a++PSTRTMIncrement009.blocks b := by
  simp only [PSTRTMIncrement009.blocks,List.flatMap_append]
theorem reverse_leftBlocks (digits : List Bool) :
    (leftBlocks digits).reverse=PSTRTMIncrement009.blocks digits.reverse := by
  induction digits with
  | nil => rfl
  | cons bit later ih =>
    change (true::bit::leftBlocks later).reverse=PSTRTMIncrement009.blocks (bit::later).reverse
    rw [List.reverse_cons,List.reverse_cons,ih,List.reverse_cons,blocks_append]
    rw [List.append_assoc]
    rfl

theorem reverse_last (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : RatOutput.Store) (source counter leftguard : List Bool) :
    (reverseTrace background context digits memory source counter leftguard).getLast?=
      some (state background 4 context (false,false) (leftBlocks digits.reverse++source) []
        (PSTRTMIncrement009.blocks digits.reverse++counter) leftguard) := by
  induction digits generalizing memory source counter with
  | nil => rfl
  | cons bit later ih =>
    rw [reverseTrace,List.getLast?_cons_of_ne_nil (reverse_nonempty _ _ _ _ _ _ _),ih]
    rw [List.reverse_cons,leftBlocks_append,blocks_append]
    simp only [leftBlocks,PSTRTMIncrement009.blocks,List.flatMap_singleton,List.append_assoc,
      List.cons_append,List.nil_append]

theorem reverse_length (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : RatOutput.Store) (source counter leftguard : List Bool) :
    (reverseTrace background context digits memory source counter leftguard).length=digits.length+2 := by
  induction digits generalizing memory source counter with
  | nil => rfl
  | cons bit later ih => simp only [reverseTrace,List.length_cons,ih]

theorem reverse_chain (doubled : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (digits : List Bool) (memory : RatOutput.Store) (source counter leftguard : List Bool) :
    (reverseTrace background context digits memory source counter leftguard).IsChain
      (fun a b => TM2.step (program doubled caller) a=some b) := by
  induction digits generalizing memory source counter with
  | nil => exact List.isChain_cons_cons.mpr ⟨reverse_end _ _ _ _ _ _ _ _,.singleton _⟩
  | cons bit later ih =>
    apply List.IsChain.cons (ih (true,true) (true::bit::source) (bit::true::counter))
    intro after selected
    rw [reverse_head] at selected
    have same : after=_ := (Option.mem_some_iff.mp selected).symm
    subst after
    exact reverse_bit _ _ _ _ _ _ _ _ _ _

def build (doubled : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (digits source old10 old11 : List Bool) :
    Path (program doubled caller)
      (state background 0 context memory (leftBlocks digits++[false,false]++source) [] old10 old11)
      (state background 5 context (false,false) (leftBlocks digits++[false,false]++source) []
        (PSTRTMIncrement009.blocks (selectDigits doubled digits)++[false,false,true]) [false])
      (old10.length+old11.length+2*digits.length+14) := by
  let packet:=leftBlocks digits++false::false::source
  let parked:=PSTRTMIncrement009.blocks digits.reverse
  let first : Path (program doubled caller)
      (state background 0 context memory packet [] old10 old11)
      (state background 6 context (false,false) packet [] [] old11) (old10.length+2) :=
    ⟨_,clear10_head _ _ _ _ _ _ _,clear10_chain _ _ _ _ _ _ _ _ _,clear10_last _ _ _ _ _ _ _,by rw [clear10_length]⟩
  let second : Path (program doubled caller)
      (state background 6 context (false,false) packet [] [] old11)
      (state background 7 context (false,false) packet [] [] []) (old11.length+2) :=
    ⟨_,clear11_head _ _ _ _ _ _ _,clear11_chain _ _ _ _ _ _ _ _ _,clear11_last _ _ _ _ _ _ _,by rw [clear11_length]⟩
  let seed:=RatPacketTransport.Path.edge (seed_step doubled caller background context (false,false) packet [])
  let parseTrace:=(RatDrop.fieldTrace true (oldBackground background [false,false,true] [false]) context 1 2
    digits (false,false) source []).map (StackIso.configuration roles)
  have parsed : Path (program doubled caller)
      (state background 1 context (false,false) packet [] [false,false,true] [false])
      (state background 2 context (true,false) source (false::false::parked) [false,false,true] [false]) (digits.length+2) :=
    ⟨parseTrace,by simp only [parseTrace,List.head?_map,RatDrop.field_head,Option.map_some,renamed_state];rfl,
      field_chain _ _ _ _ _ _ _ _ _ _,by
        simp only [parseTrace,List.getLast?_map,RatDrop.field_last,Option.map_some,renamed_state,
          RatDrop.fieldCopied,ite_true,List.append_nil,List.reverse_append,List.reverse_cons,List.reverse_nil]
        rw [reverse_leftBlocks];rfl,
      by simp only [parseTrace,List.length_map,RatDrop.field_length];rfl⟩
  let guards:=RatPacketTransport.Path.edge
    (restore_guards doubled caller background context (true,false) source parked [false,false,true] [false])
  have reversed : Path (program doubled caller)
      (state background 3 context (true,false) (false::false::source) parked [false,false,true] [false])
      (state background 4 context (false,false) packet [] (PSTRTMIncrement009.blocks digits++[false,false,true]) [false])
      (digits.length+2) :=
    ⟨_,reverse_head _ _ _ _ _ _ _,reverse_chain _ _ _ _ _ _ _ _ _,by
      rw [reverse_last];simp only [List.reverse_reverse];rfl,
      by rw [reverse_length,List.length_reverse]⟩
  let pad:=RatPacketTransport.Path.edge (pad_step doubled caller background context (false,false) digits packet [false])
  let whole:=(((((first.trans second).trans seed).trans parsed).trans guards).trans reversed).trans pad
  have result:=whole.weaken (by omega : _≤old10.length+old11.length+2*digits.length+14)
  simpa only [packet,List.append_assoc,List.cons_append,List.nil_append] using result

theorem actual (doubled : Bool) (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (number : Nat) (source old10 old11 : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (state background 0 context memory (B23_4_RatWordPrep.NatField.packet number source) [] old10 old11) ∧
      trace.IsChain (fun a b => TM2.step (program doubled caller) a=some b) ∧
      trace.getLast?=some (state background 5 context (false,false) (B23_4_RatWordPrep.NatField.packet number source) []
        (PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true]) [false]) ∧
      trace.length≤old10.length+old11.length+2*(PSTRTMNatValue017.rawPayload number).length+14 := by
  let path:=build doubled caller background context memory (PSTRTMNatValue017.rawPayload number) source old10 old11
  refine ⟨path.trace,?_,path.chain,?_,path.time⟩
  · simpa only [B23_4_RatWordPrep.NatField.packet,List.append_assoc,List.cons_append,List.nil_append] using path.head
  · simpa only [B23_4_RatWordPrep.NatField.packet,List.append_assoc,List.cons_append,List.nil_append] using path.tail

end RootB234.RuntimeCounter.Builder
