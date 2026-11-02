module

public import PSTR_WordBool_RatPair_Ports_001

/-! Actual double-packet pass. One sentinel backs both headers and all
four guarded fields; one087 restore restores the complete original15. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector

open Turing PSTRWordVM RationalControllerComputation PSTRTMRawNat010 PSTRSymbolicNaturalExport

variable {C : Type*}

def packets (sx sy : Bool) (xn xd yn yd tail : List Bool) : List Bool :=
  PSTRSymbolicRatExport.packet sx xn xd (PSTRSymbolicRatExport.packet sy yn yd tail)

def fieldSize (xn xd yn yd : List Bool) : Nat := xn.length+xd.length+yn.length+yd.length

structure Path (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b=>TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget

def Path.append {caller : Statement C} {before middle final : State C} {frontBudget backBudget : Nat}
    (front : Path caller before middle frontBudget) (back : Path caller middle final backBudget) :
    Path caller before final (frontBudget+backBudget-1) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.head
    rw [same];rfl
  have size:=congrArg List.length shape
  simp only [List.length_cons] at size
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head];rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have first:=front.count;have second:=back.count
    simp only [List.length_append]
    omega

theorem actual_collect (caller : Statement C) (background : Stack → List Bool) (context : C)
    (oldX oldY : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (sx sy : Bool) (xn xd yn yd source scratch : List Bool) :
    ∃ (trace : List (State C)) (bit : Bool),
      trace.head?=some (state background 0 context oldX oldY memory formatter
        (packets sx sy xn xd yn yd source) scratch [] [] [] []) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some (state background 7 context sx sy (bit,true,sy) formatter
        (packets sx sy xn xd yn yd source) scratch xn.reverse xd.reverse yn.reverse yd.reverse) ∧
      trace.length≤3*fieldSize xn xd yn yd+20 := by
  let yPacket:=PSTRSymbolicRatExport.packet sy yn yd source
  let afterXNum:=leftBlocks xd++false::false::yPacket
  let afterYNum:=leftBlocks yd++false::false::source
  let xNumCopied:=RatOutput.numLeft sx xn
  let xCopied:=RatOutput.outputLeft sx xn xd
  let yHeaderCopied:=[sy,true]++xCopied
  let yNumCopied:=false::false::((leftBlocks yn).reverse++yHeaderCopied)
  let allCopied:=false::false::((leftBlocks yd).reverse++yNumCopied)
  let s0:=state background 0 context oldX oldY memory formatter
    (packets sx sy xn xd yn yd source) scratch [] [] [] []
  let s1:=state background 1 context sx oldY (true,memory.2.1,sx) formatter
    (leftBlocks xn++false::false::afterXNum) (backups [sx,true]++true::scratch) [] [] [] []
  let s2:=state background 2 context sx oldY (false,false,sx) formatter
    afterXNum (backups xNumCopied++true::scratch) xn.reverse [] [] []
  let s3:=state background 3 context sx oldY (false,false,sx) formatter
    yPacket (backups xCopied++true::scratch) xn.reverse xd.reverse [] []
  let s4:=state background 4 context sx sy (true,false,sy) formatter
    (leftBlocks yn++false::false::afterYNum) (backups yHeaderCopied++true::scratch) xn.reverse xd.reverse [] []
  let s5:=state background 5 context sx sy (false,false,sy) formatter
    afterYNum (backups yNumCopied++true::scratch) xn.reverse xd.reverse yn.reverse []
  let s6:=state background 6 context sx sy (false,false,sy) formatter
    source (backups allCopied++true::scratch) xn.reverse xd.reverse yn.reverse yd.reverse
  let s7:=state background 7 context sx sy (finalBit allCopied false,true,sy) formatter
    (allCopied.reverse++source) scratch xn.reverse xd.reverse yn.reverse yd.reverse
  have boot : TM2.step (program caller) s0=some s1 :=
    start_x_step caller background context oldX oldY sx memory formatter
      (leftBlocks xn++false::false::afterXNum) scratch [] [] [] []
  let p0 : Path caller s0 s1 2:=⟨[s0,s1],rfl,List.isChain_cons_cons.mpr ⟨boot,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  obtain ⟨t1,h1,c1,l1,n1⟩:=actual_field caller false false background context sx oldY formatter sx xn
    true memory.2.1 [sx,true] afterXNum scratch [] [] [] []
  have last1 : t1.getLast?=some s2 := by
    simpa only [Bool.false_eq_true,ite_false,List.append_nil,s2,xNumCopied,RatOutput.numLeft] using l1
  let p1 : Path caller s1 s2 (xn.length+2):=⟨t1,h1,c1,last1,n1.le⟩
  obtain ⟨t2,h2,c2,l2,n2⟩:=actual_field caller false true background context sx oldY formatter sx xd
    false false xNumCopied yPacket scratch xn.reverse [] [] []
  have last2 : t2.getLast?=some s3 := by
    simpa only [Bool.false_eq_true,ite_false,ite_true,List.append_nil,s3,xCopied,RatOutput.outputLeft,xNumCopied] using l2
  let p2 : Path caller s2 s3 (xd.length+2):=⟨t2,h2,c2,last2,n2.le⟩
  have headerBack : backups yHeaderCopied++true::scratch=
      false::sy::false::true::(backups xCopied++true::scratch) := by
    rw [PSTRSymbolicNaturalExport.backups_append]
    rfl
  have startY : TM2.step (program caller) s3=some s4 := by
    dsimp only [s3,s4]
    rw [headerBack]
    exact start_y_step caller background context sx oldY sy (false,false,sx) formatter
      (leftBlocks yn++false::false::afterYNum) (backups xCopied++true::scratch) xn.reverse xd.reverse [] []
  let p3 : Path caller s3 s4 2:=⟨[s3,s4],rfl,List.isChain_cons_cons.mpr ⟨startY,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
  obtain ⟨t4,h4,c4,l4,n4⟩:=actual_field caller true false background context sx sy formatter sy yn
    true false yHeaderCopied afterYNum scratch xn.reverse xd.reverse [] []
  have last4 : t4.getLast?=some s5 := by simpa only [Bool.false_eq_true,ite_false,ite_true,List.append_nil] using l4
  let p4 : Path caller s4 s5 (yn.length+2):=⟨t4,h4,c4,last4,n4.le⟩
  obtain ⟨t5,h5,c5,l5,n5⟩:=actual_field caller true true background context sx sy formatter sy yd
    false false yNumCopied source scratch xn.reverse xd.reverse yn.reverse []
  have last5 : t5.getLast?=some s6 := by simpa only [ite_true,List.append_nil] using l5
  let p5 : Path caller s5 s6 (yd.length+2):=⟨t5,h5,c5,last5,n5.le⟩
  obtain ⟨t6,h6,c6,l6,n6⟩:=actual_restore caller background context sx sy formatter false false sy allCopied
    source scratch xn.reverse xd.reverse yn.reverse yd.reverse
  let p6 : Path caller s6 s7 (allCopied.length+2):=⟨t6,h6,c6,l6,n6.le⟩
  have copiedShape : allCopied=RatOutput.outputLeft sy yn yd++xCopied := by
    dsimp only [allCopied,yNumCopied,yHeaderCopied,RatOutput.outputLeft,RatOutput.numLeft]
    simp only [List.cons_append,List.append_assoc]
  have restored : allCopied.reverse++source=packets sx sy xn xd yn yd source := by
    rw [copiedShape,List.reverse_append,List.append_assoc,RatOutput.outputLeft_reverse,RatOutput.outputLeft_reverse]
    rfl
  have copiedSize : allCopied.length=2*fieldSize xn xd yn yd+12 := by
    rw [copiedShape,List.length_append,RatOutput.outputLeft_length,RatOutput.outputLeft_length]
    dsimp only [fieldSize]
    omega
  let whole:=(((((p0.append p1).append p2).append p3).append p4).append p5).append p6
  refine ⟨whole.trace,finalBit allCopied false,whole.head,whole.chain,?_,?_⟩
  · have endEq : s7=state background 7 context sx sy (finalBit allCopied false,true,sy) formatter
        (packets sx sy xn xd yn yd source) scratch xn.reverse xd.reverse yn.reverse yd.reverse :=
      congrArg (fun output=>state background 7 context sx sy (finalBit allCopied false,true,sy) formatter
        output scratch xn.reverse xd.reverse yn.reverse yd.reverse) restored
    exact whole.last.trans (congrArg some endEq)
  · have count:=whole.count
    dsimp only [fieldSize] at copiedSize ⊢
    omega

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector
