module
public import Structure.RootB23_Threshold_Uncapped_Walk_005
public import Structure.RootB23_Threshold_Uncapped_Steps_007
public import Structure.PA17_TM_RatArithmetic_Parse_002c

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Clean
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMRawNat010 PSTRTMNatValue017
open PA17TMRatArithmeticAllocate013

theorem blank_zeros (count : Nat) :
    Turing.ListBlank.mk (List.replicate count false) = Turing.ListBlank.mk ([] : List Bool) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [List.replicate_succ',blank_append_false,ih]

theorem blank_zeros_tail (count : Nat) :
    Turing.ListBlank.mk (List.replicate count false++[false,false]) =
      Turing.ListBlank.mk ([] : List Bool) := by
  rw [show List.replicate count false++[false,false] = List.replicate (count+2) false by
    rw [List.replicate_add]; rfl,blank_zeros]

theorem blank_false_tail (word : List Bool) (count : Nat) :
    Turing.ListBlank.mk (word++List.replicate count false) = Turing.ListBlank.mk word := by
  induction count with
  | zero => simp only [List.replicate_zero,List.append_nil]
  | succ count ih =>
    rw [List.replicate_succ',←List.append_assoc,blank_append_false,ih]

def terminal (cap : Nat) (tape : Turing.Tape Bool) : MachineState cap :=
  ⟨⟨cap,Nat.lt_succ_self cap⟩,tape⟩

/-- Direct reuse of Seq005 on the SAME middle whole Tape, retaining one
actual mapped concatenation. Both endpoints are real finite-control ports. -/
theorem joined_bounded {a b : Nat} (first : Machine a) (second : Machine b)
    (initial middle finalTape : Turing.Tape Bool) (firstCost secondCost : Nat)
    (firstRun : ∃ states, PSTRTMSeq005.RunsFrom first ⟨0,initial⟩ states (terminal a middle) ∧
      states.length ≤ firstCost)
    (secondRun : ∃ states, PSTRTMSeq005.RunsFrom second ⟨0,middle⟩ states (terminal b finalTape) ∧
      states.length ≤ secondCost) :
    ∃ states, PSTRTMSeq005.RunsFrom (PSTRTMSeq005.seqMachine first second)
      ⟨0,initial⟩ states (terminal (a+b+1) finalTape) ∧ states.length ≤ firstCost+secondCost := by
  obtain ⟨front,hfront,tfront⟩ := firstRun
  obtain ⟨later,hlater,tlater⟩ := secondRun
  have real := PSTRTMSeq005.seq_runsFrom first second ⟨0,initial⟩ (terminal a middle)
    (terminal b finalTape) front later hfront hlater
  have begin : PSTRTMSeq005.leftCfg (b:=b) (⟨0,initial⟩ : MachineState a) =
      (⟨0,initial⟩ : MachineState (a+b+1)) := rfl
  have finish : PSTRTMSeq005.rightCfg (a:=a) (terminal b finalTape) = terminal (a+b+1) finalTape := by
    change (⟨PSTRTMSeq005.rightLabel (a:=a) (⟨b,Nat.lt_succ_self b⟩ : Fin (b+1)),finalTape⟩ : MachineState (a+b+1)) = _
    unfold terminal
    congr 1
    apply Fin.ext
    change a+1+b=a+b+1
    omega
  rw [begin,finish] at real
  refine ⟨front.map (PSTRTMSeq005.leftCfg (b:=b)) ++ later.map (PSTRTMSeq005.rightCfg (a:=a)),real,?_⟩
  simp only [List.length_append,List.length_map]
  omega

def gapRight (depth : List Bool) (gap n : Nat) : List Bool :=
  blocks depth++List.replicate (2*(gap+1)) false++blocks (rawPayload n)++false::false::encodeNat n
def anchorLeft (archive : List Bool) : List Bool := false::false::false::true::archive
def depthLeft (archive depth : List Bool) : List Bool :=
  List.replicate (2*depth.length) false++anchorLeft archive
def gapLeft (archive depth : List Bool) (gap : Nat) : List Bool :=
  List.replicate (2*(gap+1)) false++depthLeft archive depth
def valueLeft (archive depth : List Bool) (gap n : Nat) : List Bool :=
  List.replicate (2*(rawPayload n).length) false++gapLeft archive depth gap
def returnGap (depth : List Bool) (gap n : Nat) : Nat :=
  1+(2*(rawPayload n).length+(2*(gap+1)+(2*depth.length+3)))

theorem gap_uncons (gap : Nat) (suffix : List Bool) :
    List.replicate (2*(gap+1)) false++suffix =
      false::false::(List.replicate (2*gap) false++suffix) := by
  rw [show 2*(gap+1)=2+2*gap by omega,List.replicate_add]
  rfl

theorem left_return_geometry (archive depth : List Bool) (gap n : Nat) :
    false::valueLeft archive depth gap n = List.replicate (returnGap depth gap n) false++true::archive := by
  simp only [valueLeft,gapLeft,depthLeft,anchorLeft,returnGap,List.replicate_add,
    show List.replicate 1 false = [false] from rfl,
    show List.replicate 3 false = [false,false,false] from rfl,
    List.nil_append,List.append_assoc,List.cons_append]

theorem payload_gap_run (archive depth : List Bool) (gap n : Nat) :
    ∃ states, PSTRTMSeq005.RunsFrom Gap.code
      ⟨0,Turing.Tape.mk₂ (depthLeft archive depth)
        (List.replicate (2*(gap+1)) false++blocks (rawPayload n)++false::false::encodeNat n)⟩ states
      ⟨2,Turing.Tape.mk₂ (gapLeft archive depth gap) (blocks (rawPayload n)++false::false::encodeNat n)⟩ ∧
      states.length ≤ 2*gap+5 := by
  cases found : rawPayload n with
  | nil =>
    have count := congrArg List.length found
    have positive : 0 < natBits n := by simp [natBits]
    simp only [rawPayload,List.length_ofFn,List.length_nil] at count
    omega
  | cons bit later =>
    refine ⟨Gap.actualTrace (depthLeft archive depth) bit
      (blocks later++false::false::encodeNat n) (gap+1),?_,?_⟩
    · simpa only [found,blocks,List.flatMap_cons,List.singleton_append,List.cons_append,
        List.append_assoc,List.nil_append,gapLeft,Gap.state] using
        Gap.pair_gap_runsFrom (depthLeft archive depth) bit (blocks later++false::false::encodeNat n) (gap+1)
    · rw [Gap.actual_length]
      omega

def depthCode : Machine 16 := PSTRTMSeq005.seqMachine Steps.anchorCode Erase.rightCode
def gapCode : Machine 19 := PSTRTMSeq005.seqMachine depthCode Gap.code
def valueCode : Machine 27 := PSTRTMSeq005.seqMachine gapCode Erase.rightCode
def rawEntryCode : Machine 30 := PSTRTMSeq005.seqMachine valueCode Steps.twoRightCode
def parsedCode : Machine 48 := PSTRTMSeq005.seqMachine rawEntryCode PA17TMRatArithmeticParse002.streamMachine
def erasedCode : Machine 56 := PSTRTMSeq005.seqMachine parsedCode Erase.leftCode
def returnedCode : Machine 58 := PSTRTMSeq005.seqMachine erasedCode (gapSeekMachine .left)
def code : Machine 60 := PSTRTMSeq005.seqMachine returnedCode Steps.clearCode

/-- Clear the actual finite exhausted-depth/gap/flagged-B/raw-B tail.
No blank suffix is assumed for the depth or B fields. The sole far-right
blank tail belongs to the original canonical raw-B output and is paid by
the earlier producer. The preserved left archive is completely arbitrary. -/
theorem scratch_contract (archive depth : List Bool) (gap n : Nat) :
    ∃ states, PSTRTMSeq005.RunsFrom code
      ⟨0,Turing.Tape.mk₂ archive (false::false::true::false::gapRight depth gap n)⟩ states
      ⟨60,Turing.Tape.mk₂ archive []⟩ ∧
      states.length ≤ (rawPayload n).length^2+21*(rawPayload n).length+8*depth.length+4*gap+39 := by
  let input := Turing.Tape.mk₂ archive (false::false::true::false::gapRight depth gap n)
  let t0 := Turing.Tape.mk₂ (anchorLeft archive) (gapRight depth gap n)
  let t1 := Turing.Tape.mk₂ (depthLeft archive depth)
    (List.replicate (2*(gap+1)) false++blocks (rawPayload n)++false::false::encodeNat n)
  let t2 := Turing.Tape.mk₂ (gapLeft archive depth gap) (blocks (rawPayload n)++false::false::encodeNat n)
  let t3 := Turing.Tape.mk₂ (valueLeft archive depth gap n) (false::false::encodeNat n)
  let t4 := Turing.Tape.mk₂ (false::false::valueLeft archive depth gap n) (encodeNat n)
  let t5 := Turing.Tape.mk₂
    (false::(leftBlocks (rawPayload n).reverse++false::false::valueLeft archive depth gap n)) []
  let t6 := Turing.Tape.mk₂ (false::valueLeft archive depth gap n) []
  let t7 := Turing.Tape.mk₂ archive [true]
  have r0 : ∃ states, PSTRTMSeq005.RunsFrom Steps.anchorCode ⟨0,input⟩ states ⟨8,t0⟩ ∧ states.length ≤ 9 :=
    ⟨Steps.anchorTrace archive (gapRight depth gap n),Steps.anchor_runsFrom _ _,by change 9 ≤ 9; exact Nat.le_refl _⟩
  have r1 : ∃ states, PSTRTMSeq005.RunsFrom Erase.rightCode ⟨0,t0⟩ states ⟨7,t1⟩ ∧ states.length ≤ 6*depth.length+3 := by
    let tail := List.replicate (2*gap) false++blocks (rawPayload n)++false::false::encodeNat n
    refine ⟨Erase.rightTrace (anchorLeft archive) depth tail,?_,?_⟩
    · have real := Erase.right_runsFrom (anchorLeft archive) depth tail
      have same : false::false::tail =
          List.replicate (2*(gap+1)) false++blocks (rawPayload n)++false::false::encodeNat n := by
        simpa only [tail,List.append_assoc] using
          (gap_uncons gap (blocks (rawPayload n)++false::false::encodeNat n)).symm
      rw [same] at real
      simpa only [Erase.rstate,t0,t1,gapRight,depthLeft,List.append_assoc] using real
    · exact (Erase.right_length _ _ _).le
  have r01 := joined_bounded Steps.anchorCode Erase.rightCode input t0 t1 9 (6*depth.length+3) r0 r1
  have r2 : ∃ states, PSTRTMSeq005.RunsFrom Gap.code ⟨0,t1⟩ states ⟨2,t2⟩ ∧ states.length ≤ 2*gap+5 :=
    payload_gap_run archive depth gap n
  have r02 := joined_bounded depthCode Gap.code input t1 t2 (9+(6*depth.length+3)) (2*gap+5) r01 r2
  have r3 : ∃ states, PSTRTMSeq005.RunsFrom Erase.rightCode ⟨0,t2⟩ states ⟨7,t3⟩ ∧
      states.length ≤ 6*(rawPayload n).length+3 :=
    ⟨Erase.rightTrace (gapLeft archive depth gap) (rawPayload n) (encodeNat n),
      Erase.right_runsFrom _ _ _,(Erase.right_length _ _ _).le⟩
  have r03 := joined_bounded gapCode Erase.rightCode input t2 t3
    (9+(6*depth.length+3)+(2*gap+5)) (6*(rawPayload n).length+3) r02 r3
  have r4 : ∃ states, PSTRTMSeq005.RunsFrom Steps.twoRightCode ⟨0,t3⟩ states ⟨2,t4⟩ ∧ states.length ≤ 3 :=
    ⟨Steps.twoRightTrace (valueLeft archive depth gap n) false false (encodeNat n),
      Steps.twoRight_runsFrom _ _ _ _,by change 3 ≤ 3; exact Nat.le_refl _⟩
  have r04 := joined_bounded valueCode Steps.twoRightCode input t3 t4
    (9+(6*depth.length+3)+(2*gap+5)+(6*(rawPayload n).length+3)) 3 r03 r4
  have r5 : ∃ states, PSTRTMSeq005.RunsFrom PA17TMRatArithmeticParse002.streamMachine
      ⟨0,t4⟩ states ⟨17,t5⟩ ∧ states.length ≤ (rawPayload n).length^2+9*(rawPayload n).length+2 :=
    ⟨PA17TMRatArithmeticParse002.streamTrace (false::false::valueLeft archive depth gap n) [] (rawPayload n) [],
      by simpa only [List.append_nil,PA17TMRatArithmeticParse002.streamState,PA17TMRatArithmeticParse002.streamFinal,t4,t5] using PA17TMRatArithmeticParse002.encodeNat_stream_runsFrom (false::false::valueLeft archive depth gap n) [] n,
      (PA17TMRatArithmeticParse002.streamTrace_length _ _ _ _).le⟩
  have r05 := joined_bounded rawEntryCode PA17TMRatArithmeticParse002.streamMachine input t4 t5
    (9+(6*depth.length+3)+(2*gap+5)+(6*(rawPayload n).length+3)+3)
    ((rawPayload n).length^2+9*(rawPayload n).length+2) r04 r5
  have r6 : ∃ states, PSTRTMSeq005.RunsFrom Erase.leftCode ⟨0,t5⟩ states ⟨7,t6⟩ ∧
      states.length ≤ 4*(rawPayload n).length+4 := by
    refine ⟨Walk.eraseLeftTrace (false::valueLeft archive depth gap n) (rawPayload n) [],?_,?_⟩
    · have real := Walk.eraseLeft_runsFrom (false::valueLeft archive depth gap n) (rawPayload n) []
      have blank : Turing.Tape.mk₂ (false::valueLeft archive depth gap n)
          (false::(List.replicate (2*(rawPayload n).length) false++[false])) = t6 := by
        dsimp only [t6]
        simp only [Turing.Tape.mk₂]
        congr 1
        rw [show false::(List.replicate (2*(rawPayload n).length) false++[false]) =
          List.replicate (2*(rawPayload n).length+2) false by
          rw [show 2*(rawPayload n).length+2=1+(2*(rawPayload n).length+1) by omega,
            List.replicate_add,List.replicate_add]; rfl,blank_zeros]
      unfold Erase.lstate at real
      rw [blank] at real
      exact real
    · exact (Walk.eraseLeft_length _ _ _).le
  have r06 := joined_bounded parsedCode Erase.leftCode input t5 t6
    (9+(6*depth.length+3)+(2*gap+5)+(6*(rawPayload n).length+3)+3+
      ((rawPayload n).length^2+9*(rawPayload n).length+2)) (4*(rawPayload n).length+4) r05 r6
  have r7 : ∃ states, PSTRTMSeq005.RunsFrom (gapSeekMachine .left) ⟨0,t6⟩ states ⟨1,t7⟩ ∧
      states.length ≤ returnGap depth gap n+2 := by
    refine ⟨Steps.returnTrace false (returnGap depth gap n) archive [],?_,?_⟩
    · have real := Steps.return_runsFrom false (returnGap depth gap n) archive []
      have before : Turing.Tape.mk₂ (List.replicate (returnGap depth gap n) false++true::archive) [false] = t6 := by
        rw [←left_return_geometry]
        dsimp only [t6]
        simp only [Turing.Tape.mk₂]
        rw [show Turing.ListBlank.mk [false] = Turing.ListBlank.mk ([] : List Bool) from blank_append_false []]
      have after : Turing.Tape.mk₂ archive (true::(List.replicate (returnGap depth gap n) false++[false])) = t7 := by
        dsimp only [t7]
        simp only [Turing.Tape.mk₂]
        congr 1
        rw [show true::(List.replicate (returnGap depth gap n) false++[false]) =
          [true]++List.replicate (returnGap depth gap n+1) false by
          rw [List.replicate_succ']; rfl,blank_false_tail]
      unfold seekState at real
      rw [before,after] at real
      exact real
    · exact (Steps.return_length _ _ _ _).le
  have r07 := joined_bounded erasedCode (gapSeekMachine .left) input t6 t7
    (9+(6*depth.length+3)+(2*gap+5)+(6*(rawPayload n).length+3)+3+
      ((rawPayload n).length^2+9*(rawPayload n).length+2)+(4*(rawPayload n).length+4))
    (returnGap depth gap n+2) r06 r7
  have r8 : ∃ states, PSTRTMSeq005.RunsFrom Steps.clearCode ⟨0,t7⟩ states
      ⟨1,Turing.Tape.mk₂ archive []⟩ ∧ states.length ≤ 2 := by
    refine ⟨Steps.clearTrace archive [],?_,by change 2 ≤ 2; exact Nat.le_refl _⟩
    have real := Steps.clear_runsFrom archive []
    have blank : Turing.Tape.mk₂ archive [false] = Turing.Tape.mk₂ archive [] := by
      simp only [Turing.Tape.mk₂]
      rw [show Turing.ListBlank.mk [false] = Turing.ListBlank.mk ([] : List Bool) from blank_append_false []]
    rw [blank] at real
    exact real
  obtain ⟨states,actual,time⟩ := joined_bounded returnedCode Steps.clearCode input t7
    (Turing.Tape.mk₂ archive [])
    (9+(6*depth.length+3)+(2*gap+5)+(6*(rawPayload n).length+3)+3+
      ((rawPayload n).length^2+9*(rawPayload n).length+2)+(4*(rawPayload n).length+4)+
      (returnGap depth gap n+2)) 2 r07 r8
  refine ⟨states,actual,?_⟩
  dsimp only [returnGap] at time
  omega

end RootB23.Threshold.Uncapped.Clean
