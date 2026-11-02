module

public import B23_4_RatWordPrep_SeqCmp_WordNativePublic_194
public import Structure.B23_5_RawInit_NativeActual036

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_WordTM0

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

abbrev Memory := B23_4_RatWordPrep.WordFinish.Store Unit
abbrev Label := B23_4_RatWordPrep.WordFinish.Label

def scale (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  (wordInput E target word).length+word.1+1

def loweringCoefficient (native decoder count : Nat) : Nat :=
  native*(2*((2*count*(2*count+1)+1)*count))+1+decoder*(count+1)^2

private theorem lowering_clock_bound (native decoder count power steps weight : Nat)
    (positive : 1≤power) (time : steps≤count*power) (cells : weight≤(count+1)*power) :
    native*(2*((2*count*(count*power+count+1)+1)*steps))+1+decoder*weight^2≤
      loweringCoefficient native decoder count*power^2 := by
  have countPaid : count≤count*power := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left count positive
  have room : count*power+count+1≤(2*count+1)*power := by nlinarith
  have actions : 2*count*(count*power+count+1)+1≤(2*count*(2*count+1)+1)*power := by
    have paid := Nat.mul_le_mul_left (2*count) room
    nlinarith
  have body := Nat.mul_le_mul_left native (Nat.mul_le_mul_left 2 (Nat.mul_le_mul actions time))
  have bodyBound : native*(2*((2*count*(count*power+count+1)+1)*steps))≤
      (native*(2*((2*count*(2*count+1)+1)*count)))*power^2 := body.trans_eq (by ring)
  have decoderBound := Nat.mul_le_mul_left decoder (Nat.pow_le_pow_left cells 2)
  have decoderPaid : decoder*weight^2≤(decoder*(count+1)^2)*power^2 := decoderBound.trans_eq (by ring)
  have square : 1≤power^2 := by simpa only [one_pow] using Nat.pow_le_pow_left positive 2
  exact (Nat.add_le_add (Nat.add_le_add bodyBound square) decoderPaid).trans_eq
    (by unfold loweringCoefficient; ring)

private theorem space_absorb (space input time coefficient power : Nat)
    (raw : space ≤ input+2*time+1) (clock : time≤coefficient*power) (charged : input+1≤power) :
    space≤(2*coefficient+2)*power := by nlinarith

/-- Complete original WORD consumer of frozen SINGLE NativeActual036.
The source/support, finite store, code and positive constants are fixed
before all original inputs. Decoder weight pays the complete16-stack
final state. Both native resources concern this same actual Bool trace. -/
theorem actual_uniform :
    ∃ states : Nat,∃ code : Machine states,∃ port : Fin (states+1),∃ coefficient degree : Nat,
      0<coefficient ∧ 0<degree ∧
      ∀ (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
        ∃ trace final,Runs code (wordInput E target word) trace final ∧ final.q=port ∧
          TM0.step code final=none ∧ final.Tape.right₀=ListBlank.mk (wordOutput E target word) ∧
          trace.length≤coefficient*(scale E target word)^degree ∧
          ∀ clock,visitedSpace code (wordInput E target word).length (trace.take clock)≤
            coefficient*(scale E target word)^degree := by
  obtain ⟨source,count,sourceDegree,_positiveCount,_positiveDegree,finite,closed,endpoint⟩ :=
    B23_4_RatWordPrep.WordFinish.Public.original_word_native
  let instMemoryFinite : Finite Memory := finite
  let instMemoryFintype : Fintype Memory := Fintype.ofFinite Memory
  let support : Finset Label := Finset.univ
  let native := TM2Native.nativeBudget source support
  let rawCoefficient := 10033000+loweringCoefficient native RawOutput.coefficient count
  let coefficient := 2*rawCoefficient+2
  let degree := 3+2*sourceDegree
  let code := RawInit.B23_5.NativeActual.machine source support
  let port := RawInit.B23_5.NativeActual.haltPort source support
  refine ⟨_,code,port,coefficient,degree,by unfold coefficient; omega,by unfold degree; omega,?_⟩
  intro E target word
  obtain ⟨sourceTrace,finalSource,facts⟩ := endpoint E target word
  let B := (wordInput E target word).length
  let power := (B+1)^sourceDegree
  have one : 1≤power := by
    simpa only [one_pow] using Nat.pow_le_pow_left (show 1≤B+1 by omega) sourceDegree
  cases traceShape : sourceTrace with
  | nil =>
    have first := facts.first
    rw [traceShape] at first
    cases first
  | cons initial rest =>
    have initialEq : initial=TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (wordInput E target word) := by
      have first := facts.first
      rw [traceShape,List.head?_cons] at first
      exact Option.some.inj first
    subst initial
    have sourceChain : (TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (wordInput E target word)::rest).IsChain
        (fun before after => TM2.step source before=some after) := by
      rw [←traceShape]
      exact facts.chain
    have sourceLast : (TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (wordInput E target word)::rest).getLast?=some finalSource := by
      rw [←traceShape]
      exact facts.last
    have bounded : ∀ current∈TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (wordInput E target word)::rest,
        ∀ slot,(current.stk slot).length≤count*power := by
      intro current present slot
      rw [←traceShape] at present
      exact (facts.boundaries current present).2 slot
    have counts : ∀ current∈TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (wordInput E target word)::rest,
        ∀ label,current.l=some label→ScannerClock.actions (source label)≤count ∧ AuxWorkspace.pushes (source label)≤count :=
      fun _ _ label _ => facts.counts label
    let data : List Datum := rawExperiment E++[Datum.rational target]++rawWord E word
    have wire : encode data=wordInput E target word := rfl
    have rawChain : (TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (encode data)::rest).IsChain
        (fun before after => TM2.step source before=some after) := by
      rw [wire]
      exact sourceChain
    have rawLast : (TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (encode data)::rest).getLast?=some finalSource := by
      rw [wire]
      exact sourceLast
    have rawBounded : ∀ current∈TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (encode data)::rest,
        ∀ slot,(current.stk slot).length≤count*power := by
      rw [wire]
      exact bounded
    have rawCounts : ∀ current∈TM2.init (Γ:=RatInput.Alphabet) (Λ:=Label) (σ:=Memory) 0 (encode data)::rest,
        ∀ label,current.l=some label→ScannerClock.actions (source label)≤count ∧ AuxWorkspace.pushes (source label)≤count := by
      rw [wire]
      exact counts
    obtain ⟨trace,final,run,atPort,halted,output,time,space⟩ := RawInit.B23_5.NativeActual.actual (Λ:=Label) (σ:=Memory)
      source support closed data finalSource rest rawChain rawLast facts.halted (count*power) count count rawBounded rawCounts
    rw [wire] at run time space
    have sourceTime : sourceTrace.length≤count*power := facts.time
    rw [traceShape,List.length_cons] at sourceTime
    have restTime : rest.length≤count*power := by omega
    have finalMass : RatInput.occupied finalSource.stk≤count*power :=
      (facts.boundaries finalSource (List.mem_of_getLast? facts.last)).1
    have finalWeight : RawOutput.weight finalSource.stk≤(count+1)*power := by
      change 1+RatInput.occupied finalSource.stk≤_
      nlinarith
    have nativeTime : RawOutputSpace.totalTime source support finalSource rest (count*power) count count≤
        loweringCoefficient native RawOutput.coefficient count*power^2 :=
      lowering_clock_bound native RawOutput.coefficient count power rest.length (RawOutput.weight finalSource.stk)
        one restTime finalWeight
    have base : B+1≤scale E target word := by unfold B scale; omega
    have scalePositive : 0<scale E target word := by omega
    have adapterPower : (B+1)^3≤(scale E target word)^degree :=
      (Nat.pow_le_pow_left base 3).trans (Nat.pow_le_pow_right scalePositive (by unfold degree; omega))
    have nativePower : power^2≤(scale E target word)^degree := by
      change ((B+1)^sourceDegree)^2≤_
      rw [←pow_mul]
      exact (Nat.pow_le_pow_left base (sourceDegree*2)).trans
        (Nat.pow_le_pow_right scalePositive (by unfold degree; omega))
    have wholeTime : 10033000*(B+1)^3+RawOutputSpace.totalTime source support finalSource rest (count*power) count count≤
        rawCoefficient*(scale E target word)^degree :=
      (Nat.add_le_add (Nat.mul_le_mul_left 10033000 adapterPower)
        (nativeTime.trans (Nat.mul_le_mul_left _ nativePower))).trans_eq
          (by unfold rawCoefficient; ring)
    have inputCharged : B+1≤(scale E target word)^degree := base.trans
      (by simpa only [pow_one] using Nat.pow_le_pow_right scalePositive (show 1≤degree by unfold degree; omega))
    have originalRun : Runs code (wordInput E target word) trace final := run
    have rawTime : trace.length≤rawCoefficient*(scale E target word)^degree := time.trans wholeTime
    have outputExact : final.Tape.right₀=ListBlank.mk (wordOutput E target word) :=
      output.trans (congrArg (fun cells : List Bool => ListBlank.mk cells) facts.output)
    refine ⟨trace,final,originalRun,atPort,halted,outputExact,?_,?_⟩
    · exact rawTime.trans (Nat.mul_le_mul_right _ (by unfold coefficient; omega))
    · intro clock
      exact space_absorb _ B _ rawCoefficient _ (space B clock) wholeTime inputCharged

/-- Exact original RCC computes contract with the original scale.
The stronger actual theorem covers all rational targets, hence in
particular the original legal target domain and length-zero words. -/
theorem computes_uniform :
    ∃ states : Nat,∃ code : Machine states,∃ coefficient degree : Nat,0<coefficient ∧ 0<degree ∧
      ∀ (E : BinaryExperiment) (target : Rat),0<target→target≤1/4→∀ word : E.StoppedWord,
        computes code (wordInput E target word) (wordOutput E target word)
          (coefficient*((wordInput E target word).length+word.1+1)^degree)
          (coefficient*((wordInput E target word).length+word.1+1)^degree) := by
  obtain ⟨states,code,_port,coefficient,degree,positive,degreePositive,actual⟩ := actual_uniform
  refine ⟨states,code,coefficient,degree,positive,degreePositive,?_⟩
  intro E target _lower _upper word
  obtain ⟨trace,final,run,_atPort,_halted,output,time,space⟩ := actual E target word
  refine ⟨trace,final,run,output,time,?_⟩
  simpa only [List.take_length,scale] using space trace.length

end B23_4_WordTM0
