module
public import Structure.PA17_TM_RatArithmetic_Width_018e

/-! One actual flag-counting round trip. Route hypotheses describe traces
of fixed code, not values inserted into a machine. The original header
counter is the frozen unary increment; every cursor and restore is paid. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018

def BoundedRun {s : Nat} (machine : Machine s) (first : Turing.Tape Bool)
    (lastLabel : Fin (s+1)) (last : Turing.Tape Bool) (bound : Nat) : Prop :=
  ∃ trace, PSTRTMSeq005.RunsFrom machine ⟨0,first⟩ trace ⟨lastLabel,last⟩ ∧ trace.length≤bound

theorem BoundedRun.seq {a b : Nat} {first : Machine a} {second : Machine b}
    {input middle output : Turing.Tape Bool} {fq : Fin (a+1)} {sq : Fin (b+1)} {lf ls : Nat}
    (hf : BoundedRun first input fq middle lf) (hs : BoundedRun second middle sq output ls) :
    BoundedRun (PSTRTMSeq005.seqMachine first second) input
      (PSTRTMSeq005.rightLabel (a:=a) sq) output (lf+ls) := by
  obtain ⟨tf,hf,hlf⟩ := hf
  obtain ⟨ts,hs,hls⟩ := hs
  refine ⟨tf.map (PSTRTMSeq005.leftCfg (b:=b))++ts.map (PSTRTMSeq005.rightCfg (a:=a)),?_,?_⟩
  · simpa only [PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero,
      PSTRTMSeq005.rightCfg] using
      PSTRTMSeq005.seq_runsFrom first second ⟨0,input⟩ ⟨fq,middle⟩ ⟨sq,output⟩ tf ts hf hs
  · rw [List.length_append,List.length_map,List.length_map]
    omega

theorem BoundedRun.mono {s : Nat} {machine : Machine s} {input output : Turing.Tape Bool}
    {q : Fin (s+1)} {a b : Nat} (run : BoundedRun machine input q output a) (hab : a≤b) :
    BoundedRun machine input q output b := by
  obtain ⟨trace,hr,hl⟩ := run
  exact ⟨trace,hr,hl.trans hab⟩

structure RouteSpec (back forward : Machine 28) (backPort forwardPort : Fin 29)
    (archive : Nat → List Bool) (home : List Bool → List Bool) (previousWidth : Nat) : Prop where
  back_run : ∀ n right, BoundedRun back (Turing.Tape.mk₂ (false::archive n) right)
    backPort (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (home right)) (2*previousWidth+26)
  forward_run : ∀ n right, right.head?=some false →
    BoundedRun forward (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (home right))
      forwardPort (Turing.Tape.mk₂ (false::archive n) right) (2*previousWidth+17)

def markedStream (earlier : List Bool) (bit : Bool) (later suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks earlier++bit::false::(PSTRTMIncrement009.blocks later++false::false::suffix)

theorem markedStream_head (earlier : List Bool) (bit : Bool) (later suffix fieldTail : List Bool)
    (hfield : earlier++bit::later=false::fieldTail) :
    (markedStream earlier bit later suffix).head?=some false := by
  have hh := congrArg List.head? hfield
  cases earlier with
  | nil => simpa [markedStream,PSTRTMIncrement009.blocks] using hh
  | cons data earlier => simpa [markedStream,PSTRTMIncrement009.blocks] using hh

def cycleBackMachine (back : Machine 28) : Machine 35 := PSTRTMSeq005.seqMachine prefixReturnMachine back
def cycleIncrementMachine (back : Machine 28) : Machine 41 :=
  PSTRTMSeq005.seqMachine (cycleBackMachine back) ROOTTMGCDCounter011.counterMachine
def cycleForwardMachine (back forward : Machine 28) : Machine 70 :=
  PSTRTMSeq005.seqMachine (cycleIncrementMachine back) forward
def cycleMachine (back forward : Machine 28) : Machine 75 :=
  PSTRTMSeq005.seqMachine (cycleForwardMachine back forward) seekRestoreMachine

/-- A counted flag really returns to the input header, increments its
left unary counter, returns to its marker and restores that flag TRUE.
Neither field width nor counter value occurs in the executable code. -/
theorem cycle_runsFrom (back forward : Machine 28) (backPort forwardPort : Fin 29)
    (archive : Nat → List Bool) (home : List Bool → List Bool) (previousWidth : Nat)
    (routes : RouteSpec back forward backPort forwardPort archive home previousWidth)
    (n : Nat) (earlier : List Bool) (bit : Bool) (later suffix fieldTail : List Bool)
    (hfield : earlier++bit::later=false::fieldTail) :
    BoundedRun (cycleMachine back forward)
      (Turing.Tape.mk₂ (false::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive n))
        (PSTRTMIncrement009.blocks later++false::false::suffix)) 75
      (Turing.Tape.mk₂ (true::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive (n+1)))
        (PSTRTMIncrement009.blocks later++false::false::suffix))
      (2*n+4*earlier.length+4*previousWidth+60) := by
  have hp : BoundedRun prefixReturnMachine
      (Turing.Tape.mk₂ (false::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive n))
        (PSTRTMIncrement009.blocks later++false::false::suffix)) 6
      (Turing.Tape.mk₂ (false::archive n) (markedStream earlier bit later suffix)) (2*earlier.length+6) := by
    refine ⟨prefixReturnTrace (archive n) earlier bit (PSTRTMIncrement009.blocks later++false::false::suffix),
      prefixReturn_runsFrom (archive n) earlier bit (PSTRTMIncrement009.blocks later++false::false::suffix),?_⟩
    rw [prefixReturnTrace_length]
  have hb := routes.back_run n (markedStream earlier bit later suffix)
  have hi : BoundedRun ROOTTMGCDCounter011.counterMachine
      (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (home (markedStream earlier bit later suffix))) 5
      (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones (n+1)) (home (markedStream earlier bit later suffix)))
      (2*n+6) := by
    refine ⟨ROOTTMGCDCounter011.fullTrace n (home (markedStream earlier bit later suffix)),
      ROOTTMGCDCounter011.counter_runsFrom n (home (markedStream earlier bit later suffix)),?_⟩
    rw [ROOTTMGCDCounter011.full_length]
  have hf := routes.forward_run (n+1) (markedStream earlier bit later suffix)
    (markedStream_head earlier bit later suffix fieldTail hfield)
  have hs : BoundedRun seekRestoreMachine
      (Turing.Tape.mk₂ (false::archive (n+1)) (markedStream earlier bit later suffix)) 4
      (Turing.Tape.mk₂ (true::bit::(PSTRTMRawNat010.leftBlocks earlier.reverse++false::archive (n+1)))
        (PSTRTMIncrement009.blocks later++false::false::suffix)) (2*earlier.length+5) := by
    refine ⟨seekRestoreTrace (false::archive (n+1)) earlier bit
        (PSTRTMIncrement009.blocks later++false::false::suffix),
      seekRestore_runsFrom (false::archive (n+1)) earlier bit
        (PSTRTMIncrement009.blocks later++false::false::suffix),?_⟩
    rw [seekRestoreTrace_length]
  have h := ((hp.seq hb).seq hi).seq hf
  have h' := h.seq hs
  apply h'.mono
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
