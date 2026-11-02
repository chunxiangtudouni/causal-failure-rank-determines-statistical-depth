module
public import Structure.PA17_TM_RatArithmetic_FrameBudget_008a
public import Common.PSTR_TM_NativeMul_112

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFrameBudget008

open Turing
open PA17TMRatArithmeticFrame005

/-- Exact original visitedSpace for every prefix of the lifted actual run. -/
theorem prefix_space (states : Nat) (machine : Machine states)
    (trace framed : List (MachineState states))
    (same : framed.map (displacement machine) = trace.map (displacement machine))
    (prefixLength inputLength : Nat) :
    visitedSpace machine inputLength (framed.take prefixLength) =
      visitedSpace machine inputLength (trace.take prefixLength) := by
  apply visitedSpace_of_displacements
  simpa only [List.map_take] using congrArg (List.take prefixLength) same

def mulScale (a b : Nat) : Nat := natBits a+natBits b+1
def mulWindow (a b : Nat) : Nat := 16384*(mulScale a b)^2+8*mulScale a b

theorem mul_input_length (a b : Nat) :
    (encodeNat a++encodeNat b).length ≤ 8*mulScale a b := by
  simp only [List.length_append,PSTRTMLength004.encodeNat_length,mulScale]
  omega

theorem mul_output_length (a b : Nat) :
    (encodeNat (a*b)).length ≤ 8*mulScale a b := by
  have hp := PSTRTMNativeMul112.product_payload_length_le a b
  simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn] at hp
  rw [PSTRTMLength004.encodeNat_length]
  unfold mulScale
  omega

/-- A genuine SAME fixed983-label multiplication invocation with both
external frames and complete canonical output, after physically producing the
displayed blank workspace. The allocation/copy producer remains separate;
no caller is permitted to treat mulWindow as free initial-input padding. -/
theorem nativeMul_framed (a b : Nat) (archive suffix : List Bool) :
    ∃ (finalLeft finalRight : Nat) (trace : List (MachineState 982)),
      PSTRTMSeq005.RunsFrom PSTRTMNativeMul112.nativeMulMachine
        ⟨0,Tape.mk₂ (List.replicate (mulWindow a b) false ++ archive)
          ((encodeNat a++encodeNat b) ++
            List.replicate (mulWindow a b+1-(encodeNat a++encodeNat b).length) false ++ suffix)⟩
        trace
        ⟨(PSTRTMNativeMul112.nativeFinal a b).q,
          Tape.mk₂ (List.replicate finalLeft false ++ archive)
            (encodeNat (a*b) ++
              List.replicate (finalRight+1-(encodeNat (a*b)).length) false ++ suffix)⟩ ∧
      8*mulScale a b ≤ finalLeft ∧ 8*mulScale a b ≤ finalRight ∧
      trace.length ≤ 16384*(mulScale a b)^2 ∧
      (∀ prefixLength inputLength,
        visitedSpace PSTRTMNativeMul112.nativeMulMachine inputLength (trace.take prefixLength) =
          visitedSpace PSTRTMNativeMul112.nativeMulMachine inputLength
            ((PSTRTMNativeMul112.nativeTrace a b).take prefixLength)) ∧
      ∀ inputLength, visitedSpace PSTRTMNativeMul112.nativeMulMachine inputLength trace ≤
        inputLength+32768*(mulScale a b)^2+1 := by
  have run := PSTRTMNativeMul112.native_runs a b
  have htime : (PSTRTMNativeMul112.nativeTrace a b).length ≤ 16384*(mulScale a b)^2 :=
    PSTRTMNativeMul112.native_length_le a b
  have hroom : (PSTRTMNativeMul112.nativeTrace a b).length ≤ mulWindow a b := by
    unfold mulWindow
    omega
  have hfrom : PSTRTMSeq005.RunsFrom PSTRTMNativeMul112.nativeMulMachine
      (TM0.init (encodeNat a++encodeNat b))
      (PSTRTMNativeMul112.nativeTrace a b) (PSTRTMNativeMul112.nativeFinal a b) :=
    ⟨run.1,run.2.1,run.2.2.1,run.2.2.2.1⟩
  obtain ⟨finalLeft,finalRight,trace,hfrun,hlen,hmap,hsum,hlend,hrend⟩ :=
    frame_runsFrom_budget PSTRTMNativeMul112.nativeMulMachine archive suffix
      (PSTRTMNativeMul112.nativeTrace a b) (TM0.init (encodeNat a++encodeNat b))
      (PSTRTMNativeMul112.nativeFinal a b) (mulWindow a b) (mulWindow a b) hfrom hroom hroom
  have hleft : 8*mulScale a b ≤ finalLeft := by
    unfold mulWindow at hlend
    omega
  have hright : 8*mulScale a b ≤ finalRight := by
    unfold mulWindow at hrend
    omega
  have inputFits : (encodeNat a++encodeNat b).length ≤ mulWindow a b+1 := by
    have hb := mul_input_length a b
    unfold mulWindow
    omega
  have outputFits : (encodeNat (a*b)).length ≤ finalRight+1 := by
    have hb := mul_output_length a b
    omega
  have hi : frameCfg (mulWindow a b) (mulWindow a b) archive suffix
      (TM0.init (encodeNat a++encodeNat b)) =
      (⟨0,Tape.mk₂ (List.replicate (mulWindow a b) false ++ archive)
        ((encodeNat a++encodeNat b) ++
          List.replicate (mulWindow a b+1-(encodeNat a++encodeNat b).length) false ++ suffix)⟩ : MachineState 982) := by
    unfold frameCfg TM0.init
    rw [frameTape_mk₁ _ _ _ _ _ inputFits]
    simp only [Fin.default_eq_zero]
  have hf : frameCfg finalLeft finalRight archive suffix (PSTRTMNativeMul112.nativeFinal a b) =
      (⟨(PSTRTMNativeMul112.nativeFinal a b).q,
        Tape.mk₂ (List.replicate finalLeft false ++ archive)
          (encodeNat (a*b) ++
            List.replicate (finalRight+1-(encodeNat (a*b)).length) false ++ suffix)⟩ : MachineState 982) := by
    unfold frameCfg
    rw [PSTRTMNativeMul112.native_final_tape_canonical,frameTape_mk₁ _ _ _ _ _ outputFits]
  rw [hi,hf] at hfrun
  refine ⟨finalLeft,finalRight,trace,hfrun,hleft,hright,?_,?_,?_⟩
  · omega
  · exact prefix_space 982 PSTRTMNativeMul112.nativeMulMachine
      (PSTRTMNativeMul112.nativeTrace a b) trace hmap
  · intro inputLength
    have hs := PSTRTMTrace002.visitedSpace_le PSTRTMNativeMul112.nativeMulMachine inputLength trace
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFrameBudget008
