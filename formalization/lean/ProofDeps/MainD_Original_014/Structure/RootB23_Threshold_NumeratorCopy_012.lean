module
public import Structure.RootB23_Threshold_SourceRoutes_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.NumeratorCopy
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031 (workSuffix)

/-- The first far destination marker is genuinely written in the
actual blank tail after the factor; this is never used on nonempty ROM. -/
def markerCode : Machine 3 := fun q _=>match q.val with
  | 0=>some (1,.move .right)
  | 1=>some (2,.write true)
  | 2=>some (3,.move .left)
  | _=>none
def markerTrace (left : List Bool) : List (MachineState 3) :=
  [⟨0,Tape.mk₂ left [false]⟩,⟨1,Tape.mk₂ (false::left) [false]⟩,
   ⟨2,Tape.mk₂ (false::left) [true]⟩,⟨3,Tape.mk₂ left [false,true]⟩]

theorem marker_bounded (left : List Bool) :
    BoundedRun markerCode (Tape.mk₂ left [false]) 3
      (Tape.mk₂ left (false::workSuffix 0 [])) 4 := by
  have endTape : Tape.mk₂ left [false,true]=Tape.mk₂ left (false::workSuffix 0 []) := by
    change Tape.mk₂ left [false,true]=Tape.mk₂ left [false,true,false,false,false]
    exact ((PA17TMRatArithmeticBankCopy024.tape_append_false left [false,true,false,false]).trans
      ((PA17TMRatArithmeticBankCopy024.tape_append_false left [false,true,false]).trans
        (PA17TMRatArithmeticBankCopy024.tape_append_false left [false,true]))).symm
  refine ⟨markerTrace left,⟨rfl,?_,?_,?_⟩,by rfl⟩
  · simp [markerTrace,List.isChain_cons_cons,TM0.step,markerCode,Tape.mk₂,
      PSTRTMRawNat010.blank_single_false]
  · change some (⟨3,Tape.mk₂ left [false,true]⟩ : MachineState 3)=_
    rw [endTape]
  · simp [TM0.step,markerCode]

def outwardMarkerCode : Machine 104 := PSTRTMSeq005.seqMachine SourceRoutes.numeratorRoute.out markerCode
def prepareCode : Machine 205 := PSTRTMSeq005.seqMachine outwardMarkerCode SourceRoutes.numeratorRoute.back
def preparePort : Fin 206 := PSTRTMSeq005.rightLabel (a:=104) SourceRoutes.numeratorRoute.backPort
def copyCode : Machine 1368 := PSTRTMSeq005.seqMachine prepareCode (RoutedCopy.copyMachine SourceRoutes.numeratorRoute)

def cost (digits den depth b : List Bool) (gap : ℕ) (q : Rat) : ℕ :=
  4*digits.length^2+(2*SourceRoutes.numCost den depth b gap q+45)*digits.length+
    5*SourceRoutes.numCost den depth b gap q+33

theorem copy_bounded (archive digits den depth b : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (depthNonempty : depth≠[]) (bNonempty : b≠[]) :
    BoundedRun copyCode (Tape.mk₂ (false::archive) (FactorWalk.numRight digits den depth b gap q [])) 1368
      (Tape.mk₂ (RoutedCopy.destinationLeft 0
        (SourceRoutes.numFinish den depth b gap q (false::archive) digits))
        (PA17TMRatArithmeticCopy006.workspace digits)) (cost digits den depth b gap q) := by
  have routes:=SourceRoutes.numerator_correct den depth b gap q nonnegative depthNonempty bNonempty
  have out:=routes.out_run (false::archive) digits []
  have marked:=marker_bounded (SourceRoutes.numFinish den depth b gap q (false::archive) digits)
  have back:=routes.back_run archive digits (workSuffix 0 [])
  have prepared:=((out.seq marked).seq back)
  have copied:=RoutedCopy.copy_bounded SourceRoutes.numeratorRoute
    (SourceRoutes.numContext den depth b gap q) (SourceRoutes.numFinish den depth b gap q)
    (SourceRoutes.numCost den depth b gap q) routes archive digits 0
  have actual:=prepared.seq copied
  rw [←SourceRoutes.num_word] at actual
  exact actual.mono (by
    simp only [cost,Nat.add_mul,Nat.mul_zero,Nat.add_zero]
    omega)

def machine : Machine 2770 := PSTRTMSeq005.seqMachine FactorSource.machine copyCode

/-- A genuine original-input packet-production stage. It has computed
the factor, written the far marker, copied every risk numerator bit and
physically reached DEST. B and the original risk source are still on the
same tape. The output is not yet the RawMul two-Rat packet. -/
theorem original_numerator_actual (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1 ≤ depth) :
    ∃ trace final, Runs machine (encode [.rational risk,.natural depth]) trace final ∧
      final.Tape=Tape.mk₂ (RoutedCopy.destinationLeft 0
        (SourceRoutes.numFinish (PSTRTMThresholdRiskSource233.denominator risk)
          (PSTRTMThresholdBBackupEntry188.result risk depth).depth (FactorSource.bDigits risk depth)
          (PSTRTMThresholdBBackupEntry188.result risk depth).gap (FactorSource.factorValue risk depth : Rat)
          [false] (PSTRTMThresholdRiskSource233.numerator risk)))
        (PA17TMRatArithmeticCopy006.workspace (PSTRTMThresholdRiskSource233.numerator risk)) ∧
      trace.length ≤ 134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3+
        cost (PSTRTMThresholdRiskSource233.numerator risk) (PSTRTMThresholdRiskSource233.denominator risk)
          (PSTRTMThresholdBBackupEntry188.result risk depth).depth (FactorSource.bDigits risk depth)
          (PSTRTMThresholdBBackupEntry188.result risk depth).gap (FactorSource.factorValue risk depth : Rat) := by
  obtain ⟨front,before,first,whole,time,_space⟩:=FactorSource.original_source_actual risk depth hr hd
  have depthNonempty:=PSTRTMThresholdRiskReturnBudget230.result_depth_ne_nil risk depth hd
  have bNonempty : FactorSource.bDigits risk depth≠[] := by
    intro equal
    have length:=congrArg List.length equal
    simp only [FactorSource.bDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn,List.length_nil] at length
    have positive : 1 ≤ natBits (PaperProofs.Statistics.controllerB risk depth) := by dsimp only [natBits];omega
    omega
  obtain ⟨part,second,partTime⟩:=copy_bounded [] (PSTRTMThresholdRiskSource233.numerator risk)
    (PSTRTMThresholdRiskSource233.denominator risk) (PSTRTMThresholdBBackupEntry188.result risk depth).depth
    (FactorSource.bDigits risk depth) (PSTRTMThresholdBBackupEntry188.result risk depth).gap
    (FactorSource.factorValue risk depth : Rat) (Nat.cast_nonneg _) depthNonempty bNonempty
  have entry : before.Tape=Tape.mk₂ [false]
      (FactorWalk.numRight (PSTRTMThresholdRiskSource233.numerator risk)
        (PSTRTMThresholdRiskSource233.denominator risk) (PSTRTMThresholdBBackupEntry188.result risk depth).depth
        (FactorSource.bDigits risk depth) (PSTRTMThresholdBBackupEntry188.result risk depth).gap
        (FactorSource.factorValue risk depth : Rat) []) := by
    rw [whole]
    have word : FactorWalk.numRight (PSTRTMThresholdRiskSource233.numerator risk)
        (PSTRTMThresholdRiskSource233.denominator risk) (PSTRTMThresholdBBackupEntry188.result risk depth).depth
        (FactorSource.bDigits risk depth) (PSTRTMThresholdBBackupEntry188.result risk depth).gap
        (FactorSource.factorValue risk depth : Rat) []=FactorSource.sourceRight risk depth++[false] := by
      simp only [FactorWalk.numRight,FactorWalk.denRight,FactorWalk.marker,FactorWalk.depthRight,FactorWalk.bRight,
        FactorSource.sourceRight,FactorSource.depthSuffix,FactorSource.bSuffix,FactorSource.factorDatum,
        PSTRTMThresholdRiskMarkers232.markerTail,List.append_assoc,List.cons_append]
    rw [word]
    exact (PA17TMRatArithmeticBankCopy024.tape_append_false [false] (FactorSource.sourceRight risk depth)).symm
  let trace:=front.map (PSTRTMSeq005.leftCfg (b:=1368))++part.map (PSTRTMSeq005.rightCfg (a:=1401))
  let endTape:=Tape.mk₂ (RoutedCopy.destinationLeft 0
    (SourceRoutes.numFinish (PSTRTMThresholdRiskSource233.denominator risk)
      (PSTRTMThresholdBBackupEntry188.result risk depth).depth (FactorSource.bDigits risk depth)
      (PSTRTMThresholdBBackupEntry188.result risk depth).gap (FactorSource.factorValue risk depth : Rat)
      [false] (PSTRTMThresholdRiskSource233.numerator risk)))
    (PA17TMRatArithmeticCopy006.workspace (PSTRTMThresholdRiskSource233.numerator risk))
  let last:=PSTRTMSeq005.rightCfg (a:=1401) (⟨1368,endTape⟩ : MachineState 1368)
  refine ⟨trace,last,?_,rfl,?_⟩
  · apply PSTRTMSeq005.seq_runs FactorSource.machine copyCode _ before _ front part first
    rw [entry]
    exact second
  · simp only [trace,List.length_append,List.length_map]
    omega

end RootB23.Threshold.NumeratorCopy
