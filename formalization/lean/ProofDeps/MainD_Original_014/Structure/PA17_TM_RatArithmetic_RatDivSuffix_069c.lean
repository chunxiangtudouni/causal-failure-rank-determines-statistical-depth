module
public import Structure.PA17_TM_RatArithmetic_RatDivSuffix_069b

/-! This is the normal, physically observed nonzero-D INTERNAL branch.
It runs the unchanged frozen 57 program from its real phase4 entry.
The final original all-input division caller must also execute the real
D-zero path; no public original operation is qualified by this hypothesis. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivSuffix069

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticWideCache045
open PA17TMRatArithmeticMulClosure059 PA17TMRatArithmeticMulController057
open PA17TMRatArithmeticRatDivFields066

def normalTimeCoefficient : Nat := 3*roundCoefficient+finishCoefficient

def normalResourceCoefficient : Nat := 2*normalTimeCoefficient+2

theorem normalResourceCoefficient_pos : 0<normalResourceCoefficient := by
  unfold normalResourceCoefficient
  omega

theorem normal_runs (x y : Rat) (hd : divDenominator x y≠0) (gapM gapD : Nat)
    (hM : gapM≤2*allocationK*(fieldWidth x y)^2)
    (hD : gapD≤2*allocationK*(fieldWidth x y)^2) :
    ∃ trace final, PSTRTMSeq005.RunsFrom mulMachine
        (entryCfg (4 : Fin 17) (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
          (bankHeader x y [mRecord x y gapM,dRecord x y gapD])) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (x/y)]) ∧
      trace.length≤normalTimeCoefficient*originalPower x y := by
  let memory := PA17TMRatArithmeticMulStart049.actualMemory x y
  obtain ⟨gapG,tg,lastG,_lowerG,upperG,segG,stepG,lenG⟩ := g_segment x y memory gapM gapD hM hD
  obtain ⟨gapU,tu,lastU,_lowerU,upperU,segU,stepU,lenU⟩ := u_segment x y memory gapM gapD gapG hM hD upperG
  obtain ⟨gapV,tv,lastV,_lowerV,upperV,segV,stepV,lenV⟩ := v_segment x y memory gapM gapD gapG gapU hM hD upperG upperU
  obtain ⟨tf,final,runF,whole,lenF⟩ := finish_segment x y hd gapM gapD gapG gapU gapV hM hD upperG upperU upperV
  have joinedGU := segment_append mulMachine _ lastG _ lastU tg tu segG segU stepG
  have joinedGUV := segment_append mulMachine _ lastU _ lastV _ tv joinedGU segV stepU
  have segF : Segment mulMachine _ tf final := ⟨runF.1,runF.2.1,runF.2.2.1⟩
  have joined := segment_append mulMachine _ lastV _ final _ tf joinedGUV segF stepV
  let trace := ((tg++tu)++tv)++tf
  have actual : PSTRTMSeq005.RunsFrom mulMachine
      (entryCfg (4 : Fin 17) (widen64 memory) (bankHeader x y [mRecord x y gapM,dRecord x y gapD])) trace final :=
    segment_runsFrom mulMachine _ _ _ joined runF.2.2.2
  have length : trace.length≤normalTimeCoefficient*originalPower x y := by
    simp only [trace,List.length_append]
    calc
      _ ≤ roundCoefficient*originalPower x y+roundCoefficient*originalPower x y+
          roundCoefficient*originalPower x y+finishCoefficient*originalPower x y :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add lenG lenU) lenV) lenF
      _ = _ := by unfold normalTimeCoefficient;ring
  exact ⟨trace,final,actual,whole,length⟩

theorem normal_contract (x y : Rat) (hd : divDenominator x y≠0) (gapM gapD : Nat)
    (hM : gapM≤2*allocationK*(fieldWidth x y)^2)
    (hD : gapD≤2*allocationK*(fieldWidth x y)^2) :
    ∃ trace final, PSTRTMSeq005.RunsFrom mulMachine
        (entryCfg (4 : Fin 17) (widen64 (PA17TMRatArithmeticMulStart049.actualMemory x y))
          (bankHeader x y [mRecord x y gapM,dRecord x y gapD])) trace final ∧
      final.Tape=Tape.mk₁ (encode [.rational (x/y)]) ∧
      trace.length≤normalResourceCoefficient*originalPower x y ∧
      ∀ prefixLength, visitedSpace mulMachine (encode [.rational x,.rational y]).length
        (trace.take prefixLength)≤normalResourceCoefficient*originalPower x y := by
  obtain ⟨trace,final,actual,whole,time⟩ := normal_runs x y hd gapM gapD hM hD
  let i := (encode [.rational x,.rational y]).length
  have input : i+1≤(i+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : (1 : Nat) ≤ i + 1) (by decide : (1 : Nat)≤4)
  have hc : normalTimeCoefficient≤normalResourceCoefficient := by unfold normalResourceCoefficient;omega
  refine ⟨trace,final,actual,whole,time.trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro prefixLength
  have space := PSTRTMTrace002.visitedSpace_le mulMachine i (trace.take prefixLength)
  have taken : (trace.take prefixLength).length≤trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  change trace.length≤normalTimeCoefficient*(i+1)^4 at time
  change visitedSpace mulMachine i (trace.take prefixLength)≤normalResourceCoefficient*(i+1)^4
  calc
    _ ≤ i+2*(trace.take prefixLength).length+1 := space
    _ ≤ i+2*(normalTimeCoefficient*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (taken.trans time)) i) 1
    _ = (i+1)+2*(normalTimeCoefficient*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(normalTimeCoefficient*(i+1)^4) := Nat.add_le_add_right input _
    _ = (2*normalTimeCoefficient+1)*(i+1)^4 := by ring
    _ ≤ normalResourceCoefficient*(i+1)^4 :=
      Nat.mul_le_mul_right _ (by unfold normalResourceCoefficient;omega)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRatDivSuffix069
