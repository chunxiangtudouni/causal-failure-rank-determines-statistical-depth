module
public import Common.PSTR_WordBool_RawInit_Assembler018

/-! Original n=2 and n=3 archive branches, both tags at every position.
No counted remaining-loop header-room qualification is imposed on these
small inputs. The true footer is retained by the actual raw parsers. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Small23
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicPairedArchive

def twoMachine : Machine 750 := Assembler.machine
def threeMachine : Machine 860 := seqMachine Assembler.machine datumCompactMachine

theorem actual_two (first second : Datum) : ∃ path final,
    Runs twoMachine (encode [first,second]) path final ∧
    final.Tape=Tape.mk₂ (countedPairLeft first second []) [true] ∧
    path.length≤30000*((encode [first,second]).length+1)^2 ∧ ∀ clock,
      visitedSpace twoMachine (encode [first,second]).length (path.take clock)≤
        30000*((encode [first,second]).length+1)^2 := by
  simpa only [twoMachine,rawTail,List.flatMap_nil,List.nil_append] using
    Assembler.actual_large first second []

theorem actual_three (first second third : Datum) : ∃ path final,
    Runs threeMachine (encode [first,second,third]) path final ∧
    final.Tape=Tape.mk₂ ((pairedDatum third).reverse++countedPairLeft first second [third]) [true] ∧
    path.length≤30128*((encode [first,second,third]).length+1)^2 ∧ ∀ clock,
      visitedSpace threeMachine (encode [first,second,third]).length (path.take clock)≤
        100000*((encode [first,second,third]).length+1)^2 := by
  obtain ⟨front,frontFinal,frontRun,frontTape,frontTime,_frontSpace⟩ :=
    Assembler.actual_large first second [third]
  obtain ⟨back,backFinal,backRun,backTape,backTime,_backSpace⟩ :=
    raw_datum_parse_compact (countedPairLeft first second [third]) third [true]
  have backRun' : RunsFrom datumCompactMachine ⟨0,frontFinal.Tape⟩ back backFinal := by
    rw [frontTape]
    simpa only [rawTail,List.flatMap_cons,List.flatMap_nil,List.append_nil] using backRun
  let path := front.map (leftCfg (b:=109))++back.map (rightCfg (a:=750))
  let final := rightCfg (a:=750) backFinal
  have run := seq_runs Assembler.machine datumCompactMachine (encode [first,second,third])
    frontFinal backFinal front back frontRun backRun'
  have thirdRoom : (encodeDatum third).length+1≤(encode [first,second,third]).length+1 := by
    simp only [encode,List.length_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_singleton]
    omega
  have backBound := backTime.trans (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left thirdRoom 2))
  have time : path.length≤30128*((encode [first,second,third]).length+1)^2 := by
    simp only [path,List.length_append,List.length_map]
    omega
  refine ⟨path,final,run,backTape,time,?_⟩
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le threeMachine
    (encode [first,second,third]).length (path.take clock)
  have take := List.length_take_le' clock path
  have inputBound : (encode [first,second,third]).length≤((encode [first,second,third]).length+1)^2 := by
    nlinarith
  have positive : 0<((encode [first,second,third]).length+1)^2 := by positivity
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Small23
