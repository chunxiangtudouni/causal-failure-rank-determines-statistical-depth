module
public import Common.PSTR_WordBool_RawInit_Assembler018

/-! The original singleton-list branch, through the real retained header
and both Datum tag parsers. This supplies the physical paired source and
unread TRUE footer. Reverse export and final Fin16 assembly are separate. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Small1
open Turing RationalControllerComputation
open RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicPairedArchive

def singletonHeader : List Bool :=
  false :: (HeaderCopy.bank (PSTRTMNatValue017.rawPayload 1) ++
    false :: false :: HeaderCopy.bank (PSTRTMNatValue017.rawPayload 1))

def machine : Machine 213 := seqMachine retainedHeaderMachine datumCompactMachine

theorem actual (value : Datum) : ∃ path final,
    Runs machine (encode [value]) path final ∧
    final.Tape = Tape.mk₂ ((pairedDatum value).reverse++singletonHeader) [true] ∧
    path.length≤1152*((encode [value]).length+1)^2 ∧
    ∀ clock, visitedSpace machine (encode [value]).length (path.take clock)≤
      4096*((encode [value]).length+1)^2 := by
  obtain ⟨header,headerFinal,headerRun,_port,headerTape,headerTime,_space⟩ :=
    actual_retained_header [value]
  obtain ⟨body,bodyFinal,bodyRun,bodyTape,bodyTime,_bodySpace⟩ :=
    raw_datum_parse_compact singletonHeader value [true]
  have bodyRun' : RunsFrom datumCompactMachine ⟨0,headerFinal.Tape⟩ body bodyFinal := by
    rw [headerTape]
    simpa only [singletonHeader,List.length_singleton,rawTail,List.flatMap_cons,
      List.flatMap_nil,List.append_nil] using bodyRun
  let path := header.map (leftCfg (b:=109))++body.map (rightCfg (a:=103))
  let final := rightCfg (a:=103) bodyFinal
  have run := seq_runs retainedHeaderMachine datumCompactMachine (encode [value])
    headerFinal bodyFinal header body headerRun bodyRun'
  have inputRoom : (encodeDatum value).length+1≤(encode [value]).length+1 := by
    simp only [encode,List.length_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_singleton]
    omega
  have bodyBound := bodyTime.trans
    (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left inputRoom 2))
  have time : path.length≤1152*((encode [value]).length+1)^2 := by
    simp only [path,List.length_append,List.length_map]
    omega
  refine ⟨path,final,run,bodyTape,time,?_⟩
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le machine (encode [value]).length (path.take clock)
  have take := List.length_take_le' clock path
  have inputBound : (encode [value]).length≤((encode [value]).length+1)^2 := by nlinarith
  have positive : 0<((encode [value]).length+1)^2 := by positivity
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Small1
