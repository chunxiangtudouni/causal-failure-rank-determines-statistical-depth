module
public import Common.PSTR_WordBool_RawInit_Assembler018
public import Common.PSTR_WordBool_RawInit_Remaining017

/-! Real all-Datum large branch n>=4: the frozen original Assembler018
and counted remaining loop share one physical Tape. All internal count,
width and archive qualifications are derived from four actual leading
Datum values, not added as premises on the original raw input. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.LargeArchive
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicRawLoop
open RationalControllerComputation.PSTRSymbolicLaneArchive
open RationalControllerComputation.PSTRSymbolicCursorArchive
open RationalControllerComputation.PSTRTMThresholdCountdownCode164
open RationalControllerComputation.PSTRTMIncrement009

noncomputable def machine : Machine (750+Remaining.support.card+1) :=
  seqMachine Assembler.machine Remaining.machine

theorem transport_port {a b : Nat} (cfg : MachineState b) (port : Fin (b+1))
    (same : cfg.q=port) :
    (rightCfg (a:=a) cfg).q=rightLabel (a:=a) port :=
  congrArg (rightLabel (a:=a)) same

theorem transport_tape {a b : Nat} (cfg : MachineState b) (target : Tape Bool)
    (same : cfg.Tape=target) : (rightCfg (a:=a) cfg).Tape=target := same

theorem space_from_time {n : Nat} (code : Machine n) (inputLength bound : Nat)
    (path : List (MachineState n)) (time : path.length≤bound) :
    ∀ clock, visitedSpace code inputLength (path.take clock) ≤ inputLength+2*bound+1 := by
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le code inputLength (path.take clock)
  have take := (List.length_take_le' clock path).trans time
  omega

theorem cubic_space_room (size : Nat) :
    size+2*(31000*(size+1)^3)+1≤100000*(size+1)^3 := by
  nlinarith only [Nat.zero_le (size^2),Nat.zero_le (size^3)]

theorem field_bytes (data : List Datum) (value : Datum) (member : value∈data) :
    (encodeDatum value).length≤(data.flatMap encodeDatum).length := by
  induction data with
  | nil => simp at member
  | cons first later ih =>
    rcases List.mem_cons.mp member with rfl | present
    · simp only [List.flatMap_cons,List.length_append]; omega
    · have short := ih present
      simp only [List.flatMap_cons,List.length_append]
      omega

theorem actual (first second third fourth : Datum) (later : List Datum) :
    let data := first::second::third::fourth::later
    let originalDigits := PSTRTMNatValue017.rawPayload data.length
    let base := false::HeaderCopy.bank originalDigits
    ∃ endDigits path final, Runs machine (encode data) path final ∧
      final.q=rightLabel (a:=750) (b:=Remaining.support.card) Remaining.haltPort ∧
      final.Tape=archiveTape data base endDigits [] true ∧
      valueDigits endDigits=0 ∧ endDigits.length=originalDigits.length ∧
      path.length≤31000*((encode data).length+1)^3 ∧ ∀ clock,
        visitedSpace machine (encode data).length (path.take clock)≤
          100000*((encode data).length+1)^3 := by
  classical
  dsimp only
  let data := first::second::third::fourth::later
  let remaining := third::fourth::later
  let originalDigits := PSTRTMNatValue017.rawPayload data.length
  let digits := predDigits (predDigits originalDigits)
  let base := false::HeaderCopy.bank originalDigits
  let size := (encode data).length
  let payload := (data.flatMap encodeDatum).length
  obtain ⟨front,frontFinal,frontRun,frontTape,frontTime,_frontSpace⟩ :=
    Assembler.actual_large first second remaining
  have nonempty : remaining≠[] := by simp [remaining]
  have archiveRoom : 3≤(allDatumPairs [first,second]).length := by
    have room := two_datums_archive_room first second
    omega
  have count : valueDigits digits=remaining.length := by
    have originalValue : valueDigits originalDigits=data.length :=
      PSTRTMNatValue017.valueDigits_rawPayload data.length
    have wholeLength : data.length=remaining.length+2 := by simp [data,remaining]
    have positive0 : 0<valueDigits originalDigits := by
      simp [originalDigits,PSTRTMNatValue017.valueDigits_rawPayload,data]
    have sub0 := pred_value originalDigits (has_true_of_value_pos originalDigits positive0)
    have enough : 0<valueDigits (predDigits originalDigits) := by
      omega
    have sub1 := pred_value (predDigits originalDigits)
      (has_true_of_value_pos (predDigits originalDigits) enough)
    change valueDigits (predDigits (predDigits originalDigits))=remaining.length
    omega
  have widthEq : digits.length=originalDigits.length := by simp only [digits,pred_length]
  have originalWidth : originalDigits.length=natBits data.length := by
    simp only [originalDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have width : 3≤digits.length := by
    rw [widthEq,originalWidth]
    have nonzero : data.length≠0 := by simp [data]
    have logBound : 2≤Nat.log2 data.length := (Nat.le_log2 nonzero).mpr (by simp [data])
    unfold natBits
    omega
  have sized : ∀ value∈remaining, (encodeDatum value).length≤payload := by
    intro value member
    apply field_bytes data value
    exact List.mem_cons_of_mem first (List.mem_cons_of_mem second member)
  obtain ⟨endDigits,back,backFinal,backRun,backPort,backTape,endValue,endWidth,backTime,_backSpace⟩ :=
    Remaining.actual [first,second] remaining base digits [] payload size nonempty archiveRoom width count sized
  have backRun' : RunsFrom Remaining.machine ⟨0,frontFinal.Tape⟩ back backFinal := by
    rw [frontTape]
    simpa only [pendingSuffix,countedPairLeft,HeaderCopy.bank,digits,originalDigits,base,
      data,remaining,allDatumPairs_cells,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.reverse_append,List.append_assoc,rawTail] using backRun
  let path := front.map (leftCfg (b:=Remaining.support.card))++back.map (rightCfg (a:=750))
  let final := rightCfg (a:=750) backFinal
  have run := seq_runs Assembler.machine Remaining.machine (encode data) frontFinal backFinal
    front back frontRun backRun'
  have layout : size=2*natBits data.length+2+payload := by
    simp only [size,payload,encode,List.length_append,PSTRTMLength004.encodeNat_length,
      List.length_singleton]; omega
  have payloadRoom : payload≤size := by omega
  have pairsSize := pairs_bytes data
  have countSize := count_bytes data
  have pairRoom : (allDatumPairs data).length≤size := by omega
  have remainingRoom : remaining.length≤size := by
    have whole : data.length=remaining.length+2 := by simp [data,remaining]
    omega
  have digitRoom : digits.length≤size := by
    rw [widthEq,originalWidth]
    omega
  have dataEq : [first,second]++remaining=data := by rfl
  rw [dataEq] at backTape backTime
  have cycle : cycleBudget (allDatumPairs data).length digits.length payload≤512*(size+1)^2 := by
    unfold cycleBudget
    nlinarith
  have tailBound := (Nat.mul_le_mul remainingRoom cycle)
  have time : path.length≤31000*(size+1)^3 := by
    have inputCube : (size+1)^2≤(size+1)^3 := by nlinarith [Nat.zero_le (size^2)]
    simp only [path,List.length_append,List.length_map]
    change front.length≤30000*(size+1)^2 at frontTime
    nlinarith [Nat.zero_le (size^2),Nat.zero_le (size^3)]
  have run' : Runs machine (encode data) path final := run
  have port' := transport_port (a:=750) (b:=Remaining.support.card) backFinal _ backPort
  have tape' := transport_tape (a:=750) (b:=Remaining.support.card) backFinal _ backTape
  refine ⟨endDigits,path,final,run',port',tape',endValue,?_,time,?_⟩
  · exact endWidth.trans widthEq
  · intro clock
    have cells := space_from_time machine size (31000*(size+1)^3) path time clock
    change visitedSpace machine size (path.take clock)≤100000*(size+1)^3
    exact cells.trans (cubic_space_room size)

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.LargeArchive
