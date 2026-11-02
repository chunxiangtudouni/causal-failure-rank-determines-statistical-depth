module

public import Common.PSTR_SYM_RawBootstrapPorts_056

/-! SOURCEONLY. Same-table composition of the original binary-header
producer, two real counter rounds and the actual N/q Datum parser. The
original-input adapter and finite Bool time/space contract are separate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawBootstrap

open Turing PSTRTMSeq005 PSTRTMIncrement009 PSTRTMNatValue017 PSTRTMRawNat010
open PSTRTMThresholdCountdownCode164 PSTRSymbolicCounter PSTRSymbolicPairedArchive
open PSTRSymbolicZeroTail PSTRSymbolicCursorPorts PSTRSymbolicCursorCode
open PA17TMRatArithmeticParse002

def bootstrapInput (count stage tools : Nat) (suffix : List Bool) : List Bool :=
  encodeNat count ++ encodeDatum (.natural stage) ++ encodeDatum (.natural tools) ++ suffix

def bootstrapTape (count stage tools : Nat) (suffix : List Bool) : Tape Bool :=
  Tape.mk₂ ((pairedDatum (.natural tools)).reverse ++ (pairedDatum (.natural stage)).reverse ++
    false :: (leftBlocks (afterTwo count).reverse ++ [false])) suffix

theorem actual_bootstrap (count stage tools : Nat) (suffix : List Bool) (room : 2 ≤ count) :
    ∃ (trace : List (TM0.Cfg Bool BootLabel)) (final : TM0.Cfg Bool BootLabel),
      trace.head? = some ⟨.entry 0,Tape.mk₁ (bootstrapInput count stage tools suffix)⟩ ∧
      trace.IsChain (fun before after => TM0.step bootstrapCode before = some after) ∧
      trace.getLast? = some final ∧ final.q = .halt ∧
      final.Tape = bootstrapTape count stage tools suffix ∧ TM0.step bootstrapCode final = none ∧
      trace.length ≤ 32 * (natBits count + 1)^2 + 18 * natBits count + 32 +
        128 * ((encodeDatum (.natural stage)).length + 1)^2 +
        128 * ((encodeDatum (.natural tools)).length + 1)^2 := by
  let digits := rawPayload count
  let once := predDigits digits
  let twice := afterTwo count
  let tail := encodeNat stage ++ encodeDatum (.natural tools) ++ suffix
  let endOnce := Tape.mk₂ (leftBlocks once.reverse ++ [false]) (false :: false :: tail)
  let endTwice := Tape.mk₂ (leftBlocks twice.reverse ++ [false]) (false :: false :: tail)
  let header := false :: (leftBlocks twice.reverse ++ [false])
  have positive := two_count_rounds count room
  have initialRun := counterEntry_runsFrom count tail
  have firstRun := counterRound_runsFrom [] digits tail positive.1
  have oneRun := right_one_runsFrom endOnce
  have rewindRun := fieldBack_runsFrom [] once (false :: tail)
  have secondRun := counterRound_runsFrom [] once tail positive.2.1
  have twoRun := right_one_runsFrom endTwice
  obtain ⟨pairTrace,pairFinal,pairRun,pairTape,pairTime⟩ := stage_tool_pair header suffix stage tools
  let part0 := nativePart bootstrapCode counterEntryMachine BootLabel.entry (fun _ => .first 0)
    (by intro q bit; rfl) _ _ _ initialRun
  let part1 := nativePart bootstrapCode counterRoundMachine BootLabel.first (fun _ => .one 18)
    (by intro q bit; rfl) _ _ _ firstRun
  let partOne := nativePart bootstrapCode right19Machine BootLabel.one (fun _ => .rewind 0)
    (by intro q bit; rfl) _ _ _ oneRun
  let partRewind := nativePart bootstrapCode fieldBackMachine BootLabel.rewind (fun _ => .second 0)
    (by intro q bit; rfl) _ _ _ rewindRun
  let part2 := nativePart bootstrapCode counterRoundMachine BootLabel.second (fun _ => .two 18)
    (by intro q bit; rfl) _ _ _ secondRun
  let partTwo := nativePart bootstrapCode right19Machine BootLabel.two (fun _ => .pair 0)
    (by intro q bit; rfl) _ _ _ twoRun
  let partPair := nativePart bootstrapCode pairMachine BootLabel.pair (fun _ => .halt)
    (by intro q bit; rfl) _ _ _ pairRun
  have edge0 := nativePart_return bootstrapCode counterEntryMachine BootLabel.entry (fun _ => .first 0)
    (by intro q bit; rfl) _ _ _ initialRun
  have bridge0 : TM0.step bootstrapCode (tagCfg BootLabel.entry (counterEntryFinal count tail)) =
      some (tagCfg BootLabel.first (⟨0,Tape.mk₂ [false] (blocks digits ++ false :: false :: tail)⟩ : MachineState 16)) := by
    simpa only [counterEntry_final_tape,tagCfg,digits] using edge0
  have edge1 := nativePart_return bootstrapCode counterRoundMachine BootLabel.first (fun _ => .one 18)
    (by intro q bit; rfl) _ _ _ firstRun
  have right18 : (18 : Fin 20) = ⟨18,by decide⟩ := by decide
  rw [right18] at edge1
  have bridge1 : TM0.step bootstrapCode (tagCfg BootLabel.first (counterRoundFinal [] digits tail)) =
      some (tagCfg BootLabel.one (rightState 18 (by decide) endOnce)) := by
    simpa only [counterRound_final_tape,tagCfg,rightState,endOnce,once] using edge1
  have movedOne : endOnce.move .right = Tape.mk₂ (false :: (leftBlocks once.reverse ++ [false])) (false :: tail) :=
    counter_end_right [] once tail
  have edgeOne := nativePart_return bootstrapCode right19Machine BootLabel.one (fun _ => .rewind 0)
    (by intro q bit; rfl) _ _ _ oneRun
  have bridgeOne : TM0.step bootstrapCode (tagCfg BootLabel.one (rightState 19 (by decide) (endOnce.move .right))) =
      some (tagCfg BootLabel.rewind (⟨0,Tape.mk₂
        (false :: (leftBlocks once.reverse ++ [false])) (false :: tail)⟩ : MachineState 5)) := by
    simpa only [rightState,tagCfg,movedOne] using edgeOne
  have edgeRewind := nativePart_return bootstrapCode fieldBackMachine BootLabel.rewind (fun _ => .second 0)
    (by intro q bit; rfl) _ _ _ rewindRun
  have bridgeRewind : TM0.step bootstrapCode (tagCfg BootLabel.rewind (fieldBackFinal [] once (false :: tail))) =
      some (tagCfg BootLabel.second (⟨0,Tape.mk₂ [false] (blocks once ++ false :: false :: tail)⟩ : MachineState 16)) := by
    simpa only [fieldBack_final_tape,tagCfg] using edgeRewind
  have edge2 := nativePart_return bootstrapCode counterRoundMachine BootLabel.second (fun _ => .two 18)
    (by intro q bit; rfl) _ _ _ secondRun
  rw [right18] at edge2
  have bridge2 : TM0.step bootstrapCode (tagCfg BootLabel.second (counterRoundFinal [] once tail)) =
      some (tagCfg BootLabel.two (rightState 18 (by decide) endTwice)) := by
    simpa only [counterRound_final_tape,tagCfg,rightState,endTwice,twice,afterTwo,once,digits] using edge2
  have movedTwo : endTwice.move .right = Tape.mk₂ header (false :: tail) := counter_end_right [] twice tail
  have edgeTwo := nativePart_return bootstrapCode right19Machine BootLabel.two (fun _ => .pair 0)
    (by intro q bit; rfl) _ _ _ twoRun
  have bridgeTwo : TM0.step bootstrapCode (tagCfg BootLabel.two (rightState 19 (by decide) (endTwice.move .right))) =
      some (tagCfg BootLabel.pair (⟨0,Tape.mk₂ header
        (encodeDatum (.natural stage) ++ encodeDatum (.natural tools) ++ suffix)⟩ : MachineState 219)) := by
    simpa only [rightState,tagCfg,movedTwo,tail,encodeDatum,List.cons_append,List.append_assoc] using edgeTwo
  let final : TM0.Cfg Bool BootLabel := ⟨.halt,pairFinal.Tape⟩
  let terminalPart : RunPart bootstrapCode final final := ⟨[final],rfl,.singleton _,rfl⟩
  have bridgePair : TM0.step bootstrapCode (tagCfg BootLabel.pair pairFinal) = some final :=
    nativePart_return bootstrapCode pairMachine BootLabel.pair (fun _ => .halt)
      (by intro q bit; rfl) _ _ _ pairRun
  let all := ((((((part0.append part1 bridge0).append partOne bridge1).append partRewind bridgeOne).append
    part2 bridgeRewind).append partTwo bridge2).append partPair bridgeTwo).append terminalPart bridgePair
  refine ⟨all.trace,final,?_,all.chain,all.last,rfl,?_,bootstrap_halt _,?_⟩
  · simpa only [tagCfg,bootstrapInput,tail,encodeDatum,List.cons_append,List.append_assoc] using all.head
  · exact pairTape
  · have initialTime := counterEntry_time_le count tail
    have firstTime := counterRound_time_le [] digits tail positive.1
    have secondTime := counterRound_time_le [] once tail positive.2.1
    have width : once.length = natBits count := by
      simp only [once,pred_length,digits,PSTRSymbolicLocator.rawPayload_length]
    have originalWidth : digits.length = natBits count := PSTRSymbolicLocator.rawPayload_length count
    have size0 : part0.trace.length = (counterEntryTrace count tail).length := List.length_map _
    have size1 : part1.trace.length = (counterRoundTrace [] digits tail).length := List.length_map _
    have sizeOne : partOne.trace.length = 2 := (List.length_map _).trans (right_one_length endOnce)
    have sizeRewind : partRewind.trace.length = 2 * once.length + 5 :=
      (List.length_map _).trans (fieldBackTrace_length [] once (false :: tail))
    have size2 : part2.trace.length = (counterRoundTrace [] once tail).length := List.length_map _
    have sizeTwo : partTwo.trace.length = 2 := (List.length_map _).trans (right_one_length endTwice)
    have sizePair : partPair.trace.length = pairTrace.length := List.length_map _
    simp only [all,RunPart.append_length,size0,size1,sizeOne,sizeRewind,size2,sizeTwo,sizePair,
      terminalPart,List.length_cons,List.length_nil]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawBootstrap
