module

public import PaperProofs.Structure.PSTR_HD_HeadsStage_057

/-! Literal positive-q heads tail. The query body occurs ONCE, at PC0.
Every later query is reached by the real final backward jump, with the same
heap and QUERY ROM. Only compile-time code offsets parameterize this list. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

def firstReturn (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .total (5 * (origin + 80)))), .jumpIfZero .old .total]

def scanLead (origin : Nat) : List PackingOp :=
  [.base (.subtract .flag .index .old),
   .base (.base (.constant .total (5 * (origin + 104)))), .jumpIfZero .flag .total,
   .base (.base (.constant .total 3)), .base (.base (.add .flag .address .total)),
   .base (.base (.loadHeap .flag .flag)),
   .base (.base (.constant .total (5 * (origin + 56)))), .jumpIfZero .flag .total,
   .base (.base (.loadHeap .value .address))] ++ successorGuard ++
  [.base (.base (.constant .total (5 * (origin + 67)))), .jumpIfZero .flag .total]

def jumpBack (target : Nat) : List PackingOp :=
  [.base (.base (.constant .flag 0)), .base (.base (.constant .total (5 * target))),
   .jumpIfZero .flag .total]

def advanceAndRepeat : List PackingOp := headsCorrect ++ jumpBack 0

def appendAndAdvance (origin : Nat) : List PackingOp := headsAppend ++ jumpBack (origin + 56)

def initializeAndScan (origin : Nat) : List PackingOp := headsInit ++ jumpBack (origin + 40)

def tailAt (origin : Nat) : List PackingOp := endpointProgram ++ stageProbe ++ firstReturn origin ++
  scanLead origin ++ advanceAndRepeat ++ appendAndAdvance origin ++ initializeAndScan origin ++ headsFinish

def headsProgram (queryBody : List PackingOp) : List PackingOp := queryBody ++ tailAt queryBody.length

theorem firstReturn_length (origin : Nat) : (firstReturn origin).length = 2 := rfl

theorem scanLead_length (origin : Nat) : (scanLead origin).length = 16 := rfl

theorem jumpBack_length (target : Nat) : (jumpBack target).length = 3 := rfl

theorem advanceAndRepeat_length : advanceAndRepeat.length = 11 := rfl

theorem appendAndAdvance_length (origin : Nat) : (appendAndAdvance origin).length = 13 := rfl

theorem initializeAndScan_length (origin : Nat) : (initializeAndScan origin).length = 24 := rfl

theorem tailAt_length (origin : Nat) : (tailAt origin).length = 111 := rfl

theorem headsProgram_length (queryBody : List PackingOp) :
    (headsProgram queryBody).length = queryBody.length + 111 := by
  simp only [headsProgram, List.length_append, tailAt_length]

theorem tailAt_code_length (origin : Nat) : (packingCode (tailAt origin)).length = 560 := by
  rw [packingCode_length, tailAt_length]

theorem headsProgram_code_length (queryBody : List PackingOp) :
    (packingCode (headsProgram queryBody)).length = 5 * queryBody.length + 560 := by
  rw [packingCode_length, headsProgram_length]
  omega

theorem tailAt_position (origin : Nat) :
    (tailAt origin).take 31 = endpointProgram ∧
    ((tailAt origin).drop 31).take 7 = stageProbe ∧
    ((tailAt origin).drop 38).take 2 = firstReturn origin ∧
    ((tailAt origin).drop 40).take 16 = scanLead origin ∧
    ((tailAt origin).drop 56).take 11 = advanceAndRepeat ∧
    ((tailAt origin).drop 67).take 13 = appendAndAdvance origin ∧
    ((tailAt origin).drop 80).take 24 = initializeAndScan origin ∧
    (tailAt origin).drop 104 = headsFinish := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tailAt_static_jumps (origin : Nat) :
    (tailAt origin)[39]'(by rw [tailAt_length]; decide) = .jumpIfZero .old .total ∧
    (tailAt origin)[42]'(by rw [tailAt_length]; decide) = .jumpIfZero .flag .total ∧
    (tailAt origin)[47]'(by rw [tailAt_length]; decide) = .jumpIfZero .flag .total ∧
    (tailAt origin)[55]'(by rw [tailAt_length]; decide) = .jumpIfZero .flag .total ∧
    (tailAt origin)[66]'(by rw [tailAt_length]; decide) = .jumpIfZero .flag .total ∧
    (tailAt origin)[79]'(by rw [tailAt_length]; decide) = .jumpIfZero .flag .total ∧
    (tailAt origin)[103]'(by rw [tailAt_length]; decide) = .jumpIfZero .flag .total := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
