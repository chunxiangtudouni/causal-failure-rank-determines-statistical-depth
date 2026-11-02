module

public import PaperProofs.Structure.PA17_UniformGenerator_035ac
public import PaperProofs.Structure.PA17_UniformGenerator_035n
public import PaperProofs.Structure.PA17_UniformGenerator_035g
public import PaperProofs.Structure.PA17_UniformGenerator_035i

/-! One dimension-independent finite generator source and its syntax-based
stream clock bound. Runtime arguments are only the original[N,q,t] ROM. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ae

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035e PA17UniformGenerator035g
  PA17UniformGenerator035i PA17UniformGenerator035j PA17UniformGenerator035k PA17UniformGenerator035m PA17UniformGenerator035n PA17UniformGenerator035ac

def cursorInit : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.constant .value 0)), .base (.base (.storeHeap .index .value))]

def generator (templates : List Template) : List PackingOp :=
  dimensionPrelude 0 ++ cursorInit ++ streams 64 0 3 1024 48 templates ++
    PA17UniformGenerator035g.copyBlock 0 1024 (48 + streamLength 64 templates)

theorem generator_length (templates : List Template) : (generator templates).length = streamLength 64 templates + 63 := by
  have hi : cursorInit.length = 3 := rfl
  simp only [generator, List.length_append, dimensionPrelude_length, hi, streams_length, PA17UniformGenerator035g.copyBlock_length]
  omega

def start : NatState := ⟨fun _ => 0, fun _ => 0, 0, false⟩

theorem start_toWord (bits : Nat) : start.toWord bits = packingInitial (fun _ => BitVec.ofNat bits 0) := rfl

def preparedEnv (N q : Nat) : Nat → Nat := fun address =>
  if address = 1 then CapacityBits.width q else if address = 2 then indexWidth 32 N q else 0

def streamFactor (stack : Nat) : List Template → Nat
  | [] => 0
  | first :: later => factor stack first + 23 + streamFactor stack later

def StreamsProductive (rom : PhysicalROM) (environment : Nat → Nat) (saved count : Nat) : List Template → Prop
  | [] => True
  | first :: later =>
      let updated := Function.update environment saved count
      Productive rom updated first ∧
        StreamsProductive rom environment saved (count + (first.denote rom updated).length + 1) later

theorem streamClock_le_output (templates : List Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (stack saved count : Nat) (hp : StreamsProductive rom environment saved count templates) :
    streamClock rom environment stack saved count templates ≤
      streamFactor stack templates * ((streamWords rom environment saved count templates).length + 1) := by
  induction templates generalizing count with
  | nil => simp only [streamClock, streamFactor, Nat.zero_mul, le_refl]
  | cons first later ih =>
    have hf := clock_le_output first rom (Function.update environment saved count) stack hp.1
    have hl := ih _ hp.2
    simp only [streamClock, streamFactor, streamWords, List.length_cons, List.length_append, measuredClock]
    nlinarith

def stepsBeforeHalt (templates : List Template) (N q t : Nat) : Nat :=
  let rom := PA17Generator.dimensionROM N q t
  let environment := preparedEnv N q
  dimensionClock N q + 3 + streamClock rom environment 64 3 0 templates +
    (9 * (streamWords rom environment 3 0 templates).length + 8)

theorem generator_trace_le (templates : List Template) (N q t bits : Nat)
    (hp : StreamsProductive (PA17Generator.dimensionROM N q t) (preparedEnv N q) 3 0 templates) :
    (packingDynamicTrace (PA17Generator.dimensionROM N q t) (generator templates)
      (stepsBeforeHalt templates N q t + 1) (packingInitial (fun _ => BitVec.ofNat bits 0))).length ≤
      12 * (6 * N + 12 * q + 55 +
        (streamFactor 64 templates + 9) * ((streamWords (PA17Generator.dimensionROM N q t) (preparedEnv N q) 3 0 templates).length + 1)) := by
  have ht := dynamicTrace_length_le (PA17Generator.dimensionROM N q t) (generator templates) bits
    (stepsBeforeHalt templates N q t + 1) (packingInitial (fun _ => BitVec.ofNat bits 0))
  have hc := dimensionClock_le N q
  have hs := streamClock_le_output templates (PA17Generator.dimensionROM N q t) (preparedEnv N q) 64 3 0 hp
  dsimp only [stepsBeforeHalt] at ht ⊢
  nlinarith

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ae
