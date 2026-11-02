module

public import PaperProofs.Paid.PDROC_Simulator_030
public import PaperProofs.Paid.PDROC_Postwrite_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Synchronize the actual controller with a genuine source run until the
source leaves this written stage. All source-prefix premises are obtained
from that run at each induction step. -/
theorem simulator_postwrite_run_shadow_upto (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (seed : SimulatorSeed P Seed) (world vworld : (P.input fee hfee).World)
    (astart vstart : ℕ) (stage : P.sharedInstance.Stage) (actualBit virtualBit : Bool)
    (hwa : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
      (seed, world) astart).ledger.written stage = some actualBit)
    (hwv : (run (P.input fee hfee) C.val .uncapped accounting source
      (seed.1, vworld) vstart).ledger.written stage = some virtualBit)
    (hh : simulatorShadow P fee hfee source seed
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) astart).history =
      (run (P.input fee hfee) C.val .uncapped accounting source (seed.1, vworld) vstart).history)
    (limit : ℕ)
    (hbefore : ∀ k < limit,
      (run (P.input fee hfee) C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).halted = false ∧
      (run (P.input fee hfee) C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).cursor = stage.val) :
    ∀ k ≤ limit, simulatorShadow P fee hfee source seed
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) (astart + k)).history =
      (run (P.input fee hfee) C.val .uncapped accounting source (seed.1, vworld) (vstart + k)).history := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  have hla := simulatorRule_legal P fee hfee C accounting source
  intro k
  induction k with
  | zero => intro _; simpa only [Nat.add_zero] using hh
  | succ k ih =>
    intro hk
    have hki : k < limit := Nat.lt_of_succ_le hk
    have hi := ih (Nat.le_of_succ_le hk)
    have hv := hbefore k hki
    obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hla (seed, world) (astart + k)
    obtain ⟨vn, _, vp⟩ := run_has_prefix input C.val .uncapped accounting source hl (seed.1, vworld) (vstart + k)
    have hfields := simulator_prefix_state_projection input C.val .uncapped accounting actual seed _ _ ap
      source seed.1 _ _ vp (simulatorSeedDraw P fee hfee source) seed hi
    have ha := hfields.2.1.trans hv.1
    have hc := hfields.1.trans hv.2
    have haw := run_written_some_after input C.val .uncapped accounting actual hla (seed, world)
      astart k stage actualBit hwa
    have hvw := run_written_some_after input C.val .uncapped accounting source hl (seed.1, vworld)
      vstart k stage virtualBit hwv
    have astep := run_actualStep_of_active input C.val .uncapped accounting actual hla (seed, world) (astart + k) ha
    have vstep := run_actualStep_of_active input C.val .uncapped accounting source hl (seed.1, vworld) (vstart + k) hv.1
    have hn := simulator_postwrite_step_shadow P fee hfee C accounting source hl seed
      (input.truthAt world) (worldTapes input world) ap ha stage hc
      (by rw [haw]; exact Option.some_ne_none actualBit)
      (input.truthAt vworld) (worldTapes input vworld) vp hv.1 hi.symm hv.2
      (by rw [hvw]; exact Option.some_ne_none virtualBit) astep vstep
    simpa only [Nat.add_assoc] using hn

end PDROC
