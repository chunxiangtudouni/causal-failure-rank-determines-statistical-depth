module

public import PaperProofs.Paid.CalibratedBackend

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory

namespace PDMenu

open PaperProofs PaperProofs.Paid

theorem calibrationMarksLaw_eval (P : Parameters) (stage : P.sharedInstance.Stage)
    (level : Fin (P.certificate.M + 1)) :
    P.calibrationMarksLaw.map (fun marks => marks stage level) =
      Statistics.BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight level.val) := by
  exact ((measurePreserving_eval (fun index : Fin (P.certificate.M + 1) =>
      Statistics.BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight index.val)) level).comp
    (measurePreserving_eval (fun _ : P.sharedInstance.Stage => Measure.pi (fun index : Fin (P.certificate.M + 1) =>
      Statistics.BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight index.val))) stage)).map_eq

theorem calibrationMarksClaims (P : Parameters) : P.CalibrationMarksClaims := by
  intro stage level
  have hmark : Measurable (fun marks : P.CalibrationMarks => marks stage level) :=
    (measurable_pi_apply level).comp (measurable_pi_apply stage)
  have hfair : Measurable (fun seed : MenuSeed P.certificate.stages P.tools => seed stage) :=
    measurable_pi_apply stage
  have hprod := Measure.map_prod_map (menuSeedLaw P.certificate.stages P.tools) P.calibrationMarksLaw
    hfair hmark
  have hmenu : (menuSeedLaw P.certificate.stages P.tools).map (fun seed => seed stage) =
      Statistics.BinarySymmetric.Parameters.fairGuessLaw :=
    menuSeedLaw_eval P.certificate.stages P.tools stage
  rw [hmenu, calibrationMarksLaw_eval] at hprod
  have hswap := congrArg (fun μ => μ.map Prod.swap) hprod
  rw [Measure.prod_swap, Measure.map_map measurable_swap
    (hfair.prodMap hmark)] at hswap
  exact hswap.symm

end PDMenu
