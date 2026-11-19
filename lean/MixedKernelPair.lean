import MixedCommutator
import NavierStokes.R3.LpNormTools

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.MixedCommutator

open ProblemStatement Comparison

/-- Transfer the absolutely integrated mixed Young bound to a dominated complex pairing. -/
theorem norm_kernel_pair_le {g k : Space → ℝ} {r : Space → ℂ}
    {K : Space → Space → ℝ} (hg : Measurable g) (hk : Measurable k) (hr : Measurable r)
    (hg43 : MemLp g (4 / 3) volume) (hk43 : MemLp k (4 / 3) volume) (hr2 : MemLp r 2 volume)
    (hdom : ∀ x y, ‖K x y‖ ≤ ‖k (y - x)‖) :
    ‖∫ x, g x • ∫ y, K x y • r y‖ ≤
      comparisonLpNorm 2 r * (comparisonLpNorm (4 / 3) g * comparisonLpNorm (4 / 3) k) := by
  have hmajor (x : Space) :
      ‖g x • ∫ y, K x y • r y‖ₑ ≤ ∫⁻ y, ‖g x‖ₑ * ‖k (y - x)‖ₑ * ‖r y‖ₑ := by
    rw [enorm_smul]
    calc
      _ ≤ ‖g x‖ₑ * ∫⁻ y, ‖K x y • r y‖ₑ :=
        mul_le_mul_of_nonneg_left (enorm_integral_le_lintegral_enorm _) (by positivity)
      _ ≤ ‖g x‖ₑ * ∫⁻ y, ‖k (y - x)‖ₑ * ‖r y‖ₑ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply lintegral_mono
        intro y
        change ‖K x y • r y‖ₑ ≤ ‖k (y - x)‖ₑ * ‖r y‖ₑ
        rw [enorm_smul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hdom x y)
      _ = _ := by
        rw [← lintegral_const_mul (‖g x‖ₑ)
          (f := fun y => ‖k (y - x)‖ₑ * ‖r y‖ₑ) (by fun_prop)]
        simp only [mul_assoc]
  have hswap : (∫⁻ x, ∫⁻ y, ‖g x‖ₑ * ‖k (y - x)‖ₑ * ‖r y‖ₑ) =
      ∫⁻ y, ‖r y‖ₑ * majorant (fun x => ‖g x‖ₑ) (fun z => ‖k z‖ₑ) y := by
    rw [lintegral_lintegral_swap (by fun_prop)]
    apply lintegral_congr
    intro y
    rw [majorant, lintegral_mul_const _ (by fun_prop), mul_comm]
  have hraw := (enorm_integral_le_lintegral_enorm (μ := (volume : Measure Space))
    (fun x : Space => g x • ∫ y, K x y • r y)).trans (lintegral_mono hmajor)
  rw [hswap] at hraw
  have hy := hraw.trans (paired_majorant_le hg.enorm hk.enorm hr.enorm)
  have hnorm : ‖∫ x, g x • ∫ y, K x y • r y‖ₑ ≤ eLpNorm r 2 volume *
      (eLpNorm g (4 / 3) volume * eLpNorm k (4 / 3) volume) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := g) (p := 4 / 3) (by norm_num) (by finiteness),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (f := k) (p := 4 / 3) (by norm_num) (by finiteness)]
    norm_num only [ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.rpow_two]
    convert hy using 1
  have hfin := ENNReal.mul_ne_top hr2.eLpNorm_ne_top
    (ENNReal.mul_ne_top hg43.eLpNorm_ne_top hk43.eLpNorm_ne_top)
  simpa only [comparisonLpNorm, ENNReal.toReal_mul, toReal_enorm] using
    ENNReal.toReal_mono hfin hnorm

end NavierStokesR3.MixedCommutator
