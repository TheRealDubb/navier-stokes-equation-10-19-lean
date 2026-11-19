import Lemma105PaperFlux

/-! A pressure-independent check of the zero weighted-velocity case. -/

noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.PaperFluxZero
open ProblemStatement Comparison Lemma105PaperFlux

/-- Vanishing of the localized sixth norm forces the actual flux integrand to vanish a.e. -/
theorem integrand_ae_zero {ρ : Space → ℝ} {w : Space → Space}
    (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) (hw : Continuous w)
    (hzero : comparisonLpNorm 6 (fun x => ρ x ^ 4 • w x) = 0) (π : Space → ℝ) :
    ∀ᵐ x ∂volume, π x * fderiv ℝ (fun y => ρ y ^ 8) x (w x) = 0 := by
  let f := fun x => ρ x ^ 4 • w x
  have hs4 : HasCompactSupport (fun x => ρ x ^ 4) :=
    hs.comp_left (g := fun s : ℝ => s ^ 4) (by norm_num)
  have hm : MemLp f 6 volume :=
    ((hρ.continuous.pow 4).smul hw).memLp_of_hasCompactSupport hs4.smul_right
  have hn : eLpNorm f 6 volume = 0 :=
    ((ENNReal.toReal_eq_zero_iff (eLpNorm f 6 volume)).mp hzero).resolve_right hm.eLpNorm_ne_top
  have hvan := (eLpNorm_eq_zero_iff hm.1 (by norm_num : (6 : ℝ≥0∞) ≠ 0)).mp hn
  filter_upwards [hvan] with x hx
  change ρ x ^ 4 • w x = 0 at hx
  rw [← fourthPower_mul_residual w (hρ.differentiable (by simp) x)]
  rcases smul_eq_zero.mp hx with hx | hx
  · simp [hx]
  · simp [Lemma105PaperFlux.residual, hx]

end NavierStokesR3.PaperFluxZero
