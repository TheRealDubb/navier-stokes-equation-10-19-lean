import Lemma105PaperFlux
import NavierStokes.R3.PressureFlux

/-! Compact Schwartz tests for two commutations of a single rescaled cutoff. -/

noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.PaperFluxTests

open ProblemStatement Comparison

def firstResidual (ρ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  8 * ρ x * fderiv ℝ ρ x (w x)

private theorem firstResidual_smooth {ρ : Space → ℝ} {w : Space → Space}
    (hρ : ContDiff ℝ ∞ ρ) (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (firstResidual ρ w) :=
  (contDiff_const.mul hρ).mul ((hρ.fderiv_right (m := ∞) (by simp)).clm_apply hw)

private theorem firstResidual_compact {ρ : Space → ℝ} (hs : HasCompactSupport ρ)
    (w : Space → Space) : HasCompactSupport (firstResidual ρ w) := by
  apply hs.mono
  intro x hx
  change ρ x ≠ 0
  intro hz
  apply hx
  simp [firstResidual, hz]

variable {ρ : Space → ℝ} {w : Space → Space}

def psi1 (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) (hw : ContDiff ℝ ∞ w) : ComplexTest :=
  PressureRecovery.realTest (firstResidual ρ w) (firstResidual_smooth hρ hw) (firstResidual_compact hs w)

def psi3 (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) (hw : ContDiff ℝ ∞ w) : ComplexTest :=
  PressureRecovery.realTest (Lemma105PaperFlux.residual ρ w)
    (Lemma105PaperFlux.residual_smooth hρ hw) (Lemma105PaperFlux.residual_hasCompactSupport hs w)

def psi7 (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) (hw : ContDiff ℝ ∞ w) : ComplexTest :=
  PressureRecovery.realTest (PressureFlux.fluxFunction (fun x => ρ x ^ 8) w)
    (PressureFlux.fluxFunction_smooth (hρ.pow 8) hw)
    (PressureFlux.fluxFunction_compact (hs.comp_left (g := fun s : ℝ => s ^ 8) (by norm_num)) w)

theorem psi3_eq (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) (hw : ContDiff ℝ ∞ w) (x : Space) :
    psi3 hρ hs hw x = (ρ x ^ 2) • psi1 hρ hs hw x := by
  simp only [psi3, psi1, PressureRecovery.realTest_apply, Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  unfold Lemma105PaperFlux.residual firstResidual
  ring

theorem psi7_eq (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) (hw : ContDiff ℝ ∞ w) (x : Space) :
    psi7 hρ hs hw x = (ρ x ^ 2) ^ 2 • psi3 hρ hs hw x := by
  simp only [psi7, psi3, PressureRecovery.realTest_apply, Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  change fderiv ℝ (fun y => ρ y ^ 8) x (w x) = (ρ x ^ 2) ^ 2 * Lemma105PaperFlux.residual ρ w x
  rw [← Lemma105PaperFlux.fourthPower_mul_residual w (hρ.differentiable (by simp) x)]
  ring

theorem psi1_two_le (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1)
    {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R) (hd : ∀ x, ‖fderiv ℝ ρ x‖ ≤ L / R) :
    comparisonLpNorm 2 (psi1 hρ hs hw : Space → ℂ) ≤ (8 * (L/R)) * comparisonLpNorm 2 w := by
  have hK : 0 ≤ 8 * (L/R) := by positivity
  calc
    _ = comparisonLpNorm 2 (firstResidual ρ w) := PressureFlux.lpNorm_ofReal _ _
    _ ≤ comparisonLpNorm 2 (fun x => (8 * (L/R)) • w x) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hw2.const_smul (8 * (L/R)))
      intro x
      change ‖firstResidual ρ w x‖ ≤ ‖(8 * (L/R)) • w x‖
      rw [norm_smul, Real.norm_of_nonneg hK]
      have happly := ((fderiv ℝ ρ x).le_opNorm (w x)).trans
        (mul_le_mul_of_nonneg_right (hd x) (norm_nonneg _))
      calc
        ‖firstResidual ρ w x‖ = (8 * ρ x) * ‖fderiv ℝ ρ x (w x)‖ := by
          simp [firstResidual, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]
        _ ≤ 8 * ((L/R) * ‖w x‖) := mul_le_mul (by linarith [hρ1 x]) happly
          (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    _ = _ := by rw [LpNormTools.lpNorm_const_smul, Real.norm_of_nonneg hK]

theorem psi3_four_le (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1)
    {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R) (hd : ∀ x, ‖fderiv ℝ ρ x‖ ≤ L / R) :
    comparisonLpNorm 4 (psi3 hρ hs hw : Space → ℂ) ≤ (8 * (L/R)) *
      (comparisonLpNorm 2 w ^ (1/4 : ℝ) *
        comparisonLpNorm 6 (fun x => ρ x ^ 4 • w x) ^ (3/4 : ℝ)) := by
  calc
    _ = comparisonLpNorm 4 (Lemma105PaperFlux.residual ρ w) := PressureFlux.lpNorm_ofReal _ _
    _ ≤ _ := (Lemma105PaperFlux.residual_three_four hρ hs hw hw2 hρ0 hρ1 hL hR hd).2.2.2

end NavierStokesR3.PaperFluxTests
