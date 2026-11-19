import NavierStokes.R3.WeightedInterpolation
import NavierStokes.R3.LpNormTools

/-! The fourth-power multiplier and scalar residual test in equation (10.19).
The variable `φ` is the already rescaled spatial cutoff at radius `R`. -/

noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.Lemma105PaperFlux

open ProblemStatement Comparison

/-- Removing the fourth-power pressure multiplier leaves three powers of the cutoff. -/
def residual (φ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  8 * φ x ^ 3 * fderiv ℝ φ x (w x)

theorem fourthPower_mul_residual {φ : Space → ℝ} (w : Space → Space)
    {x : Space} (hφ : DifferentiableAt ℝ φ x) :
    φ x ^ 4 * residual φ w x = fderiv ℝ (fun y => φ y ^ 8) x (w x) := by
  have hd : fderiv ℝ (fun y => φ y ^ 8) x = (8 * φ x ^ 7) • fderiv ℝ φ x := by
    simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
      ((hasDerivAt_pow 8 (φ x)).comp_hasFDerivAt x hφ.hasFDerivAt).fderiv
  rw [hd]
  simp only [residual, _root_.smul_apply, smul_eq_mul]
  ring

theorem residual_smooth {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (residual φ w) :=
  (contDiff_const.mul (hφ.pow 3)).mul
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply hw)

theorem residual_hasCompactSupport {φ : Space → ℝ} (hs : HasCompactSupport φ)
    (w : Space → Space) : HasCompactSupport (residual φ w) := by
  apply hs.mono
  intro x hx
  change φ x ≠ 0
  intro hzero
  apply hx
  simp [residual, hzero]

private theorem norm_residual_le {φ : Space → ℝ} {w : Space → Space} (x : Space)
    (hφ : 0 ≤ φ x) {D : ℝ} (hd : ‖fderiv ℝ φ x‖ ≤ D) :
    ‖residual φ w x‖ ≤ (8 * D) * ‖φ x ^ 3 • w x‖ := by
  have happly := ((fderiv ℝ φ x).le_opNorm (w x)).trans
    (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  calc
    ‖residual φ w x‖ = 8 * φ x ^ 3 * ‖fderiv ℝ φ x (w x)‖ := by
      simp [residual, norm_mul, Real.norm_eq_abs, abs_of_nonneg hφ]
    _ ≤ 8 * φ x ^ 3 * (D * ‖w x‖) :=
      mul_le_mul_of_nonneg_left happly (by positivity)
    _ = (8 * D) * ‖φ x ^ 3 • w x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hφ 3)]
      ring

private theorem lpNorm_le_of_pointwise_factor {p : ℝ≥0∞} {f : Space → ℝ}
    {v : Space → Space} {K : ℝ} (hK : 0 ≤ K) (hv : MemLp v p volume)
    (hle : ∀ x, ‖f x‖ ≤ K * ‖v x‖) :
    comparisonLpNorm p f ≤ K * comparisonLpNorm p v := by
  calc
    comparisonLpNorm p f ≤ comparisonLpNorm p (fun x => K • v x) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hv.const_smul K)
      intro x
      change ‖f x‖ ≤ ‖K • v x‖
      rw [norm_smul, Real.norm_of_nonneg hK]
      exact hle x
    _ = K * comparisonLpNorm p v := by
      rw [LpNormTools.lpNorm_const_smul, Real.norm_of_nonneg hK]

/-- The scalar test has both conjugate exponents needed by the two pressure pieces.
Smooth compact localization supplies the weighted sixth moment of the velocity. -/
theorem residual_three_four {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L R : ℝ} (hL : 0 ≤ L) (hR : 0 < R)
    (hd : ∀ x, ‖fderiv ℝ φ x‖ ≤ L / R) :
    MemLp (residual φ w) 3 volume ∧ MemLp (residual φ w) 4 volume ∧
    comparisonLpNorm 3 (residual φ w) ≤
      (8 * (L / R)) * (comparisonLpNorm 2 w ^ (1 / 2 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 2 : ℝ)) ∧
    comparisonLpNorm 4 (residual φ w) ≤
      (8 * (L / R)) * (comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ)) := by
  have hs4 : HasCompactSupport (fun x => φ x ^ 4) :=
    hs.comp_left (g := fun s : ℝ => s ^ 4) (by norm_num)
  have hw6 : MemLp (fun x => φ x ^ 4 • w x) 6 volume :=
    ((hφ.continuous.pow 4).smul hw.continuous).memLp_of_hasCompactSupport hs4.smul_right
  obtain ⟨hthree, hthreeBound⟩ := WeightedInterpolation.cutoff_interpolation_three
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hw6
  obtain ⟨hfour, hfourBound⟩ := WeightedInterpolation.cutoff_interpolation_four
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hw6
  have hK : 0 ≤ 8 * (L / R) := by positivity
  have hnorm (x : Space) := norm_residual_le (w := w) x (hφ0 x) (hd x)
  have hmono (x : Space) : ‖φ x ^ 3 • w x‖ ≤ ‖φ x ^ 2 • w x‖ := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg (hφ0 x) 3),
      Real.norm_of_nonneg (pow_nonneg (hφ0 x) 2)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      φ x ^ 3 = φ x ^ 2 * φ x := by ring
      _ ≤ φ x ^ 2 * 1 := mul_le_mul_of_nonneg_left (hφ1 x) (pow_nonneg (hφ0 x) 2)
      _ = φ x ^ 2 := mul_one _
  have hmem (p : ℝ≥0∞) : MemLp (residual φ w) p volume :=
    (residual_smooth hφ hw).continuous.memLp_of_hasCompactSupport (residual_hasCompactSupport hs w)
  refine ⟨hmem 3, hmem 4, ?_, ?_⟩
  · exact (lpNorm_le_of_pointwise_factor hK hthree (fun x =>
      (hnorm x).trans (mul_le_mul_of_nonneg_left (hmono x) hK))).trans
      (mul_le_mul_of_nonneg_left hthreeBound hK)
  · exact (lpNorm_le_of_pointwise_factor hK hfour hnorm).trans
      (mul_le_mul_of_nonneg_left hfourBound hK)

end NavierStokesR3.Lemma105PaperFlux
