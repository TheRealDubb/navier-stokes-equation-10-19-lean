import NavierStokes.R3.ComparisonCutoffs

/-! Uniform scaling estimates for an arbitrary smooth compact paper cutoff. -/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokesR3.PaperFluxScaling

open ProblemStatement

/-- Dilation of the fixed spatial cutoff. -/
def scaled (φ : Space → ℝ) (R : ℝ) (x : Space) : ℝ :=
  φ (R⁻¹ • x)

theorem exists_bounds {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (h₀ : ∀ x, 0 ≤ φ x) (h₁ : ∀ x, φ x ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ R : ℝ, 0 < R →
      ContDiff ℝ ∞ (scaled φ R) ∧ HasCompactSupport (scaled φ R) ∧
      (∀ x, 0 ≤ scaled φ R x) ∧ (∀ x, scaled φ R x ≤ 1) ∧
      (∀ x, ‖fderiv ℝ (scaled φ R) x‖ ≤ L / R) ∧
      (∀ x y, |scaled φ R x - scaled φ R y| ≤ (L / R) * ‖x - y‖) ∧
      ∀ x y, |scaled φ R x ^ 2 - scaled φ R y ^ 2| ≤ (2 * L / R) * ‖x - y‖ := by
  obtain ⟨C, hC⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hφ.continuous_fderiv (by simp))
  let L := max C 0
  have hL : 0 ≤ L := le_max_right _ _
  refine ⟨L, hL, ?_⟩
  intro R hR
  let d : Space →L[ℝ] Space := R⁻¹ • ContinuousLinearMap.id ℝ Space
  have hd : ‖d‖ ≤ R⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hR.le)
    intro x
    change ‖R⁻¹ • x‖ ≤ R⁻¹ * ‖x‖
    rw [ComparisonCutoffs.norm_scaled hR, div_eq_inv_mul]
  have hsmooth : ContDiff ℝ ∞ (scaled φ R) := hφ.comp d.contDiff
  have hder : ∀ x, ‖fderiv ℝ (scaled φ R) x‖ ≤ L / R := by
    intro x
    change ‖fderiv ℝ (φ ∘ d) x‖ ≤ _
    rw [fderiv_comp x ((contDiff_infty.1 hφ 1).differentiable (by simp) _)
      d.differentiableAt, d.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul ((hC (d x)).trans (le_max_left _ _)) hd (norm_nonneg _) hL).trans_eq
        (div_eq_mul_inv _ _).symm)
  have hlip (x y : Space) : |scaled φ R x - scaled φ R y| ≤ (L / R) * ‖x - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z (_ : z ∈ (univ : Set Space)) =>
        (contDiff_infty.1 hsmooth 1).differentiable (by simp) z)
      (fun z (_ : z ∈ (univ : Set Space)) => hder z)
      (convex_univ : Convex ℝ (univ : Set Space)) (mem_univ y) (mem_univ x)
  refine ⟨hsmooth, hc.comp_smul (inv_ne_zero hR.ne'), fun x => h₀ _, fun x => h₁ _,
    hder, hlip, ?_⟩
  intro x y
  have hsum : |scaled φ R x + scaled φ R y| ≤ 2 := by
    change |φ _ + φ _| ≤ 2
    rw [abs_of_nonneg (add_nonneg (h₀ _) (h₀ _))]
    linarith only [h₁ (R⁻¹ • x), h₁ (R⁻¹ • y)]
  calc
    |scaled φ R x ^ 2 - scaled φ R y ^ 2| =
        |scaled φ R x - scaled φ R y| * |scaled φ R x + scaled φ R y| := by
          rw [← abs_mul]
          congr 1
          ring
    _ ≤ ((L / R) * ‖x - y‖) * 2 :=
      mul_le_mul (hlip x y) hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring

end NavierStokesR3.PaperFluxScaling
