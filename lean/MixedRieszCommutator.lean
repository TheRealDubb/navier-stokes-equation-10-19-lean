import MixedKernelPair
import NavierStokes.R3.HeatKernelCommutator

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.MixedRieszCommutator

open ProblemStatement Comparison

/-- The second commutator in the fourth-power split pairs a localized tensor in
`L^(4/3)` with a test bounded in `L²`. The `L⁴` membership of a Schwartz test
allows the pinned heat representation to be used pointwise. -/
theorem riesz_commutator_pair_bound (i j : Fin 3) {φ g : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hgMeas : Measurable g) (hg43 : MemLp g (4 / 3) volume)
    (ψ ψh : ComplexTest) (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψ4 : MemLp (fun x => ψ x) 4 volume) (hψ2 : MemLp (fun x => ψ x) 2 volume) :
    ‖∫ x : Space, g x • (rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x)‖ ≤
      (rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm (4 / 3) g * comparisonLpNorm 2 (fun x => ψ x) := by
  let D := heatKernelTimeConstant * max (2 * L) 1
  have hmax : 0 ≤ max (2 * L) 1 := le_trans zero_le_one (le_max_right _ _)
  have hD : 0 ≤ D := mul_nonneg heatKernelTimeConstant_pos.le hmax
  have hdom (x y : Space) : ‖heatCommutatorKernel i j φ x y‖ ≤
      ‖D * radialCommutatorKernel R (y - x)‖ := by
    rw [Real.norm_of_nonneg (mul_nonneg hD (radialCommutatorKernel_nonneg hR _))]
    have heven : radialCommutatorKernel R (y - x) = radialCommutatorKernel R (x - y) := by
      unfold radialCommutatorKernel
      rw [norm_sub_rev y x]
    rw [heven]
    exact heatCommutatorKernel_bound i j hR hφ hLip x y
  have hpair := MixedCommutator.norm_kernel_pair_le
    (k := fun z => D * radialCommutatorKernel R z) hgMeas
    (measurable_const.mul (radialCommutatorKernel_measurable R)) ψ.continuous.measurable
    hg43 ((radialCommutatorKernel_memLp hR).const_mul D) hψ2 hdom
  have hscale : comparisonLpNorm (4 / 3) (fun y => D * radialCommutatorKernel R y) =
      D * comparisonLpNorm (4 / 3) (radialCommutatorKernel R) :=
    PairedKernelBound.lpNorm_const_smul_of_nonneg hD
  rw [hscale, radialCommutatorKernel_lpNorm_scale hR] at hpair
  simp_rw [riesz_commutator_eq_heatKernel i j hR hφm hφ hLip ψ ψh hψh hψ4]
  apply hpair.trans
  change _ ≤ ((heatKernelTimeConstant * (comparisonLpNorm (4 / 3) (radialCommutatorKernel 1) + 1)) *
      max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) * comparisonLpNorm (4 / 3) g *
      comparisonLpNorm 2 (fun x => ψ x)
  unfold D
  have hRpow := Real.rpow_nonneg hR.le (-(3 / 4) : ℝ)
  have hg0 := LpNormTools.lpNorm_nonneg (4 / 3) g
  have hr0 := LpNormTools.lpNorm_nonneg 2 (fun x => ψ x)
  have hrest := mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg heatKernelTimeConstant_pos.le hmax) hRpow) hg0) hr0
  linarith only [hrest]

end NavierStokesR3.MixedRieszCommutator
