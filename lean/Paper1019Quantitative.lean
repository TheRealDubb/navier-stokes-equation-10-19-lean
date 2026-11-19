import Paper1019
import PaperFluxSlice

/-! Quantitative physical flux at one radius and time with a chosen tensor envelope. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.Paper1019

open ProblemStatement Comparison
open NavierStokes.PeriodicUniqueness (spatial_smooth)

/-- The envelope G covers both the unweighted tensor and M times M + 2U₂.
The two coefficients after summing the nine tensor components depend only on L. -/
theorem physical_informative {T t : ℝ} {u v : VelocityField} {p P : PressureField}
    (H : PressureRecovery.Hypotheses T u v p P) (ht : t ∈ Ioo 0 T)
    {L M U₂ U₆ G : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hU₂ : 0 ≤ U₂)
    (hU₆ : 0 ≤ U₆) (hG : 0 ≤ G) (hcover : M * (M + 2 * U₂) ≤ G)
    {R : ℝ} (hR : 0 < R) {ρ : Space → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ)
    (h01 : ∀ x, ρ x ∈ Icc (0 : ℝ) 1)
    (hd : ∀ x, ‖fderiv ℝ ρ x‖ ≤ L / R)
    (hlip : ∀ x y, |ρ x - ρ y| ≤ L / R * ‖x - y‖)
    (hlip₂ : ∀ x y, |ρ x ^ 2 - ρ y ^ 2| ≤ (2 * L) / R * ‖x - y‖)
    (hw : MemLp (fun x => (u - v) (t,x)) 2 volume)
    (hwM : comparisonLpNorm 2 (fun x => (u - v) (t,x)) ≤ M)
    (hu2 : MemLp (fun x => u (t,x)) 2 volume) (huU₂ : comparisonLpNorm 2 (fun x => u (t,x)) ≤ U₂)
    (hu6 : MemLp (fun x => u (t,x)) 6 volume) (huU₆ : comparisonLpNorm 6 (fun x => u (t,x)) ≤ U₆)
    (hg : ∀ i j, Integrable (tensorDiff u v t i j) volume ∧ comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G) :
    let B := comparisonLpNorm 6 (fun x => ρ x ^ 4 • (v (t,x) - u (t,x)))
    let A := 8 * L
    let K := rieszCommutatorConstant * (max (2 * (2 * L)) 1 + max (2 * L) 1)
    |∫ x : Space, (P (t,x) - p (t,x)) * fderiv ℝ (fun y => ρ y ^ 8) x (v (t,x) - u (t,x))| ≤
      9 * (A / R * M * (B + 2 * U₆) * B ^ (1/2 : ℝ) * M ^ (1/2 : ℝ) +
        (A * K) * G * R ^ (-(7/4 : ℝ)) * B ^ (3/4 : ℝ) * M ^ (1/4 : ℝ)) := by
  have hu := spatial_smooth H.smooth_u (Ioo_subset_Icc_self ht)
  have hv := spatial_smooth H.smooth_v (Ioo_subset_Icc_self ht)
  have hphysical := physical_le_of_pair H ht hρ hs (fun i j =>
    PaperFluxSlice.pair_informative hL hM hU₂ hU₆ hG hcover hR hρ hs h01 hd hlip hlip₂
      (u := u) (v := v) (t := t) hu hv hw hwM hu2 huU₂ hu6 huU₆ i j (hg i j).1 (hg i j).2)
  have hflip : (fun x => ρ x ^ 4 • (v (t,x) - u (t,x))) =
      -(fun x => ρ x ^ 4 • (u-v) (t,x)) := by
    funext x
    change ρ x ^ 4 • (v (t,x) - u (t,x)) = -(ρ x ^ 4 • (u (t,x) - v (t,x)))
    rw [← smul_neg, neg_sub]
  have hB : comparisonLpNorm 6 (fun x => ρ x ^ 4 • (v (t,x) - u (t,x))) =
      cutoffL6 ρ (u-v) t := by
    rw [hflip, comparisonLpNorm, eLpNorm_neg]; rfl
  dsimp only
  rw [hB]
  exact hphysical

end NavierStokesR3.Paper1019
