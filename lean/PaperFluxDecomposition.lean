import NavierStokes.R3.PressureFlux

/-! Twice commute the spatial cutoff before applying the Fourier multiplier's L² bound. -/

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal

namespace NavierStokesR3.PaperFluxDecomposition

open ProblemStatement Comparison PressureFlux

theorem local_l2_bound (i j : Fin 3) {f : Space → ℝ} (hf : MemLp f 2 volume)
    (ψ : ComplexTest) :
    ‖pressurePair i j f ψ‖ ≤ comparisonLpNorm 2 f * comparisonLpNorm 2 (fun x => ψ x) := by
  let d := rieszTest i j ψ
  have hd : MemLp d 2 volume := RieszTestOperators.memLp_rieszTest i j ψ
  have hf' : MemLp (fun x => (f x : ℂ)) 2 volume := hf.ofReal
  have hnorm : comparisonLpNorm 2 d ≤ comparisonLpNorm 2 (fun x => ψ x) := by
    rw [LpNormTools.lpNorm_two_eq_sqrt_l2Sq hd, LpNormTools.lpNorm_two_eq_sqrt_l2Sq (ψ.memLp 2)]
    exact Real.sqrt_le_sqrt (RieszTestOperators.integral_norm_sq_rieszTest_le i j ψ)
  have hprod := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1) hf'.1 hd.1
    (fun a b : ℂ => a * b) 1 (Eventually.of_forall fun x => by simp [nnnorm_mul])
  have he : eLpNorm (fun x => (f x : ℂ) * d x) 1 volume ≤
      eLpNorm (fun x => (f x : ℂ)) 2 volume * eLpNorm d 2 volume := by
    simpa only [ENNReal.coe_one, one_mul] using hprod
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hf'.eLpNorm_ne_top hd.eLpNorm_ne_top) he
  rw [ENNReal.toReal_mul] at ht
  calc
    ‖pressurePair i j f ψ‖ ≤ ∫ x, ‖(f x : ℂ) * d x‖ := norm_integral_le_integral_norm _
    _ = comparisonLpNorm 1 (fun x => (f x : ℂ) * d x) :=
      (LpNormTools.lpNorm_one_eq_integral_norm (hf'.integrable_mul hd)).symm
    _ ≤ comparisonLpNorm 2 (fun x => (f x : ℂ)) * comparisonLpNorm 2 d := ht
    _ ≤ _ := by
      rw [lpNorm_ofReal]
      exact mul_le_mul_of_nonneg_left hnorm (LpNormTools.lpNorm_nonneg _ _)

theorem split_twice (i j : Fin 3) {ρ g : Space → ℝ} (hρ : Continuous ρ)
    (hs : HasCompactSupport ρ) (hg : Continuous g) (hg1 : Integrable g volume)
    (ψ₁ ψ₃ ψ₇ : ComplexTest) :
    ‖pressurePair i j g ψ₇‖ ≤
      comparisonLpNorm 2 (fun x => ρ x ^ 6 * g x) * comparisonLpNorm 2 (fun x => ψ₁ x) +
      ‖commutatorPair i j (fun x => ρ x ^ 4) g ψ₃ ψ₇‖ +
      ‖commutatorPair i j (fun x => ρ x ^ 2) (fun x => ρ x ^ 4 * g x) ψ₁ ψ₃‖ := by
  have hw (n : ℕ) (hn : n ≠ 0) (p : ℝ≥0∞) :
      MemLp (fun x => ρ x ^ n * g x) p volume :=
    ((hρ.pow n).mul hg).memLp_of_hasCompactSupport
      ((hs.comp_left (g := fun s : ℝ => s ^ n) (by simp [hn])).mul_right)
  have hpow : (fun x => ρ x ^ 2 * (ρ x ^ 4 * g x)) = (fun x => ρ x ^ 6 * g x) := by
    funext x; ring
  have h₁ := pressurePair_decomposition i j (h := fun x => ρ x ^ 4) hg1 (hw 4 (by decide) (6/5)) ψ₃ ψ₇
  have h₂ := pressurePair_decomposition i j (memLp_one_iff_integrable.mp (hw 4 (by decide) 1))
    (h := fun x => ρ x ^ 2) (hpow ▸ hw 6 (by decide) (6/5)) ψ₁ ψ₃
  change pressurePair i j g ψ₇ = pressurePair i j (fun x => ρ x ^ 4 * g x) ψ₃ + _ at h₁
  change pressurePair i j (fun x => ρ x ^ 4 * g x) ψ₃ =
    pressurePair i j (fun x => ρ x ^ 2 * (ρ x ^ 4 * g x)) ψ₁ + _ at h₂
  rw [hpow] at h₂
  rw [h₁, h₂]
  let f := fun x => ρ x ^ 6 * g x
  let P := pressurePair i j f ψ₁
  let Q := commutatorPair i j (fun x => ρ x ^ 2) (fun x => ρ x ^ 4 * g x) ψ₁ ψ₃
  let S := commutatorPair i j (fun x => ρ x ^ 4) g ψ₃ ψ₇
  change ‖P + Q + S‖ ≤ comparisonLpNorm 2 f * comparisonLpNorm 2 (fun x => ψ₁ x) + ‖S‖ + ‖Q‖
  have hP : ‖P‖ ≤ comparisonLpNorm 2 f * comparisonLpNorm 2 (fun x => ψ₁ x) :=
    local_l2_bound i j (hw 6 (by decide) 2) ψ₁
  linarith only [norm_add_le (P + Q) S, norm_add_le P Q, hP]

end NavierStokesR3.PaperFluxDecomposition
