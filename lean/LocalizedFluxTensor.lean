import NavierStokes.R3.WeightedInterpolation
import NavierStokes.R3.LpNormTools

/-! Componentwise tensor estimates for the second pressure commutation. -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.LocalizedFluxTensor

open ProblemStatement Comparison

/-- A fixed time slice, in the manuscript's order of the two velocities. -/
def weightedTensor (ρ : Space → ℝ) (n : ℕ) (u v : Space → Space)
    (i j : Fin 3) (x : Space) : ℝ :=
  ρ x ^ n * (v x i * v x j - u x i * u x j)

private theorem tensorComponent_le (u v : Space) (i j : Fin 3) :
    ‖v i * v j - u i * u j‖ ≤ ‖v - u‖ ^ 2 + 2 * (‖v - u‖ * ‖u‖) := by
  have component (a b : Space) (k l : Fin 3) : ‖a k * b l‖ ≤ ‖a‖ * ‖b‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le a k) (PiLp.norm_apply_le b l)
      (norm_nonneg _) (norm_nonneg _)
  have expand : v i * v j - u i * u j =
      (v - u) i * (v - u) j + ((v - u) i * u j + u i * (v - u) j) := by
    change _ = (v i - u i) * (v j - u j) + ((v i - u i) * u j + u i * (v j - u j))
    ring
  rw [expand]
  calc
    _ ≤ ‖(v - u) i * (v - u) j‖ + ‖(v - u) i * u j + u i * (v - u) j‖ := norm_add_le _ _
    _ ≤ ‖(v - u) i * (v - u) j‖ + (‖(v - u) i * u j‖ + ‖u i * (v - u) j‖) :=
      add_le_add_right (norm_add_le _ _) _
    _ ≤ ‖v - u‖ * ‖v - u‖ + (‖v - u‖ * ‖u‖ + ‖u‖ * ‖v - u‖) :=
      add_le_add (component _ _ _ _) (add_le_add (component _ _ _ _) (component _ _ _ _))
    _ = _ := by ring

private theorem tensorHolder {ρ : Space → ℝ} {u v : Space → Space} (i j : Fin 3)
    (hρ : Continuous ρ) (hu : Continuous u) (hv : Continuous v) (hρ0 : ∀ x, 0 ≤ ρ x)
    {k m n : ℕ} {p q r : ℝ≥0∞}
    (hquad : ∀ x, ρ x ^ n ≤ ρ x ^ k * ρ x ^ m) (hcross : ∀ x, ρ x ^ n ≤ ρ x ^ k)
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (hr : 0 < r.toReal)
    (hrp : r.toReal < p.toReal) (hfrac : 1 / r.toReal = 1 / p.toReal + 1 / q.toReal)
    (hq1 : 1 ≤ q)
    (hW : MemLp (fun x => ρ x ^ k • (v x - u x)) p volume)
    (hZ : MemLp (fun x => ρ x ^ m • (v x - u x)) q volume)
    (hU : MemLp u q volume) :
    MemLp (weightedTensor ρ n u v i j) r volume ∧
      comparisonLpNorm r (weightedTensor ρ n u v i j) ≤
        comparisonLpNorm p (fun x => ρ x ^ k • (v x - u x)) *
          (comparisonLpNorm q (fun x => ρ x ^ m • (v x - u x)) + 2 * comparisonLpNorm q u) := by
  let W := fun x => ρ x ^ k • (v x - u x)
  let Z := fun x => ρ x ^ m • (v x - u x)
  let S := fun x => ‖Z x‖ + (‖u x‖ + ‖u x‖)
  have hS : MemLp S q volume := hZ.norm.add (hU.norm.add hU.norm)
  have hcoord {f : Space → Space} (hf : Continuous f) (l : Fin 3) : Continuous (fun x => f x l) :=
    (continuous_apply l).comp ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp hf)
  have hmeas : AEStronglyMeasurable (weightedTensor ρ n u v i j) volume :=
    ((hρ.pow n).mul (((hcoord hv i).mul (hcoord hv j)).sub ((hcoord hu i).mul (hcoord hu j)))).aestronglyMeasurable
  have hpoint (x : Space) : ‖weightedTensor ρ n u v i j x‖ ≤ ‖W x‖ * ‖S x‖ := by
    have hS0 : 0 ≤ S x := by dsimp [S]; positivity
    rw [Real.norm_of_nonneg hS0]
    simp only [weightedTensor, norm_mul, Real.norm_of_nonneg (pow_nonneg (hρ0 x) n),
      S, W, Z, norm_smul,
      Real.norm_of_nonneg (pow_nonneg (hρ0 x) k), Real.norm_of_nonneg (pow_nonneg (hρ0 x) m)]
    apply (mul_le_mul_of_nonneg_left (tensorComponent_le (u x) (v x) i j) (pow_nonneg (hρ0 x) n)).trans
    nlinarith only [mul_le_mul_of_nonneg_right (hquad x) (sq_nonneg ‖v x - u x‖),
      mul_le_mul_of_nonneg_right (hcross x) (mul_nonneg (norm_nonneg (v x - u x)) (norm_nonneg (u x)))]
  obtain ⟨hT, hTnorm⟩ := WeightedInterpolation.memLp_and_lpNorm_le_rpow_mul
    (a := 1) (b := 1) hW hS hmeas hp hq hr (by norm_num) (by norm_num)
    (by simpa using hrp) (by simpa using hfrac)
    (Filter.Eventually.of_forall fun x => by simpa only [Real.rpow_one] using hpoint x)
  have hsum : comparisonLpNorm q S ≤ comparisonLpNorm q Z + 2 * comparisonLpNorm q u := by
    have huu := LpNormTools.lpNorm_add_le hq1 hU.norm hU.norm
    have hzu := LpNormTools.lpNorm_add_le hq1 hZ.norm (hU.norm.add hU.norm)
    change comparisonLpNorm q S ≤ comparisonLpNorm q (fun x => ‖Z x‖) +
      comparisonLpNorm q (fun x => ‖u x‖ + ‖u x‖) at hzu
    have h := hzu.trans (add_le_add_right huu _)
    simpa only [comparisonLpNorm, eLpNorm_norm, two_mul] using h
  refine ⟨hT, ?_⟩
  simp only [Real.rpow_one] at hTnorm
  exact hTnorm.trans (mul_le_mul_of_nonneg_left hsum (LpNormTools.lpNorm_nonneg p W))

private theorem weightedSix {ρ : Space → ℝ} {u v : Space → Space}
    (hρ : Continuous ρ) (hs : HasCompactSupport ρ) (hu : Continuous u) (hv : Continuous v) :
    MemLp (fun x => ρ x ^ 4 • (v x - u x)) 6 volume := by
  have hs4 : HasCompactSupport (fun x => ρ x ^ 4) :=
    hs.comp_left (g := fun a : ℝ => a ^ 4) (by norm_num)
  exact ((hρ.pow 4).smul (hv.sub hu)).memLp_of_hasCompactSupport hs4.smul_right

theorem weightedTensor_two {ρ : Space → ℝ} {u v : Space → Space} (i j : Fin 3)
    (hρ : Continuous ρ) (hs : HasCompactSupport ρ) (hu : Continuous u) (hv : Continuous v)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1)
    (hw : MemLp (fun x => v x - u x) 2 volume) (hu6 : MemLp u 6 volume) :
    MemLp (weightedTensor ρ 6 u v i j) 2 volume ∧
      comparisonLpNorm 2 (weightedTensor ρ 6 u v i j) ≤
        (comparisonLpNorm 2 (fun x => v x - u x) ^ (1 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => ρ x ^ 4 • (v x - u x)) ^ (1 / 2 : ℝ)) *
          (comparisonLpNorm 6 (fun x => ρ x ^ 4 • (v x - u x)) + 2 * comparisonLpNorm 6 u) := by
  have hB := weightedSix hρ hs hu hv
  obtain ⟨hW, hb⟩ := WeightedInterpolation.cutoff_interpolation_three
    hρ.aestronglyMeasurable hρ0 hw hB
  obtain ⟨hmem, hnorm⟩ := tensorHolder (k := 2) (m := 4) (n := 6)
    (r := 2) i j hρ hu hv hρ0 (fun x => le_of_eq (by ring))
    (fun x => by
      calc
        ρ x ^ 6 = ρ x ^ 2 * ρ x ^ 4 := by ring
        _ ≤ ρ x ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (hρ0 x) (hρ1 x)) (sq_nonneg _)
        _ = _ := mul_one _)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hW hB hu6
  exact ⟨hmem, hnorm.trans (mul_le_mul_of_nonneg_right hb
    (add_nonneg (LpNormTools.lpNorm_nonneg _ _) (mul_nonneg (by norm_num) (LpNormTools.lpNorm_nonneg _ _))))⟩

theorem weightedTensor_four_thirds {ρ : Space → ℝ} {u v : Space → Space} (i j : Fin 3)
    (hρ : Continuous ρ) (hs : HasCompactSupport ρ) (hu : Continuous u) (hv : Continuous v)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1)
    (hw : MemLp (fun x => v x - u x) 2 volume) (hu2 : MemLp u 2 volume) :
    MemLp (weightedTensor ρ 4 u v i j) (4 / 3) volume ∧
      comparisonLpNorm (4 / 3) (weightedTensor ρ 4 u v i j) ≤
        (comparisonLpNorm 2 (fun x => v x - u x) ^ (1 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => ρ x ^ 4 • (v x - u x)) ^ (3 / 4 : ℝ)) *
          (comparisonLpNorm 2 (fun x => v x - u x) + 2 * comparisonLpNorm 2 u) := by
  obtain ⟨hW, hb⟩ := WeightedInterpolation.cutoff_interpolation_four
    hρ.aestronglyMeasurable hρ0 hw (weightedSix hρ hs hu hv)
  have hc (x : Space) : ρ x ^ 4 ≤ ρ x ^ 3 := by
    calc
      ρ x ^ 4 = ρ x ^ 3 * ρ x := by ring
      _ ≤ ρ x ^ 3 * 1 := mul_le_mul_of_nonneg_left (hρ1 x) (pow_nonneg (hρ0 x) 3)
      _ = _ := mul_one _
  have hZ : MemLp (fun x => ρ x ^ 0 • (v x - u x)) 2 volume := by simpa using hw
  obtain ⟨hmem, hnorm⟩ := tensorHolder (k := 3) (m := 0) (n := 4) (r := 4 / 3)
    i j hρ hu hv hρ0 (fun x => by simpa using hc x) hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hW hZ hu2
  simp only [pow_zero, one_smul] at hnorm
  exact ⟨hmem, hnorm.trans (mul_le_mul_of_nonneg_right hb
    (add_nonneg (LpNormTools.lpNorm_nonneg _ _) (mul_nonneg (by norm_num) (LpNormTools.lpNorm_nonneg _ _))))⟩

/-- Both bounds on upstream's time slices, tensor difference and weighted sixth norm. -/
theorem tensorDiff_bounds {ρ : Space → ℝ} {u v : VelocityField} {t : ℝ} (i j : Fin 3)
    (hρ : Continuous ρ) (hs : HasCompactSupport ρ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∀ x, ρ x ≤ 1)
    (hw : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu2 : MemLp (fun x => u (t, x)) 2 volume) (hu6 : MemLp (fun x => u (t, x)) 6 volume) :
    let M := comparisonLpNorm 2 (fun x => (u - v) (t, x))
    let B := cutoffL6 ρ (u - v) t
    let U : ℝ≥0∞ → ℝ := fun p => comparisonLpNorm p (fun x => u (t, x))
    let g := fun (n : ℕ) x => ρ x ^ n * tensorDiff u v t i j x
    (MemLp (g 6) 2 volume ∧ comparisonLpNorm 2 (g 6) ≤
      (M ^ (1/2 : ℝ) * B ^ (1/2 : ℝ)) * (B + 2 * U 6)) ∧
    (MemLp (g 4) (4 / 3) volume ∧ comparisonLpNorm (4 / 3) (g 4) ≤
      (M ^ (1/4 : ℝ) * B ^ (3/4 : ℝ)) * (M + 2 * U 2)) := by
  let a : Space → Space := fun x => u (t, x)
  let b : Space → Space := fun x => v (t, x)
  let w : Space → Space := fun x => (u - v) (t, x)
  have hneg : (fun x => b x - a x) = -w := funext fun x => (neg_sub _ _).symm
  have hnegB : (fun x => ρ x ^ 4 • (b x - a x)) = -(fun x => ρ x ^ 4 • w x) := by
    funext x
    change ρ x ^ 4 • (b x - a x) = -(ρ x ^ 4 • (a x - b x))
    rw [← smul_neg, neg_sub]
  have hwr : MemLp (fun x => b x - a x) 2 volume := hneg ▸ hw.neg
  have hM : comparisonLpNorm 2 (fun x => b x - a x) = comparisonLpNorm 2 w := by
    rw [hneg, comparisonLpNorm, eLpNorm_neg]; rfl
  have hB : comparisonLpNorm 6 (fun x => ρ x ^ 4 • (b x - a x)) = cutoffL6 ρ (u - v) t := by
    rw [hnegB, comparisonLpNorm, eLpNorm_neg]; rfl
  have transfer {n : ℕ} {p : ℝ≥0∞} {K : ℝ} (h : MemLp (weightedTensor ρ n a b i j) p volume ∧
      comparisonLpNorm p (weightedTensor ρ n a b i j) ≤ K) :
      MemLp (fun x => ρ x ^ n * tensorDiff u v t i j x) p volume ∧
      comparisonLpNorm p (fun x => ρ x ^ n * tensorDiff u v t i j x) ≤ K := by
    have heq : (fun x => ρ x ^ n * tensorDiff u v t i j x) = -(weightedTensor ρ n a b i j) := by
      funext x
      change ρ x ^ n * (a x i * a x j - b x i * b x j) = -(ρ x ^ n * (b x i * b x j - a x i * a x j))
      ring
    rw [heq]
    exact ⟨h.1.neg, by simpa only [comparisonLpNorm, eLpNorm_neg] using h.2⟩
  exact ⟨by simpa only [hM, hB] using transfer (weightedTensor_two i j hρ hs hu hv hρ0 hρ1 hwr hu6),
    by simpa only [hM, hB] using transfer (weightedTensor_four_thirds i j hρ hs hu hv hρ0 hρ1 hwr hu2)⟩

end NavierStokesR3.LocalizedFluxTensor
