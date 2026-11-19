import PaperFluxDecomposition
import PaperFluxTests
import LocalizedFluxTensor
import MixedRieszCommutator
import FluxEnvelope

/-! A single constant for all scalar Riesz pairings of the original flux test. -/

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal

namespace NavierStokesR3.PaperFluxSlice

open ProblemStatement Comparison PressureFlux PaperFluxTests

/-- The three contributions from the local double-Riesz operator and the two commutations. -/
theorem pair_three_term {L M U₂ U₆ G : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hU₂ : 0 ≤ U₂) (hU₆ : 0 ≤ U₆) (hG : 0 ≤ G)
    {R : ℝ} (hR : 0 < R) {ρ : Space → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ)
    (h01 : ∀ x, ρ x ∈ Icc (0 : ℝ) 1)
    (hd : ∀ x, ‖fderiv ℝ ρ x‖ ≤ L / R)
    (hlip : ∀ x y, |ρ x - ρ y| ≤ L / R * ‖x - y‖)
    (hlip₂ : ∀ x y, |ρ x ^ 2 - ρ y ^ 2| ≤ (2 * L) / R * ‖x - y‖)
    {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hwM : comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M)
    (hu2 : MemLp (fun x => u (t, x)) 2 volume)
    (huU₂ : comparisonLpNorm 2 (fun x => u (t, x)) ≤ U₂)
    (hu6 : MemLp (fun x => u (t, x)) 6 volume)
    (huU₆ : comparisonLpNorm 6 (fun x => u (t, x)) ≤ U₆)
    (i j : Fin 3) (hg : Integrable (tensorDiff u v t i j) volume)
    (hgG : comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G) :
    let B := cutoffL6 ρ (u-v) t
    let A := 8 * L
    let K₁ := rieszCommutatorConstant * max (2 * (2 * L)) 1
    let K₂ := rieszCommutatorConstant * max (2 * L) 1
    ‖pressurePair i j (tensorDiff u v t i j) (psi7 hρ hs (hu.sub hv))‖ ≤
      A * (M ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) * (B + 2 * U₆)) * (M / R) +
      (K₁ * A) * (G * R ^ (-(3 / 4 : ℝ))) * (M ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) / R) +
      (K₂ * A) * (B ^ (3 / 4 : ℝ) * M ^ (1 / 4 : ℝ) * (M + 2 * U₂)) *
        R ^ (-(3 / 4 : ℝ)) * (M / R) := by
  let A := 8 * L
  let K₁ := rieszCommutatorConstant * max (2 * (2 * L)) 1
  let K₂ := rieszCommutatorConstant * max (2 * L) 1
  have hK₁ : 0 ≤ K₁ := mul_nonneg rieszCommutatorConstant_pos.le
    (zero_le_one.trans (le_max_right _ _))
  have hK₂ : 0 ≤ K₂ := mul_nonneg rieszCommutatorConstant_pos.le
    (zero_le_one.trans (le_max_right _ _))
  let g := tensorDiff u v t i j
  let m := comparisonLpNorm 2 (fun x => (u-v) (t,x))
  let B := cutoffL6 ρ (u-v) t
  let z₁ := psi1 hρ hs (hu.sub hv)
  let z₃ := psi3 hρ hs (hu.sub hv)
  let z₇ := psi7 hρ hs (hu.sub hv)
  have hB : 0 ≤ B := LpNormTools.lpNorm_nonneg _ _
  have hm : 0 ≤ m := LpNormTools.lpNorm_nonneg _ _
  have hρ0 := fun x => (h01 x).1
  have hρ1 := fun x => (h01 x).2
  have hρ₂ : ∀ x, ρ x ^ 2 ∈ Icc (0 : ℝ) 1 :=
    fun x => ⟨sq_nonneg _, pow_le_one₀ (hρ0 x) (hρ1 x)⟩
  have hgc : Continuous g := LocalizedTensorBounds.continuous_tensorDiff hu.continuous hv.continuous i j
  obtain ⟨⟨_, hg6bound⟩, ⟨hg43, hg43bound⟩⟩ :=
    LocalizedFluxTensor.tensorDiff_bounds i j hρ.continuous hs hu.continuous hv.continuous
      hρ0 hρ1 hw hu2 hu6
  have hg6' : comparisonLpNorm 2 (fun x => ρ x ^ 6 * g x) ≤
      M ^ (1/2 : ℝ) * B ^ (1/2 : ℝ) * (B + 2 * U₆) := by
    apply hg6bound.trans
    dsimp only
    gcongr
    exact add_nonneg hB (mul_nonneg (by norm_num) (LpNormTools.lpNorm_nonneg _ _))
  have hg43' : comparisonLpNorm (4/3) (fun x => ρ x ^ 4 * g x) ≤
      M ^ (1/4 : ℝ) * B ^ (3/4 : ℝ) * (M + 2 * U₂) := by
    apply hg43bound.trans
    dsimp only
    gcongr
    exact add_nonneg hm (mul_nonneg (by norm_num) (LpNormTools.lpNorm_nonneg _ _))
  have hz1 : comparisonLpNorm 2 (z₁ : Space → ℂ) ≤ (8 * (L/R)) * M :=
    (psi1_two_le hρ hs (hu.sub hv) hw hρ0 hρ1 hL hR hd).trans
      (mul_le_mul_of_nonneg_left hwM (by positivity))
  have hz3 : comparisonLpNorm 4 (z₃ : Space → ℂ) ≤ (8 * (L/R)) *
      (M ^ (1/4 : ℝ) * B ^ (3/4 : ℝ)) := by
    apply (psi3_four_le hρ hs (hu.sub hv) hw hρ0 hρ1 hL hR hd).trans
    change (8 * (L/R)) * (m ^ (1/4 : ℝ) * B ^ (3/4 : ℝ)) ≤ _
    gcongr
  have hlocal := mul_le_mul hg6' hz1 (LpNormTools.lpNorm_nonneg 2 _)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg hB _)) (by positivity))
  have hc₁ := Comparison.riesz_commutator_pair_bound i j hR (hρ.continuous.pow 2).measurable
    hρ₂ hlip₂ hg z₃ z₇ (psi7_eq hρ hs (hu.sub hv)) (z₃.memLp 4)
  have hc₁' : ‖commutatorPair i j (fun x => ρ x ^ 4) g z₃ z₇‖ ≤
      K₁ * R ^ (-(3/4 : ℝ)) * G * ((8 * (L/R)) * (M ^ (1/4 : ℝ) * B ^ (3/4 : ℝ))) := by
    apply le_trans _ (mul_le_mul (mul_le_mul_of_nonneg_left hgG
      (mul_nonneg hK₁ (Real.rpow_nonneg hR.le _))) hz3 (LpNormTools.lpNorm_nonneg _ _)
      (mul_nonneg (mul_nonneg hK₁ (Real.rpow_nonneg hR.le _)) hG))
    simpa only [commutatorPair, K₁, g, Pi.pow_apply, ← pow_mul, Nat.reduceMul] using hc₁
  have hc₂ := MixedRieszCommutator.riesz_commutator_pair_bound i j hR hρ.continuous.measurable
    h01 hlip ((hρ.continuous.pow 4).mul hgc).measurable hg43 z₁ z₃ (psi3_eq hρ hs (hu.sub hv))
    (z₁.memLp 4) (z₁.memLp 2)
  have hc₂' : ‖commutatorPair i j (fun x => ρ x ^ 2) (fun x => ρ x ^ 4 * g x) z₁ z₃‖ ≤
      K₂ * R ^ (-(3/4 : ℝ)) *
      (M ^ (1/4 : ℝ) * B ^ (3/4 : ℝ) * (M + 2 * U₂)) * ((8 * (L/R)) * M) := by
    apply hc₂.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hg43' (mul_nonneg hK₂ (Real.rpow_nonneg hR.le _)))
      hz1 (LpNormTools.lpNorm_nonneg 2 _)
      (mul_nonneg (mul_nonneg hK₂ (Real.rpow_nonneg hR.le _)) (by positivity))
  have hsum := (PaperFluxDecomposition.split_twice i j hρ.continuous hs hgc hg z₁ z₃ z₇).trans
    (add_le_add (add_le_add hlocal hc₁') hc₂')
  apply hsum.trans_eq
  change _ = A * (M ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) * (B + 2 * U₆)) * (M / R) +
      (K₁ * A) * (G * R ^ (-(3 / 4 : ℝ))) * (M ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) / R) +
      (K₂ * A) * (B ^ (3 / 4 : ℝ) * M ^ (1 / 4 : ℝ) * (M + 2 * U₂)) *
        R ^ (-(3 / 4 : ℝ)) * (M / R)
  dsimp only [A]
  ring

theorem exists_pair_envelope {L M U₂ U₆ G : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hU₂ : 0 ≤ U₂) (hU₆ : 0 ≤ U₆) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ} (_hR : 0 < R) {ρ : Space → ℝ}
        (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ)
        (_h01 : ∀ x, ρ x ∈ Icc (0 : ℝ) 1)
        (_hd : ∀ x, ‖fderiv ℝ ρ x‖ ≤ L / R)
        (_hlip : ∀ x y, |ρ x - ρ y| ≤ L / R * ‖x - y‖)
        (_hlip₂ : ∀ x y, |ρ x ^ 2 - ρ y ^ 2| ≤ (2 * L) / R * ‖x - y‖)
        {u v : VelocityField} {t : ℝ}
        (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
        (_hw : MemLp (fun x => (u - v) (t, x)) 2 volume)
        (_hwM : comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M)
        (_hu2 : MemLp (fun x => u (t, x)) 2 volume)
        (_huU₂ : comparisonLpNorm 2 (fun x => u (t, x)) ≤ U₂)
        (_hu6 : MemLp (fun x => u (t, x)) 6 volume)
        (_huU₆ : comparisonLpNorm 6 (fun x => u (t, x)) ≤ U₆)
        (i j : Fin 3) (_hg : Integrable (tensorDiff u v t i j) volume)
        (_hgG : comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G),
      ‖pressurePair i j (tensorDiff u v t i j) (psi7 hρ hs (hu.sub hv))‖ ≤
        C / R * ((cutoffL6 ρ (u-v) t + 1) * cutoffL6 ρ (u-v) t ^ (1/2 : ℝ) +
          R ^ (-(3/4 : ℝ)) * cutoffL6 ρ (u-v) t ^ (3/4 : ℝ)) := by
  let A := 8 * L
  let K₁ := rieszCommutatorConstant * max (2 * (2 * L)) 1
  let K₂ := rieszCommutatorConstant * max (2 * L) 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK₁ : 0 ≤ K₁ := mul_nonneg rieszCommutatorConstant_pos.le
    (zero_le_one.trans (le_max_right _ _))
  have hK₂ : 0 ≤ K₂ := mul_nonneg rieszCommutatorConstant_pos.le
    (zero_le_one.trans (le_max_right _ _))
  obtain ⟨C, hC, hc⟩ := FluxEnvelope.exists_scalar_envelope hA (mul_nonneg hK₁ hA)
    (mul_nonneg hK₂ hA) hM hU₂ hU₆ hG
  refine ⟨C, hC, ?_⟩
  intro R hR ρ hρ hs h01 hd hlip hlip₂ u v t hu hv hw hwM hu2 huU₂ hu6 huU₆ i j hg hgG
  exact (pair_three_term hL hM hU₂ hU₆ hG hR hρ hs h01 hd hlip hlip₂ hu hv hw hwM
    hu2 huU₂ hu6 huU₆ i j hg hgG).trans (hc hR (LpNormTools.lpNorm_nonneg _ _))

/-- The two-term quantitative estimate with an envelope G covering both tensor contributions. -/
theorem pair_informative {L M U₂ U₆ G : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hU₂ : 0 ≤ U₂) (hU₆ : 0 ≤ U₆) (hG : 0 ≤ G)
    (hcover : M * (M + 2 * U₂) ≤ G)
    {R : ℝ} (hR : 0 < R) {ρ : Space → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ)
    (h01 : ∀ x, ρ x ∈ Icc (0 : ℝ) 1)
    (hd : ∀ x, ‖fderiv ℝ ρ x‖ ≤ L / R)
    (hlip : ∀ x y, |ρ x - ρ y| ≤ L / R * ‖x - y‖)
    (hlip₂ : ∀ x y, |ρ x ^ 2 - ρ y ^ 2| ≤ (2 * L) / R * ‖x - y‖)
    {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hwM : comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M)
    (hu2 : MemLp (fun x => u (t, x)) 2 volume)
    (huU₂ : comparisonLpNorm 2 (fun x => u (t, x)) ≤ U₂)
    (hu6 : MemLp (fun x => u (t, x)) 6 volume)
    (huU₆ : comparisonLpNorm 6 (fun x => u (t, x)) ≤ U₆)
    (i j : Fin 3) (hg : Integrable (tensorDiff u v t i j) volume)
    (hgG : comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G) :
    let B := cutoffL6 ρ (u-v) t
    let A := 8 * L
    let K := rieszCommutatorConstant * (max (2 * (2 * L)) 1 + max (2 * L) 1)
    ‖pressurePair i j (tensorDiff u v t i j) (psi7 hρ hs (hu.sub hv))‖ ≤
      A / R * M * (B + 2 * U₆) * B ^ (1/2 : ℝ) * M ^ (1/2 : ℝ) +
      (A * K) * G * R ^ (-(7/4 : ℝ)) * B ^ (3/4 : ℝ) * M ^ (1/4 : ℝ) := by
  let A := 8 * L
  let K₁ := rieszCommutatorConstant * max (2 * (2 * L)) 1
  let K₂ := rieszCommutatorConstant * max (2 * L) 1
  let B := cutoffL6 ρ (u-v) t
  have hB : 0 ≤ B := LpNormTools.lpNorm_nonneg _ _
  have hK₂ : 0 ≤ K₂ := mul_nonneg rieszCommutatorConstant_pos.le
    (zero_le_one.trans (le_max_right _ _))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have factor : 0 ≤ (K₂ * A) * R ^ (-(3 / 4 : ℝ)) *
      (M ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) / R) := by positivity
  have step := mul_le_mul_of_nonneg_left hcover factor
  have hpow : R ^ (-(7/4 : ℝ)) = R ^ (-(3/4 : ℝ)) / R := by
    calc
      _ = R ^ ((-(3/4 : ℝ)) - 1) := by norm_num
      _ = _ := by rw [Real.rpow_sub hR, Real.rpow_one]
  have hraw := pair_three_term hL hM hU₂ hU₆ hG hR hρ hs h01 hd hlip hlip₂
    hu hv hw hwM hu2 huU₂ hu6 huU₆ i j hg hgG
  apply hraw.trans
  change A * (M ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) * (B + 2 * U₆)) * (M / R) +
      (K₁ * A) * (G * R ^ (-(3 / 4 : ℝ))) * (M ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) / R) +
      (K₂ * A) * (B ^ (3 / 4 : ℝ) * M ^ (1 / 4 : ℝ) * (M + 2 * U₂)) *
        R ^ (-(3 / 4 : ℝ)) * (M / R) ≤
    A / R * M * (B + 2 * U₆) * B ^ (1/2 : ℝ) * M ^ (1/2 : ℝ) +
      (A * (rieszCommutatorConstant * (max (2 * (2 * L)) 1 + max (2 * L) 1))) *
      G * R ^ (-(7/4 : ℝ)) * B ^ (3/4 : ℝ) * M ^ (1/4 : ℝ)
  rw [hpow]
  have total := add_le_add (le_refl
    (A / R * M * (B + 2 * U₆) * B ^ (1/2 : ℝ) * M ^ (1/2 : ℝ) +
      (K₁ * A) * R ^ (-(3/4 : ℝ)) * (M ^ (1/4 : ℝ) * B ^ (3/4 : ℝ) / R) * G)) step
  apply le_trans _ (total.trans ?_)
  · apply le_of_eq
    ring
  · apply le_of_eq
    dsimp only [K₁, K₂]
    ring

end NavierStokesR3.PaperFluxSlice
