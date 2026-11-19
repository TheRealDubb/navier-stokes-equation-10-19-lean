import NavierStokes.R3.CompactComparisonBounds
import NavierStokes.R3.PressureRecovery

/-! Time-uniform data norms for the two-commutator pressure estimate. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal ContDiff

namespace NavierStokesR3.FluxEnvelope

open ProblemStatement Comparison

/-- A continuous reference field with common compact support has bounded spatial
`L⁶` norm on each closed comparison slab. -/
theorem exists_lpNorm_six_bound {T : ℝ} {u : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ t ∈ Icc (0 : ℝ) T,
      MemLp (fun x : Space => u (t, x)) 6 volume ∧
        comparisonLpNorm 6 (fun x : Space => u (t, x)) ≤ U := by
  have hcont : ContinuousOn (fun t => ∫ x : Space, ‖u (t, x)‖ ^ 6) (Icc (0 : ℝ) T) := by
    apply CompactTimeIntegral.continuousOn_integral
      (F := fun z : SpaceTime => ‖u z‖ ^ 6) hK (hu.norm.pow 6)
    intro t ht x hx
    have hzero : u (t, x) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y : Space => u (t, y))
        (fun h => hx (hsupp t ht h))
    simp [hzero]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨(max C 0) ^ (6 : ℝ)⁻¹, by positivity, ?_⟩
  intro t ht
  have hLp : MemLp (fun x : Space => u (t, x)) 6 volume :=
    (CompactTimeIntegral.continuous_slice hu ht).memLp_of_hasCompactSupport
      (CompactComparisonBounds.hasCompactSupport_slice hK hsupp ht)
  refine ⟨hLp, ?_⟩
  have heq := MemLp.eLpNorm_eq_integral_rpow_norm
    (p := (6 : ℝ≥0∞)) (by norm_num) (by norm_num) hLp
  norm_num only [ENNReal.toReal_ofNat] at heq
  have hnorm : comparisonLpNorm 6 (fun x : Space => u (t, x)) =
      (∫ x : Space, ‖u (t, x)‖ ^ 6) ^ (6 : ℝ)⁻¹ := by
    rw [comparisonLpNorm, heq, ENNReal.toReal_ofReal]
    · rw [one_div]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun x => Real.rpow_natCast (‖u (t, x)‖) 6)
    · positivity
  rw [hnorm]
  apply Real.rpow_le_rpow (integral_nonneg (fun x => by positivity)) _ (by positivity)
  exact (le_abs_self _).trans ((hC t ht).trans (le_max_left _ _))

/-- The four constants depend on the original slab data. The velocity
difference and tensor both use the upstream reference-minus-competitor convention. -/
theorem exists_uniform_slice_bounds {T : ℝ} {u v : VelocityField}
    {p q : PressureField} {K : Set Space}
    (H : PressureRecovery.Hypotheses T u v p q) (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x : Space => u (t, x)) ⊆ K) :
    ∃ W U₂ U₆ G : ℝ, 0 ≤ W ∧ 0 ≤ U₂ ∧ 0 ≤ U₆ ∧ 0 ≤ G ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        (MemLp (fun x : Space => u (t, x) - v (t, x)) 2 volume ∧
          comparisonLpNorm 2 (fun x : Space => u (t, x) - v (t, x)) ≤ W) ∧
        (MemLp (fun x : Space => u (t, x)) 2 volume ∧
          comparisonLpNorm 2 (fun x : Space => u (t, x)) ≤ U₂) ∧
        (MemLp (fun x : Space => u (t, x)) 6 volume ∧
          comparisonLpNorm 6 (fun x : Space => u (t, x)) ≤ U₆) ∧
        ∀ i j : Fin 3, Integrable (tensorDiff u v t i j) volume ∧
          comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G := by
  have hum : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume :=
    fun t ht => (CompactTimeIntegral.continuous_slice H.smooth_u.continuousOn ht).aestronglyMeasurable
  have hvm : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x : Space => v (t, x)) volume :=
    fun t ht => (CompactTimeIntegral.continuous_slice H.smooth_v.continuousOn ht).aestronglyMeasurable
  obtain ⟨W, hW, hw⟩ := uniformFiniteEnergy_lpNorm_two_bound
    (fun t ht => (hum t ht).sub (hvm t ht))
      (uniformFiniteEnergy_sub hum hvm H.energy_u H.energy_v)
  obtain ⟨U₂, hU₂, hu₂⟩ := uniformFiniteEnergy_lpNorm_two_bound hum H.energy_u
  obtain ⟨U₆, hU₆, hu₆⟩ := exists_lpNorm_six_bound H.smooth_u.continuousOn hK hsupp
  obtain ⟨G, hG, hg⟩ := uniformFiniteEnergy_tensorDiff_lpNorm_one_bound
    hum hvm H.energy_u H.energy_v
  exact ⟨W, U₂, U₆, G, hW, hU₂, hU₆, hG, fun t ht =>
    ⟨hw t ht, hu₂ t ht, hu₆ t ht, hg t ht⟩⟩

/-- The constants of the two commutations and the four uniform data norms
combine into one constant, independent of the cutoff radius and of `B`. -/
theorem exists_scalar_envelope {a b c M U₂ U₆ G : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hU₂ : 0 ≤ U₂) (hU₆ : 0 ≤ U₆) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R B : ℝ}, 0 < R → 0 ≤ B →
      a * (M ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) * (B + 2 * U₆)) * (M / R) +
      b * (G * R ^ (-(3 / 4 : ℝ))) * (M ^ (1 / 4 : ℝ) * B ^ (3 / 4 : ℝ) / R) +
      c * (B ^ (3 / 4 : ℝ) * M ^ (1 / 4 : ℝ) * (M + 2 * U₂)) *
        R ^ (-(3 / 4 : ℝ)) * (M / R) ≤
      C / R * ((B + 1) * B ^ (1 / 2 : ℝ) +
        R ^ (-(3 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by
  let A := a * M ^ (1 / 2 : ℝ) * M
  let D := b * G * M ^ (1 / 4 : ℝ) +
    c * M ^ (1 / 4 : ℝ) * (M + 2 * U₂) * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C := max (A * (1 + 2 * U₆)) D
  have hC : 0 ≤ C := hD.trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro R B hR hB
  have hscale : B + 2 * U₆ ≤ (1 + 2 * U₆) * (B + 1) := by
    nlinarith only [mul_nonneg hU₆ hB]
  have hfirst : A * (B + 2 * U₆) ≤ C * (B + 1) := calc
    _ ≤ A * ((1 + 2 * U₆) * (B + 1)) := mul_le_mul_of_nonneg_left hscale hA
    _ = (A * (1 + 2 * U₆)) * (B + 1) := (mul_assoc _ _ _).symm
    _ ≤ C * (B + 1) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have htotal := add_le_add
    (mul_le_mul_of_nonneg_right hfirst (Real.rpow_nonneg hB (1 / 2 : ℝ)))
    (mul_le_mul_of_nonneg_right (show D ≤ C from le_max_right _ _)
      (mul_nonneg (Real.rpow_nonneg hR.le (-(3 / 4 : ℝ))) (Real.rpow_nonneg hB (3 / 4 : ℝ))))
  calc
    _ = (A * (B + 2 * U₆) * B ^ (1 / 2 : ℝ) +
        D * (R ^ (-(3 / 4 : ℝ)) * B ^ (3 / 4 : ℝ))) / R := by
          dsimp [A, D]
          ring
    _ ≤ (C * (B + 1) * B ^ (1 / 2 : ℝ) +
        C * (R ^ (-(3 / 4 : ℝ)) * B ^ (3 / 4 : ℝ))) / R :=
      div_le_div_of_nonneg_right htotal hR.le
    _ = _ := by ring

end NavierStokesR3.FluxEnvelope
