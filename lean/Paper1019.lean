import PaperFluxTests
import PaperFluxScaling
import FluxEnvelope
import EssentialEnergy
import PaperFluxSlice
import NavierStokes.R3.ActualPressureFlux

/-! The physical pressure flux for the original single-radius cutoff powers. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.Paper1019

open ProblemStatement Comparison
open NavierStokes.PeriodicUniqueness (spatial_smooth)

/-- Two reversals carry the recovered pressure pairing to the manuscript's signs. -/
theorem physical_le_of_pair {T t : ℝ} {u v : VelocityField} {p P : PressureField}
    (H : PressureRecovery.Hypotheses T u v p P) (ht : t ∈ Ioo 0 T)
    {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hs : HasCompactSupport ρ) {E : ℝ}
    (hpairs : ∀ i j : Fin 3, ‖pressurePair i j (tensorDiff u v t i j)
      (PaperFluxTests.psi7 hρ hs (ActualPressureFlux.difference_slice_smooth H ht))‖ ≤ E) :
    |∫ x : Space, (P (t,x) - p (t,x)) *
      fderiv ℝ (fun y => ρ y ^ 8) x (v (t,x) - u (t,x))| ≤ 9 * E := by
  let χ := fun x => ρ x ^ 8
  let w := fun x : Space => (u - v) (t,x)
  have hχ : ContDiff ℝ ∞ χ := hρ.pow 8
  have hcχ : HasCompactSupport χ := hs.comp_left (g := fun s : ℝ => s ^ 8) (by norm_num)
  have hw : ContDiff ℝ ∞ w := ActualPressureFlux.difference_slice_smooth H ht
  let f := PressureFlux.fluxFunction χ w
  have hf : ContDiff ℝ ∞ f := PressureFlux.fluxFunction_smooth hχ hw
  have hcf : HasCompactSupport f := PressureFlux.fluxFunction_compact hcχ w
  let z := PressureFlux.canonicalFlux (tensorDiff u v t) f hf hcf
  have hid := ActualPressureFlux.pressure_flux_eq_canonical H ht hχ hcχ
  have hsign : (∫ x : Space, (P (t,x) - p (t,x)) * fderiv ℝ χ x (v (t,x) - u (t,x))) =
      ∫ x : Space, (p - P) (t,x) * fderiv ℝ χ x ((u - v) (t,x)) := by
    apply integral_congr_ae
    filter_upwards with x
    change (P (t,x) - p (t,x)) * fderiv ℝ χ x (v (t,x) - u (t,x)) =
      (p (t,x) - P (t,x)) * fderiv ℝ χ x (u (t,x) - v (t,x))
    rw [← neg_sub (p (t,x)) (P (t,x)), ← neg_sub (u (t,x)) (v (t,x)), map_neg, neg_mul_neg]
  have hre : (∫ x : Space, (P (t,x) - p (t,x)) * fderiv ℝ χ x (v (t,x) - u (t,x))) = z.re :=
    hsign.trans hid
  exact (congrArg abs hre).le.trans ((Complex.abs_re_le_norm z).trans (PressureFlux.norm_canonicalFlux_le hf hcf hpairs))

/-- One constant for the physical pressure-flux bound, every radius and every interior time. -/
theorem exists_uniform_physical_bound {T : ℝ} {u v : VelocityField} {p P : PressureField}
    {K : Set Space} (H : PressureRecovery.Hypotheses T u v p P) (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t,x)) ⊆ K)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    ∃ C_T : ℝ, 0 ≤ C_T ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      let ρ := PaperFluxScaling.scaled φ R
      let B := comparisonLpNorm 6 (fun x => ρ x ^ 4 • (v (t,x) - u (t,x)))
      |∫ x : Space, (P (t,x) - p (t,x)) * fderiv ℝ (fun y => ρ y ^ 8) x
        (v (t,x) - u (t,x))| ≤ C_T / R * ((B + 1) * B ^ (1/2 : ℝ) + R ^ (-(3/4 : ℝ)) * B ^ (3/4 : ℝ)) := by
  obtain ⟨M, U₂, U₆, G, hM, hU₂, hU₆, hG, hslice⟩ :=
    FluxEnvelope.exists_uniform_slice_bounds H hK hsupp
  obtain ⟨L, hL, hscaled⟩ := PaperFluxScaling.exists_bounds hφ hc hφ0 hφ1
  obtain ⟨C, hC, hpairs⟩ := PaperFluxSlice.exists_pair_envelope hL hM hU₂ hU₆ hG
  refine ⟨9 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro R hR t ht
  let ρ := PaperFluxScaling.scaled φ R
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨hρ, hs, h0, h1, hd, hlip, hlip₂⟩ := hscaled R hR0
  have ht' := Ioo_subset_Icc_self ht
  obtain ⟨hw, hu₂, hu₆, hg⟩ := hslice t ht'
  have hu := spatial_smooth H.smooth_u ht'
  have hv := spatial_smooth H.smooth_v ht'
  have hfinal := physical_le_of_pair H ht hρ hs (fun i j =>
    hpairs hR0 hρ hs (fun x => ⟨h0 x, h1 x⟩) hd hlip hlip₂ (u := u) (v := v) (t := t)
      hu hv hw.1 hw.2 hu₂.1 hu₂.2 hu₆.1 hu₆.2 i j (hg i j).1 (hg i j).2)
  have hflip : (fun x => ρ x ^ 4 • (v (t,x) - u (t,x))) =
      -(fun x => ρ x ^ 4 • (u - v) (t,x)) := by
    funext x
    change ρ x ^ 4 • (v (t,x) - u (t,x)) = -(ρ x ^ 4 • (u (t,x) - v (t,x)))
    rw [← smul_neg, neg_sub]
  have hB : comparisonLpNorm 6 (fun x => ρ x ^ 4 • (v (t,x) - u (t,x))) =
      cutoffL6 ρ (u-v) t := by
    rw [hflip, comparisonLpNorm, eLpNorm_neg]; rfl
  change |∫ x : Space, (P (t,x) - p (t,x)) * fderiv ℝ (fun y => ρ y ^ 8) x
    (v (t,x) - u (t,x))| ≤ 9 * C / R * _
  rw [hB]
  exact hfinal.trans_eq (by ring)

/-- Equation (10.19) under the original smooth compact-reference and common-force hypotheses.
The estimate is independent of whether the initial values coincide. -/
theorem equation_10_19 {T : ℝ} (hT : 0 < T) {u v : VelocityField} {p P : PressureField}
    {K : Set Space} (hu : ContDiffOn ℝ ∞ u (slab 0 T)) (hv : ContDiffOn ℝ ∞ v (slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (slab 0 T)) (hP : ContDiffOn ℝ ∞ P (slab 0 T)) (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t,x)) ⊆ K)
    (hev : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      MemLp (fun x : Space => v (t,x)) 2 volume ∧
        comparisonLpNorm 2 (fun x : Space => v (t,x)) ≤ M)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, NavierStokes.ProblemStatement.spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, NavierStokes.ProblemStatement.spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual 1 u p t x = navierStokesResidual 1 v P t x)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (_hunit : ∀ x : Space, ‖x‖ ≤ 1 → φ x = 1) :
    ∃ C_T : ℝ, 0 ≤ C_T ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo (0 : ℝ) T,
      let ρ := PaperFluxScaling.scaled φ R
      let B := comparisonLpNorm 6 (fun x => ρ x ^ 4 • (v (t,x) - u (t,x)))
      |∫ x : Space, (P (t,x) - p (t,x)) * fderiv ℝ (fun y => ρ y ^ 8) x
        (v (t,x) - u (t,x))| ≤ C_T / R * ((B + 1) * B ^ (1/2 : ℝ) + R ^ (-(3/4 : ℝ)) * B ^ (3/4 : ℝ)) := by
  have heu := CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab hu hK hsupp
  have hev' := EssentialEnergy.uniformFiniteEnergy_of_ae_bound hT hv.continuousOn hev
  let H : PressureRecovery.Hypotheses T u v p P :=
    ⟨hT, hu, hv, hp, hP, hdu, hdv, (fun t ht x => by simpa using hNS t ht x), heu, hev'⟩
  exact exists_uniform_physical_bound H hK hsupp hφ hc hφ0 hφ1

end NavierStokesR3.Paper1019
