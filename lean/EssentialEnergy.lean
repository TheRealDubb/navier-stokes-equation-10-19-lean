import NavierStokes.R3.ComparisonFiniteEnergy
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Essential-in-time kinetic energy bounds for a continuous velocity field. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace NavierStokesR3.EssentialEnergy

open ProblemStatement Comparison

/-- Points satisfying an almost-everywhere condition on a nondegenerate closed
interval approximate every point of the interval, including both endpoints. -/
private theorem exists_good_times {T : ℝ} (hT : 0 < T) {P : ℝ → Prop}
    (h : ∀ᵐ r ∂volume.restrict (Icc 0 T), P r) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ s : ℕ → ℝ, (∀ n, s n ∈ Icc 0 T ∧ P (s n)) ∧ Tendsto s atTop (𝓝 t) := by
  let good := {r : ℝ | r ∈ Icc 0 T ∧ P r}
  have hdense : Dense {r : ℝ | r ∈ Icc 0 T → P r} :=
    Measure.dense_of_ae (μ := volume) ((ae_restrict_iff' measurableSet_Icc).mp h)
  have hi : Ioo (0 : ℝ) T ⊆ closure good := by
    intro s hs
    rw [mem_closure_iff]
    intro V hV hsV
    obtain ⟨r, ⟨hrV, hr⟩, hP⟩ := hdense.inter_open_nonempty (V ∩ Ioo 0 T)
      (hV.inter isOpen_Ioo) ⟨s, hsV, hs⟩
    exact ⟨r, hrV, ⟨hr.1.le, hr.2.le⟩, hP ⟨hr.1.le, hr.2.le⟩⟩
  have hin : t ∈ closure (Ioo (0 : ℝ) T) := by rwa [closure_Ioo hT.ne]
  exact mem_closure_iff_seq_limit.mp (closure_minimal hi isClosed_closure hin)

/-- Continuity on the closed slab upgrades an essential uniform spatial `L²`
bound to the pointwise-in-time finite energy required by the pressure theorem. -/
theorem uniformFiniteEnergy_of_ae_bound {T : ℝ} {v : VelocityField}
    (hT : 0 < T) (hv : ContinuousOn v (slab 0 T))
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      MemLp (fun x : Space => v (t, x)) 2 volume ∧
        comparisonLpNorm 2 (fun x : Space => v (t, x)) ≤ M) :
    UniformFiniteEnergy (Icc (0 : ℝ) T) v := by
  obtain ⟨M, hM, hbound⟩ := hbound
  refine ⟨(1 / 2 : ℝ) * M ^ 2, by positivity, ?_⟩
  intro t ht
  obtain ⟨s, hs, hst⟩ := exists_good_times hT hbound ht
  let g := fun (r : ℝ) (x : Space) => ‖v (r, x)‖ ^ 2
  have hgc {r : ℝ} (hr : r ∈ Icc 0 T) : Continuous (g r) :=
    (continuous_slice_of_continuousOn hv hr).norm.pow 2
  have hg0 (r : ℝ) (x : Space) : 0 ≤ g r x := sq_nonneg _
  have hsbound (n : ℕ) : ∫⁻ x, ENNReal.ofReal (g (s n) x) ≤ ENNReal.ofReal (M ^ 2) := by
    obtain ⟨hm, hnorm⟩ := (hs n).2
    have hInt : Integrable (g (s n)) volume :=
      (memLp_two_iff_integrable_sq_norm hm.1).mp hm
    rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (hg0 _))]
    apply ENNReal.ofReal_le_ofReal
    change l2Sq (fun x : Space => v (s n, x)) ≤ M ^ 2
    rw [← LpNormTools.lpNorm_two_sq_eq_l2Sq hm]
    exact pow_le_pow_left₀ (LpNormTools.lpNorm_nonneg _ _) hnorm 2
  have hst' : Tendsto s atTop (𝓝[Icc 0 T] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hst, Eventually.of_forall (fun n => (hs n).1)⟩
  have hconv (x : Space) :
      Tendsto (fun n => ENNReal.ofReal (g (s n) x)) atTop (𝓝 (ENNReal.ofReal (g t x))) := by
    have htime : ContinuousOn (fun r : ℝ => v (r, x)) (Icc 0 T) :=
      hv.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => ⟨hr, mem_univ x⟩)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((htime.norm.pow 2) t ht).tendsto.comp hst')
  have hfatou : ∫⁻ x, ENNReal.ofReal (g t x) ≤ ENNReal.ofReal (M ^ 2) := calc
    _ = ∫⁻ x : Space, liminf (fun n => ENNReal.ofReal (g (s n) x)) atTop :=
      lintegral_congr (fun x => (hconv x).liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (g (s n) x)) atTop :=
      lintegral_liminf_le (fun n => (ENNReal.continuous_ofReal.comp (hgc (hs n).1)).measurable)
    _ ≤ _ := by
      simpa using Filter.liminf_le_liminf (f := (atTop : Filter ℕ))
        (Eventually.of_forall hsbound)
  have hInt : Integrable (g t) volume := by
    refine ⟨(hgc ht).aestronglyMeasurable, ?_⟩
    change (∫⁻ x, ‖g t x‖ₑ) < ⊤
    simpa only [Real.enorm_of_nonneg (hg0 _ _)] using hfatou.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hInt, mul_le_mul_of_nonneg_left ?_ (by norm_num)⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (hg0 _))] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg M)).mp hfatou

end NavierStokesR3.EssentialEnergy
