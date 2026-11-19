import NavierStokes.ProblemStatement
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The positive convolution majorant used when commuting a second cutoff
power in (10.19). The input exponents are both 4/3 and the output exponent is 2.
The ENNReal formulation retains absolute-integrability information. -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.MixedCommutator

open NavierStokes.ProblemStatement

def majorant (f g : Space → ℝ≥0∞) (x : Space) : ℝ≥0∞ :=
  ∫⁻ y : Space, f y * g (x - y)

private theorem measurable_majorant {f g : Space → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) : Measurable (majorant f g) := by
  apply Measurable.lintegral_prod_right
  exact (hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))

private theorem lintegral_majorant {f g : Space → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : Space, majorant f g x) = (∫⁻ y, f y) * (∫⁻ z, g z) := by
  unfold majorant
  rw [lintegral_lintegral_swap
    ((hf.comp measurable_snd).mul (hg.comp (measurable_fst.sub measurable_snd))).aemeasurable]
  have hinner (y : Space) : (∫⁻ x : Space, f y * g (x - y)) = f y * (∫⁻ x, g x) := by
    rw [lintegral_const_mul (μ := volume) (f := fun x : Space => g (x - y)) (f y) (by fun_prop),
      lintegral_sub_right_eq_self g]
  simp_rw [hinner]
  exact lintegral_mul_const _ hf

private theorem integrand_split (a b : ℝ≥0∞) :
    (a ^ (2 / 3 : ℝ) * b ^ (2 / 3 : ℝ)) *
      (a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ)) = a * b := by
  calc
    _ = (a ^ (2 / 3 : ℝ) * a ^ (1 / 3 : ℝ)) *
        (b ^ (2 / 3 : ℝ) * b ^ (1 / 3 : ℝ)) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

private theorem cs_sq {f g : Space → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x) ^ 2 ≤ (∫⁻ x, f x ^ 2) * (∫⁻ x, g x ^ 2) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space)
    Real.HolderConjugate.two_two hf.aemeasurable hg.aemeasurable
  have hs := pow_le_pow_left' h 2
  have hsqrt (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← ENNReal.rpow_mul_natCast]
    norm_num
  simpa only [Pi.mul_apply, ENNReal.rpow_two, mul_pow, hsqrt] using hs

private theorem majorant_sq_le {f g : Space → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (x : Space) :
    majorant f g x ^ 2 ≤
      majorant (fun y => f y ^ (4 / 3 : ℝ)) (fun y => g y ^ (4 / 3 : ℝ)) x *
        ((∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ) *
         (∫⁻ y, g y ^ (4 / 3 : ℝ)) ^ (1 / 2 : ℝ)) := by
  have hcs := cs_sq
    (f := fun y => f y ^ (2 / 3 : ℝ) * g (x - y) ^ (2 / 3 : ℝ))
    (g := fun y => f y ^ (1 / 3 : ℝ) * g (x - y) ^ (1 / 3 : ℝ))
    (by fun_prop) (by fun_prop)
  simp only [integrand_split, mul_pow, ← ENNReal.rpow_mul_natCast] at hcs
  norm_num at hcs
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space)
    Real.HolderConjugate.two_two (f := fun y => f y ^ (2 / 3 : ℝ))
    (g := fun y => g (x - y) ^ (2 / 3 : ℝ)) (by fun_prop) (by fun_prop)
  simp only [Pi.mul_apply, ← ENNReal.rpow_mul] at hh
  norm_num at hh
  have hneg : MeasurePreserving (fun y : Space => -y) volume volume :=
    (LinearIsometryEquiv.neg ℝ : Space ≃ₗᵢ[ℝ] Space).measurePreserving
  have hreflect : MeasurePreserving (fun y : Space => x - y) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left volume x).comp hneg
  have htranslate := hreflect.lintegral_comp (hg.pow_const (4 / 3 : ℝ))
  change (∫⁻ y : Space, g (x - y) ^ (4 / 3 : ℝ)) = (∫⁻ y, g y ^ (4 / 3 : ℝ)) at htranslate
  rw [htranslate] at hh
  exact hcs.trans (mul_le_mul_of_nonneg_left hh (by positivity))

/-- The squared Young estimate for the symmetric pair (4/3, 4/3). -/
theorem majorant_young {f g : Space → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, majorant f g x ^ 2) ≤
      (∫⁻ x, f x ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ) *
      (∫⁻ x, g x ^ (4 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
  let F := ∫⁻ x, f x ^ (4 / 3 : ℝ)
  let G := ∫⁻ x, g x ^ (4 / 3 : ℝ)
  have hpow (a : ℝ≥0∞) : a * a ^ (1 / 2 : ℝ) = a ^ (3 / 2 : ℝ) := by
    conv_lhs => lhs; rw [← ENNReal.rpow_one a]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  calc
    _ ≤ ∫⁻ x : Space,
        majorant (fun y => f y ^ (4 / 3 : ℝ)) (fun y => g y ^ (4 / 3 : ℝ)) x *
          (F ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)) := lintegral_mono (majorant_sq_le hf hg)
    _ = (F * G) * (F ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)) := by
      rw [lintegral_mul_const _ (measurable_majorant (hf.pow_const _) (hg.pow_const _)),
        lintegral_majorant (hf.pow_const _) (hg.pow_const _)]
    _ = (F * F ^ (1 / 2 : ℝ)) * (G * G ^ (1 / 2 : ℝ)) := by ac_rfl
    _ = _ := by rw [hpow, hpow]

/-- Absolute trilinear bound with constant one. The factors may be magnitudes of
the localized tensor, the radial commutator majorant, and the residual test. -/
theorem paired_majorant_le {f k r : Space → ℝ≥0∞}
    (hf : Measurable f) (hk : Measurable k) (hr : Measurable r) :
    (∫⁻ y, r y * majorant f k y) ≤
      (∫⁻ y, r y ^ 2) ^ (1 / 2 : ℝ) *
      ((∫⁻ x, f x ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
       (∫⁻ z, k z ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure Space)
    Real.HolderConjugate.two_two hr.aemeasurable (measurable_majorant hf hk).aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  have hy := ENNReal.rpow_le_rpow (majorant_young hf hk) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hy
  norm_num at hy
  exact h.trans (mul_le_mul_of_nonneg_left hy (by positivity))

end NavierStokesR3.MixedCommutator
