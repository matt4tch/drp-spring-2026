import DRPSpring2026.Analyticity.Tao
import DRPSpring2026.Analyticity.Estimates
import Mathlib

/-!
# Pointwise limits of iterated derivatives

This module is the first application of Tao's analyticity theorem.  Operator
generalizations should import this result rather than being added here.
-/

open Filter
open scoped ContDiff

namespace DRPSpring2026

private lemma exists_iteratedDeriv_bound {f g : ℝ → ℝ}
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ iteratedDeriv n f x) atTop (nhds (g x))) :
    ∀ x : ℝ, ∃ C : ℝ, ∀ n : ℕ, ‖iteratedDeriv n f x‖ ≤ C := by
  intro x
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    (Metric.isBounded_range_of_tendsto _ (hlim x))
  refine ⟨C, fun n ↦ ?_⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using hC (Set.mem_range_self n)

private lemma analyticOnNhd_of_hasEntireExtension {f : ℝ → ℝ}
    (hf : HasEntireExtension f) : AnalyticOnNhd ℝ f Set.univ := by
  obtain ⟨F, hF, hFf⟩ := hf
  have hfrestrict : f = fun x : ℝ ↦ (F (x : ℂ)).re := by
    funext x
    simpa using congrArg Complex.re (hFf x).symm
  rw [hfrestrict]
  intro x _
  exact (hF.analyticAt (x : ℂ)).re_ofReal

/--
If the iterated derivatives of a smooth real function converge pointwise,
then their limit is smooth and is a fixed point of ordinary differentiation.
-/
theorem iteratedDeriv_limit {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ iteratedDeriv n f x) atTop (nhds (g x))) :
    ContDiff ℝ ∞ g ∧ deriv g = g := by
  have hbounded := exists_iteratedDeriv_bound hlim
  have hfanalytic : AnalyticOnNhd ℝ f Set.univ :=
    analyticOnNhd_of_hasEntireExtension (tao_analyticity hf hbounded)
  obtain ⟨C, hC⟩ := hbounded 0
  have hglobal : ∀ n x, ‖iteratedDeriv n f x‖ ≤ C * Real.exp ‖x‖ :=
    by simpa using norm_iteratedDeriv_le_mul_exp_sub hfanalytic hC
  have hgbound : ∀ x, ‖g x‖ ≤ C * Real.exp ‖x‖ := by
    intro x
    exact le_of_tendsto (tendsto_norm.comp (hlim x))
      (Filter.Eventually.of_forall fun n ↦ hglobal n x)
  have hintegral : ∀ a b : ℝ, g b - g a = ∫ x in a..b, g x := by
    intro a b
    have hftc : ∀ n : ℕ,
        (∫ x in a..b, iteratedDeriv (n + 1) f x) =
          iteratedDeriv n f b - iteratedDeriv n f a := by
      intro n
      rw [iteratedDeriv_succ]
      have hcont : Continuous (deriv (iteratedDeriv n f)) := by
        rw [← iteratedDeriv_succ]
        exact hf.continuous_iteratedDeriv (n + 1) (mod_cast le_top)
      exact intervalIntegral.integral_deriv_eq_sub
        (fun _ _ ↦
          (hf.differentiable_iteratedDeriv n (mod_cast ENat.coe_lt_top n)).differentiableAt)
        (hcont.intervalIntegrable a b)
    have hdct : Tendsto
        (fun n : ℕ ↦ ∫ x in a..b, iteratedDeriv (n + 1) f x) atTop
        (nhds (∫ x in a..b, g x)) := by
      apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun x ↦ C * Real.exp ‖x‖)
      · exact Filter.Eventually.of_forall fun n ↦
          (hf.continuous_iteratedDeriv (n + 1) (mod_cast le_top)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun n ↦ Filter.Eventually.of_forall fun x _ ↦
          hglobal (n + 1) x
      · exact (by fun_prop : Continuous (fun x : ℝ ↦ C * Real.exp ‖x‖)).intervalIntegrable a b
      · exact Filter.Eventually.of_forall fun x _ ↦
          (tendsto_add_atTop_iff_nat 1).mpr (hlim x)
    have hright : Tendsto
        (fun n : ℕ ↦ iteratedDeriv n f b - iteratedDeriv n f a) atTop
        (nhds (∫ x in a..b, g x)) := by
      simpa only [hftc] using hdct
    exact tendsto_nhds_unique ((hlim b).sub (hlim a)) hright
  have hCnonneg : 0 ≤ C := (norm_nonneg (iteratedDeriv 0 f 0)).trans (hC 0)
  have hgcontinuous : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x₀
    let K : NNReal := ⟨C * Real.exp (‖x₀‖ + 1), mul_nonneg hCnonneg (Real.exp_pos _).le⟩
    have hKbound : ∀ z ∈ Set.Icc (x₀ - 1) (x₀ + 1), ‖g z‖ ≤ (K : ℝ) := by
      intro z hz
      have hzx₀ : ‖z - x₀‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hz.1, hz.2]
      have hzNorm : ‖z‖ ≤ ‖x₀‖ + 1 := by
        calc
          ‖z‖ = ‖x₀ + (z - x₀)‖ := by ring_nf
          _ ≤ ‖x₀‖ + ‖z - x₀‖ := norm_add_le _ _
          _ ≤ ‖x₀‖ + 1 := by gcongr
      calc
        ‖g z‖ ≤ C * Real.exp ‖z‖ := hgbound z
        _ ≤ C * Real.exp (‖x₀‖ + 1) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzNorm) hCnonneg
        _ = (K : ℝ) := rfl
    have hLip : LipschitzOnWith K g (Set.Icc (x₀ - 1) (x₀ + 1)) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hbetween : ∀ z ∈ Set.uIoc x y, z ∈ Set.Icc (x₀ - 1) (x₀ + 1) := by
        intro z hz
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hz) with hxy | hyx
        · exact ⟨by linarith [hx.1, hy.1, hxy.1], by linarith [hx.2, hy.2, hxy.2]⟩
        · exact ⟨by linarith [hx.1, hy.1, hyx.1], by linarith [hx.2, hy.2, hyx.2]⟩
      calc
        dist (g x) (g y) = ‖g y - g x‖ := by rw [dist_comm, dist_eq_norm]
        _ = ‖∫ z in x..y, g z‖ := congrArg norm (hintegral x y)
        _ ≤ (K : ℝ) * |y - x| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (fun z hz ↦ hKbound z (hbetween z hz))
        _ = (K : ℝ) * dist x y := by rw [Real.dist_eq, abs_sub_comm]
    exact (hLip.continuousOn x₀ ⟨by linarith, by linarith⟩).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))
  have hgidentity : g = fun x ↦ g 0 + ∫ t in 0..x, g t := by
    funext x
    linarith [hintegral 0 x]
  have hgHasDeriv : ∀ x, HasDerivAt g (g x) x := by
    intro x
    have hprimitive : HasDerivAt (fun y ↦ g 0 + ∫ t in 0..y, g t) (g x) x :=
      (hgcontinuous.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add (g 0)
    exact hprimitive.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ congrFun hgidentity y)
  have hgdiff : Differentiable ℝ g := fun x ↦ (hgHasDeriv x).differentiableAt
  have hderiv : deriv g = g := by
    funext x
    exact (hgHasDeriv x).deriv
  have hiter : ∀ n : ℕ, iteratedDeriv n g = g := by
    intro n
    induction n with
    | zero => exact iteratedDeriv_zero
    | succ n ih =>
        rw [iteratedDeriv_succ, ih, hderiv]
  have hgsmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_infty]
    intro n
    rw [contDiff_nat_iff_iteratedDeriv]
    constructor
    · intro m _
      rw [hiter m]
      exact hgcontinuous
    · intro m _
      rw [hiter m]
      exact hgdiff
  exact ⟨hgsmooth, hderiv⟩

end DRPSpring2026
