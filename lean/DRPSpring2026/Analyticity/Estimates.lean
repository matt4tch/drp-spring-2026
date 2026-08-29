import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Estimates for globally analytic real functions

The main estimate in this file is the Taylor-series bound used both in Tao's
analyticity theorem and in its pointwise-limit application.
-/

namespace DRPSpring2026

private lemma iteratedDeriv_iteratedDeriv (f : ℝ → ℝ) (n k : ℕ) :
    iteratedDeriv n (iteratedDeriv k f) = iteratedDeriv (n + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate]
  exact (Function.iterate_add_apply deriv n k f).symm

private lemma norm_le_mul_exp_sub_of_analyticOnNhd {q : ℝ → ℝ}
    (hq : AnalyticOnNhd ℝ q Set.univ) {c C : ℝ}
    (hC : ∀ n : ℕ, ‖iteratedDeriv n q c‖ ≤ C) (x : ℝ) :
    ‖q x‖ ≤ C * Real.exp ‖x - c‖ := by
  let coeff : ℕ → ℝ := fun n ↦ iteratedDeriv n q c / n.factorial
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ coeff
  have hp_top : p.radius = ⊤ := by
    apply p.radius_eq_top_of_summable_norm
    intro r
    have hs : Summable (fun n : ℕ ↦ C * ((r : ℝ) ^ n / n.factorial)) :=
      (Real.summable_pow_div_factorial (r : ℝ)).mul_left C
    refine hs.of_nonneg_of_le (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _)) ?_
    intro n
    simp only [p, coeff, FormalMultilinearSeries.ofScalars_norm, norm_div,
      Real.norm_natCast]
    calc
      (‖iteratedDeriv n q c‖ / (n.factorial : ℝ)) * (r : ℝ) ^ n
          ≤ (C / (n.factorial : ℝ)) * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hC n) (by positivity))
          (by positivity)
      _ = C * ((r : ℝ) ^ n / (n.factorial : ℝ)) := by ring
  have hpseries : HasFPowerSeriesOnBall q p c p.radius := by
    have hpos : 0 < p.radius := by rw [hp_top]; simp
    apply AnalyticOn.hasFPowerSeriesOnBall hpos
    exact hq.analyticOn.mono (Set.subset_univ _)
  have hqsum : q x = ∑' n : ℕ, coeff n * (x - c) ^ n := by
    calc
      q x = p.sum (x - c) := by
        convert hpseries.sum (y := x - c) (by simp [hp_top]) using 1
        ring_nf
      _ = ∑' n : ℕ, coeff n * (x - c) ^ n := by
        simpa [p, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
          (FormalMultilinearSeries.ofScalars_sum_eq coeff (x - c))
  have hterm : Summable (fun n : ℕ ↦ ‖coeff n * (x - c) ^ n‖) := by
    have hs := p.summable_norm_apply
      (show x - c ∈ Metric.eball (0 : ℝ) p.radius by simp [hp_top])
    simpa [p, coeff, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm]
      using hs
  have hmajor : Summable (fun n : ℕ ↦ C * (‖x - c‖ ^ n / n.factorial)) :=
    (Real.summable_pow_div_factorial ‖x - c‖).mul_left C
  have hterm_le : ∀ n : ℕ,
      ‖coeff n * (x - c) ^ n‖ ≤ C * (‖x - c‖ ^ n / n.factorial) := by
    intro n
    simp only [coeff, norm_mul, norm_div, Real.norm_natCast, norm_pow]
    calc
      (‖iteratedDeriv n q c‖ / (n.factorial : ℝ)) * ‖x - c‖ ^ n
          ≤ (C / (n.factorial : ℝ)) * ‖x - c‖ ^ n :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hC n) (by positivity))
          (by positivity)
      _ = C * (‖x - c‖ ^ n / (n.factorial : ℝ)) := by ring
  calc
    ‖q x‖ = ‖∑' n : ℕ, coeff n * (x - c) ^ n‖ := congrArg norm hqsum
    _ ≤ ∑' n : ℕ, ‖coeff n * (x - c) ^ n‖ := norm_tsum_le_tsum_norm hterm
    _ ≤ ∑' n : ℕ, C * (‖x - c‖ ^ n / n.factorial) :=
      Summable.tsum_le_tsum hterm_le hterm hmajor
    _ = C * Real.exp ‖x - c‖ := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- A uniform bound on all Taylor coefficients at one point gives exponential
control of every iterated derivative of a globally analytic real function. -/
theorem norm_iteratedDeriv_le_mul_exp_sub {q : ℝ → ℝ}
    (hq : AnalyticOnNhd ℝ q Set.univ) {c C : ℝ}
    (hC : ∀ n : ℕ, ‖iteratedDeriv n q c‖ ≤ C) :
    ∀ k x, ‖iteratedDeriv k q x‖ ≤ C * Real.exp ‖x - c‖ := by
  intro k x
  apply norm_le_mul_exp_sub_of_analyticOnNhd
  · simpa [iteratedDeriv_eq_iterate] using hq.iterated_deriv k
  · intro n
    rw [iteratedDeriv_iteratedDeriv]
    exact hC (n + k)

end DRPSpring2026
