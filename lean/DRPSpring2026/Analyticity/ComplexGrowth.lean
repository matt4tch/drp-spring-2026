import DRPSpring2026.Analyticity.Estimates
import Mathlib

/-!
# Exponential growth of canonical entire extensions

This module packages the complex Taylor-series estimate needed by the
degenerate first-order operator argument.
-/

open scoped ContDiff

namespace DRPSpring2026

/--
An analytic real function whose derivatives at zero are uniformly bounded has
an entire extension of exponential type at most one.
-/
theorem exists_entire_extension_norm_le_exp {f : ℝ → ℝ} {C : ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ)
    (hC : ∀ n : ℕ, ‖iteratedDeriv n f 0‖ ≤ C) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ x : ℝ, F (x : ℂ) = (f x : ℂ)) ∧
      ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp ‖z‖ := by
  let coeffR : ℕ → ℝ := fun n ↦ iteratedDeriv n f 0 / n.factorial
  let pR : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ coeffR
  have hpRtop : pR.radius = ⊤ := by
    simpa [pR, coeffR] using radius_eq_top_of_iteratedDeriv_bound hC
  have hfseries : HasFPowerSeriesOnBall f pR 0 pR.radius := by
    apply AnalyticOn.hasFPowerSeriesOnBall (by rw [hpRtop]; simp)
    exact hf.analyticOn.mono (Set.subset_univ _)
  let coeffC : ℕ → ℂ := fun n ↦ ((iteratedDeriv n f 0 : ℝ) : ℂ) / n.factorial
  let pC : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ coeffC
  have hpCtop : pC.radius = ⊤ := by
    apply pC.radius_eq_top_of_summable_norm
    intro r
    have hs : Summable (fun n : ℕ ↦ C * ((r : ℝ) ^ n / n.factorial)) :=
      (Real.summable_pow_div_factorial (r : ℝ)).mul_left C
    refine hs.of_nonneg_of_le (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _)) ?_
    intro n
    simp only [pC, coeffC, FormalMultilinearSeries.ofScalars_norm, norm_div,
      norm_natCast, Complex.norm_real]
    calc
      (‖iteratedDeriv n f 0‖ / (n.factorial : ℝ)) * (r : ℝ) ^ n
          ≤ (C / (n.factorial : ℝ)) * (r : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hC n) (by positivity))
          (by positivity)
      _ = C * ((r : ℝ) ^ n / (n.factorial : ℝ)) := by ring
  let F : ℂ → ℂ := pC.sum
  have hFanalytic : AnalyticOnNhd ℂ F Set.univ := by
    simpa [F, hpCtop] using pC.analyticOnNhd
  refine ⟨F, fun z ↦ (hFanalytic z trivial).differentiableAt, ?_, ?_⟩
  · intro x
    have hreal : f x = pR.sum x := by
      convert hfseries.sum (y := x) (by simp [hpRtop]) using 1
      ring_nf
    have hpRsum : pR.sum x = ∑' n : ℕ, coeffR n * x ^ n := by
      simpa [pR, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
        (FormalMultilinearSeries.ofScalars_sum_eq coeffR x)
    have hpCsum : F (x : ℂ) = ∑' n : ℕ, coeffC n * (x : ℂ) ^ n := by
      simpa [F, pC, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
        (FormalMultilinearSeries.ofScalars_sum_eq coeffC (x : ℂ))
    calc
      F (x : ℂ) = ∑' n : ℕ, coeffC n * (x : ℂ) ^ n := hpCsum
      _ = ∑' n : ℕ, ((coeffR n * x ^ n : ℝ) : ℂ) := by
        apply tsum_congr
        intro n
        simp [coeffC, coeffR]
      _ = ((∑' n : ℕ, coeffR n * x ^ n : ℝ) : ℂ) :=
        (RCLike.ofReal_tsum (𝕜 := ℂ) (fun n : ℕ ↦ coeffR n * x ^ n)).symm
      _ = (pR.sum x : ℂ) := congrArg ((↑) : ℝ → ℂ) hpRsum.symm
      _ = (f x : ℂ) := congrArg ((↑) : ℝ → ℂ) hreal.symm
  · intro z
    have hterm : Summable (fun n : ℕ ↦ ‖coeffC n * z ^ n‖) := by
      have hs := pC.summable_norm_apply
        (show z ∈ Metric.eball (0 : ℂ) pC.radius by simp [hpCtop])
      simpa [pC, coeffC, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
        mul_comm] using hs
    have hmajor : Summable (fun n : ℕ ↦ C * (‖z‖ ^ n / n.factorial)) :=
      (Real.summable_pow_div_factorial ‖z‖).mul_left C
    have hterm_le : ∀ n : ℕ,
        ‖coeffC n * z ^ n‖ ≤ C * (‖z‖ ^ n / n.factorial) := by
      intro n
      simp only [coeffC, norm_mul, norm_div, norm_natCast, Complex.norm_real, norm_pow]
      calc
        (‖iteratedDeriv n f 0‖ / (n.factorial : ℝ)) * ‖z‖ ^ n
            ≤ (C / (n.factorial : ℝ)) * ‖z‖ ^ n :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hC n) (by positivity))
            (by positivity)
        _ = C * (‖z‖ ^ n / (n.factorial : ℝ)) := by ring
    have hsum : F z = ∑' n : ℕ, coeffC n * z ^ n := by
      simpa [F, pC, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
        (FormalMultilinearSeries.ofScalars_sum_eq coeffC z)
    calc
      ‖F z‖ = ‖∑' n : ℕ, coeffC n * z ^ n‖ := congrArg norm hsum
      _ ≤ ∑' n : ℕ, ‖coeffC n * z ^ n‖ := norm_tsum_le_tsum_norm hterm
      _ ≤ ∑' n : ℕ, C * (‖z‖ ^ n / n.factorial) :=
        Summable.tsum_le_tsum hterm_le hterm hmajor
      _ = C * Real.exp ‖z‖ := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

end DRPSpring2026
