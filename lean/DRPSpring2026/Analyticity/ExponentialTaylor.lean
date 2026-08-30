import DRPSpring2026.Analyticity.Estimates
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# Exponentially weighted Taylor series

This file formalizes the finite-head/small-tail estimate used in the DRP
write-up.  It is kept separate from the differential-operator applications.
-/

open Filter

namespace DRPSpring2026

/-- If the coefficients of an exponential generating function tend to zero,
then the function is `o(exp x)` along the positive real axis. -/
theorem tendsto_exp_neg_mul_tsum_pow_div_factorial {a : ℕ → ℝ}
    (ha : Tendsto a atTop (nhds 0)) :
    Tendsto (fun x : ℝ ↦ Real.exp (-x) *
      ∑' n : ℕ, a n * (x ^ n / n.factorial)) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    (Metric.isBounded_range_of_tendsto _ ha)
  have haM : ∀ n, |a n| ≤ M := by
    intro n
    simpa [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using
      hM (Set.mem_range_self n)
  have hMnonneg : 0 ≤ M := (abs_nonneg (a 0)).trans (haM 0)
  have hsummable : ∀ x : ℝ, Summable (fun n : ℕ ↦ a n * (x ^ n / n.factorial)) := by
    intro x
    apply Summable.of_norm_bounded
    · exact (Real.summable_pow_div_factorial |x|).mul_left M
    · intro n
      simp only [norm_mul, Real.norm_eq_abs, norm_div, norm_pow]
      have hfac : |(n.factorial : ℝ)| = n.factorial :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [hfac]
      exact mul_le_mul_of_nonneg_right (haM n)
        (div_nonneg (pow_nonneg (abs_nonneg x) _) (Nat.cast_nonneg _))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK'⟩ := Metric.tendsto_atTop.1 ha (ε / 2) (by positivity)
  have hK : ∀ n ≥ K, |a n| < ε / 2 := by
    intro n hn
    simpa [Real.dist_eq] using hK' n hn
  let head : ℝ → ℝ := fun x ↦
    ∑ n ∈ Finset.range K, |a n| / n.factorial * (x ^ n * Real.exp (-x))
  have hhead : Tendsto head atTop (nhds 0) := by
    simpa [head] using
      tendsto_finsetSum (Finset.range K) (fun n _ ↦
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).const_mul
          (|a n| / n.factorial))
  obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.1 hhead (ε / 2) (by positivity))
  refine ⟨max R 0, fun x hx ↦ ?_⟩
  have hxR : R ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
  have hheadlt : |head x| < ε / 2 := by
    simpa [Real.dist_eq] using hR x hxR
  have hheadnonneg : 0 ≤ head x := by
    dsimp [head]
    positivity
  have hheadlt' : head x < ε / 2 := by simpa [abs_of_nonneg hheadnonneg] using hheadlt
  let term : ℕ → ℝ := fun n ↦ |a n| * (x ^ n / n.factorial)
  let base : ℕ → ℝ := fun n ↦ x ^ n / n.factorial
  have hterm : Summable term := by
    apply Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial x).mul_left M)
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact mul_le_mul_of_nonneg_right (haM n)
        (div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
    · exact mul_nonneg (abs_nonneg _) (div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
  have hbase : Summable base := by
    exact Real.summable_pow_div_factorial x
  have htail : (∑' n : ℕ, term (n + K)) ≤ (ε / 2) * (∑' n : ℕ, base (n + K)) := by
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum
    · intro n
      dsimp [term, base]
      exact mul_le_mul_of_nonneg_right (le_of_lt (hK (n + K) (Nat.le_add_left K n)))
        (div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
    · exact (summable_nat_add_iff K).2 hterm
    · exact ((summable_nat_add_iff K).2 hbase).mul_left (ε / 2)
  have htailbase : (∑' n : ℕ, base (n + K)) ≤ Real.exp x := by
    have hsplit := hbase.sum_add_tsum_nat_add K
    have hheadbase : 0 ≤ ∑ n ∈ Finset.range K, base n := by
      apply Finset.sum_nonneg
      intro n hn
      exact div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _)
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    linarith
  have hnorm : |∑' n : ℕ, a n * (x ^ n / n.factorial)| ≤ ∑' n : ℕ, term n := by
    have htermEq : term = fun n : ℕ ↦ ‖a n * (x ^ n / n.factorial)‖ := by
      funext n
      simp [term, norm_mul, norm_div, norm_pow, Real.norm_eq_abs, abs_of_nonneg hx0]
    rw [htermEq]
    have hnormsum : Summable (fun n : ℕ ↦ ‖a n * (x ^ n / n.factorial)‖) := by
      rw [← htermEq]
      exact hterm
    exact norm_tsum_le_tsum_norm hnormsum
  have hsplit := hterm.sum_add_tsum_nat_add K
  have hheadEq : Real.exp (-x) * (∑ n ∈ Finset.range K, term n) = head x := by
    dsimp [term, head]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hexpcancel : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-x) * |∑' n : ℕ, a n * (x ^ n / n.factorial)|
        ≤ Real.exp (-x) * (∑' n : ℕ, term n) :=
      mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    _ = head x + Real.exp (-x) * (∑' n : ℕ, term (n + K)) := by
      rw [← hsplit, mul_add, hheadEq]
    _ ≤ head x + Real.exp (-x) * ((ε / 2) * (∑' n : ℕ, base (n + K))) := by
      gcongr
    _ ≤ head x + Real.exp (-x) * ((ε / 2) * Real.exp x) := by
      gcongr
    _ = head x + ε / 2 := by
      congr 1
      calc
        Real.exp (-x) * (ε / 2 * Real.exp x) =
            (ε / 2) * (Real.exp (-x) * Real.exp x) := by ring
        _ = ε / 2 := by rw [hexpcancel, mul_one]
    _ < ε := by linarith

/-- Taylor-coefficient decay for a globally analytic function implies
exponential decay after multiplication by `exp (-x)`. -/
theorem tendsto_exp_neg_mul_of_iteratedDeriv_tendsto_zero {q : ℝ → ℝ} {c : ℝ}
    (hq : AnalyticOnNhd ℝ q Set.univ)
    (hcoeff : Tendsto (fun n : ℕ ↦ iteratedDeriv n q c) atTop (nhds 0)) :
    Tendsto (fun x : ℝ ↦ Real.exp (-x) * q x) atTop (nhds 0) := by
  let a : ℕ → ℝ := fun n ↦ iteratedDeriv n q c
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    (Metric.isBounded_range_of_tendsto _ hcoeff)
  have haC : ∀ n, ‖a n‖ ≤ C := by
    intro n
    simpa [a, Metric.mem_closedBall, dist_zero_right] using hC (Set.mem_range_self n)
  let coeff : ℕ → ℝ := fun n ↦ a n / n.factorial
  let p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ coeff
  have hp_top : p.radius = ⊤ := by
    simpa [p, coeff, a] using radius_eq_top_of_iteratedDeriv_bound (f := q) (x := c) haC
  have hpseries : HasFPowerSeriesOnBall q p c p.radius := by
    have hpos : 0 < p.radius := by rw [hp_top]; simp
    apply AnalyticOn.hasFPowerSeriesOnBall hpos
    exact hq.analyticOn.mono (Set.subset_univ _)
  have hqsum : ∀ x : ℝ, q x = ∑' n : ℕ, a n * ((x - c) ^ n / n.factorial) := by
    intro x
    calc
      q x = p.sum (x - c) := by
        convert hpseries.sum (y := x - c) (by simp [hp_top]) using 1
        ring_nf
      _ = ∑' n : ℕ, coeff n * (x - c) ^ n := by
        simpa [p, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
          (FormalMultilinearSeries.ofScalars_sum_eq coeff (x - c))
      _ = ∑' n : ℕ, a n * ((x - c) ^ n / n.factorial) := by
        apply tsum_congr
        intro n
        simp [coeff]
        ring
  have hshift : Tendsto (fun x : ℝ ↦ x - c) atTop atTop := by
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right atTop (-c) (tendsto_id'.2 le_rfl)
  have hweighted := (tendsto_exp_neg_mul_tsum_pow_div_factorial
    (a := a) (by simpa [a] using hcoeff)).comp hshift
  have hscaled := hweighted.const_mul (Real.exp (-c))
  convert hscaled using 1
  · funext x
    rw [hqsum x]
    simp only [Function.comp_apply]
    rw [← mul_assoc]
    rw [← Real.exp_add]
    congr 2
    ring
  · simp

end DRPSpring2026
