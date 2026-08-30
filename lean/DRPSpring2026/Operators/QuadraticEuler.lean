import DRPSpring2026.Analyticity.ExponentialTaylor
import DRPSpring2026.IteratedDerivative.Limit
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Iteration of the quadratic Euler operator

The operator `f ↦ x² f'` is conjugate to ordinary differentiation by the
reciprocal coordinate `y = -1/x`.  The two reciprocal charts are treated
separately; the entire extension on the negative chart then forces its
exponential constant to vanish.
-/

open Filter
open scoped ContDiff Polynomial

namespace DRPSpring2026

/-- The differential operator `x² d/dx`. -/
noncomputable def quadraticEulerOperator (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ x ^ 2 * deriv f x

lemma contDiff_quadraticEulerOperator {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (quadraticEulerOperator f) := by
  exact (contDiff_id.pow 2).mul (contDiff_infty_iff_deriv.mp hf).2

/-- Pull a function back by the involution `y ↦ -1/y`. -/
noncomputable def reciprocalPullback (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y ↦ f (-y⁻¹)

lemma contDiffOn_reciprocalPullback {f : ℝ → ℝ} {I : Set ℝ}
    (hf : ContDiff ℝ ∞ f) (hI : ∀ y ∈ I, y ≠ 0) :
    ContDiffOn ℝ ∞ (reciprocalPullback f) I := by
  have hi : ContDiffOn ℝ ∞ (fun y : ℝ ↦ -y⁻¹) I :=
    (contDiff_id.contDiffOn.inv hI).neg
  change ContDiffOn ℝ ∞ (fun y : ℝ ↦ f (-y⁻¹)) I
  simpa only [Function.comp_def] using hf.comp_contDiffOn hi

lemma deriv_reciprocalPullback {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {y : ℝ} (hy : y ≠ 0) :
    deriv (reciprocalPullback f) y = reciprocalPullback (quadraticEulerOperator f) y := by
  have hcomp := hf.differentiableAt.hasDerivAt.comp y (hasDerivAt_inv hy).neg
  change deriv (f ∘ (-Inv.inv)) y =
    (-y⁻¹) ^ 2 * deriv f (-y⁻¹)
  rw [hcomp.deriv]
  field_simp
  simp

private lemma contDiff_quadraticEulerOperator_iterate {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ∀ n : ℕ, ContDiff ℝ ∞ ((quadraticEulerOperator^[n]) f)
  | 0 => by simpa using hf
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact contDiff_quadraticEulerOperator
        (contDiff_quadraticEulerOperator_iterate hf n)

lemma iteratedDeriv_reciprocalPullback {f : ℝ → ℝ} {I : Set ℝ}
    (hIopen : IsOpen I) (hI : ∀ y ∈ I, y ≠ 0) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Set.EqOn (iteratedDeriv n (reciprocalPullback f))
      (reciprocalPullback ((quadraticEulerOperator^[n]) f)) I := by
  induction n with
  | zero => intro y hy; rfl
  | succ n ih =>
      intro y hy
      rw [iteratedDeriv_succ, Function.iterate_succ_apply']
      have heq : iteratedDeriv n (reciprocalPullback f) =ᶠ[nhds y]
          reciprocalPullback ((quadraticEulerOperator^[n]) f) :=
        Filter.mem_of_superset (hIopen.mem_nhds hy) ih
      rw [heq.deriv_eq]
      exact deriv_reciprocalPullback
        ((contDiff_quadraticEulerOperator_iterate hf n).differentiable (by simp)) (hI y hy)

private lemma reciprocal_ne_zero_on_Iio : ∀ _y ∈ Set.Iio (0 : ℝ), _y ≠ 0 :=
  fun _y hy ↦ ne_of_lt hy

private lemma reciprocal_ne_zero_on_Ioi : ∀ _y ∈ Set.Ioi (0 : ℝ), _y ≠ 0 :=
  fun _y hy ↦ ne_of_gt hy

private lemma reciprocal_chart_limit {f g : ℝ → ℝ} {I : Set ℝ}
    (hIopen : IsOpen I) (hIpre : IsPreconnected I) (hIne : I.Nonempty)
    (hIzero : ∀ y ∈ I, y ≠ 0) (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ, Tendsto
      (fun n : ℕ ↦ (quadraticEulerOperator^[n]) f x) atTop (nhds (g x))) :
    HasEntireExtensionOn (reciprocalPullback f) I ∧
      ∃ C : ℝ, Set.EqOn (reciprocalPullback g) (fun y ↦ C * Real.exp y) I := by
  have hFlim : ∀ y ∈ I, Tendsto
      (fun n : ℕ ↦ iteratedDeriv n (reciprocalPullback f) y) atTop
      (nhds (reciprocalPullback g y)) := by
    intro y hy
    exact (hlim (-y⁻¹)).congr'
      (Filter.Eventually.of_forall fun n ↦
        (iteratedDeriv_reciprocalPullback hIopen hIzero hf n hy).symm)
  obtain ⟨hentire, hGsmooth, hGfixed⟩ :=
    iteratedDeriv_limit_on hIopen hIpre hIne
      (contDiffOn_reciprocalPullback hf hIzero) hFlim
  refine ⟨hentire, ?_⟩
  exact eqOn_const_mul_exp_of_deriv_eq_self hIopen hIpre hIne
    (hGsmooth.differentiableOn (by simp)) hGfixed

private lemma negative_chart_constant_eq_zero {f g : ℝ → ℝ} {C : ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ, Tendsto
      (fun n : ℕ ↦ (quadraticEulerOperator^[n]) f x) atTop (nhds (g x)))
    (hentire : HasEntireExtensionOn (reciprocalPullback f) (Set.Ioi 0))
    (hchart : Set.EqOn (reciprocalPullback g) (fun y ↦ C * Real.exp y) (Set.Ioi 0)) :
    C = 0 := by
  obtain ⟨F, hFdiff, hFreal⟩ := hentire
  let q : ℝ → ℝ := fun y ↦ (F (y : ℂ)).re
  have hqanalytic : AnalyticOnNhd ℝ q Set.univ := by
    intro y hy
    exact (hFdiff.analyticAt (y : ℂ)).re_ofReal
  have hqeq : Set.EqOn q (reciprocalPullback f) (Set.Ioi 0) := by
    intro y hy
    simpa [q] using congrArg Complex.re (hFreal y hy)
  have hqeventually : q =ᶠ[nhds (1 : ℝ)] reciprocalPullback f :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds (by norm_num)) hqeq
  have hqiter : ∀ n : ℕ, iteratedDeriv n q 1 =
      (quadraticEulerOperator^[n]) f (-1) := by
    intro n
    calc
      iteratedDeriv n q 1 = iteratedDeriv n (reciprocalPullback f) 1 :=
        Filter.EventuallyEq.eq_of_nhds (hqeventually.iteratedDeriv n)
      _ = reciprocalPullback ((quadraticEulerOperator^[n]) f) 1 :=
        iteratedDeriv_reciprocalPullback isOpen_Ioi reciprocal_ne_zero_on_Ioi hf n
          (by norm_num)
      _ = (quadraticEulerOperator^[n]) f (-1) := by
        norm_num [reciprocalPullback]
  have hqcoeff : Tendsto (fun n : ℕ ↦ iteratedDeriv n q 1) atTop (nhds (g (-1))) := by
    convert hlim (-1) using 1
    ext n
    exact hqiter n
  have hgchart : g (-1) = C * Real.exp 1 := by
    simpa [reciprocalPullback] using hchart (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
  let h : ℝ → ℝ := fun y ↦ q y - C * Real.exp y
  have hanalytic : AnalyticOnNhd ℝ h Set.univ := by
    have hcexp : AnalyticOnNhd ℝ (fun y : ℝ ↦ C * Real.exp y) Set.univ :=
      analyticOnNhd_const.mul analyticOnNhd_rexp
    change AnalyticOnNhd ℝ (q - fun y : ℝ ↦ C * Real.exp y) Set.univ
    exact hqanalytic.sub hcexp
  have hexpiter : ∀ n : ℕ, iteratedDeriv n (fun y : ℝ ↦ C * Real.exp y) 1 =
      C * Real.exp 1 := by
    intro n
    rw [iteratedDeriv_const_mul_field]
    have he := congrFun (iteratedDeriv_exp_const_mul n 1) 1
    simpa using congrArg (fun z : ℝ ↦ C * z) he
  have hiter : ∀ n : ℕ, iteratedDeriv n h 1 =
      iteratedDeriv n q 1 - C * Real.exp 1 := by
    intro n
    change iteratedDeriv n (q - fun y : ℝ ↦ C * Real.exp y) 1 = _
    rw [iteratedDeriv_sub hqanalytic.contDiff.contDiffAt
      (contDiff_const.mul Real.contDiff_exp).contDiffAt, hexpiter]
  have hcoeff : Tendsto (fun n : ℕ ↦ iteratedDeriv n h 1) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ C * Real.exp 1) atTop
        (nhds (C * Real.exp 1)) := tendsto_const_nhds
    have ht := hqcoeff.sub hconst
    convert ht using 1
    · ext n
      exact hiter n
    · rw [hgchart]
      simp
  have hhweighted : Tendsto (fun y : ℝ ↦ Real.exp (-y) * h y) atTop (nhds 0) :=
    tendsto_exp_neg_mul_of_iteratedDeriv_tendsto_zero hanalytic hcoeff
  have hqweighted : Tendsto (fun y : ℝ ↦ Real.exp (-y) * q y) atTop (nhds C) := by
    convert hhweighted.const_add C using 1
    · funext y
      dsimp [h]
      rw [mul_sub]
      have he : Real.exp (-y) * (C * Real.exp y) = C := by
        calc
          Real.exp (-y) * (C * Real.exp y) = C * (Real.exp (-y) * Real.exp y) := by ring
          _ = C := by rw [← Real.exp_add]; simp
      rw [he]
      ring
    · simp
  have hpullweighted : Tendsto
      (fun y : ℝ ↦ Real.exp (-y) * reciprocalPullback f y) atTop (nhds 0) := by
    have hinv : Tendsto (fun y : ℝ ↦ -y⁻¹) atTop (nhds 0) :=
      by simpa using
        (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ ↦ y⁻¹) atTop (nhds 0)).neg
    have hpull : Tendsto (fun y : ℝ ↦ reciprocalPullback f y) atTop (nhds (f 0)) := by
      change Tendsto (f ∘ fun y : ℝ ↦ -y⁻¹) atTop (nhds (f 0))
      exact hf.continuous.continuousAt.tendsto.comp hinv
    have hexp : Tendsto (fun y : ℝ ↦ Real.exp (-y)) atTop (nhds 0) := by
      simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa using hexp.mul hpull
  have hqweightedZero : Tendsto (fun y : ℝ ↦ Real.exp (-y) * q y) atTop (nhds 0) := by
    apply hpullweighted.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [hqeq hy]
  exact tendsto_nhds_unique hqweighted hqweightedZero

/-- Classification of pointwise limits for `f ↦ x² f'`.  The sole free
parameter is the coefficient of mathlib's standard smooth flat function. -/
theorem quadraticEulerOperator_iterate_limit_classification {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ, Tendsto
      (fun n : ℕ ↦ (quadraticEulerOperator^[n]) f x) atTop (nhds (g x))) :
    ∃ C : ℝ, g = fun x ↦ C * expNegInvGlue x := by
  obtain ⟨_, Cpos, hpos⟩ := reciprocal_chart_limit isOpen_Iio isPreconnected_Iio
    ⟨-1, by norm_num⟩ reciprocal_ne_zero_on_Iio hf hlim
  obtain ⟨hnegEntire, Cneg, hneg⟩ := reciprocal_chart_limit isOpen_Ioi isPreconnected_Ioi
    ⟨1, by norm_num⟩ reciprocal_ne_zero_on_Ioi hf hlim
  have hCneg : Cneg = 0 :=
    negative_chart_constant_eq_zero hf hlim hnegEntire hneg
  refine ⟨Cpos, funext fun x ↦ ?_⟩
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hy : -x⁻¹ ∈ Set.Ioi (0 : ℝ) := by
      rw [Set.mem_Ioi]
      have hi : x⁻¹ < 0 := inv_lt_zero.mpr hx
      linarith
    have hvalue := hneg hy
    rw [hCneg] at hvalue
    simpa [reciprocalPullback, expNegInvGlue.zero_of_nonpos hx.le] using hvalue
  · have hshift := (tendsto_add_atTop_iff_nat 1).mpr (hlim 0)
    have hzero : (fun n : ℕ ↦ (quadraticEulerOperator^[n + 1]) f 0) = fun _ ↦ 0 := by
      funext n
      rw [Function.iterate_succ_apply']
      simp [quadraticEulerOperator]
    rw [hzero] at hshift
    exact tendsto_nhds_unique tendsto_const_nhds hshift |>.symm.trans (by simp)
  · have hy : -x⁻¹ ∈ Set.Iio (0 : ℝ) := by
      rw [Set.mem_Iio]
      have hi : 0 < x⁻¹ := inv_pos.mpr hx
      linarith
    have hvalue := hpos hy
    have hinvol : -(-x⁻¹)⁻¹ = x := by field_simp
    simpa [reciprocalPullback, hinvol, expNegInvGlue, not_le_of_gt hx] using hvalue

/-- The limit is smooth and is fixed by the quadratic Euler operator. -/
theorem quadraticEulerOperator_iterate_limit {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ, Tendsto
      (fun n : ℕ ↦ (quadraticEulerOperator^[n]) f x) atTop (nhds (g x))) :
    ContDiff ℝ ∞ g ∧ quadraticEulerOperator g = g := by
  obtain ⟨C, rfl⟩ := quadraticEulerOperator_iterate_limit_classification hf hlim
  constructor
  · exact contDiff_const.mul expNegInvGlue.contDiff
  · funext x
    simp only [quadraticEulerOperator]
    have hflat : HasDerivAt expNegInvGlue (x⁻¹ ^ 2 * expNegInvGlue x) x := by
      simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x
    rw [(hflat.const_mul C).deriv]
    by_cases hx : x = 0
    · subst x
      simp
    · simp
      field_simp

end DRPSpring2026
