import DRPSpring2026.Analyticity.ComplexGrowth
import DRPSpring2026.Analyticity.PhragmenLindelof
import DRPSpring2026.Analyticity.Tao

/-!
# Iteration of the Euler operator

The Euler operator `f ↦ x f'` is conjugate to ordinary differentiation on
each open half-line by `x = σ exp y`, but its zero at the origin requires a
separate rigidity argument.
-/

open Filter
open scoped ContDiff

namespace DRPSpring2026

/-- The Euler differential operator `x d/dx`. -/
noncomputable def eulerOperator (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ x * deriv f x

lemma contDiff_eulerOperator {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (eulerOperator f) := by
  exact contDiff_id.mul (contDiff_infty_iff_deriv.mp hf).2

namespace Euler

/-- Pull a real function back along the parametrization `y ↦ σ exp y`. -/
noncomputable def expPullback (σ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun y ↦ f (σ * Real.exp y)

lemma contDiff_expPullback (σ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (expPullback σ f) := by
  exact hf.comp (contDiff_const.mul Real.contDiff_exp)

lemma deriv_expPullback (σ : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (expPullback σ f) = expPullback σ (eulerOperator f) := by
  funext y
  have hinner : HasDerivAt (fun t : ℝ ↦ σ * Real.exp t) (σ * Real.exp y) y :=
    (Real.hasDerivAt_exp y).const_mul σ
  have hcomp := (hf.differentiableAt.hasDerivAt.comp y hinner)
  change deriv (f ∘ fun t : ℝ ↦ σ * Real.exp t) y =
    σ * Real.exp y * deriv f (σ * Real.exp y)
  simpa [mul_comm] using hcomp.deriv

lemma iteratedDeriv_expPullback (σ : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) :
    iteratedDeriv n (expPullback σ f) = expPullback σ ((eulerOperator^[n]) f) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      exact deriv_expPullback σ ((contDiff_eulerOperator_iterate hf n).differentiable (by simp))
where
  contDiff_eulerOperator_iterate {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
      ∀ n : ℕ, ContDiff ℝ ∞ ((eulerOperator^[n]) f)
    | 0 => by simpa using hf
    | n + 1 => by
        rw [Function.iterate_succ_apply']
        exact contDiff_eulerOperator (contDiff_eulerOperator_iterate hf n)

lemma eulerOperator_affine (a b : ℝ) :
    eulerOperator (fun x ↦ a + b * x) = fun x ↦ b * x := by
  funext x
  simp [eulerOperator, mul_comm]

lemma eulerOperator_linear (b : ℝ) :
    eulerOperator (fun x ↦ b * x) = fun x ↦ b * x := by
  simpa using eulerOperator_affine 0 b

/-- The quadratic Taylor estimate at zero used after the exponential change of variables. -/
lemma exists_norm_sub_affine_le_sq {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |x| < 1 →
      |f x - f 0 - deriv f 0 * x| ≤ K * x ^ 2 := by
  have hcont : ContinuousOn (fun x ↦ ‖iteratedDeriv 2 f x‖) (Set.Icc (-1 : ℝ) 1) :=
    (hf.continuous_iteratedDeriv (m := 2)
      (WithTop.coe_le_coe.mpr (ENat.coe_lt_top 2).le)).norm.continuousOn
  obtain ⟨xm, hxm, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by linarith : (-1 : ℝ) ≤ 1)) hcont
  let K : ℝ := ‖iteratedDeriv 2 f xm‖ / 2
  refine ⟨K, by positivity, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp
  have hxI : x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [abs_lt] at hx
    exact ⟨hx.1.le, hx.2.le⟩
  have huI : Set.uIcc 0 x ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    rcases le_total 0 x with h0x | hx0'
    · rw [Set.uIcc_of_le h0x] at hz
      exact ⟨by linarith [hz.1], hz.2.trans hxI.2⟩
    · rw [Set.uIcc_comm, Set.uIcc_of_le hx0'] at hz
      exact ⟨hxI.1.trans hz.1, by linarith [hz.2]⟩
  obtain ⟨z, hz, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (x := x) (x₀ := 0) (n := 1)
      (Ne.symm hx0) ((hf.of_le
        (WithTop.coe_le_coe.mpr (ENat.coe_lt_top 2).le)).contDiffOn)
  have hzI : z ∈ Set.Icc (-1 : ℝ) 1 := huI (Set.uIoo_subset_uIcc_self hz)
  have hzbound : ‖iteratedDeriv 2 f z‖ ≤ ‖iteratedDeriv 2 f xm‖ := hmax hzI
  have hpoly : taylorWithinEval f 1 (Set.uIcc 0 x) 0 x = f 0 + deriv f 0 * x := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
      Nat.cast_one, Nat.factorial_one, pow_zero, pow_one, smul_eq_mul]
    have hu : UniqueDiffOn ℝ (Set.uIcc 0 x) := uniqueDiffOn_uIcc (Ne.symm hx0)
    rw [iteratedDerivWithin_zero, iteratedDerivWithin_eq_iteratedDeriv hu
      ((hf.of_le (by simp)).contDiffAt) Set.left_mem_uIcc]
    simp [iteratedDeriv_one, mul_comm]
  have hleft : f x - f 0 - deriv f 0 * x =
      f x - taylorWithinEval f 1 (Set.uIcc 0 x) 0 x := by rw [hpoly]; ring
  rw [hleft, hrem]
  norm_num [abs_div, abs_mul, abs_pow]
  dsimp [K]
  have hzbound' : |iteratedDeriv 2 f z| ≤ |iteratedDeriv 2 f xm| := by
    simpa [Real.norm_eq_abs] using hzbound
  calc
    |iteratedDeriv 2 f z| * x ^ 2 / 2 =
        (|iteratedDeriv 2 f z| / 2) * x ^ 2 := by ring
    _ ≤ (|iteratedDeriv 2 f xm| / 2) * x ^ 2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hzbound' (by norm_num))
        (sq_nonneg x)

private lemma exists_iterate_bound_of_tendsto {L : (ℝ → ℝ) → ℝ → ℝ}
    {f g : ℝ → ℝ}
    (hlim : ∀ x : ℝ, Tendsto (fun n : ℕ ↦ (L^[n]) f x) atTop (nhds (g x)))
    (x : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖(L^[n]) f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    (Metric.isBounded_range_of_tendsto _ (hlim x))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun n ↦ ?_⟩
  have hn : ‖(L^[n]) f x‖ ≤ C := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hC (Set.mem_range_self n)
  exact hn.trans (le_max_left _ _)

private lemma expPullback_eq_affine (σ : ℝ) (hσ : |σ| = 1)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ (eulerOperator^[n]) f x) atTop (nhds (g x))) :
    expPullback σ f = fun y ↦ f 0 + deriv f 0 * (σ * Real.exp y) := by
  let F : ℝ → ℝ := expPullback σ f
  have hFsmooth : ContDiff ℝ ∞ F := contDiff_expPullback σ hf
  have hbounded : ∀ y : ℝ, ∃ C : ℝ, ∀ n : ℕ, ‖iteratedDeriv n F y‖ ≤ C := by
    intro y
    obtain ⟨C, hC, hCb⟩ := exists_iterate_bound_of_tendsto hlim (σ * Real.exp y)
    refine ⟨C, fun n ↦ ?_⟩
    change ‖iteratedDeriv n (expPullback σ f) y‖ ≤ C
    rw [iteratedDeriv_expPullback σ hf n]
    exact hCb n
  have hFanalytic : AnalyticOnNhd ℝ F Set.univ := by
    obtain ⟨Fℂ, hFℂ, hFℂF⟩ := tao_analyticity hFsmooth hbounded
    let q : ℝ → ℝ := fun x ↦ (Fℂ (x : ℂ)).re
    have hq : AnalyticOnNhd ℝ q Set.univ := fun x _ ↦ (hFℂ.analyticAt (x : ℂ)).re_ofReal
    have hEq : F = q := by
      funext x
      simpa [q] using congrArg Complex.re (hFℂF x).symm
    simpa [hEq] using hq
  obtain ⟨M, hMpos, hM⟩ := exists_iterate_bound_of_tendsto hlim σ
  have hFM : ∀ n : ℕ, ‖iteratedDeriv n F 0‖ ≤ M := by
    intro n
    rw [iteratedDeriv_expPullback σ hf n]
    simpa [expPullback] using hM n
  obtain ⟨Fℂ, hFℂdiff, hFℂreal, hFℂgrowth⟩ :=
    exists_entire_extension_norm_le_exp hFanalytic hFM
  let a : ℝ := f 0
  let b : ℝ := deriv f 0
  let H : ℂ → ℂ := fun z ↦ Fℂ z - a - (σ * b : ℝ) * Complex.exp z
  have hHdiff : Differentiable ℂ H := by
    fun_prop
  let C : ℝ := M + |a| + |b|
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hHglobal : ∀ z : ℂ, ‖H z‖ ≤ C * Real.exp (1 * ‖z‖) := by
    intro z
    calc
      ‖H z‖ ≤ ‖Fℂ z‖ + ‖(a : ℂ)‖ + ‖((σ * b : ℝ) : ℂ) * Complex.exp z‖ := by
        dsimp [H]
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ M * Real.exp ‖z‖ + |a| + |b| * Real.exp ‖z‖ := by
        gcongr
        · exact hFℂgrowth z
        · simp
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, hσ, one_mul,
            Complex.norm_exp]
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (Complex.re_le_norm z)) (abs_nonneg b)
      _ ≤ (M + |a| + |b|) * Real.exp ‖z‖ := by
        have he : 1 ≤ Real.exp ‖z‖ := Real.one_le_exp (norm_nonneg z)
        calc
          M * Real.exp ‖z‖ + |a| + |b| * Real.exp ‖z‖
              ≤ M * Real.exp ‖z‖ + |a| * Real.exp ‖z‖ + |b| * Real.exp ‖z‖ := by
                have ha := mul_le_mul_of_nonneg_left he (abs_nonneg a)
                nlinarith
          _ = (M + |a| + |b|) * Real.exp ‖z‖ := by ring
      _ = C * Real.exp (1 * ‖z‖) := by simp [C]
  obtain ⟨K, hK, hTaylor⟩ := exists_norm_sub_affine_le_sq hf
  let A : ℝ := K + 1
  have hHdecay : ∀ y : ℝ, y ≤ -1 → ‖H (y : ℂ)‖ ≤ A * Real.exp (2 * y) := by
    intro y hy
    have hy0 : y < 0 := hy.trans_lt (by norm_num)
    have hexplt : Real.exp y < 1 := Real.exp_lt_one_iff.mpr hy0
    have hreal := hTaylor (σ * Real.exp y) (by simpa [abs_mul, hσ] using hexplt)
    have hHreal : H (y : ℂ) =
        ((f (σ * Real.exp y) - f 0 - deriv f 0 * (σ * Real.exp y) : ℝ) : ℂ) := by
      simp [H, a, b, hFℂreal, F, expPullback, mul_comm, mul_left_comm]
    have hσsq : σ ^ 2 = 1 := by nlinarith [sq_abs σ]
    rw [hHreal, Complex.norm_real, Real.norm_eq_abs]
    calc
      |f (σ * Real.exp y) - f 0 - deriv f 0 * (σ * Real.exp y)|
          ≤ K * (σ * Real.exp y) ^ 2 := hreal
      _ = K * Real.exp (2 * y) := by
        rw [mul_pow, hσsq, one_mul, pow_two, ← Real.exp_add]
        congr 2
        ring
      _ ≤ A * Real.exp (2 * y) :=
        mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (Real.exp_pos _).le
  have hHzero : H = 0 :=
    entire_eq_zero_of_exp_type_one_of_neg_real_decay hHdiff hCpos
      (by simpa using hHglobal) hHdecay
  funext y
  have hz := congrFun hHzero (y : ℂ)
  have hreal := hFℂreal y
  simp only [Pi.zero_apply] at hz
  change F y = f 0 + deriv f 0 * (σ * Real.exp y)
  apply Complex.ofReal_injective
  rw [← hreal]
  dsimp [H, a, b] at hz
  calc
    Fℂ (y : ℂ) = (f 0 : ℂ) + ((σ * deriv f 0 : ℝ) : ℂ) * Complex.exp y := by
      linear_combination hz
    _ = ((f 0 + deriv f 0 * (σ * Real.exp y) : ℝ) : ℂ) := by
      push_cast
      ring

end Euler

/--
Classification for the simple-zero operator `f ↦ x f'`, following the two
exponential coordinate charts in the DRP write-up.
-/
theorem eulerOperator_iterate_limit_classification {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ (eulerOperator^[n]) f x) atTop (nhds (g x))) :
    f = (fun x ↦ f 0 + deriv f 0 * x) ∧
      g = (fun x ↦ deriv f 0 * x) := by
  have hpos := Euler.expPullback_eq_affine 1 (by norm_num) hf hlim
  have hneg := Euler.expPullback_eq_affine (-1) (by norm_num) hf hlim
  have hfaffine : f = fun x ↦ f 0 + deriv f 0 * x := by
    funext x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · let y := Real.log (-x)
      have hexp : -Real.exp y = x := by
        dsimp [y]
        rw [Real.exp_log (neg_pos.mpr hx)]
        ring
      have := congrFun hneg y
      simpa [Euler.expPullback, hexp] using this
    · simp
    · let y := Real.log x
      have hexp : Real.exp y = x := by simp [y, Real.exp_log hx]
      have := congrFun hpos y
      simpa [Euler.expPullback, hexp] using this
  refine ⟨hfaffine, ?_⟩
  funext x
  have hshift := (tendsto_add_atTop_iff_nat 1).mpr (hlim x)
  let b : ℝ := deriv f 0
  have hLf : eulerOperator f = fun x ↦ b * x := by
    rw [hfaffine]
    exact Euler.eulerOperator_affine _ _
  have hiter : ∀ n : ℕ, (eulerOperator^[n + 1]) f = fun x ↦ b * x := by
    intro n
    induction n with
    | zero => simpa using hLf
    | succ n ih =>
        rw [Nat.succ_add, Function.iterate_succ_apply', ih, Euler.eulerOperator_linear]
  have hconst : (fun n : ℕ ↦ (eulerOperator^[n + 1]) f x) =
      fun _ ↦ deriv f 0 * x := by
    funext n
    simpa [b] using congrFun (hiter n) x
  rw [hconst] at hshift
  exact tendsto_nhds_unique tendsto_const_nhds hshift |>.symm

/-- The limit is smooth and fixed by the Euler operator. -/
theorem eulerOperator_iterate_limit {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ (eulerOperator^[n]) f x) atTop (nhds (g x))) :
    ContDiff ℝ ∞ g ∧ eulerOperator g = g := by
  obtain ⟨_, hg⟩ := eulerOperator_iterate_limit_classification hf hlim
  rw [hg]
  exact ⟨contDiff_const.mul contDiff_id, Euler.eulerOperator_linear _⟩

end DRPSpring2026
