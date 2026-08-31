import DRPSpring2026.Analyticity.Tao

/-!
# Pointwise limits of iterated derivatives

This module is the first application of Tao's analyticity theorem.  Operator
generalizations should import this result rather than being added here.
-/

open Filter
open scoped ContDiff

namespace DRPSpring2026

private lemma exists_iteratedDeriv_bound_on {f g : ℝ → ℝ} {I : Set ℝ}
    (hlim : ∀ x ∈ I,
      Tendsto (fun n : ℕ ↦ iteratedDeriv n f x) atTop (nhds (g x))) :
    ∀ x ∈ I, ∃ C : ℝ, ∀ n : ℕ, ‖iteratedDeriv n f x‖ ≤ C := by
  intro x hx
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    (Metric.isBounded_range_of_tendsto _ (hlim x hx))
  refine ⟨C, fun n ↦ ?_⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using hC (Set.mem_range_self n)

/--
The local derivative-limit theorem on a connected open subset of the real
line.  It records the local Tao extension as well as the fixed-point equation.
-/
theorem iteratedDeriv_limit_on {f g : ℝ → ℝ} {I : Set ℝ}
    (hIopen : IsOpen I) (hIpre : IsPreconnected I) (hIne : I.Nonempty)
    (hf : ContDiffOn ℝ ∞ f I)
    (hlim : ∀ x ∈ I,
      Tendsto (fun n : ℕ ↦ iteratedDeriv n f x) atTop (nhds (g x))) :
    HasEntireExtensionOn f I ∧ ContDiffOn ℝ ∞ g I ∧ Set.EqOn (deriv g) g I := by
  have hbounded := exists_iteratedDeriv_bound_on hlim
  have hentire : HasEntireExtensionOn f I :=
    tao_analyticity_on hIopen hIpre hIne hf hbounded
  obtain ⟨F, hF, hFf⟩ := hentire
  let q : ℝ → ℝ := fun x ↦ (F (x : ℂ)).re
  have hqanalytic : AnalyticOnNhd ℝ q Set.univ := by
    intro x _
    exact (hF.analyticAt (x : ℂ)).re_ofReal
  have hfq : Set.EqOn f q I := by
    intro x hx
    simpa [q] using congrArg Complex.re (hFf x hx).symm
  have hfqEventually : ∀ x ∈ I, f =ᶠ[nhds x] q := by
    intro x hx
    exact Filter.mem_of_superset (hIopen.mem_nhds hx) hfq
  have hderivEq : ∀ n : ℕ, Set.EqOn (iteratedDeriv n f) (iteratedDeriv n q) I := by
    intro n x hx
    exact Filter.EventuallyEq.eq_of_nhds ((hfqEventually x hx).iteratedDeriv n)
  obtain ⟨c, hcI⟩ := hIne
  obtain ⟨C, hC⟩ := hbounded c hcI
  have hqC : ∀ n : ℕ, ‖iteratedDeriv n q c‖ ≤ C := by
    intro n
    rw [← hderivEq n hcI]
    exact hC n
  have hqglobal : ∀ n x, ‖iteratedDeriv n q x‖ ≤ C * Real.exp ‖x - c‖ :=
    norm_iteratedDeriv_le_mul_exp_sub hqanalytic hqC
  have hfbound : ∀ n x, x ∈ I →
      ‖iteratedDeriv n f x‖ ≤ C * Real.exp ‖x - c‖ := by
    intro n x hx
    rw [hderivEq n hx]
    exact hqglobal n x
  have hgbound : ∀ x ∈ I, ‖g x‖ ≤ C * Real.exp ‖x - c‖ := by
    intro x hx
    exact le_of_tendsto (tendsto_norm.comp (hlim x hx))
      (Filter.Eventually.of_forall fun n ↦ hfbound n x hx)
  have huI : ∀ {a b : ℝ}, a ∈ I → b ∈ I → Set.uIcc a b ⊆ I := by
    intro a b ha hb x hx
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hx
      exact hIpre.ordConnected.out ha hb hx
    · rw [Set.uIcc_comm, Set.uIcc_of_le hba] at hx
      exact hIpre.ordConnected.out hb ha hx
  have hintegral : ∀ a ∈ I, ∀ b ∈ I, g b - g a = ∫ x in a..b, g x := by
    intro a ha b hb
    have habI := huI ha hb
    have hftc : ∀ n : ℕ,
        (∫ x in a..b, iteratedDeriv (n + 1) q x) =
          iteratedDeriv n q b - iteratedDeriv n q a := by
      intro n
      rw [iteratedDeriv_succ]
      have hcont : Continuous (deriv (iteratedDeriv n q)) := by
        rw [← iteratedDeriv_succ]
        exact hqanalytic.contDiff.continuous_iteratedDeriv (n + 1) (mod_cast le_top)
      exact intervalIntegral.integral_deriv_eq_sub
        (fun _ _ ↦ (hqanalytic.contDiff.differentiable_iteratedDeriv' n).differentiableAt)
        (hcont.intervalIntegrable a b)
    have hdct : Tendsto
        (fun n : ℕ ↦ ∫ x in a..b, iteratedDeriv (n + 1) q x) atTop
        (nhds (∫ x in a..b, g x)) := by
      apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun x ↦ C * Real.exp ‖x - c‖)
      · exact Filter.Eventually.of_forall fun n ↦
          (hqanalytic.contDiff.continuous_iteratedDeriv (n + 1)
            (mod_cast le_top)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun n ↦ Filter.Eventually.of_forall fun x hx ↦
          hqglobal (n + 1) x
      · exact (by fun_prop : Continuous (fun x : ℝ ↦ C * Real.exp ‖x - c‖)).intervalIntegrable a b
      · filter_upwards [] with x hx
        have hxI : x ∈ I := habI (Set.uIoc_subset_uIcc hx)
        exact ((tendsto_add_atTop_iff_nat 1).mpr (hlim x hxI)).congr'
          (Filter.Eventually.of_forall fun n ↦ hderivEq (n + 1) hxI)
    have hright : Tendsto
        (fun n : ℕ ↦ iteratedDeriv n q b - iteratedDeriv n q a) atTop
        (nhds (∫ x in a..b, g x)) := by
      simpa only [hftc] using hdct
    have hlimb : Tendsto (fun n : ℕ ↦ iteratedDeriv n q b) atTop (nhds (g b)) := by
      convert hlim b hb using 1
      ext n
      exact (hderivEq n hb).symm
    have hlima : Tendsto (fun n : ℕ ↦ iteratedDeriv n q a) atTop (nhds (g a)) := by
      convert hlim a ha using 1
      ext n
      exact (hderivEq n ha).symm
    have hend : Tendsto
        (fun n : ℕ ↦ iteratedDeriv n q b - iteratedDeriv n q a) atTop
        (nhds (g b - g a)) := hlimb.sub hlima
    exact tendsto_nhds_unique hend hright
  have hCnonneg : 0 ≤ C := (norm_nonneg (iteratedDeriv 0 f c)).trans (hC 0)
  have hgcontinuousOn : ContinuousOn g I := by
    intro x₀ hx₀
    obtain ⟨r, hr, hrI⟩ := Metric.isOpen_iff.mp hIopen x₀ hx₀
    let ρ : ℝ := r / 2
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    let K : NNReal :=
      ⟨C * Real.exp (‖x₀ - c‖ + ρ), mul_nonneg hCnonneg (Real.exp_pos _).le⟩
    have hKI : Set.Icc (x₀ - ρ) (x₀ + ρ) ⊆ I := by
      intro z hz
      apply hrI
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> dsimp [ρ] at hz ⊢ <;> linarith [hz.1, hz.2]
    have hKbound : ∀ z ∈ Set.Icc (x₀ - ρ) (x₀ + ρ), ‖g z‖ ≤ (K : ℝ) := by
      intro z hz
      have hzc : ‖z - c‖ ≤ ‖x₀ - c‖ + ρ := by
        calc
          ‖z - c‖ = ‖(x₀ - c) + (z - x₀)‖ := by ring_nf
          _ ≤ ‖x₀ - c‖ + ‖z - x₀‖ := norm_add_le _ _
          _ ≤ ‖x₀ - c‖ + ρ := by
            gcongr
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith [hz.1, hz.2]
      exact (hgbound z (hKI hz)).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzc) hCnonneg)
    have hLip : LipschitzOnWith K g (Set.Icc (x₀ - ρ) (x₀ + ρ)) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have hbetween : ∀ z ∈ Set.uIoc x y, z ∈ Set.Icc (x₀ - ρ) (x₀ + ρ) := by
        intro z hz
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hz) with hxy | hyx
        · exact ⟨by linarith [hx.1, hy.1, hxy.1], by linarith [hx.2, hy.2, hxy.2]⟩
        · exact ⟨by linarith [hx.1, hy.1, hyx.1], by linarith [hx.2, hy.2, hyx.2]⟩
      calc
        dist (g x) (g y) = ‖g y - g x‖ := by rw [dist_comm, dist_eq_norm]
        _ = ‖∫ z in x..y, g z‖ := congrArg norm (hintegral x (hKI hx) y (hKI hy))
        _ ≤ (K : ℝ) * |y - x| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (fun z hz ↦ hKbound z (hbetween z hz))
        _ = (K : ℝ) * dist x y := by rw [Real.dist_eq, abs_sub_comm]
    exact (hLip.continuousOn x₀
      ⟨by dsimp [ρ]; linarith, by dsimp [ρ]; linarith⟩).continuousAt
        (Icc_mem_nhds (by dsimp [ρ]; linarith) (by dsimp [ρ]; linarith)) |>.continuousWithinAt
  have hgHasDeriv : ∀ x ∈ I, HasDerivAt g (g x) x := by
    intro x hx
    have hgcontAt : ContinuousAt g x :=
      (hgcontinuousOn x hx).continuousAt (hIopen.mem_nhds hx)
    have hprimitive : HasDerivAt (fun y ↦ g c + ∫ t in c..y, g t) (g x) x :=
      (intervalIntegral.integral_hasDerivAt_right
        ((hgcontinuousOn.mono (huI hcI hx)).intervalIntegrable)
        (hgcontinuousOn.stronglyMeasurableAtFilter hIopen x hx) hgcontAt).const_add (g c)
    have heq : g =ᶠ[nhds x] fun y ↦ g c + ∫ t in c..y, g t := by
      filter_upwards [hIopen.mem_nhds hx] with y hy
      linarith [hintegral c hcI y hy]
    exact hprimitive.congr_of_eventuallyEq heq
  have hgdiffOn : DifferentiableOn ℝ g I := fun x hx ↦ (hgHasDeriv x hx).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv g) g I := fun x hx ↦ (hgHasDeriv x hx).deriv
  let H : ℝ → ℝ := fun x ↦ Real.exp (-x) * g x
  have hHdiff : DifferentiableOn ℝ H I := by
    intro x hx
    exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).differentiableAt.mul
      (hgHasDeriv x hx).differentiableAt |>.differentiableWithinAt
  have hHderiv : Set.EqOn (deriv H) 0 I := by
    intro x hx
    have he : HasDerivAt (fun y ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa only [Function.comp_def, mul_neg, mul_one] using
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have hh := he.mul (hgHasDeriv x hx)
    change deriv ((fun y ↦ Real.exp (-y)) * g) x = 0
    exact hh.deriv.trans (by ring)
  have hHconst : ∀ x ∈ I, H x = H c := fun x hx ↦
    hIopen.is_const_of_deriv_eq_zero hIpre hHdiff hHderiv hx hcI
  let gs : ℝ → ℝ := fun x ↦ (Real.exp (-c) * g c) * Real.exp x
  have hggs : Set.EqOn g gs I := by
    intro x hx
    calc
      g x = Real.exp x * (Real.exp (-x) * g x) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ = Real.exp x * (Real.exp (-c) * g c) :=
        congrArg (fun z : ℝ ↦ Real.exp x * z) (hHconst x hx)
      _ = gs x := by simp [gs, mul_comm, mul_left_comm]
  have hgsmooth : ContDiffOn ℝ ∞ g I := by
    have hs : ContDiff ℝ ∞ gs := by
      exact contDiff_const.mul Real.contDiff_exp
    exact hs.contDiffOn.congr (fun x hx ↦ hggs hx)
  exact ⟨⟨F, hF, hFf⟩, hgsmooth, hderiv⟩

/-- A solution of `g' = g` on a nonempty connected open set is a constant
multiple of the real exponential there. -/
theorem eqOn_const_mul_exp_of_deriv_eq_self {g : ℝ → ℝ} {I : Set ℝ}
    (hIopen : IsOpen I) (hIpre : IsPreconnected I) (hIne : I.Nonempty)
    (hg : DifferentiableOn ℝ g I) (hderiv : Set.EqOn (deriv g) g I) :
    ∃ C : ℝ, Set.EqOn g (fun x ↦ C * Real.exp x) I := by
  obtain ⟨c, hc⟩ := hIne
  let H : ℝ → ℝ := fun x ↦ Real.exp (-x) * g x
  have hHdiff : DifferentiableOn ℝ H I := by
    intro x hx
    exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).differentiableAt.mul
      ((hg x hx).differentiableAt (hIopen.mem_nhds hx)) |>.differentiableWithinAt
  have hHderiv : Set.EqOn (deriv H) 0 I := by
    intro x hx
    have he : HasDerivAt (fun y ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
      simpa only [Function.comp_def, mul_neg, mul_one] using
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have hh := he.mul ((hg x hx).differentiableAt (hIopen.mem_nhds hx)).hasDerivAt
    change deriv ((fun y ↦ Real.exp (-y)) * g) x = 0
    rw [hh.deriv, hderiv hx]
    ring
  have hHconst : ∀ x ∈ I, H x = H c := fun x hx ↦
    hIopen.is_const_of_deriv_eq_zero hIpre hHdiff hHderiv hx hc
  refine ⟨Real.exp (-c) * g c, fun x hx ↦ ?_⟩
  calc
    g x = Real.exp x * (Real.exp (-x) * g x) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ = Real.exp x * (Real.exp (-c) * g c) :=
      congrArg (fun z : ℝ ↦ Real.exp x * z) (hHconst x hx)
    _ = (Real.exp (-c) * g c) * Real.exp x := by ring

/--
If the iterated derivatives of a smooth real function converge pointwise,
then their limit is smooth and is a fixed point of ordinary differentiation.
-/
theorem iteratedDeriv_limit {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ iteratedDeriv n f x) atTop (nhds (g x))) :
    ContDiff ℝ ∞ g ∧ deriv g = g := by
  obtain ⟨_, hg, hd⟩ :=
    iteratedDeriv_limit_on isOpen_univ isPreconnected_univ Set.univ_nonempty
      hf.contDiffOn (fun x _ ↦ hlim x)
  exact ⟨contDiffOn_univ.mp hg, funext fun x ↦ hd (Set.mem_univ x)⟩

end DRPSpring2026
