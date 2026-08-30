import Mathlib

/-!
# An exponential-type uniqueness principle

This file isolates the Phragmén--Lindelöf input used for an operator whose
leading coefficient has a simple zero.  The normalization below is precisely
the one needed in the DRP argument: type one versus decay of order two.
-/

open Filter Set Complex Asymptotics
open scoped Topology Real

namespace DRPSpring2026

/--
An entire function of exponential type one which decays like `exp (2t)` on a
negative real ray is zero.
-/
theorem entire_eq_zero_of_exp_type_one_of_neg_real_decay
    {H : ℂ → ℂ} {C A T : ℝ}
    (hH : Differentiable ℂ H)
    (hC : 0 < C)
    (hglobal : ∀ z : ℂ, ‖H z‖ ≤ C * Real.exp ‖z‖)
    (hdecay : ∀ t : ℝ, t ≤ T → ‖H (t : ℂ)‖ ≤ A * Real.exp (2 * t)) :
    H = 0 := by
  let q : ℝ := 3 / 2
  let β : ℝ := 7 / 4
  let p : ℂ → ℂ := fun z ↦ z ^ (q : ℂ)
  let Q : ℂ → ℂ := fun z ↦ H (-p z) * Complex.exp ((β : ℂ) * p z)
  have hpDiff : DifferentiableOn ℂ p {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.cpow_const differentiableOn_id
    intro z hz
    exact Or.inl hz
  have hpCont : ContinuousOn p {z : ℂ | 0 ≤ z.re} := by
    intro z hz
    exact Complex.continuousAt_cpow_const_of_re_pos (Or.inl hz) (by norm_num [q]) |>.continuousWithinAt
  have hQdc : DiffContOnCl ℂ Q {z : ℂ | 0 < z.re} := by
    constructor
    · intro z hz
      have hpAt : DifferentiableAt ℂ p z := by
        dsimp [p]
        exact differentiableAt_id.cpow_const (Or.inl hz)
      dsimp [Q]
      exact ((hH.differentiableAt.comp z hpAt.neg).mul
        ((((differentiableAt_const (c := (β : ℂ))).mul hpAt)).cexp)).differentiableWithinAt
    · rw [closure_setOf_lt_re]
      intro z hz
      dsimp [Q]
      have hleft := hH.continuous.continuousAt.comp_continuousWithinAt (hpCont z hz).neg
      have hβcont : ContinuousWithinAt (fun _ : ℂ ↦ (β : ℂ)) {z : ℂ | 0 ≤ z.re} z :=
        continuousWithinAt_const
      have hright := (hβcont.mul (hpCont z hz)).cexp
      change ContinuousWithinAt
        ((fun w ↦ H (-p w)) * (fun w ↦ Complex.exp ((β : ℂ) * p w)))
        {z : ℂ | 0 ≤ z.re} z
      simpa [Function.comp_def] using hleft.mul hright
  have hQgrowth : ∃ c < (2 : ℝ), ∃ B,
      Q =O[Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}]
        fun z ↦ Real.exp (B * ‖z‖ ^ c) := by
    refine ⟨q, by norm_num [q], 1 + β, ?_⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, Filter.Eventually.of_forall fun z ↦ ?_⟩
    have hpNorm : ‖p z‖ = ‖z‖ ^ q := by simp [p, Complex.norm_cpow_real]
    calc
      ‖Q z‖ = ‖H (-p z)‖ * Real.exp (β * (p z).re) := by
        simp [Q, Complex.norm_exp, β]
      _ ≤ (C * Real.exp ‖p z‖) * Real.exp (β * (p z).re) := by
        gcongr
        simpa using hglobal (-p z)
      _ ≤ C * Real.exp ((1 + β) * ‖z‖ ^ q) := by
        rw [mul_assoc, ← Real.exp_add, hpNorm]
        have hre : (p z).re ≤ ‖p z‖ := Complex.re_le_norm _
        have hβ : 0 ≤ β := by norm_num [β]
        rw [hpNorm] at hre
        have := mul_le_mul_of_nonneg_left hre hβ
        gcongr
        linarith
      _ = C * ‖Real.exp ((1 + β) * ‖z‖ ^ q)‖ := by
        rw [Real.norm_eq_abs, Real.abs_exp]
  have hpImagRe : ∀ y : ℝ,
      (p (y * I)).re = -(‖y‖ ^ q * (Real.sqrt 2 / 2)) := by
    intro y
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · change ((((y : ℂ) * I) ^ (q : ℂ)).re) = _
      rw [Complex.cpow_ofReal_re]
      have harg : ((y : ℂ) * I).arg = -(Real.pi / 2) :=
        Complex.arg_eq_neg_pi_div_two_iff.mpr (by simp [hy])
      rw [harg]
      have htrig : Real.cos (-(Real.pi / 2) * q) = -(Real.sqrt 2 / 2) := by
        rw [show -(Real.pi / 2) * q = -(Real.pi - Real.pi / 4) by
          dsimp [q]; ring]
        rw [Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_four]
      rw [htrig]
      simp only [norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs]
      ring
    · simp [p, q]
    · change ((((y : ℂ) * I) ^ (q : ℂ)).re) = _
      rw [Complex.cpow_ofReal_re]
      have harg : ((y : ℂ) * I).arg = Real.pi / 2 :=
        Complex.arg_eq_pi_div_two_iff.mpr (by simp [hy])
      rw [harg]
      have htrig : Real.cos (Real.pi / 2 * q) = -(Real.sqrt 2 / 2) := by
        rw [show Real.pi / 2 * q = Real.pi - Real.pi / 4 by
          dsimp [q]; ring]
        rw [Real.cos_pi_sub, Real.cos_pi_div_four]
      rw [htrig]
      simp only [norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs]
      ring
  have hQimag : ∃ D : ℝ, ∀ y : ℝ, ‖Q (y * I)‖ ≤ D := by
    refine ⟨C, fun y ↦ ?_⟩
    have hsqrt : 1 - β * (Real.sqrt 2 / 2) ≤ 0 := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hs0 := Real.sqrt_nonneg 2
      dsimp [β]
      nlinarith
    have hpNorm : ‖p (y * I)‖ = ‖y‖ ^ q := by
      simp [p, Complex.norm_cpow_real, Real.norm_eq_abs]
    calc
      ‖Q (y * I)‖ = ‖H (-p (y * I))‖ * Real.exp (β * (p (y * I)).re) := by
        simp [Q, Complex.norm_exp, β]
      _ ≤ (C * Real.exp ‖p (y * I)‖) * Real.exp (β * (p (y * I)).re) := by
        gcongr
        simpa using hglobal (-p (y * I))
      _ = C * Real.exp ((1 - β * (Real.sqrt 2 / 2)) * (‖y‖ ^ q)) := by
        rw [mul_assoc, ← Real.exp_add, hpNorm, hpImagRe]
        congr 2
        ring
      _ ≤ C * 1 := by
        gcongr
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg hsqrt (Real.rpow_nonneg (norm_nonneg y) q)
      _ = C := mul_one C
  have hQdecay : SuperpolynomialDecay atTop Real.exp fun x : ℝ ↦ ‖Q x‖ := by
    intro n
    let d : ℝ := 2 - β
    have hd : 0 < d := by norm_num [d, β]
    have hpow : Tendsto (fun x : ℝ ↦ x ^ (q - 1)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num [q])
    have hinner : Tendsto (fun x : ℝ ↦ (n : ℝ) - d * x ^ (q - 1)) atTop atBot :=
      by
        simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left atTop (n : ℝ)
          (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hd hpow))
    have hexponent : Tendsto (fun x : ℝ ↦ (n : ℝ) * x - d * x ^ q) atTop atBot := by
      have hprod := tendsto_id.atTop_mul_atBot₀ hinner
      apply hprod.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.rpow_sub_one hx.ne']
      simp only [id_eq]
      field_simp [hx.ne']
    have hupper : Tendsto
        (fun x : ℝ ↦ A * Real.exp ((n : ℝ) * x - d * x ^ q)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp hexponent).const_mul A
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall fun x ↦ mul_nonneg (by positivity) (norm_nonneg _)
    · have hrpow : Tendsto (fun x : ℝ ↦ x ^ q) atTop atTop :=
        tendsto_rpow_atTop (by norm_num [q])
      have hT : ∀ᶠ x : ℝ in atTop, -(x ^ q) ≤ T :=
        (tendsto_neg_atTop_atBot.comp hrpow).eventually (eventually_le_atBot T)
      filter_upwards [eventually_gt_atTop (0 : ℝ), hT] with x hx hxT
      have hpReal : p (x : ℂ) = ((x ^ q : ℝ) : ℂ) := by
        dsimp [p]
        exact (Complex.ofReal_cpow hx.le q).symm
      have hQbound : ‖Q x‖ ≤ A * Real.exp (-d * x ^ q) := by
        calc
          ‖Q x‖ = ‖H (-((x ^ q : ℝ) : ℂ))‖ * Real.exp (β * x ^ q) := by
            simp [Q, hpReal, Complex.norm_exp]
          _ ≤ (A * Real.exp (2 * (-(x ^ q)))) * Real.exp (β * x ^ q) := by
            gcongr
            simpa only [Complex.ofReal_neg] using hdecay (-(x ^ q)) hxT
          _ = A * Real.exp (-d * x ^ q) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            dsimp [d]
            ring
      calc
        Real.exp x ^ n * ‖Q x‖
            ≤ Real.exp x ^ n * (A * Real.exp (-d * x ^ q)) :=
          mul_le_mul_of_nonneg_left hQbound (by positivity)
        _ = A * Real.exp ((n : ℝ) * x - d * x ^ q) := by
          rw [← Real.exp_nat_mul]
          calc
            Real.exp ((n : ℝ) * x) * (A * Real.exp (-d * x ^ q)) =
                A * (Real.exp ((n : ℝ) * x) * Real.exp (-d * x ^ q)) := by ring
            _ = A * Real.exp ((n : ℝ) * x - d * x ^ q) := by
              rw [← Real.exp_add]
              congr 2
              ring
  have hQzero : Set.EqOn Q 0 {z : ℂ | 0 ≤ z.re} :=
    PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay
      hQdc hQgrowth hQdecay hQimag
  have hneg : ∀ x : ℝ, 0 < x → H (-((x ^ q : ℝ) : ℂ)) = 0 := by
    intro x hx
    have hqx := hQzero (by simpa using hx.le : (x : ℂ) ∈ {z : ℂ | 0 ≤ z.re})
    have hexpne : Complex.exp ((β : ℂ) * p x) ≠ 0 := Complex.exp_ne_zero _
    dsimp [Q] at hqx
    rw [mul_eq_zero] at hqx
    rcases hqx with h | h
    · simpa [p, Complex.ofReal_cpow hx.le, q] using h
    · exact (hexpne h).elim
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (-1 : ℂ), H z = 0 := by
    let s : ℝ → ℂ := fun x ↦ -((x ^ q : ℝ) : ℂ)
    have hscont : ContinuousAt s 1 := by
      dsimp [s]
      exact (Complex.continuous_ofReal.continuousAt.comp
        (Real.continuousAt_rpow_const 1 q (Or.inl one_ne_zero))).neg
    have hs : Tendsto s (𝓝[>] (1 : ℝ)) (𝓝[≠] (-1 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · change Tendsto s (𝓝 1 ⊓ 𝓟 (Ioi 1)) (𝓝 (-1 : ℂ))
        simpa [s, q] using hscont.tendsto.mono_left inf_le_left
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have hpowgt : 1 < x ^ q := Real.one_lt_rpow hx (by norm_num [q])
        change s x ≠ (-1 : ℂ)
        intro heq
        have hreal : x ^ q = 1 := by
          apply Complex.ofReal_injective
          simpa [s] using congrArg Neg.neg heq
        exact hpowgt.ne' hreal
    apply hs.frequently
    have hzero : ∀ᶠ x : ℝ in 𝓝[>] 1, H (s x) = 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simpa [s] using hneg x (zero_lt_one.trans hx)
    exact hzero.frequently
  have hHanalytic : AnalyticOnNhd ℂ H Set.univ := fun z _ ↦ hH.analyticAt z
  have hHzero : Set.EqOn H 0 Set.univ :=
    hHanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ _) hfreq
  funext z
  exact hHzero (Set.mem_univ z)

end DRPSpring2026
