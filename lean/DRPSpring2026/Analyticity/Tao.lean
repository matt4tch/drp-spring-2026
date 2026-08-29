import DRPSpring2026.Analyticity.Estimates
import Mathlib

/-!
# Tao's analyticity theorem

This module contains the analyticity input used by the ordinary-derivative
application.  It is deliberately independent of the later differential
operators in the DRP write-up.
-/

open Filter
open scoped ContDiff

namespace DRPSpring2026

private lemma radius_eq_top_of_iteratedDeriv_bound {f : ℝ → ℝ} {x C : ℝ}
    (hC : ∀ n : ℕ, ‖iteratedDeriv n f x‖ ≤ C) :
    let p : FormalMultilinearSeries ℝ ℝ ℝ :=
      FormalMultilinearSeries.ofScalars ℝ (fun n ↦ iteratedDeriv n f x / n.factorial)
    p.radius = ⊤ := by
  intro p
  apply p.radius_eq_top_of_summable_norm
  intro r
  have hs : Summable (fun n : ℕ ↦ C * ((r : ℝ) ^ n / n.factorial)) :=
    (Real.summable_pow_div_factorial (r : ℝ)).mul_left C
  refine hs.of_nonneg_of_le (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.2 _)) ?_
  intro n
  simp only [p, FormalMultilinearSeries.ofScalars_norm, norm_div, Real.norm_natCast]
  calc
    (‖iteratedDeriv n f x‖ / (n.factorial : ℝ)) * (r : ℝ) ^ n
        ≤ (C / (n.factorial : ℝ)) * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hC n) (by positivity))
        (by positivity)
    _ = C * ((r : ℝ) ^ n / (n.factorial : ℝ)) := by ring

private lemma exists_global_analytic_continuation {f : ℝ → ℝ} {x C : ℝ}
    (hfx : AnalyticAt ℝ f x)
    (hC : ∀ n : ℕ, ‖iteratedDeriv n f x‖ ≤ C) :
    ∃ q : ℝ → ℝ, AnalyticOnNhd ℝ q Set.univ ∧ f =ᶠ[nhds x] q := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (fun n ↦ iteratedDeriv n f x / n.factorial)
  have hp_top : p.radius = ⊤ := radius_eq_top_of_iteratedDeriv_bound hC
  have hfp : HasFPowerSeriesAt f p x := by
    simpa [p] using hfx.hasFPowerSeriesAt
  let q : ℝ → ℝ := fun y ↦ p.sum (y - x)
  have hq : AnalyticOnNhd ℝ q Set.univ := by
    have hp : AnalyticOnNhd ℝ p.sum Set.univ := by
      simpa [hp_top] using p.analyticOnNhd
    have hrange : Set.range (fun y : ℝ ↦ y + x) = Set.univ := by
      ext y
      simp only [Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨y - x, by ring⟩
    rw [← hrange]
    simpa [q] using hp.comp_sub x
  refine ⟨q, hq, ?_⟩
  obtain ⟨r, hfr⟩ := hfp
  have hqtop : HasFPowerSeriesOnBall q p x p.radius := by
    simpa [q] using (p.hasFPowerSeriesOnBall (by rw [hp_top]; simp)).comp_sub x
  have hqr : HasFPowerSeriesOnBall q p x r := hqtop.mono hfr.r_pos hfr.r_le
  exact Filter.mem_of_superset (Metric.eball_mem_nhds x hfr.r_pos) (hfr.unique hqr)

private lemma analyticAt_of_iteratedDeriv_bound_on_Ioo {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {a b C x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b)
    (hC : ∀ n : ℕ, ∀ x ∈ Set.Ioo a b, ‖iteratedDeriv n f x‖ ≤ C) :
    AnalyticAt ℝ f x₀ := by
  have hCnonneg : 0 ≤ C := (norm_nonneg (iteratedDeriv 0 f x₀)).trans (hC 0 x₀ hx₀)
  let δ : ℝ := min (x₀ - a) (b - x₀) / 2
  have hδ : 0 < δ := by
    have hleft : 0 < x₀ - a := sub_pos.mpr hx₀.1
    have hright : 0 < b - x₀ := sub_pos.mpr hx₀.2
    dsimp [δ]
    positivity
  have hball : Metric.ball x₀ δ ⊆ Set.Ioo a b := by
    intro y hy
    have hxy : |y - x₀| < δ := by simpa [Real.dist_eq, abs_sub_comm] using hy
    rw [abs_lt] at hxy
    dsimp [δ] at hxy
    constructor <;> linarith [min_le_left (x₀ - a) (b - x₀),
      min_le_right (x₀ - a) (b - x₀)]
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ (fun n ↦ iteratedDeriv n f x₀ / n.factorial)
  have hp_top : p.radius = ⊤ :=
    radius_eq_top_of_iteratedDeriv_bound (fun n ↦ hC n x₀ hx₀)
  let q : ℝ → ℝ := fun y ↦ p.sum (y - x₀)
  have hqtop : HasFPowerSeriesOnBall q p x₀ p.radius := by
    simpa [q] using (p.hasFPowerSeriesOnBall (by rw [hp_top]; simp)).comp_sub x₀
  have hfeq : f =ᶠ[nhds x₀] q := by
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with y hy
    have hyI : y ∈ Set.Ioo a b := hball hy
    by_cases hyx : y = x₀
    · subst y
      rw [show q x₀ = p.sum 0 by simp [q]]
      change f x₀ = p.sum 0
      dsimp [p]
      change f x₀ = FormalMultilinearSeries.ofScalarsSum
        (fun n ↦ iteratedDeriv n f x₀ / n.factorial) 0
      simp
    · have hu : UniqueDiffOn ℝ (Set.uIcc x₀ y) := uniqueDiffOn_uIcc (Ne.symm hyx)
      have hpartial : ∀ n : ℕ,
          taylorWithinEval f n (Set.uIcc x₀ y) x₀ y =
            p.partialSum (n + 1) (y - x₀) := by
        intro n
        rw [taylor_within_apply]
        simp only [p, FormalMultilinearSeries.partialSum,
          FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [iteratedDerivWithin_eq_iteratedDeriv hu
          (hf.of_le (mod_cast le_top)).contDiffAt
          Set.left_mem_uIcc]
        field_simp
      have htoq : Tendsto
          (fun n : ℕ ↦ taylorWithinEval f n (Set.uIcc x₀ y) x₀ y) atTop (nhds (q y)) := by
        have h := hqtop.tendsto_partialSum
          (y := y - x₀) (by simp [hp_top])
        have hshift := (tendsto_add_atTop_iff_nat 1).mpr h
        convert hshift using 1
        · ext n
          exact hpartial n
        · congr 2
          ring
      have hrem : ∀ n : ℕ,
          ‖f y - taylorWithinEval f n (Set.uIcc x₀ y) x₀ y‖ ≤
            C * |y - x₀| ^ (n + 1) / (n + 1).factorial := by
        intro n
        obtain ⟨z, hz, hzrem⟩ :=
          taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hyx)
            (hf.of_le (mod_cast le_top)).contDiffOn
        have hzI : z ∈ Set.Ioo a b := by
          have hzcc : z ∈ Set.uIcc x₀ y := Set.uIoo_subset_uIcc_self hz
          rcases le_total x₀ y with hxy | hyx
          · rw [Set.uIcc_of_le hxy] at hzcc
            exact ⟨hx₀.1.trans_le hzcc.1, hzcc.2.trans_lt hyI.2⟩
          · rw [Set.uIcc_comm, Set.uIcc_of_le hyx] at hzcc
            exact ⟨hyI.1.trans_le hzcc.1, hzcc.2.trans_lt hx₀.2⟩
        rw [hzrem, norm_div, norm_mul, norm_pow, Real.norm_natCast]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hC (n + 1) z hzI) (by positivity)) (by positivity)
      have hzero : Tendsto
          (fun n : ℕ ↦ C * |y - x₀| ^ (n + 1) / (n + 1).factorial) atTop (nhds 0) := by
        have h := FloorSemiring.tendsto_pow_div_factorial_atTop |y - x₀|
        have hshift := (tendsto_add_atTop_iff_nat 1).mpr h
        convert hshift.const_mul C using 1 <;> ring_nf
      have htof : Tendsto
          (fun n : ℕ ↦ taylorWithinEval f n (Set.uIcc x₀ y) x₀ y) atTop (nhds (f y)) := by
        rw [Metric.tendsto_atTop] at hzero ⊢
        intro ε hε
        obtain ⟨N, hN⟩ := hzero ε hε
        refine ⟨N, fun n hn ↦ ?_⟩
        have hNn := hN n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hNn
        · have hlt := (hrem n).trans_lt hNn
          simpa [Real.dist_eq, abs_sub_comm, Real.norm_eq_abs] using hlt
        · positivity
      exact tendsto_nhds_unique htof htoq
  exact hqtop.analyticAt.congr hfeq.symm

private lemma isOpen_setOf_eventuallyEq (f q : ℝ → ℝ) :
    IsOpen {x | f =ᶠ[nhds x] q} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨u, hu, huo, hxu⟩ := mem_nhds_iff.mp hx
  refine mem_nhds_iff.mpr ⟨u, ?_, huo, hxu⟩
  intro y hy
  exact Filter.mem_of_superset (huo.mem_nhds hy) hu

private lemma eqOn_connectedComponent_of_analyticAt
    {f q : ℝ → ℝ} {G : Set ℝ} {x : ℝ}
    (hG : IsOpen G) (hx : x ∈ G)
    (hbound : ∀ y : ℝ, ∃ C : ℝ, ∀ n : ℕ, ‖iteratedDeriv n f y‖ ≤ C)
    (hgood : ∀ y ∈ G, AnalyticAt ℝ f y)
    (hq : AnalyticOnNhd ℝ q Set.univ) (hfxq : f =ᶠ[nhds x] q) :
    Set.EqOn f q (connectedComponentIn G x) := by
  let E : Set ℝ := {y | f =ᶠ[nhds y] q}
  let W : Set ℝ := G ∩ Eᶜ
  have hE : IsOpen E := isOpen_setOf_eventuallyEq f q
  have hW : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨C, hC⟩ := hbound y
    obtain ⟨r, hr, hfyr⟩ := exists_global_analytic_continuation (hgood y hy.1) hC
    obtain ⟨v, hv, hvo, hyv⟩ := mem_nhds_iff.mp hfyr
    refine mem_nhds_iff.mpr ⟨v ∩ G, ?_, hvo.inter hG, ⟨hyv, hy.1⟩⟩
    intro z hz
    refine ⟨hz.2, ?_⟩
    intro hzE
    have hfzr : f =ᶠ[nhds z] r :=
      Filter.mem_of_superset (hvo.mem_nhds hz.1) hv
    have hqr : q = r := hq.eq_of_eventuallyEq hr (hzE.symm.trans hfzr)
    apply hy.2
    simpa [E, hqr] using hfyr
  have hUsub : connectedComponentIn G x ⊆ G := connectedComponentIn_subset G x
  have hUsubE : connectedComponentIn G x ⊆ E := by
    apply isPreconnected_connectedComponentIn.subset_left_of_subset_union hE hW
    · exact Set.disjoint_left.mpr fun _ hye hyw ↦ hyw.2 hye
    · intro y hy
      by_cases hyE : y ∈ E
      · exact Or.inl hyE
      · exact Or.inr ⟨hUsub hy, hyE⟩
    · exact ⟨x, mem_connectedComponentIn hx, hfxq⟩
  intro y hy
  exact Filter.EventuallyEq.eq_of_nhds (hUsubE hy)

private lemma exists_boundary_mem_compl_connectedComponentIn
    {G : Set ℝ} (hG : IsOpen G) {a b x : ℝ}
    (hx : x ∈ G) (hGI : G ⊆ Set.Ioo a b)
    (hbad : (Set.Ioo a b \ G).Nonempty) :
    ∃ c, c ∈ closure (connectedComponentIn G x) ∧ c ∈ Set.Ioo a b ∧ c ∉ G := by
  let U := connectedComponentIn G x
  by_contra h
  push Not at h
  have hclsubG : closure U ∩ Set.Ioo a b ⊆ G := by
    intro y hy
    exact h y hy.1 hy.2
  have hxU : x ∈ U := mem_connectedComponentIn hx
  have hxI : x ∈ Set.Ioo a b := hGI hx
  have hpre : IsPreconnected (closure U ∩ Set.Ioo a b) :=
    (isPreconnected_connectedComponentIn.closure.ordConnected.inter
      isPreconnected_Ioo.ordConnected).isPreconnected
  have hclsubU : closure U ∩ Set.Ioo a b ⊆ U :=
    hpre.subset_connectedComponentIn ⟨subset_closure hxU, hxI⟩ hclsubG
  have hUeq : U = closure U ∩ Set.Ioo a b := by
    apply Set.Subset.antisymm
    · intro y hy
      exact ⟨subset_closure hy, hGI (connectedComponentIn_subset G x hy)⟩
    · exact hclsubU
  have hUopen : IsOpen U := hG.connectedComponentIn
  let V := Set.Ioo a b ∩ (closure U)ᶜ
  have hVopen : IsOpen V := isOpen_Ioo.inter isClosed_closure.isOpen_compl
  have hIsub : Set.Ioo a b ⊆ U ∪ V := by
    intro y hy
    by_cases hycl : y ∈ closure U
    · exact Or.inl (hclsubU ⟨hycl, hy⟩)
    · exact Or.inr ⟨hy, hycl⟩
  have hIinterU : (Set.Ioo a b ∩ U).Nonempty := ⟨x, hxI, hxU⟩
  have hI_U : Set.Ioo a b ⊆ U :=
    isPreconnected_Ioo.subset_left_of_subset_union hUopen hVopen
      (Set.disjoint_left.mpr fun y hyU hyV ↦ hyV.2 (hUeq.subset hyU).1)
      hIsub hIinterU
  obtain ⟨y, hyI, hyG⟩ := hbad
  exact hyG (connectedComponentIn_subset G x (hI_U hyI))

/-- A real-valued function is the restriction of an entire complex function. -/
def HasEntireExtension (f : ℝ → ℝ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    ∀ x : ℝ, F (x : ℂ) = (f x : ℂ)

/--
Tao's analyticity theorem: if all iterated derivatives of a smooth real
function are pointwise bounded, then the function extends to an entire
function.

This is Theorem 1 in the Spring 2026 DRP write-up.
-/
theorem tao_analyticity {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hbound : ∀ x : ℝ, ∃ C : ℝ, ∀ n : ℕ, ‖iteratedDeriv n f x‖ ≤ C) :
    HasEntireExtension f := by
  let S : ℕ → Set ℝ := fun N ↦
    {x | ∀ k : ℕ, ‖iteratedDeriv k f x‖ ≤ (N : ℝ)}
  have hSclosed : ∀ N, IsClosed (S N) := by
    intro N
    simp only [S, Set.setOf_forall]
    apply isClosed_iInter
    intro k
    exact isClosed_le
      (hf.continuous_iteratedDeriv k (mod_cast le_top)).norm continuous_const
  have hScover : ⋃ N, S N = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨C, hC⟩ := hbound x
    obtain ⟨N : ℕ, hN⟩ := exists_nat_ge C
    exact Set.mem_iUnion.mpr ⟨N, fun k ↦ (hC k).trans hN⟩
  let X : Set ℝ := {x | ¬AnalyticAt ℝ f x}
  have hXclosed : IsClosed X := by
    change IsClosed {x | AnalyticAt ℝ f x}ᶜ
    exact (isOpen_analyticAt ℝ f).isClosed_compl
  have hfanalytic : AnalyticOnNhd ℝ f Set.univ := by
    intro x _
    by_contra hxanalytic
    have hXne : X.Nonempty := ⟨x, hxanalytic⟩
    letI : Nonempty X := hXne.to_subtype
    letI : CompleteSpace X := hXclosed.completeSpace_coe
    let T : ℕ → Set X := fun N ↦ Subtype.val ⁻¹' S N
    have hTclosed : ∀ N, IsClosed (T N) := fun N ↦
      (hSclosed N).preimage continuous_subtype_val
    have hTcover : ⋃ N, T N = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      have hy : (y : ℝ) ∈ ⋃ N, S N := by rw [hScover]; trivial
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨N, hN⟩
    obtain ⟨N, y, hy⟩ := nonempty_interior_of_iUnion_of_closed hTclosed hTcover
    have hyT : T N ∈ nhds y := mem_interior_iff_mem_nhds.mp hy
    obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hyT
    let a : ℝ := (y : ℝ) - ε / 2
    let b : ℝ := (y : ℝ) + ε / 2
    have hab : a < b := by dsimp [a, b]; linarith
    have hyI : (y : ℝ) ∈ Set.Ioo a b := by
      dsimp [a, b]
      constructor <;> linarith
    have hIXne : (Set.Ioo a b ∩ X).Nonempty := ⟨y, hyI, y.property⟩
    have hIXS : Set.Ioo a b ∩ X ⊆ S N := by
      intro z hz
      have hzball : (⟨z, hz.2⟩ : X) ∈ Metric.ball y ε := by
        rw [Metric.mem_ball]
        change dist z (y : ℝ) < ε
        rw [Real.dist_eq]
        rw [abs_lt]
        dsimp [a, b] at hz
        rcases hz.1 with ⟨hzl, hzr⟩
        constructor <;> linarith
      exact hεT hzball
    let G : Set ℝ := Set.Ioo a b \ X
    have hGopen : IsOpen G := IsOpen.sdiff isOpen_Ioo hXclosed
    have hGI : G ⊆ Set.Ioo a b := fun _ hz ↦ hz.1
    have hbad : (Set.Ioo a b \ G).Nonempty := by
      obtain ⟨z, hzI, hzX⟩ := hIXne
      exact ⟨z, hzI, fun hzG ↦ hzG.2 hzX⟩
    let B : ℝ := (N : ℝ) * Real.exp (b - a)
    have hB : ∀ k : ℕ, ∀ z ∈ Set.Ioo a b, ‖iteratedDeriv k f z‖ ≤ B := by
      intro k z hzI
      by_cases hzX : z ∈ X
      · have hzN := hIXS ⟨hzI, hzX⟩ k
        calc
          ‖iteratedDeriv k f z‖ ≤ (N : ℝ) := hzN
          _ ≤ (N : ℝ) * Real.exp (b - a) := by
            nth_rewrite 1 [← mul_one (N : ℝ)]
            exact mul_le_mul_of_nonneg_left
              (Real.one_le_exp (sub_nonneg.mpr hab.le)) (Nat.cast_nonneg N)
      · have hzG : z ∈ G := ⟨hzI, hzX⟩
        obtain ⟨Cz, hCz⟩ := hbound z
        obtain ⟨q, hq, hfqz⟩ :=
          exists_global_analytic_continuation (by simpa [X] using hzX) hCz
        let U := connectedComponentIn G z
        have hUopen : IsOpen U := hGopen.connectedComponentIn
        have hfqU : Set.EqOn f q U :=
          eqOn_connectedComponent_of_analyticAt hGopen hzG hbound
            (fun w hw ↦ by simpa [G, X] using hw.2) hq hfqz
        obtain ⟨c, hccl, hcI, hcG⟩ :=
          exists_boundary_mem_compl_connectedComponentIn hGopen hzG hGI hbad
        have hcX : c ∈ X := by
          show ¬AnalyticAt ℝ f c
          intro hca
          apply hcG
          exact ⟨hcI, by simpa [X] using hca⟩
        have hcN : ∀ m : ℕ, ‖iteratedDeriv m f c‖ ≤ (N : ℝ) :=
          hIXS ⟨hcI, hcX⟩
        have hqSmooth : ContDiff ℝ ∞ q := hq.contDiff
        have hderivEq : ∀ m : ℕ,
            Set.EqOn (iteratedDeriv m f) (iteratedDeriv m q) U := by
          intro m w hw
          have hlocal : f =ᶠ[nhds w] q :=
            Filter.mem_of_superset (hUopen.mem_nhds hw) hfqU
          exact Filter.EventuallyEq.eq_of_nhds (hlocal.iteratedDeriv m)
        have hderivEqCl : ∀ m : ℕ,
            Set.EqOn (iteratedDeriv m f) (iteratedDeriv m q) (closure U) := by
          intro m
          exact (hderivEq m).closure
            (hf.continuous_iteratedDeriv m (mod_cast le_top))
            (hqSmooth.continuous_iteratedDeriv m (mod_cast le_top))
        have hqc : ∀ m : ℕ, ‖iteratedDeriv m q c‖ ≤ (N : ℝ) := by
          intro m
          rw [← hderivEqCl m hccl]
          exact hcN m
        have hzU : z ∈ U := mem_connectedComponentIn hzG
        have hdist : ‖z - c‖ ≤ b - a := by
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [hzI.1, hzI.2, hcI.1, hcI.2]
        rw [hderivEq k hzU]
        calc
          ‖iteratedDeriv k q z‖ ≤ (N : ℝ) * Real.exp ‖z - c‖ :=
            norm_iteratedDeriv_le_mul_exp_sub hq hqc k z
          _ ≤ (N : ℝ) * Real.exp (b - a) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdist) (Nat.cast_nonneg N)
    obtain ⟨w, hwI, hwX⟩ := hIXne
    exact hwX (analyticAt_of_iteratedDeriv_bound_on_Ioo hf hwI
      (fun k z hz ↦ hB k z hz))
  obtain ⟨C, hC⟩ := hbound 0
  let coeffR : ℕ → ℝ := fun n ↦ iteratedDeriv n f 0 / n.factorial
  let pR : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ coeffR
  have hpRtop : pR.radius = ⊤ := by
    simpa [pR, coeffR] using radius_eq_top_of_iteratedDeriv_bound hC
  have hfseries : HasFPowerSeriesOnBall f pR 0 pR.radius := by
    apply AnalyticOn.hasFPowerSeriesOnBall (by rw [hpRtop]; simp)
    exact hfanalytic.analyticOn.mono (Set.subset_univ _)
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
  refine ⟨F, fun z ↦ (hFanalytic z trivial).differentiableAt, ?_⟩
  intro x
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

end DRPSpring2026
