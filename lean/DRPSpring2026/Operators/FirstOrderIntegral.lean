import DRPSpring2026.Operators.FirstOrder
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral coordinates for nondegenerate first-order operators

This file constructs the coordinate and integrating factor used in the DRP
write-up from the hypotheses that the coefficients are smooth and the leading
coefficient is nowhere zero.  It then instantiates the abstract interface in
`DRPSpring2026.Operators.FirstOrder`.
-/

open Filter Set Topology
open scoped ContDiff

namespace DRPSpring2026

namespace FirstOrder

/-- The primitive of `q` based at the origin. -/
noncomputable def integralPrimitive (q : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t in 0..x, q t

lemma hasDerivAt_integralPrimitive {q : ℝ → ℝ} (hq : Continuous q) (x : ℝ) :
    HasDerivAt (integralPrimitive q) (q x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (hq.intervalIntegrable _ _) hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt

lemma deriv_integralPrimitive {q : ℝ → ℝ} (hq : Continuous q) :
    deriv (integralPrimitive q) = q := by
  funext x
  exact (hasDerivAt_integralPrimitive hq x).deriv

lemma contDiff_integralPrimitive {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (integralPrimitive q) := by
  apply (contDiff_infty_iff_deriv).2
  refine ⟨fun x ↦ (hasDerivAt_integralPrimitive hq.continuous x).differentiableAt, ?_⟩
  simpa [deriv_integralPrimitive hq.continuous] using hq

/-- The coordinate `Φ(x) = ∫₀ˣ 1/a(t) dt` from the write-up. -/
noncomputable def firstOrderCoordinate (a : ℝ → ℝ) : ℝ → ℝ :=
  integralPrimitive fun x ↦ (a x)⁻¹

lemma contDiff_firstOrderCoordinate {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (ha₀ : ∀ x, a x ≠ 0) : ContDiff ℝ ∞ (firstOrderCoordinate a) := by
  exact contDiff_integralPrimitive (ha.inv ha₀)

lemma hasDerivAt_firstOrderCoordinate {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (ha₀ : ∀ x, a x ≠ 0) (x : ℝ) :
    HasDerivAt (firstOrderCoordinate a) (a x)⁻¹ x := by
  exact hasDerivAt_integralPrimitive (ha.inv ha₀).continuous x

lemma deriv_firstOrderCoordinate {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (ha₀ : ∀ x, a x ≠ 0) (x : ℝ) :
    deriv (firstOrderCoordinate a) x = (a x)⁻¹ :=
  (hasDerivAt_firstOrderCoordinate ha ha₀ x).deriv

lemma firstOrderCoordinate_injective {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (ha₀ : ∀ x, a x ≠ 0) : Function.Injective (firstOrderCoordinate a) := by
  intro x y hxy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · obtain ⟨c, _, hc⟩ := exists_deriv_eq_zero hlt
      (contDiff_firstOrderCoordinate ha ha₀).continuous.continuousOn hxy
    rw [deriv_firstOrderCoordinate ha ha₀ c] at hc
    exact False.elim ((inv_ne_zero (ha₀ c)) hc)
  · exact heq
  · obtain ⟨c, _, hc⟩ := exists_deriv_eq_zero hgt
      (contDiff_firstOrderCoordinate ha ha₀).continuous.continuousOn hxy.symm
    rw [deriv_firstOrderCoordinate ha ha₀ c] at hc
    exact False.elim ((inv_ne_zero (ha₀ c)) hc)

lemma firstOrderCoordinate_isOpenEmbedding {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) :
    IsOpenEmbedding (firstOrderCoordinate a) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (contDiff_firstOrderCoordinate ha ha₀).continuous
    (firstOrderCoordinate_injective ha ha₀)
    (isOpenMap_of_hasStrictDerivAt
      (fun x ↦ (contDiff_firstOrderCoordinate ha ha₀).contDiffAt.hasStrictDerivAt'
        (hasDerivAt_firstOrderCoordinate ha ha₀ x) (by simp))
      (fun x ↦ inv_ne_zero (ha₀ x)))

/-- The integral coordinate is a local homeomorphism when `a` is nowhere zero. -/
lemma firstOrderCoordinate_isLocalHomeomorph {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) :
    IsLocalHomeomorph (firstOrderCoordinate a) :=
  (firstOrderCoordinate_isOpenEmbedding ha ha₀).isLocalHomeomorph

/-- The coordinate as an open partial homeomorphism from `ℝ` onto its range. -/
noncomputable def firstOrderCoordinatePartialHomeomorph {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) : OpenPartialHomeomorph ℝ ℝ :=
  (firstOrderCoordinate_isOpenEmbedding ha ha₀).toOpenPartialHomeomorph
    (firstOrderCoordinate a)

/-- The total inverse supplied by the coordinate's open partial
homeomorphism.  Its values outside the coordinate range are irrelevant. -/
noncomputable def firstOrderCoordinateInverse {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) : ℝ → ℝ :=
  (firstOrderCoordinatePartialHomeomorph ha ha₀).symm

lemma firstOrderCoordinateInverse_apply {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) (x : ℝ) :
    firstOrderCoordinateInverse ha ha₀ (firstOrderCoordinate a x) = x := by
  exact (firstOrderCoordinate_isOpenEmbedding ha ha₀).toOpenPartialHomeomorph_left_inv

/-- On the coordinate range, applying the coordinate after its chosen inverse is the identity. -/
lemma firstOrderCoordinate_apply_inverse {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0)
    {y : ℝ} (hy : y ∈ Set.range (firstOrderCoordinate a)) :
    firstOrderCoordinate a (firstOrderCoordinateInverse ha ha₀ y) = y := by
  exact IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
    (f := firstOrderCoordinate a) (firstOrderCoordinate_isOpenEmbedding ha ha₀) hy

lemma contDiffOn_firstOrderCoordinateInverse {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) :
    ContDiffOn ℝ ∞ (firstOrderCoordinateInverse ha ha₀)
      (Set.range (firstOrderCoordinate a)) := by
  intro y hy
  let e := firstOrderCoordinatePartialHomeomorph ha ha₀
  have hyt : y ∈ e.target := by
    simpa [e, firstOrderCoordinatePartialHomeomorph] using hy
  apply ContDiffAt.contDiffWithinAt
  exact e.contDiffAt_symm_deriv (inv_ne_zero (ha₀ (e.symm y))) hyt
    (by simpa [e, firstOrderCoordinatePartialHomeomorph] using
      hasDerivAt_firstOrderCoordinate ha ha₀ (e.symm y))
    (by simpa [e, firstOrderCoordinatePartialHomeomorph] using
      (contDiff_firstOrderCoordinate ha ha₀).contDiffAt)

lemma hasDerivAt_firstOrderCoordinateInverse {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0)
    {y : ℝ} (hy : y ∈ Set.range (firstOrderCoordinate a)) :
    HasDerivAt (firstOrderCoordinateInverse ha ha₀)
      (a (firstOrderCoordinateInverse ha ha₀ y)) y := by
  let e := firstOrderCoordinatePartialHomeomorph ha ha₀
  have hyt : y ∈ e.target := by
    simpa [e, firstOrderCoordinatePartialHomeomorph] using hy
  have h := e.hasDerivAt_symm hyt (inv_ne_zero (ha₀ (e.symm y)))
    (by simpa [e, firstOrderCoordinatePartialHomeomorph] using
      hasDerivAt_firstOrderCoordinate ha ha₀ (e.symm y))
  simpa [firstOrderCoordinateInverse, e] using h

/-- The integrating factor pulled back to the original coordinate. -/
noncomputable def firstOrderMultiplier (a b : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ Real.exp (integralPrimitive (fun t ↦ b t / a t) x)

lemma contDiff_firstOrderMultiplier {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0) :
    ContDiff ℝ ∞ (firstOrderMultiplier a b) := by
  exact Real.contDiff_exp.comp (contDiff_integralPrimitive (hb.div ha ha₀))

lemma hasDerivAt_firstOrderMultiplier {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (x : ℝ) : HasDerivAt (firstOrderMultiplier a b)
      (firstOrderMultiplier a b x * (b x / a x)) x := by
  change HasDerivAt (fun x ↦ Real.exp (integralPrimitive (fun t ↦ b t / a t) x))
    (Real.exp (integralPrimitive (fun t ↦ b t / a t) x) * (b x / a x)) x
  exact (Real.hasDerivAt_exp (integralPrimitive (fun t ↦ b t / a t) x)).comp x
    (hasDerivAt_integralPrimitive (hb.div ha ha₀).continuous x)

/-- The integrating factor in the coordinate variable.  This is the
write-up's `W`, expressed after changing variables in its defining integral. -/
noncomputable def firstOrderWeight {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) : ℝ → ℝ :=
  fun y ↦ firstOrderMultiplier a b (firstOrderCoordinateInverse ha ha₀ y)

lemma firstOrderWeight_ne_zero {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) (y : ℝ) :
    firstOrderWeight (b := b) ha ha₀ y ≠ 0 := by
  exact Real.exp_ne_zero _

lemma contDiffOn_firstOrderWeight {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0) :
    ContDiffOn ℝ ∞ (firstOrderWeight (b := b) ha ha₀)
      (Set.range (firstOrderCoordinate a)) := by
  exact (contDiff_firstOrderMultiplier ha hb ha₀).comp_contDiffOn
    (contDiffOn_firstOrderCoordinateInverse ha ha₀)

lemma hasDerivAt_firstOrderWeight {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    {y : ℝ} (hy : y ∈ Set.range (firstOrderCoordinate a)) :
    HasDerivAt (firstOrderWeight (b := b) ha ha₀)
      (firstOrderWeight (b := b) ha ha₀ y *
        b (firstOrderCoordinateInverse ha ha₀ y)) y := by
  let x := firstOrderCoordinateInverse ha ha₀ y
  have hcomp := (hasDerivAt_firstOrderMultiplier ha hb ha₀ x).comp y
    (hasDerivAt_firstOrderCoordinateInverse ha ha₀ hy)
  dsimp [x] at hcomp
  have hcompfun : HasDerivAt
      (fun z ↦ firstOrderMultiplier a b (firstOrderCoordinateInverse ha ha₀ z))
      (firstOrderMultiplier a b (firstOrderCoordinateInverse ha ha₀ y) *
        (b (firstOrderCoordinateInverse ha ha₀ y) /
          a (firstOrderCoordinateInverse ha ha₀ y)) *
        a (firstOrderCoordinateInverse ha ha₀ y)) y := by
    change HasDerivAt (firstOrderMultiplier a b ∘ firstOrderCoordinateInverse ha ha₀) _ y
    exact hcomp
  apply hcompfun.congr_deriv
  simp only [firstOrderWeight]
  field_simp [ha₀]

lemma contDiff_firstOrderOperator {a b h : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (firstOrderOperator a b h) := by
  exact ha.mul (contDiff_infty_iff_deriv.mp hh).2 |>.add (hb.mul hh)

private lemma contDiff_firstOrderOperator_iterate {a b h : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h) :
    ∀ n : ℕ, ContDiff ℝ ∞ ((firstOrderOperator a b)^[n] h)
  | 0 => by simpa using hh
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact contDiff_firstOrderOperator ha hb (contDiff_firstOrderOperator_iterate ha hb hh n)

lemma deriv_firstOrderTransform {a b h : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (hh : ContDiff ℝ ∞ h) {y : ℝ} (hy : y ∈ Set.range (firstOrderCoordinate a)) :
    deriv (fun z ↦ firstOrderWeight (b := b) ha ha₀ z *
      h (firstOrderCoordinateInverse ha ha₀ z)) y =
      firstOrderWeight (b := b) ha ha₀ y *
        firstOrderOperator a b h (firstOrderCoordinateInverse ha ha₀ y) := by
  let x := firstOrderCoordinateInverse ha ha₀ y
  have hhinv : HasDerivAt (fun z ↦ h (firstOrderCoordinateInverse ha ha₀ z))
      (deriv h x * a x) y :=
    (hh.differentiable (by simp)).differentiableAt.hasDerivAt.comp y
      (hasDerivAt_firstOrderCoordinateInverse ha ha₀ hy)
  have hprod := (hasDerivAt_firstOrderWeight ha hb ha₀ hy).mul hhinv
  change deriv (firstOrderWeight (b := b) ha ha₀ *
    fun z ↦ h (firstOrderCoordinateInverse ha ha₀ z)) y = _
  rw [hprod.deriv]
  dsimp [firstOrderOperator, x]
  ring

lemma iteratedDeriv_firstOrderTransform {a b h : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (hh : ContDiff ℝ ∞ h) (n : ℕ) :
    Set.EqOn
      (iteratedDeriv n (fun y ↦ firstOrderWeight (b := b) ha ha₀ y *
        h (firstOrderCoordinateInverse ha ha₀ y)))
      (fun y ↦ firstOrderWeight (b := b) ha ha₀ y *
        ((firstOrderOperator a b)^[n] h) (firstOrderCoordinateInverse ha ha₀ y))
      (Set.range (firstOrderCoordinate a)) := by
  induction n with
  | zero => intro y hy; rfl
  | succ n ih =>
      intro y hy
      rw [iteratedDeriv_succ, Function.iterate_succ_apply']
      have heq : iteratedDeriv n (fun y ↦ firstOrderWeight (b := b) ha ha₀ y *
          h (firstOrderCoordinateInverse ha ha₀ y)) =ᶠ[nhds y]
          (fun y ↦ firstOrderWeight (b := b) ha ha₀ y *
            ((firstOrderOperator a b)^[n] h) (firstOrderCoordinateInverse ha ha₀ y)) :=
        Filter.mem_of_superset
          ((firstOrderCoordinate_isOpenEmbedding ha ha₀).isOpen_range.mem_nhds hy) ih
      rw [heq.deriv_eq]
      exact deriv_firstOrderTransform ha hb ha₀
        (contDiff_firstOrderOperator_iterate ha hb hh n) hy

/-- The concrete change-of-variables data constructed from the integral
coordinate and integrating factor. -/
noncomputable def integralFirstOrderChangeOfVariables {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0) :
    FirstOrderChangeOfVariables a b where
  interval := Set.range (firstOrderCoordinate a)
  isOpen_interval := (firstOrderCoordinate_isOpenEmbedding ha ha₀).isOpen_range
  isPreconnected_interval := isPreconnected_range
    (contDiff_firstOrderCoordinate ha ha₀).continuous
  interval_nonempty := Set.range_nonempty _
  coordinate := firstOrderCoordinate a
  inverse := firstOrderCoordinateInverse ha ha₀
  coordinate_mem := fun x ↦ Set.mem_range_self x
  inverse_coordinate := firstOrderCoordinateInverse_apply ha ha₀
  weight := firstOrderWeight (b := b) ha ha₀
  weight_ne_zero := fun y _ ↦ firstOrderWeight_ne_zero ha ha₀ y
  transform_contDiffOn := fun {h} hh ↦
    (contDiffOn_firstOrderWeight ha hb ha₀).mul
      (hh.comp_contDiffOn (contDiffOn_firstOrderCoordinateInverse ha ha₀))
  iteratedDeriv_transform := fun h hh n ↦
    iteratedDeriv_firstOrderTransform ha hb ha₀ hh n
  pullback_contDiff := fun {H} hH ↦ by
    have hcomp : ContDiff ℝ ∞ (fun x ↦ H (firstOrderCoordinate a x)) := by
      simpa only [Function.comp_def] using
        hH.comp_contDiff (contDiff_firstOrderCoordinate ha ha₀) (fun x ↦ Set.mem_range_self x)
    have hweight : ContDiff ℝ ∞
        (fun x ↦ firstOrderWeight (b := b) ha ha₀ (firstOrderCoordinate a x)) := by
      simpa only [Function.comp_def] using
        (contDiffOn_firstOrderWeight ha hb ha₀).comp_contDiff
          (contDiff_firstOrderCoordinate ha ha₀) (fun x ↦ Set.mem_range_self x)
    exact hcomp.div hweight (fun x ↦ firstOrderWeight_ne_zero ha ha₀ _)

end FirstOrder

/-- The unconditional convergence theorem for a smooth nondegenerate
first-order operator. -/
theorem firstOrderOperator_iterate_limit {a b f g : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ ((firstOrderOperator a b)^[n] f) x)
        atTop (nhds (g x))) :
    ContDiff ℝ ∞ g ∧ firstOrderOperator a b g = g :=
  firstOrderOperator_iterate_limit_of_changeOfVariables
    (FirstOrder.integralFirstOrderChangeOfVariables ha hb ha₀) hf hlim

namespace FirstOrder

/-- The normalized positive solution of `a g' + b g = g`. -/
noncomputable def firstOrderSolutionFactor (a b : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ Real.exp (integralPrimitive (fun t ↦ (1 - b t) / a t) x)

lemma contDiff_firstOrderSolutionFactor {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0) :
    ContDiff ℝ ∞ (firstOrderSolutionFactor a b) := by
  exact Real.contDiff_exp.comp
    (contDiff_integralPrimitive ((contDiff_const.sub hb).div ha ha₀))

lemma hasDerivAt_firstOrderSolutionFactor {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (x : ℝ) : HasDerivAt (firstOrderSolutionFactor a b)
      (firstOrderSolutionFactor a b x * ((1 - b x) / a x)) x := by
  change HasDerivAt
    (fun x ↦ Real.exp (integralPrimitive (fun t ↦ (1 - b t) / a t) x))
    (Real.exp (integralPrimitive (fun t ↦ (1 - b t) / a t) x) *
      ((1 - b x) / a x)) x
  exact (Real.hasDerivAt_exp _).comp x
    (hasDerivAt_integralPrimitive ((contDiff_const.sub hb).div ha ha₀).continuous x)

lemma firstOrderSolutionFactor_ne_zero (a b : ℝ → ℝ) (x : ℝ) :
    firstOrderSolutionFactor a b x ≠ 0 :=
  Real.exp_ne_zero _

lemma firstOrderOperator_const_mul_solutionFactor {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (C : ℝ) :
    firstOrderOperator a b (fun x ↦ C * firstOrderSolutionFactor a b x) =
      fun x ↦ C * firstOrderSolutionFactor a b x := by
  funext x
  simp only [firstOrderOperator]
  rw [((hasDerivAt_firstOrderSolutionFactor ha hb ha₀ x).const_mul C).deriv]
  field_simp [ha₀]
  ring

/-- Smooth fixed points of a nondegenerate first-order operator are exactly
the scalar multiples of the usual exponential solution. -/
theorem firstOrderOperator_fixed_point_classification {a b g : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (hg : ContDiff ℝ ∞ g) (hfixed : firstOrderOperator a b g = g) :
    ∃ C : ℝ, g = fun x ↦ C * firstOrderSolutionFactor a b x := by
  have hgderiv : ∀ x, deriv g x = ((1 - b x) / a x) * g x := by
    intro x
    have hx := congrFun hfixed x
    dsimp [firstOrderOperator] at hx
    field_simp [ha₀]
    nlinarith [hx]
  let v : ℝ → ℝ := fun x ↦ g x / firstOrderSolutionFactor a b x
  have hvdiff : Differentiable ℝ v := by
    exact (hg.differentiable (by simp)).div
      ((contDiff_firstOrderSolutionFactor ha hb ha₀).differentiable (by simp))
      (firstOrderSolutionFactor_ne_zero a b)
  have hvderiv : ∀ x, deriv v x = 0 := by
    intro x
    have hquot := (hg.differentiable (by simp) x).hasDerivAt.div
      (hasDerivAt_firstOrderSolutionFactor ha hb ha₀ x)
      (firstOrderSolutionFactor_ne_zero a b x)
    change deriv (g / firstOrderSolutionFactor a b) x = 0
    rw [hquot.deriv, hgderiv]
    ring
  refine ⟨g 0, funext fun x ↦ ?_⟩
  have hvconst := is_const_of_deriv_eq_zero hvdiff hvderiv x 0
  dsimp [v] at hvconst
  have hfactor0 : firstOrderSolutionFactor a b 0 = 1 := by
    simp [firstOrderSolutionFactor, integralPrimitive]
  rw [hfactor0, div_one] at hvconst
  exact (div_eq_iff (firstOrderSolutionFactor_ne_zero a b x)).mp hvconst

end FirstOrder

/-- Smooth fixed points of a nondegenerate first-order operator are exactly
the scalar multiples of the usual exponential solution. -/
theorem firstOrderOperator_fixed_point_classification {a b g : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (hg : ContDiff ℝ ∞ g) (hfixed : firstOrderOperator a b g = g) :
    ∃ C : ℝ, g = fun x ↦ C * FirstOrder.firstOrderSolutionFactor a b x :=
  FirstOrder.firstOrderOperator_fixed_point_classification ha hb ha₀ hg hfixed

/-- Classification of all pointwise limits for a smooth nondegenerate
first-order operator. -/
theorem firstOrderOperator_iterate_limit_classification {a b f g : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (ha₀ : ∀ x, a x ≠ 0)
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ ((firstOrderOperator a b)^[n] f) x)
        atTop (nhds (g x))) :
    ∃ C : ℝ, g = fun x ↦ C * FirstOrder.firstOrderSolutionFactor a b x := by
  obtain ⟨hg, hfixed⟩ := firstOrderOperator_iterate_limit ha hb ha₀ hf hlim
  exact firstOrderOperator_fixed_point_classification ha hb ha₀ hg hfixed

/-- The document's case `L f = a f'`: every pointwise iterate limit is a
multiple of `exp (∫₀ˣ 1/a)`. -/
theorem weightedDerivative_iterate_limit_classification {a f g : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ ((firstOrderOperator a 0)^[n] f) x)
        atTop (nhds (g x))) :
    ∃ C : ℝ, g = fun x ↦
      C * Real.exp (FirstOrder.integralPrimitive (fun t ↦ (a t)⁻¹) x) := by
  obtain ⟨C, hC⟩ := firstOrderOperator_iterate_limit_classification
    ha contDiff_const ha₀ hf hlim
  refine ⟨C, hC.trans ?_⟩
  funext x
  change C * Real.exp (FirstOrder.integralPrimitive (fun t ↦ (1 - 0) / a t) x) =
    C * Real.exp (FirstOrder.integralPrimitive (fun t ↦ (a t)⁻¹) x)
  simp

/-- The document's case `L f = a f' + f`: every pointwise iterate limit is
constant. -/
theorem weightedDerivativeAddSelf_iterate_limit_classification {a f g : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (ha₀ : ∀ x, a x ≠ 0) (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ ((firstOrderOperator a 1)^[n] f) x)
        atTop (nhds (g x))) :
    ∃ C : ℝ, g = fun _ ↦ C := by
  obtain ⟨C, hC⟩ := firstOrderOperator_iterate_limit_classification
    ha contDiff_const ha₀ hf hlim
  refine ⟨C, hC.trans ?_⟩
  funext x
  change C * Real.exp (FirstOrder.integralPrimitive (fun t ↦ (1 - 1) / a t) x) = C
  simp [FirstOrder.integralPrimitive]

end DRPSpring2026
