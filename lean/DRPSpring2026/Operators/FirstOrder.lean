import DRPSpring2026.IteratedDerivative.Limit
import Mathlib

/-!
# Nondegenerate first-order linear differential operators

This file isolates the change-of-variables calculation from the local Tao
theorem.  `FirstOrderChangeOfVariables` records exactly the coordinate and
integrating-factor identities used in the DRP write-up; the convergence
argument below is independent of their eventual construction from integrals.
-/

open Filter
open scoped ContDiff

namespace DRPSpring2026

/-- The first-order operator `f ↦ a f' + b f`. -/
noncomputable def firstOrderOperator (a b f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ a x * deriv f x + b x * f x

/--
The data and identities supplied by the coordinate
`φ(x) = ∫ t in 0..x, (a t)⁻¹` and its integrating factor.  Keeping this as a
structure makes the operator argument reusable and gives the construction of
the integral coordinate a sharply delimited API.
-/
structure FirstOrderChangeOfVariables (a b : ℝ → ℝ) where
  coefficient_ne_zero : ∀ x, a x ≠ 0
  interval : Set ℝ
  isOpen_interval : IsOpen interval
  isPreconnected_interval : IsPreconnected interval
  interval_nonempty : interval.Nonempty
  coordinate : ℝ → ℝ
  inverse : ℝ → ℝ
  coordinate_mem : ∀ x, coordinate x ∈ interval
  inverse_coordinate : ∀ x, inverse (coordinate x) = x
  weight : ℝ → ℝ
  weight_ne_zero : ∀ y ∈ interval, weight y ≠ 0
  transform_contDiffOn : ∀ {h : ℝ → ℝ}, ContDiff ℝ ∞ h →
    ContDiffOn ℝ ∞ (fun y ↦ weight y * h (inverse y)) interval
  iteratedDeriv_transform : ∀ (h : ℝ → ℝ) (n : ℕ),
    Set.EqOn
      (iteratedDeriv n (fun y ↦ weight y * h (inverse y)))
      (fun y ↦ weight y * ((firstOrderOperator a b)^[n] h) (inverse y)) interval
  pullback_contDiff : ∀ {H : ℝ → ℝ}, ContDiffOn ℝ ∞ H interval →
    ContDiff ℝ ∞ (fun x ↦ H (coordinate x) / weight (coordinate x))

namespace FirstOrderChangeOfVariables

/-- The weighted pushforward used to conjugate the operator to `deriv`. -/
def transform {a b : ℝ → ℝ} (cv : FirstOrderChangeOfVariables a b)
    (h : ℝ → ℝ) : ℝ → ℝ :=
  fun y ↦ cv.weight y * h (cv.inverse y)

/-- Pull a function on the coordinate interval back to the real line. -/
noncomputable def pullback {a b : ℝ → ℝ} (cv : FirstOrderChangeOfVariables a b)
    (H : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ H (cv.coordinate x) / cv.weight (cv.coordinate x)

lemma pullback_transform {a b h : ℝ → ℝ} (cv : FirstOrderChangeOfVariables a b) :
    cv.pullback (cv.transform h) = h := by
  funext x
  simp [pullback, transform, cv.inverse_coordinate x,
    cv.weight_ne_zero _ (cv.coordinate_mem x)]

end FirstOrderChangeOfVariables

/--
The convergence theorem for a general first-order operator, once the
document's integral coordinate and integrating factor have been constructed.
The proof is the conjugation argument from the write-up followed by
`iteratedDeriv_limit_on`.
-/
theorem firstOrderOperator_iterate_limit_of_changeOfVariables
    {a b f g : ℝ → ℝ} (cv : FirstOrderChangeOfVariables a b)
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ x : ℝ,
      Tendsto (fun n : ℕ ↦ ((firstOrderOperator a b)^[n] f) x)
        atTop (nhds (g x))) :
    ContDiff ℝ ∞ g ∧ firstOrderOperator a b g = g := by
  let F : ℝ → ℝ := cv.transform f
  let G : ℝ → ℝ := cv.transform g
  have hFsmooth : ContDiffOn ℝ ∞ F cv.interval := by
    change ContDiffOn ℝ ∞ (fun y ↦ cv.weight y * f (cv.inverse y)) cv.interval
    exact cv.transform_contDiffOn hf
  have hFlim : ∀ y ∈ cv.interval,
      Tendsto (fun n : ℕ ↦ iteratedDeriv n F y) atTop (nhds (G y)) := by
    intro y hy
    have hweighted : Tendsto
        (fun n : ℕ ↦ cv.weight y * ((firstOrderOperator a b)^[n] f) (cv.inverse y))
        atTop (nhds (cv.weight y * g (cv.inverse y))) :=
      tendsto_const_nhds.mul (hlim (cv.inverse y))
    exact hweighted.congr'
      (Filter.Eventually.of_forall fun n ↦ by
        change cv.weight y * ((firstOrderOperator a b)^[n] f) (cv.inverse y) =
          iteratedDeriv n (fun y ↦ cv.weight y * f (cv.inverse y)) y
        exact (cv.iteratedDeriv_transform f n hy).symm)
  obtain ⟨_, hGsmooth, hGfixed⟩ :=
    iteratedDeriv_limit_on cv.isOpen_interval cv.isPreconnected_interval
      cv.interval_nonempty hFsmooth hFlim
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [← cv.pullback_transform (h := g)]
    exact cv.pullback_contDiff hGsmooth
  refine ⟨hgSmooth, funext fun x ↦ ?_⟩
  let y := cv.coordinate x
  have hy : y ∈ cv.interval := cv.coordinate_mem x
  have hone := cv.iteratedDeriv_transform g 1 hy
  have htransformEq : cv.transform (firstOrderOperator a b g) y = cv.transform g y := by
    calc
      cv.transform (firstOrderOperator a b g) y = iteratedDeriv 1 G y := by
        change cv.weight y * firstOrderOperator a b g (cv.inverse y) =
          iteratedDeriv 1 (fun y ↦ cv.weight y * g (cv.inverse y)) y
        exact hone.symm
      _ = G y := by simpa [iteratedDeriv_one] using hGfixed hy
      _ = cv.transform g y := rfl
  change a x * deriv g x + b x * g x = g x
  dsimp [FirstOrderChangeOfVariables.transform, y] at htransformEq
  rw [cv.inverse_coordinate x] at htransformEq
  exact mul_left_cancel₀ (cv.weight_ne_zero _ (cv.coordinate_mem x)) htransformEq

end DRPSpring2026
