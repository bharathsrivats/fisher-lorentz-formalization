/-
# The logit coordinate and natural gradient

Formalises B. G. Srivats, "The Lorentz Factor in Binary Classification:
Natural Gradient Descent and the Fisher-Lorentz Identity", Zenodo preprint.

In the logit coordinate the Fisher information is the *reciprocal* of the
visibility-coordinate one, up to a factor of four.
-/
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic
import FisherLorentz.Basic

namespace FisherLorentz

open Real Set

/-- The sigmoid link: `V = tanh(f/2)` relates the logit `f` to the
visibility `V`. -/
noncomputable def logitToVisibility (f : ℝ) : ℝ := Real.tanh (f / 2)

/-- The logit link lands in the open interval. -/
theorem logitToVisibility_mem (f : ℝ) : logitToVisibility f ∈ Ioo (-1:ℝ) 1 :=
  ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

/-- Fisher information in the logit coordinate: `I(f) = p(1-p)`. -/
noncomputable def fisherLogit (V : ℝ) : ℝ := pPlus V * pMinus V

/-- **The reciprocal relation.** `I_logit = (1 − V²)/4 = 1/(4 γ²(V))`.
The logit coordinate carries the inverse of the visibility-coordinate
Fisher information, so a natural-gradient step is damped by exactly the
factor that the visibility-coordinate Fisher information is amplified by. -/
theorem fisherLogit_eq_inv {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    fisherLogit V = 1 / (4 * gammaSq V) := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  simp only [fisherLogit, pPlus, pMinus, gammaSq]
  field_simp
  ring

/-- **The step-size ratio.** The Euclidean and natural-gradient steps in the
visibility coordinate differ by exactly `γ²(V)`. -/
theorem step_ratio {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    fisherInfo V * (4 * fisherLogit V) = 1 := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  rw [fisherInfo_eq_gammaSq h, fisherLogit_eq_inv h]
  simp only [gammaSq]
  field_simp

end FisherLorentz
