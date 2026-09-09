/-
# Speed limits, Cramér-Rao, and the Planckian visibility

Formalises:
* B. G. Srivats, "Observer Limits and Thermodynamics of Binary Quantum
  Measurement" (Pramana, under review), Theorem 3 and the Planckian
  proposition.
* B. G. Srivats, "Fisher-Information Speed Limits" (Fluctuation and Noise
  Letters, under review), Theorem 1 and its corollaries.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import FisherLorentz.Basic

namespace FisherLorentz

open Real Set

/-- **The reciprocal identity.** `γ²(V)·(1 − V²) = 1`.
Every energy-precision statement in the corpus rests on this. -/
theorem gammaSq_mul_one_sub_sq {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    gammaSq V * (1 - V ^ 2) = 1 := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  simp only [gammaSq]
  field_simp

/-- **Cramér-Rao in the visibility coordinate.**
The variance floor for `N` independent binary observations is
`1/(N I(V)) = (1 − V²)/N`. -/
theorem cramerRao_floor {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) {N : ℝ} (hN : 0 < N) :
    1 / (N * fisherInfo V) = (1 - V ^ 2) / N := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  rw [fisherInfo_eq_gammaSq h]
  simp only [gammaSq]
  field_simp

/-- The Planckian visibility `V_P = √(1 − ln 2)`. -/
noncomputable def planckianVisibility : ℝ := Real.sqrt (1 - Real.log 2)

lemma log_two_lt_one : Real.log 2 < 1 := by
  linarith [Real.log_two_lt_d9]

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `V_P` lies in the open interval `(0,1)`. -/
theorem planckianVisibility_mem : planckianVisibility ∈ Ioo (0:ℝ) 1 := by
  have h1 : (0:ℝ) < 1 - Real.log 2 := by linarith [log_two_lt_one]
  constructor
  · exact Real.sqrt_pos.mpr h1
  · rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt h1.le (by linarith [log_two_pos])

/-- `V_P² = 1 − ln 2`. -/
@[simp] theorem planckianVisibility_sq :
    planckianVisibility ^ 2 = 1 - Real.log 2 := by
  have h1 : (0:ℝ) ≤ 1 - Real.log 2 := by linarith [log_two_lt_one]
  simp only [planckianVisibility]
  exact Real.sq_sqrt h1

/-- **The Planckian operating point.** `γ²(V_P) = 1 / ln 2 = log₂ e`.
At this visibility the measurement operates at the Landauer efficiency point. -/
theorem gammaSq_planckian : gammaSq planckianVisibility = 1 / Real.log 2 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simp only [gammaSq, planckianVisibility_sq]
  norm_num

/-- The energy-precision floor at the Planckian point is `kT (ln 2)²`,
i.e. `(ln 2)²` in units of `kT`. -/
theorem planckian_floor :
    (Real.log 2) * (1 - planckianVisibility ^ 2) = (Real.log 2) ^ 2 := by
  rw [planckianVisibility_sq]; ring

/-- **Energy-precision relation, geometric content.**
Whatever the constant `c = kT ln 2`, the bound `E·Var ≥ c (1 − V²)` is the
same statement as `E·Var ≥ c / γ²(V)`. -/
theorem energyPrecision_forms {V c : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    c * (1 - V ^ 2) = c / gammaSq V := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  simp only [gammaSq]
  field_simp

end FisherLorentz
