/-
# Quantum computation: Grover, batteries, and the Zeno threshold

Formalises B. G. Srivats, "The Squared Lorentz Factor in Quantum
Computation: Grover Search, Quantum Batteries, and the Zeno Effect",
Next Research 10, 101888 (2026), doi:10.1016/j.nexres.2026.101888.
-/
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic
import FisherLorentz.Basic
import FisherLorentz.Conformal
import FisherLorentz.Gudermannian

namespace FisherLorentz

open Real Set

/-! ## Grover: the Fisher cost is the Beltrami-Klein distance -/

/-- **`artanh` is an antiderivative of the Fisher information.**
`d/dV artanh V = γ²(V) = I(V)`. Hence the accumulated Fisher cost
`∫₀^{V_f} I(V) dV` equals the Beltrami-Klein distance `artanh V_f`,
which is the paper's `C_Fisher`. -/
theorem hasDerivAt_artanh_eq_fisherInfo {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt Real.artanh (fisherInfo V) V := by
  rw [fisherInfo_eq_gammaSq h, gammaSq]
  exact hasDerivAt_artanh h

/-- The Grover final visibility for an `N`-item search, `V_f = √(1 − 1/N)`. -/
noncomputable def groverVisibility (N : ℝ) : ℝ := Real.sqrt (1 - 1/N)

/-- For `N ≥ 1` the Grover visibility lies in `[0,1)`. -/
theorem groverVisibility_mem {N : ℝ} (hN : 1 < N) :
    groverVisibility N ∈ Ico (0:ℝ) 1 := by
  have h1 : (0:ℝ) < 1/N := by positivity
  have h2 : 1/N < 1 := by rw [div_lt_one (by linarith)]; linarith
  constructor
  · exact Real.sqrt_nonneg _
  · rw [groverVisibility, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

/-- `V_f² = 1 − 1/N`, so `γ²(V_f) = N`: the Grover Fisher information at the
end of the search is exactly the search space size. -/
theorem gammaSq_groverVisibility {N : ℝ} (hN : 1 < N) :
    gammaSq (groverVisibility N) = N := by
  have hN0 : N ≠ 0 := by linarith
  have h1 : (0:ℝ) ≤ 1 - 1/N := by
    have : 1/N ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hsq : groverVisibility N ^ 2 = 1 - 1/N := by
    simp only [groverVisibility]; exact Real.sq_sqrt h1
  have hone : 1 - groverVisibility N ^ 2 = 1/N := by rw [hsq]; ring
  simp only [gammaSq, hone]
  rw [one_div_one_div]

/-! ## Quantum batteries: the geometric distance ratio -/

/-- The geometric distance ratio of the battery section:
`R(r) = arcsin r / (2 artanh r) = gd(η)/(2η)`. -/
noncomputable def batteryRatio (r : ℝ) : ℝ :=
  Real.arcsin r / (2 * Real.artanh r)

/-- **The battery ratio is the Gudermannian ratio.**
`R(r) = gd(η) / (2η)` with `η = artanh r`, by the Gudermannian bridge. -/
theorem batteryRatio_eq_gd {r : ℝ} (h : r ∈ Ioo (-1:ℝ) 1) :
    batteryRatio r = gd (Real.artanh r) / (2 * Real.artanh r) := by
  rw [batteryRatio, ← arcsin_eq_gd_artanh h]

/-! ## The Zeno threshold -/

/-- **The Zeno threshold.** At `V = 1/√2` the Fisher information is exactly
`2`, the crossover identified in the paper. -/
theorem gammaSq_zeno_threshold : gammaSq (1 / Real.sqrt 2) = 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  simp only [gammaSq, div_pow, one_pow, h2]
  norm_num

/-- The threshold visibility lies in the open interval. -/
theorem zeno_threshold_mem : (1 / Real.sqrt 2) ∈ Ioo (-1:ℝ) 1 := by
  have h1 : (1:ℝ) < Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2 := by positivity
  constructor
  · have : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
    linarith
  · rw [div_lt_one hpos]; exact h1

end FisherLorentz
