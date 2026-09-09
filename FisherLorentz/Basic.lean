/-
Copyright (c) 2026 Bharath G. Srivats.

# The Fisher-Lorentz anchor identity

Formalisation of the central identity of

  B. G. Srivats, "Fisher Information Is the Squared Lorentz Factor",
  Quantum Reports 8(3), 68 (2026), doi:10.3390/quantum8030068, Eqs. (1)-(2).

Main result: for a two-outcome (binary) measurement with visibility
`V ∈ (-1,1)`, outcome probabilities `(1±V)/2`, the Fisher information
with respect to `V` equals the squared Lorentz factor `γ²(V) = 1/(1-V²)`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace FisherLorentz

open Set

/-! ## The binary measurement family -/

/-- Probability of outcome `+` at visibility `V`. -/
noncomputable def pPlus (V : ℝ) : ℝ := (1 + V) / 2

/-- Probability of outcome `-` at visibility `V`. -/
noncomputable def pMinus (V : ℝ) : ℝ := (1 - V) / 2

@[simp] lemma pPlus_add_pMinus (V : ℝ) : pPlus V + pMinus V = 1 := by
  unfold pPlus pMinus; ring

lemma pPlus_pos {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) : 0 < pPlus V := by
  unfold pPlus; linarith [h.1]

lemma pMinus_pos {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) : 0 < pMinus V := by
  unfold pMinus; linarith [h.2]

/-- The product of the two outcome probabilities is `(1 - V²)/4`. -/
lemma pPlus_mul_pMinus (V : ℝ) : pPlus V * pMinus V = (1 - V ^ 2) / 4 := by
  unfold pPlus pMinus; ring

/-! ## Derivatives, proven (not assumed) -/

@[simp] lemma deriv_pPlus (V : ℝ) : deriv pPlus V = 1 / 2 := by
  unfold pPlus
  rw [deriv_div_const]
  simp

@[simp] lemma deriv_pMinus (V : ℝ) : deriv pMinus V = -(1 / 2) := by
  unfold pMinus
  rw [deriv_div_const]
  simp
  ring

/-! ## Fisher information -/

/-- Fisher information of the binary family at visibility `V`, in the
score form `Σ_x (∂_V p_x)² / p_x`. -/
noncomputable def fisherInfo (V : ℝ) : ℝ :=
  (deriv pPlus V) ^ 2 / pPlus V + (deriv pMinus V) ^ 2 / pMinus V

/-- The squared Lorentz factor. -/
noncomputable def gammaSq (V : ℝ) : ℝ := 1 / (1 - V ^ 2)

/-! ## The anchor identity -/

/-- **Fisher information is the squared Lorentz factor.**
For a binary measurement of visibility `V ∈ (-1,1)`,
`I(V) = 1/(1 - V²) = γ²(V)`. -/
theorem fisherInfo_eq_gammaSq {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    fisherInfo V = gammaSq V := by
  have h1 : (1 : ℝ) + V ≠ 0 := by linarith [h.1]
  have h2 : (1 : ℝ) - V ≠ 0 := by linarith [h.2]
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  have hV : (1 : ℝ) - V ^ 2 ≠ 0 := ne_of_gt hpos
  simp only [fisherInfo, gammaSq, deriv_pPlus, deriv_pMinus, pPlus, pMinus]
  field_simp
  ring

/-- Equivalent form: `I(V) = 1 / (4 p₊ p₋)`. -/
theorem fisherInfo_eq_inv_four_mul_prod {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    fisherInfo V = 1 / (4 * (pPlus V * pMinus V)) := by
  rw [fisherInfo_eq_gammaSq h, pPlus_mul_pMinus]
  unfold gammaSq
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  have hV : (1 : ℝ) - V ^ 2 ≠ 0 := ne_of_gt hpos
  field_simp

/-- The identity at `V = 0` (maximally uncertain measurement): `I(0) = 1`. -/
example : fisherInfo 0 = 1 := by
  rw [fisherInfo_eq_gammaSq (by norm_num)]
  unfold gammaSq; norm_num

/-- `γ²` diverges as `V → ±1`: `γ²` is unbounded on `(-1,1)`.
Concretely, `γ²(V) ≥ M` once `V² ≥ 1 - 1/M`. -/
theorem gammaSq_ge {V M : ℝ} (hM : 0 < M) (h : V ∈ Ioo (-1:ℝ) 1)
    (hV : 1 - V ^ 2 ≤ 1 / M) : M ≤ gammaSq V := by
  have hpos : 0 < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  unfold gammaSq
  rw [le_div_iff₀ hpos]
  calc M * (1 - V ^ 2) ≤ M * (1 / M) := by nlinarith
    _ = 1 := by field_simp

end FisherLorentz
