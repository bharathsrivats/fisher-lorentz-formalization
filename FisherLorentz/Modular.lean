/-
# Modular structure on the qubit

Formalisation of results from

  B. G. Srivats, "A Modular Speed Limit on the Qubit" (OSID, under review),
  Proposition 1 and the surrounding modular machinery.

The modular operator of a faithful qubit state acts on `M₂(ℂ)` by
`Δ(X) = ρ X ρ⁻¹`. On matrix units it is diagonal, with spectrum
`{1, 1, e^{2η}, e^{-2η}}` where `η = artanh V` is the Bloch rapidity.

The ratio `λ = p/(1-p) = e^{2η}` proved here is the Araki-Woods /
Powers type-classification parameter of the infinite tensor product
`⊗(M₂(ℂ), ω_p)`. See `03_TRACK_C_TYPE3/`.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import FisherLorentz.Basic

namespace FisherLorentz

open Real Set Matrix

/-! ## The rapidity and the modular ratio -/

/-- The Bloch rapidity `η = artanh V`. -/
noncomputable def rapidity (V : ℝ) : ℝ := Real.artanh V

/-- The modular ratio `λ(V) = p₊/p₋ = (1+V)/(1-V)`. -/
noncomputable def modRatio (V : ℝ) : ℝ := pPlus V / pMinus V

/-- `λ = (1+V)/(1-V)`, directly from the outcome probabilities. -/
theorem modRatio_eq {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    modRatio V = (1 + V) / (1 - V) := by
  have h2 : (1:ℝ) - V ≠ 0 := by linarith [h.2]
  simp only [modRatio, pPlus, pMinus]
  field_simp

/-- **The modular ratio is `e^{2η}`.**
`p/(1-p) = (1+V)/(1-V) = exp(2 artanh V)`.
This is the eigenvalue of the modular operator in Proposition 1, and it is
the Powers/Araki-Woods type parameter. -/
theorem modRatio_eq_exp_two_rapidity {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    modRatio V = Real.exp (2 * rapidity V) := by
  have h1 : (0:ℝ) < 1 + V := by linarith [h.1]
  have h2 : (0:ℝ) < 1 - V := by linarith [h.2]
  rw [modRatio_eq h, rapidity, Real.artanh_eq_half_log (Ioo_subset_Icc_self h)]
  rw [show 2 * ((1:ℝ)/2 * Real.log ((1 + V) / (1 - V)))
        = Real.log ((1 + V) / (1 - V)) by ring]
  exact (Real.exp_log (div_pos h1 h2)).symm

/-- The rapidity recovers the visibility: `tanh η = V`. -/
theorem tanh_rapidity {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    Real.tanh (rapidity V) = V := Real.tanh_artanh h

/-- `γ² = cosh²η`: the squared Lorentz factor is the squared hyperbolic cosine
of the rapidity. -/
theorem gammaSq_eq_cosh_sq {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    gammaSq V = Real.cosh (rapidity V) ^ 2 := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  have hc : Real.cosh (rapidity V) = 1 / Real.sqrt (1 - V ^ 2) := Real.cosh_artanh h
  rw [gammaSq, hc, div_pow, one_pow, Real.sq_sqrt hpos.le]

/-! ## The modular operator on `M₂(ℂ)` -/

/-- The modular operator `Δ(X) = ρ X ρ⁻¹`. -/
noncomputable def modOp (ρ X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := ρ * X * ρ⁻¹

/-- The faithful diagonal state `diag(p, 1-p)`. -/
noncomputable def rhoDiag (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(p : ℂ), 0; 0, 1 - (p : ℂ)]

/-- Its explicit inverse. -/
noncomputable def rhoDiagInv (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((p : ℂ))⁻¹, 0; 0, ((1 : ℂ) - (p : ℂ))⁻¹]

section
variable {p : ℝ} (hp : 0 < p) (hp1 : p < 1)

include hp hp1

lemma cast_p_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'

lemma cast_q_ne : (1 : ℂ) - (p : ℂ) ≠ 0 := by
  have hq : ((1 : ℝ) - p) ≠ 0 := by linarith
  have hcast : (((1 : ℝ) - p : ℝ) : ℂ) = (1 : ℂ) - (p : ℂ) := by push_cast; ring
  rw [← hcast]; exact_mod_cast hq

lemma rhoDiag_mul_inv : rhoDiag p * rhoDiagInv p = 1 := by
  have h1 := cast_p_ne hp hp1
  have h2 := cast_q_ne hp hp1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoDiag, rhoDiagInv, Matrix.mul_apply, Fin.sum_univ_two,
          mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]

lemma inv_rhoDiag : (rhoDiag p)⁻¹ = rhoDiagInv p :=
  Matrix.inv_eq_right_inv (rhoDiag_mul_inv hp hp1)

/-- **Proposition 1, off-diagonal eigenvector `E₀₁`.**
`Δ(E₀₁) = (p/(1-p)) E₀₁`. The eigenvalue is the modular ratio `λ = e^{2η}`. -/
theorem modOp_E01 :
    modOp (rhoDiag p) !![0, 1; 0, 0]
      = ((p : ℂ) / ((1 : ℂ) - (p : ℂ))) • !![0, 1; 0, 0] := by
  have h1 := cast_p_ne hp hp1
  have h2 := cast_q_ne hp hp1
  rw [modOp, inv_rhoDiag hp hp1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoDiag, rhoDiagInv, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]

/-- **Proposition 1, off-diagonal eigenvector `E₁₀`.**
`Δ(E₁₀) = ((1-p)/p) E₁₀`, eigenvalue `λ⁻¹ = e^{-2η}`. -/
theorem modOp_E10 :
    modOp (rhoDiag p) !![0, 0; 1, 0]
      = (((1 : ℂ) - (p : ℂ)) / (p : ℂ)) • !![0, 0; 1, 0] := by
  have h1 := cast_p_ne hp hp1
  have h2 := cast_q_ne hp hp1
  rw [modOp, inv_rhoDiag hp hp1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoDiag, rhoDiagInv, Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]

/-- **Proposition 1, diagonal eigenvectors.** Both carry eigenvalue `1`. -/
theorem modOp_E00 :
    modOp (rhoDiag p) !![1, 0; 0, 0] = !![1, 0; 0, 0] := by
  have h1 := cast_p_ne hp hp1
  have h2 := cast_q_ne hp hp1
  rw [modOp, inv_rhoDiag hp hp1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoDiag, rhoDiagInv, Matrix.mul_apply, Fin.sum_univ_two,
          mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]

theorem modOp_E11 :
    modOp (rhoDiag p) !![0, 0; 0, 1] = !![0, 0; 0, 1] := by
  have h1 := cast_p_ne hp hp1
  have h2 := cast_q_ne hp hp1
  rw [modOp, inv_rhoDiag hp hp1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoDiag, rhoDiagInv, Matrix.mul_apply, Fin.sum_univ_two,
          mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]

end

/-- **The modular spectrum is `{1, 1, λ, λ⁻¹}` with `λ = e^{2η}`.**
Combining the four eigenvector computations with `modRatio_eq_exp_two_rapidity`:
the nontrivial modular eigenvalue at visibility `V` is `exp(2 artanh V)`. -/
theorem modOp_nontrivial_eigenvalue {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    modOp (rhoDiag (pPlus V)) !![0, 1; 0, 0]
      = ((Real.exp (2 * rapidity V) : ℝ) : ℂ) • !![0, 1; 0, 0] := by
  have hp : 0 < pPlus V := pPlus_pos h
  have hp1 : pPlus V < 1 := by
    simp only [pPlus]; linarith [h.2]
  rw [modOp_E01 hp hp1]
  congr 1
  have key : modRatio V = Real.exp (2 * rapidity V) :=
    modRatio_eq_exp_two_rapidity h
  have hq : pMinus V ≠ 0 := (pMinus_pos h).ne'
  have : (pPlus V : ℝ) / (pMinus V : ℝ) = Real.exp (2 * rapidity V) := by
    simpa [modRatio] using key
  have hcast : ((1 : ℂ) - ((pPlus V : ℝ) : ℂ)) = ((pMinus V : ℝ) : ℂ) := by
    simp only [pPlus, pMinus]; push_cast; ring
  rw [hcast, ← this]
  push_cast
  ring

end FisherLorentz
