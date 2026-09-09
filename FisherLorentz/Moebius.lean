/-
# Möbius covariance and the SLOCC transformation law

Formalises:
* B. G. Srivats, "Möbius Covariance, Effect Classification, and a
  Holographic Correspondence for Qubit Fisher Information" (under review),
  Theorem 1.
* B. G. Srivats, "The Algebra of the Qubit: Fourteen Theorems on
  I(V) = γ²(V)", Zenodo, Theorems T8 and T11a.

Einstein velocity addition on the visibility coordinate is
`V ⊕ ξ = (V + ξ)/(1 + Vξ)`. The Fisher information is not invariant under
it; it carries the conformal weight `γ²(ξ)(1 + Vξ)²`.
-/
import Mathlib.Tactic
import FisherLorentz.Basic

namespace FisherLorentz

open Set

/-- Einstein addition of visibilities, `V ⊕ ξ = (V + ξ)/(1 + Vξ)`. -/
noncomputable def einsteinAdd (V ξ : ℝ) : ℝ := (V + ξ) / (1 + V * ξ)

@[inherit_doc] infixl:65 " ⊕ᵥ " => einsteinAdd

/-- The denominator `1 + Vξ` is positive on the open square. -/
lemma one_add_mul_pos {V ξ : ℝ} (hV : V ∈ Ioo (-1:ℝ) 1) (hξ : ξ ∈ Ioo (-1:ℝ) 1) :
    (0:ℝ) < 1 + V * ξ := by
  nlinarith [hV.1, hV.2, hξ.1, hξ.2]

/-- **The key algebraic identity behind Möbius covariance.**
`1 − (V ⊕ ξ)² = (1 − V²)(1 − ξ²)/(1 + Vξ)²`. -/
theorem one_sub_einsteinAdd_sq {V ξ : ℝ}
    (hV : V ∈ Ioo (-1:ℝ) 1) (hξ : ξ ∈ Ioo (-1:ℝ) 1) :
    1 - (V ⊕ᵥ ξ) ^ 2 = (1 - V ^ 2) * (1 - ξ ^ 2) / (1 + V * ξ) ^ 2 := by
  have hd : (0:ℝ) < 1 + V * ξ := one_add_mul_pos hV hξ
  have hne : (1:ℝ) + V * ξ ≠ 0 := ne_of_gt hd
  simp only [einsteinAdd, div_pow]
  field_simp
  ring

/-- Einstein addition maps the open interval to itself. -/
theorem einsteinAdd_mem {V ξ : ℝ}
    (hV : V ∈ Ioo (-1:ℝ) 1) (hξ : ξ ∈ Ioo (-1:ℝ) 1) :
    V ⊕ᵥ ξ ∈ Ioo (-1:ℝ) 1 := by
  have hd : (0:ℝ) < 1 + V * ξ := one_add_mul_pos hV hξ
  constructor
  · rw [einsteinAdd, lt_div_iff₀ hd]; nlinarith [hV.1, hV.2, hξ.1, hξ.2]
  · rw [einsteinAdd, div_lt_one hd]; nlinarith [hV.1, hV.2, hξ.1, hξ.2]

/-- **Theorem 1 (Möbius covariance).**
Under Einstein addition the Fisher information transforms with weight
`γ²(ξ)(1 + Vξ)²`:
`I(V ⊕ ξ) = γ²(ξ)(1 + Vξ)² · I(V)`.
Fisher information is therefore **not** an `SL(2,ℂ)` invariant. -/
theorem fisherInfo_einsteinAdd {V ξ : ℝ}
    (hV : V ∈ Ioo (-1:ℝ) 1) (hξ : ξ ∈ Ioo (-1:ℝ) 1) :
    fisherInfo (V ⊕ᵥ ξ) = gammaSq ξ * (1 + V * ξ) ^ 2 * fisherInfo V := by
  have hd : (0:ℝ) < 1 + V * ξ := one_add_mul_pos hV hξ
  have hne : (1:ℝ) + V * ξ ≠ 0 := ne_of_gt hd
  have hV2 : (0:ℝ) < 1 - V ^ 2 := by nlinarith [hV.1, hV.2]
  have hξ2 : (0:ℝ) < 1 - ξ ^ 2 := by nlinarith [hξ.1, hξ.2]
  rw [fisherInfo_eq_gammaSq (einsteinAdd_mem hV hξ), fisherInfo_eq_gammaSq hV]
  simp only [gammaSq]
  rw [one_sub_einsteinAdd_sq hV hξ]
  field_simp

/-- **T11a, the SLOCC transformation law**, in multiplicative form:
`γ²(V ⊕ ξ) = γ²(V) γ²(ξ) (1 + Vξ)²`. -/
theorem gammaSq_einsteinAdd {V ξ : ℝ}
    (hV : V ∈ Ioo (-1:ℝ) 1) (hξ : ξ ∈ Ioo (-1:ℝ) 1) :
    gammaSq (V ⊕ᵥ ξ) = gammaSq V * gammaSq ξ * (1 + V * ξ) ^ 2 := by
  have h := fisherInfo_einsteinAdd hV hξ
  rw [fisherInfo_eq_gammaSq (einsteinAdd_mem hV hξ), fisherInfo_eq_gammaSq hV] at h
  linarith [h]

/-- Einstein addition is commutative. -/
theorem einsteinAdd_comm (V ξ : ℝ) : V ⊕ᵥ ξ = ξ ⊕ᵥ V := by
  simp only [einsteinAdd]; ring_nf

/-- Zero is the identity for Einstein addition. -/
@[simp] theorem einsteinAdd_zero (V : ℝ) : V ⊕ᵥ 0 = V := by
  simp [einsteinAdd]

@[simp] theorem zero_einsteinAdd (V : ℝ) : (0:ℝ) ⊕ᵥ V = V := by
  simp [einsteinAdd]

/-- Einstein addition has inverses: `V ⊕ (−V) = 0`. -/
@[simp] theorem einsteinAdd_neg_self (V : ℝ) : V ⊕ᵥ (-V) = 0 := by
  simp [einsteinAdd]

end FisherLorentz
