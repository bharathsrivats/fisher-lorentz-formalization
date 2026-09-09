/-
# Thomas-Wigner kinematics of sequential qubit measurements

Formalises B. G. Srivats, "Lorentz Kinematics of Sequential Binary Qubit
Measurements" (J. Math. Phys., under review), Theorem 1, and the same result
as T2 of "The Algebra of the Qubit".

The half-rapidity identity `tanh(η/2) = Vγ/(γ+1)` is what converts the
Bloch-coordinate form of the Thomas-Wigner angle into the rapidity form.
-/
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import FisherLorentz.Basic
import FisherLorentz.Identities

namespace FisherLorentz

open Real Set

/-- `sinh(artanh V) = V·γ(V)`. -/
theorem sinh_artanh_eq {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    Real.sinh (Real.artanh V) = V * gamma V := by
  rw [Real.sinh_artanh h, gamma]
  ring

/-- `cosh(artanh V) = γ(V)`. -/
theorem cosh_artanh_eq {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    Real.cosh (Real.artanh V) = gamma V := by
  rw [Real.cosh_artanh h, gamma]

/-- `tanh y = sinh(2y)/(cosh(2y) + 1)`, the half-angle form. -/
lemma tanh_eq_sinh_two_div (y : ℝ) :
    Real.tanh y = Real.sinh (2*y) / (Real.cosh (2*y) + 1) := by
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  have hpy : Real.cosh y ^ 2 - Real.sinh y ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq y
  have hden : Real.cosh (2*y) + 1 = 2 * Real.cosh y ^ 2 := by
    rw [Real.cosh_two_mul]; nlinarith [hpy]
  rw [Real.sinh_two_mul, hden, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- **The half-rapidity identity.** `tanh(η/2) = V γ /(γ + 1)`,
with `η = artanh V` and `γ = γ(V)`. This is the substitution that converts
the Bloch form of the Thomas-Wigner angle into the rapidity form. -/
theorem tanh_half_rapidity {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    Real.tanh (Real.artanh V / 2) = V * gamma V / (gamma V + 1) := by
  have hgpos : 0 < gamma V := by
    have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
    simp only [gamma]; positivity
  have key := tanh_eq_sinh_two_div (Real.artanh V / 2)
  rw [show 2 * (Real.artanh V / 2) = Real.artanh V by ring] at key
  rw [key, sinh_artanh_eq h, cosh_artanh_eq h]

/-- The Thomas-Wigner angle in Bloch coordinates, as the paper writes it:
`tan(Ω/2) = V₁V₂γ₁γ₂ sin θ / [(γ₁+1)(γ₂+1) + V₁V₂γ₁γ₂ cos θ]`. -/
noncomputable def twTanHalfBloch (V₁ V₂ θ : ℝ) : ℝ :=
  V₁ * V₂ * gamma V₁ * gamma V₂ * Real.sin θ /
    ((gamma V₁ + 1) * (gamma V₂ + 1) + V₁ * V₂ * gamma V₁ * gamma V₂ * Real.cos θ)

/-- The same angle in rapidity coordinates:
`tan(Ω/2) = tanh(η₁/2) tanh(η₂/2) sin θ / [1 + tanh(η₁/2) tanh(η₂/2) cos θ]`. -/
noncomputable def twTanHalfRapidity (V₁ V₂ θ : ℝ) : ℝ :=
  let t₁ := Real.tanh (Real.artanh V₁ / 2)
  let t₂ := Real.tanh (Real.artanh V₂ / 2)
  t₁ * t₂ * Real.sin θ / (1 + t₁ * t₂ * Real.cos θ)

/-- Algebraic core: `(P/Q)s / (1 + (P/Q)c) = Ps / (Q + Pc)` for `Q ≠ 0`.
Both sides vanish together when the denominator does, so no side condition
on `Q + Pc` is needed. -/
lemma ratio_rescale (P Q s c : ℝ) (hQ : Q ≠ 0) :
    (P/Q) * s / (1 + (P/Q) * c) = P * s / (Q + P * c) := by
  have hrw : 1 + (P/Q) * c = (Q + P * c) / Q := by field_simp
  rw [hrw]
  by_cases h : Q + P * c = 0
  · simp [h]
  · rw [div_div_eq_mul_div]
    field_simp

/-- **The two forms of the Thomas-Wigner angle agree.** -/
theorem twTanHalf_eq {V₁ V₂ : ℝ}
    (h₁ : V₁ ∈ Ioo (-1:ℝ) 1) (h₂ : V₂ ∈ Ioo (-1:ℝ) 1) (θ : ℝ) :
    twTanHalfRapidity V₁ V₂ θ = twTanHalfBloch V₁ V₂ θ := by
  have hg₁ : 0 < gamma V₁ := by
    have : (0:ℝ) < 1 - V₁ ^ 2 := by nlinarith [h₁.1, h₁.2]
    simp only [gamma]; positivity
  have hg₂ : 0 < gamma V₂ := by
    have : (0:ℝ) < 1 - V₂ ^ 2 := by nlinarith [h₂.1, h₂.2]
    simp only [gamma]; positivity
  have hd₁ : gamma V₁ + 1 ≠ 0 := ne_of_gt (by linarith)
  have hd₂ : gamma V₂ + 1 ≠ 0 := ne_of_gt (by linarith)
  have hQ : (gamma V₁ + 1) * (gamma V₂ + 1) ≠ 0 := mul_ne_zero hd₁ hd₂
  simp only [twTanHalfRapidity, twTanHalfBloch,
             tanh_half_rapidity h₁, tanh_half_rapidity h₂]
  have hsplit : V₁ * gamma V₁ / (gamma V₁ + 1) * (V₂ * gamma V₂ / (gamma V₂ + 1))
      = (V₁ * V₂ * gamma V₁ * gamma V₂) / ((gamma V₁ + 1) * (gamma V₂ + 1)) := by
    field_simp
  rw [hsplit]
  exact ratio_rescale _ _ _ _ hQ

/-- **Equal visibilities at right angle.** At `θ = π/2` and `V₁ = V₂ = V`,
the angle reduces to `tan(Ω/2) = tanh²(η/2)`. -/
theorem twTanHalf_orthogonal {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    twTanHalfRapidity V V (Real.pi / 2)
      = Real.tanh (Real.artanh V / 2) ^ 2 := by
  simp only [twTanHalfRapidity, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring_nf

end FisherLorentz
