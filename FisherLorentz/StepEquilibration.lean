/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

# Step equilibration of a qubit in the visibility coordinate

A two-level system is taken through gap quenches, each followed by full equilibration. At
equilibrium the visibility is `V = tanh η`, where the rapidity `η` is half the gap in units of `kT`.
This file proves the non-asymptotic statements: the entropy produced in a step in closed form, the
one-step reset, the three-point identity, the Einstein-addition form, the energy balance, and the
lower bound `(gd η_N)² / (2 N)` on the entropy produced by any increasing schedule of `N` steps.
-/
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.Chebyshev
import FisherLorentz.Basic
import FisherLorentz.Moebius
import FisherLorentz.Gudermannian

namespace FisherLorentz

open Real Set

/-- The relative entropy of two Bernoulli laws of the binary family, by visibility. -/
noncomputable def relEntropyV (V₁ V₂ : ℝ) : ℝ :=
  pPlus V₁ * log (pPlus V₁ / pPlus V₂) + pMinus V₁ * log (pMinus V₁ / pMinus V₂)

private lemma artanh_half_log {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    Real.artanh V = (log (1 + V) - log (1 - V)) / 2 := by
  have hmem : V ∈ Icc (-1:ℝ) 1 := ⟨h.1.le, h.2.le⟩
  rw [Real.artanh_eq_half_log hmem, log_div (by linarith [h.1]) (by linarith [h.2])]
  ring

private lemma log_gammaSq {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    log (gammaSq V) = -(log (1 + V) + log (1 - V)) := by
  have h1 : (0:ℝ) < 1 + V := by linarith [h.1]
  have h2 : (0:ℝ) < 1 - V := by linarith [h.2]
  have : gammaSq V = 1 / ((1 + V) * (1 - V)) := by unfold gammaSq; congr 1; ring
  rw [this, one_div, log_inv, log_mul h1.ne' h2.ne']

/-- **The entropy produced in a step, exactly.**
`D = log (γ₂ / γ₁) - V₁ (η₂ - η₁)`, with `log (γ₂ / γ₁)` written through `γ²`. -/
theorem relEntropyV_eq {V₁ V₂ : ℝ} (h₁ : V₁ ∈ Ioo (-1:ℝ) 1) (h₂ : V₂ ∈ Ioo (-1:ℝ) 1) :
    relEntropyV V₁ V₂ = (log (gammaSq V₂) - log (gammaSq V₁)) / 2
      - V₁ * (Real.artanh V₂ - Real.artanh V₁) := by
  have a1 : (0:ℝ) < 1 + V₁ := by linarith [h₁.1]
  have a2 : (0:ℝ) < 1 - V₁ := by linarith [h₁.2]
  have b1 : (0:ℝ) < 1 + V₂ := by linarith [h₂.1]
  have b2 : (0:ℝ) < 1 - V₂ := by linarith [h₂.2]
  have e1 : pPlus V₁ / pPlus V₂ = (1 + V₁) / (1 + V₂) := by
    unfold pPlus; field_simp
  have e2 : pMinus V₁ / pMinus V₂ = (1 - V₁) / (1 - V₂) := by
    unfold pMinus; field_simp
  rw [relEntropyV, e1, e2, log_div a1.ne' b1.ne', log_div a2.ne' b2.ne', log_gammaSq h₁,
    log_gammaSq h₂, artanh_half_log h₁, artanh_half_log h₂]
  unfold pPlus pMinus
  ring

@[simp] lemma gammaSq_zero : gammaSq 0 = 1 := by simp [gammaSq]

/-- **One-step reset.** From the maximally mixed state the entropy produced is `log γ(V)`. -/
theorem relEntropyV_zero {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    relEntropyV 0 V = log (gammaSq V) / 2 := by
  rw [relEntropyV_eq ⟨by norm_num, by norm_num⟩ h]
  simp

/-- The one-step reset in the error `ε`: `-(1/2) log (4 ε (1 - ε))`. -/
theorem relEntropyV_zero_error {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    relEntropyV 0 (1 - 2 * ε) = -(log (4 * ε * (1 - ε))) / 2 := by
  have hV : (1 - 2 * ε) ∈ Ioo (-1:ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [relEntropyV_zero hV]
  have : gammaSq (1 - 2 * ε) = (4 * ε * (1 - ε))⁻¹ := by
    unfold gammaSq; rw [one_div]; congr 1; ring
  rw [this, log_inv]

/-- The logit of a population: `x = log ((1 - p) / p)`, twice the rapidity. -/
noncomputable def logitGap (p : ℝ) : ℝ := log ((1 - p) / p)

/-- Bernoulli relative entropy in the excited population. -/
noncomputable def klBern (p q : ℝ) : ℝ :=
  p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

/-- **The three-point identity**, which says that inserting a point between two others lowers the
sum and inserting a point outside raises it. -/
theorem klBern_three_point {a b c : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (hb : b ∈ Ioo (0:ℝ) 1)
    (hc : c ∈ Ioo (0:ℝ) 1) :
    klBern a c = klBern a b + klBern b c + (a - b) * (logitGap c - logitGap b) := by
  have a0 := ha.1.ne'; have b0 := hb.1.ne'; have c0 := hc.1.ne'
  have a1 : 1 - a ≠ 0 := by linarith [ha.2] |> fun h : 0 < 1 - a => h.ne'
  have b1 : 1 - b ≠ 0 := by linarith [hb.2] |> fun h : 0 < 1 - b => h.ne'
  have c1 : 1 - c ≠ 0 := by linarith [hc.2] |> fun h : 0 < 1 - c => h.ne'
  unfold klBern logitGap
  rw [log_div a0 c0, log_div a1 c1, log_div a0 b0, log_div a1 b1, log_div b0 c0, log_div b1 c1,
    log_div c1 c0, log_div b1 b0]
  ring

/-- The rapidity adds under Einstein addition. -/
theorem artanh_einsteinAdd {V ξ : ℝ} (hV : V ∈ Ioo (-1:ℝ) 1) (hξ : ξ ∈ Ioo (-1:ℝ) 1) :
    Real.artanh (einsteinAdd V ξ) = Real.artanh V + Real.artanh ξ := by
  have hS := einsteinAdd_mem hV hξ
  have hd := one_add_mul_pos hV hξ
  have v1 : (0:ℝ) < 1 + V := by linarith [hV.1]
  have v2 : (0:ℝ) < 1 - V := by linarith [hV.2]
  have x1 : (0:ℝ) < 1 + ξ := by linarith [hξ.1]
  have x2 : (0:ℝ) < 1 - ξ := by linarith [hξ.2]
  have e1 : 1 + einsteinAdd V ξ = (1 + V) * (1 + ξ) / (1 + V * ξ) := by
    unfold einsteinAdd; field_simp; ring
  have e2 : 1 - einsteinAdd V ξ = (1 - V) * (1 - ξ) / (1 + V * ξ) := by
    unfold einsteinAdd; field_simp; ring
  rw [artanh_half_log hS, artanh_half_log hV, artanh_half_log hξ, e1, e2,
    log_div (by positivity) hd.ne', log_div (by positivity) hd.ne',
    log_mul v1.ne' x1.ne', log_mul v2.ne' x2.ne']
  ring

/-- **A gap quench as a boost.** A step that adds rapidity `artanh ξ` produces entropy
`log γ(ξ) + log (1 + V ξ) - V artanh ξ`. -/
theorem relEntropyV_einsteinAdd {V ξ : ℝ} (hV : V ∈ Ioo (-1:ℝ) 1) (hξ : ξ ∈ Ioo (-1:ℝ) 1) :
    relEntropyV V (einsteinAdd V ξ) =
      log (gammaSq ξ) / 2 + log (1 + V * ξ) - V * Real.artanh ξ := by
  have hS := einsteinAdd_mem hV hξ
  have hd := one_add_mul_pos hV hξ
  have g1 : gammaSq V ≠ 0 := by
    have : (0:ℝ) < 1 - V ^ 2 := by nlinarith [hV.1, hV.2]
    unfold gammaSq; positivity
  have g2 : gammaSq ξ ≠ 0 := by
    have : (0:ℝ) < 1 - ξ ^ 2 := by nlinarith [hξ.1, hξ.2]
    unfold gammaSq; positivity
  rw [relEntropyV_eq hV hS, artanh_einsteinAdd hV hξ, gammaSq_einsteinAdd hV hξ,
    log_mul (mul_ne_zero g1 g2) (pow_ne_zero 2 hd.ne'), log_mul g1 g2, log_pow]
  push_cast
  ring

/-- **First law.** Work and heat over a schedule telescope to the final energy. Here `ω` is the gap
and `p` the excited population at each stage. -/
theorem first_law (ω p : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((ω (i + 1) - ω i) * p i + ω (i + 1) * (p (i + 1) - p i))
      = ω N * p N - ω 0 * p 0 := by
  rw [← Finset.sum_range_sub (fun i => ω i * p i) N]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## The lower bound through the Gudermannian -/

/-- The entropy produced by the step between rapidities `a` and `b`. -/
noncomputable def stepEntropy (a b : ℝ) : ℝ := log (cosh b / cosh a) - tanh a * (b - a)

private lemma hasDerivAt_tanh (t : ℝ) : HasDerivAt tanh (1 / cosh t ^ 2) t := by
  have h := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (cosh_pos t).ne'
  have e : (sinh / cosh : ℝ → ℝ) = tanh := by
    funext x; exact (Real.tanh_eq_sinh_div_cosh x).symm
  have v : (cosh t * cosh t - sinh t * sinh t) / cosh t ^ 2 = 1 / cosh t ^ 2 := by
    congr 1; nlinarith [Real.cosh_sq t]
  rw [v, e] at h
  exact h

private lemma hasDerivAt_gd (t : ℝ) : HasDerivAt gd (1 / cosh t) t := by
  have h0 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have h1 : HasDerivAt (fun x : ℝ => tanh (x / 2)) (1 / cosh (t / 2) ^ 2 * (1 / 2)) t :=
    HasDerivAt.comp (h₂ := tanh) (h := fun x : ℝ => x / 2) t (hasDerivAt_tanh (t / 2)) h0
  have h2 := h1.arctan
  have h3 := h2.const_mul (2:ℝ)
  have hc : cosh t = cosh (t / 2) ^ 2 + sinh (t / 2) ^ 2 := by
    have := Real.cosh_two_mul (t / 2)
    rwa [show 2 * (t / 2) = t by ring] at this
  have hcp : (0:ℝ) < cosh (t / 2) := cosh_pos _
  have hct : (0:ℝ) < cosh t := cosh_pos _
  have val : 2 * (1 / (1 + tanh (t / 2) ^ 2) * (1 / cosh (t / 2) ^ 2 * (1 / 2))) = 1 / cosh t := by
    rw [Real.tanh_eq_sinh_div_cosh, hc]
    have hs : cosh (t / 2) ^ 2 + sinh (t / 2) ^ 2 ≠ 0 := by rw [← hc]; exact hct.ne'
    field_simp
  rw [val] at h3
  exact h3

private lemma hasDerivAt_log_cosh (t : ℝ) : HasDerivAt (fun x => log (cosh x)) (tanh t) t := by
  have h := (Real.hasDerivAt_cosh t).log (cosh_pos t).ne'
  rwa [← Real.tanh_eq_sinh_div_cosh] at h

private lemma cosh_le_cosh_of_le {s t : ℝ} (h0 : 0 ≤ s) (h : s ≤ t) : cosh s ≤ cosh t := by
  rw [Real.cosh_le_cosh, abs_of_nonneg h0, abs_of_nonneg (h0.trans h)]
  exact h

/-- `tanh t - tanh a ≥ (gd t - gd a) / cosh t` for `0 ≤ a ≤ t`. -/
private lemma tanh_sub_ge {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    (gd t - gd a) / cosh t ≤ tanh t - tanh a := by
  have hu : ∀ s, HasDerivAt (fun s => tanh s - gd s / cosh t) (1 / cosh s ^ 2 - 1 / cosh s / cosh t) s :=
    fun s => (hasDerivAt_tanh s).sub ((hasDerivAt_gd s).div_const _)
  have hmono : MonotoneOn (fun s => tanh s - gd s / cosh t) (Icc a t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a t)
      (fun s _ => (hu s).continuousAt.continuousWithinAt)
      (fun s _ => (hu s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [interior_Icc] at hs
    rw [(hu s).deriv]
    have hs0 : 0 ≤ s := ha.trans hs.1.le
    have hcs : (0:ℝ) < cosh s := cosh_pos s
    have hct : (0:ℝ) < cosh t := cosh_pos t
    have hle := cosh_le_cosh_of_le hs0 hs.2.le
    have : 1 / cosh s / cosh t ≤ 1 / cosh s ^ 2 := by
      rw [div_div, sq]
      exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hle hcs.le)
    linarith
  have h := hmono (left_mem_Icc.mpr hat) (right_mem_Icc.mpr hat) hat
  have e : (gd t - gd a) / cosh t = gd t / cosh t - gd a / cosh t := sub_div _ _ _
  rw [e]; linarith

/-- **The pointwise bound.** For an outward step, `D ≥ (1/2) (Δ gd)²`. -/
theorem stepEntropy_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (gd b - gd a) ^ 2 / 2 ≤ stepEntropy a b := by
  set g : ℝ → ℝ := fun t => log (cosh t) - log (cosh a) - tanh a * (t - a) - (gd t - gd a) ^ 2 / 2
    with hg
  have hd : ∀ t, HasDerivAt g (tanh t - tanh a - (gd t - gd a) * (1 / cosh t)) t := by
    intro t
    have h1 := ((hasDerivAt_log_cosh t).sub_const (log (cosh a))).sub
      (((hasDerivAt_id t).sub_const a).const_mul (tanh a))
    have h2 := (((hasDerivAt_gd t).sub_const (gd a)).pow 2).div_const 2
    have h3 := h1.sub h2
    have h4 := h3.congr_deriv (g' := tanh t - tanh a - (gd t - gd a) * (1 / cosh t))
      (by simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; norm_num; ring)
    exact h4
  have hmono : MonotoneOn g (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hd t).deriv]
    have := tanh_sub_ge ha ht.1.le
    rw [div_eq_mul_one_div] at this
    linarith
  have h := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have g0 : g a = 0 := by simp [hg]
  rw [g0] at h
  have e : stepEntropy a b = log (cosh b) - log (cosh a) - tanh a * (b - a) := by
    unfold stepEntropy
    rw [log_div (cosh_pos b).ne' (cosh_pos a).ne']
  rw [e]
  have hb : g b = log (cosh b) - log (cosh a) - tanh a * (b - a) - (gd b - gd a) ^ 2 / 2 := rfl
  linarith

/-- **The bound for all `N`.** Any increasing schedule of `N` steps from rapidity `0` produces
entropy at least `(gd η_N)² / (2 N)`. -/
theorem sum_stepEntropy_ge (η : ℕ → ℝ) (hmono : Monotone η) (h0 : η 0 = 0) {N : ℕ} (hN : 0 < N) :
    gd (η N) ^ 2 / (2 * N) ≤ ∑ i ∈ Finset.range N, stepEntropy (η i) (η (i + 1)) := by
  have hnn : ∀ i, 0 ≤ η i := fun i => by rw [← h0]; exact hmono (Nat.zero_le i)
  have hsum : ∑ i ∈ Finset.range N, (gd (η (i + 1)) - gd (η i)) = gd (η N) := by
    rw [Finset.sum_range_sub (fun i => gd (η i)) N, h0]
    simp [gd]
  have hcs : (∑ i ∈ Finset.range N, (gd (η (i + 1)) - gd (η i))) ^ 2
      ≤ (Finset.range N).card * ∑ i ∈ Finset.range N, (gd (η (i + 1)) - gd (η i)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hsum, Finset.card_range] at hcs
  have hpt : ∑ i ∈ Finset.range N, (gd (η (i + 1)) - gd (η i)) ^ 2 / 2
      ≤ ∑ i ∈ Finset.range N, stepEntropy (η i) (η (i + 1)) :=
    Finset.sum_le_sum fun i _ => stepEntropy_ge (hnn i) (hmono (Nat.le_succ i))
  rw [← Finset.sum_div] at hpt
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- A step in rapidity is the same relative entropy, written in visibility. -/
theorem relEntropyV_tanh (a b : ℝ) : relEntropyV (tanh a) (tanh b) = stepEntropy a b := by
  have hT : ∀ x : ℝ, tanh x ∈ Ioo (-1:ℝ) 1 := fun x => ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  have hc : ∀ x : ℝ, log (gammaSq (tanh x)) = 2 * log (cosh x) := by
    intro x
    have h : gammaSq (tanh x) = cosh x ^ 2 := by
      unfold gammaSq
      rw [Real.tanh_eq_sinh_div_cosh]
      have hcx := (cosh_pos x).ne'
      have hk : cosh x ^ 2 - sinh x ^ 2 = 1 := by nlinarith [Real.cosh_sq x]
      field_simp
      nlinarith [hk]
    rw [h, log_pow]; push_cast; ring
  rw [relEntropyV_eq (hT a) (hT b), hc a, hc b, Real.artanh_tanh, Real.artanh_tanh]
  unfold stepEntropy
  rw [log_div (cosh_pos b).ne' (cosh_pos a).ne']
  ring

end FisherLorentz
