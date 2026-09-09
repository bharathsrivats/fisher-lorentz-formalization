/-
# Domain identities of the Fisher-Lorentz corpus

Machine-checked forms of the central identity of three further published
papers, each reduced to the binary Fisher information of `Basic.lean`.

* BioSystems 266, 105847 (2026): the Hill coefficient identity.
* Theory in Biosciences (R1): the Wright-Fisher drift identity.
* Three Fisher-Rao Identities, EJPAM: the Jeffreys prior density.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import FisherLorentz.Basic

namespace FisherLorentz

open Real Set

/-! ## BioSystems: the Hill coefficient is Fisher information -/

/-- Fractional occupancy in the log-dose coordinate `θ = ln(c/K_d)`:
the logistic `p(θ) = 1/(1 + e^{-n θ})`. -/
noncomputable def hillOccupancy (n θ : ℝ) : ℝ := 1 / (1 + Real.exp (-(n * θ)))

/-- Occupancy is `1/2` at the midpoint. -/
@[simp] theorem hillOccupancy_zero (n : ℝ) : hillOccupancy n 0 = 1 / 2 := by
  simp [hillOccupancy]
  norm_num

/-- Occupancy lies strictly in `(0,1)`. -/
theorem hillOccupancy_mem (n θ : ℝ) : hillOccupancy n θ ∈ Ioo (0:ℝ) 1 := by
  have he : 0 < Real.exp (-(n * θ)) := Real.exp_pos _
  constructor
  · simp only [hillOccupancy]; positivity
  · simp only [hillOccupancy]
    rw [div_lt_one (by linarith)]
    linarith

/-- The Fisher information of a Bernoulli observation whose success
probability is `p`, in a parameter with `dp/dθ = n p (1-p)`:
`I_θ = (dp/dθ)² / (p(1-p)) = n² p (1-p)`. -/
noncomputable def hillFisher (n θ : ℝ) : ℝ :=
  let p := hillOccupancy n θ
  (n * p * (1 - p)) ^ 2 / (p * (1 - p))

/-- **The Hill identity.** `I_θ = n² p(1-p)` for every `θ`. -/
theorem hillFisher_eq (n θ : ℝ) :
    hillFisher n θ = n ^ 2 * hillOccupancy n θ * (1 - hillOccupancy n θ) := by
  have hp := hillOccupancy_mem n θ
  have h0 : hillOccupancy n θ ≠ 0 := ne_of_gt hp.1
  have h1 : (1 : ℝ) - hillOccupancy n θ ≠ 0 := by
    have := hp.2; intro hc; linarith [sub_eq_zero.mp hc]
  simp only [hillFisher]
  field_simp

/-- **BioSystems main result.** At the Hill midpoint the Fisher information
is exactly `n_H² / 4`. -/
theorem hillFisher_midpoint (n : ℝ) : hillFisher n 0 = n ^ 2 / 4 := by
  rw [hillFisher_eq, hillOccupancy_zero]
  ring

/-- Worked value: `n_H = 2.8` (hemoglobin) gives `1.96`. -/
example : hillFisher 2.8 0 = 1.96 := by
  rw [hillFisher_midpoint]; norm_num

/-- Worked value: `n_H = 10.3` (bacterial flagellar motor) gives `26.5225`. -/
example : hillFisher 10.3 0 = 26.5225 := by
  rw [hillFisher_midpoint]; norm_num

/-! ## PopGen: Wright-Fisher drift is inverse Fisher information -/

/-- The one-generation Wright-Fisher variance of the visibility coordinate,
`Var(ΔV) = 4 p(1-p) / (2 N_e)`, written directly from the binomial. -/
noncomputable def wfVariance (V : ℝ) (Ne : ℝ) : ℝ :=
  4 * (pPlus V * pMinus V) / (2 * Ne)

/-- **PopGen Theorem 1.** `Var(ΔV | V) = 1 / (2 N_e γ²(V))`.
Genetic drift is inverse Fisher information on the allele-frequency
manifold. -/
theorem wfVariance_eq_inv_gammaSq {V Ne : ℝ} (h : V ∈ Ioo (-1:ℝ) 1)
    (hNe : 0 < Ne) :
    wfVariance V Ne = 1 / (2 * Ne * gammaSq V) := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  have hNe' : Ne ≠ 0 := ne_of_gt hNe
  simp only [wfVariance, gammaSq, pPlus, pMinus]
  field_simp
  ring

/-! ## EJPAM: the Jeffreys prior on the binary manifold -/

/-- The Lorentz factor `γ(V) = 1/√(1-V²)`. -/
noncomputable def gamma (V : ℝ) : ℝ := 1 / Real.sqrt (1 - V ^ 2)

/-- `γ² is the square of γ`, tying `Basic.gammaSq` to the square root form. -/
theorem gamma_sq_eq_gammaSq {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    gamma V ^ 2 = gammaSq V := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  simp only [gamma, gammaSq, div_pow, one_pow]
  rw [Real.sq_sqrt hpos.le]

/-- The Jeffreys prior density on the binary manifold is `γ(V)/π`,
i.e. the square root of the Fisher information, normalised. -/
noncomputable def jeffreysDensity (V : ℝ) : ℝ := gamma V / Real.pi

/-- The Jeffreys density is the normalised root of the Fisher information. -/
theorem jeffreysDensity_eq_sqrt_fisher {V : ℝ} (h : V ∈ Ioo (-1:ℝ) 1) :
    jeffreysDensity V = Real.sqrt (fisherInfo V) / Real.pi := by
  have hpos : (0:ℝ) < 1 - V ^ 2 := by nlinarith [h.1, h.2]
  have hg : (0:ℝ) < gamma V := by
    simp only [gamma]; positivity
  rw [fisherInfo_eq_gammaSq h, ← gamma_sq_eq_gammaSq h,
      Real.sqrt_sq hg.le, jeffreysDensity]

end FisherLorentz
