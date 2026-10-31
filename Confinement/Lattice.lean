/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

Lattice gauge theory on the torus `(ℤ/L)ⁿ × ℤ/Lₜ`, spacetime dimension `d = n + 1`, for a gauge
group `G` with a normalised character `χ`. The Wilson weight is `exp (J ∑ₚ Re χ(Qₚ))`; for
`G = SU(N)` and `χ = Tr / N`, the coupling `J` is the conventional `β_W = 2N/g²`.

Time is singled out only so that the slab structure is visible in the types: a link is either
horizontal (in a time slice) or vertical (between consecutive slices), and a plaquette is either
horizontal (four horizontal links) or vertical (two vertical links in the same slab, two
horizontal links).
-/
import Confinement.Expansion

open MeasureTheory

namespace Confinement

/-- Spatial sites. -/
abbrev Space (n L : ℕ) := Fin n → ZMod L

/-- A link: `Sum.inl (x, t, μ)` runs from `(x, t)` to `(x + e μ, t)`, and `Sum.inr (x, t)` runs
from `(x, t)` to `(x, t + 1)`. -/
abbrev Link (n L Lt : ℕ) := (Space n L × ZMod Lt × Fin n) ⊕ (Space n L × ZMod Lt)

/-- Labels of the vertical plaquettes. -/
abbrev VP (n L Lt : ℕ) := Space n L × ZMod Lt × Fin n

/-- Labels of the horizontal plaquettes, with `μ < ν` imposed by a filter in the action. -/
abbrev HP (n L Lt : ℕ) := Space n L × ZMod Lt × Fin n × Fin n

variable {n L Lt : ℕ}

/-- The unit vector in direction `μ`. -/
def e (μ : Fin n) : Space n L := Pi.single μ 1

variable {G : Type*} [Group G]

/-- A horizontal link variable. -/
def hor (U : Link n L Lt → G) (x : Space n L) (t : ZMod Lt) (μ : Fin n) : G := U (Sum.inl (x, t, μ))

/-- A vertical link variable. -/
def ver (U : Link n L Lt → G) (x : Space n L) (t : ZMod Lt) : G := U (Sum.inr (x, t))

/-- Holonomy of a plaquette in a time slice. -/
def Qh (U : Link n L Lt → G) (p : HP n L Lt) : G :=
  let (x, t, μ, ν) := p
  hor U x t μ * hor U (x + e μ) t ν * (hor U (x + e ν) t μ)⁻¹ * (hor U x t ν)⁻¹

/-- Holonomy of the vertical plaquette `(x, t) → (x, t+1) → (x+μ, t+1) → (x+μ, t) → (x, t)`. -/
def Qv (U : Link n L Lt → G) (p : VP n L Lt) : G :=
  let (x, t, μ) := p
  ver U x t * hor U x (t + 1) μ * (ver U (x + e μ) t)⁻¹ * (hor U x t μ)⁻¹

/-- The ordered product of the vertical links from `(x, t₀)` up `T` steps. -/
def vline (U : Link n L Lt → G) (x : Space n L) (t₀ : ZMod Lt) (T : ℕ) : G :=
  ((List.range T).map fun i : ℕ => ver U x (t₀ + (i : ZMod Lt))).prod

/-- The ordered product of the horizontal links from `x` along `μ`, `R` steps, at time `t`. -/
def hline (U : Link n L Lt → G) (x : Space n L) (t : ZMod Lt) (μ : Fin n) (R : ℕ) : G :=
  ((List.range R).map fun j : ℕ => hor U (x + (j : ZMod L) • e μ) t μ).prod

/-- The holonomy around the `R × T` rectangle with corner `(x, t₀)` in the plane of `μ` and time:
up at `x`, across at `t₀ + T`, down at `x + R e μ`, back at `t₀`. -/
def rectangle (U : Link n L Lt → G) (x : Space n L) (t₀ : ZMod Lt) (μ : Fin n) (R T : ℕ) : G :=
  vline U x t₀ T * hline U x (t₀ + (T : ZMod Lt)) μ R *
    (vline U (x + (R : ZMod L) • e μ) t₀ T)⁻¹ * (hline U x t₀ μ R)⁻¹

variable [NeZero L] [NeZero Lt]

/-- The Wilson action of the plaquettes in time slices, `μ < ν`. -/
noncomputable def actionH (χ : G → ℂ) (U : Link n L Lt → G) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (HP n L Lt)).filter (fun p => p.2.2.1 < p.2.2.2), (χ (Qh U p)).re

/-- The Wilson action of the vertical plaquettes. -/
noncomputable def actionV (χ : G → ℂ) (U : Link n L Lt → G) : ℝ :=
  ∑ p : VP n L Lt, (χ (Qv U p)).re

/-- The Wilson weight `exp (J ∑ₚ Re χ(Qₚ))`, summed over every plaquette once. -/
noncomputable def wilsonWeight (χ : G → ℂ) (J : ℝ) (U : Link n L Lt → G) : ℝ :=
  Real.exp (J * (actionH χ U + actionV χ U))

variable [MeasurableSpace G]

/-- The product of the single-link measures. -/
noncomputable def linkMeasure (μ₀ : Measure G) : Measure (Link n L Lt → G) :=
  Measure.pi fun _ => μ₀

/-- The Gibbs expectation of `f` for the Wilson weight. -/
noncomputable def gibbs (μ₀ : Measure G) (χ : G → ℂ) (J : ℝ) (f : (Link n L Lt → G) → ℂ) : ℂ :=
  (∫ U : Link n L Lt → G, f U * ((wilsonWeight χ J U : ℝ) : ℂ) ∂(linkMeasure μ₀)) /
    ((∫ U : Link n L Lt → G, wilsonWeight χ J U ∂(linkMeasure μ₀) : ℝ) : ℂ)

end Confinement
