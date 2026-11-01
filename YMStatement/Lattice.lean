import Mathlib
import YMStatement.GaugeGroup
import YMStatement.Euclidean

/-!
# Wilson's lattice approximation and the continuum-limit clause

Clay (Jaffe-Witten, section 6.5, clay_ym.txt lines 540-545) describes Wilson's lattice approach:
a gauge-invariant lattice action, a finite-dimensional integral for compact G on a compact
lattice, and the task of proving limits of expectations of gauge-invariant observables as the
spacing tends to zero and the volume to infinity.

Footnote 2 (lines 619-621) excludes weak existence by compactness unless properties of the limit,
such as the gap and the axioms, are also established. The clause below allows a limit along a sequence; the main statement demands the axioms and the gap
for that limit.

The curvature is not free data: it is the plaquette holonomy computed from the link variables.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap

noncomputable section

namespace YMStatement

section Lattice

variable (G : Type) [Group G] [TopologicalSpace G]

/-- Sites of the periodic lattice `(ℤ/(L+1)ℤ)⁴`. -/
abbrev Site (L : ℕ) := Fin 4 → Fin (L + 1)

/-- Positively oriented links `(x, μ)`, from `x` to `x + e_μ`. -/
abbrev Link (L : ℕ) := Site L × Fin 4

/-- A lattice gauge field: a group element on every positively oriented link. -/
abbrev LatticeGaugeField (L : ℕ) := Link L → G

variable {G}

/-- The neighbouring site `x + e_μ` (periodic boundary conditions). -/
def siteShift {L : ℕ} (x : Site L) (μ : Fin 4) : Site L :=
  Function.update x μ (x μ + 1)

/-- Plaquette holonomy `U_{μν}(x) = U(x,μ) U(x+e_μ,ν) U(x+e_ν,μ)⁻¹ U(x,ν)⁻¹`: the lattice curvature. -/
def plaquette {L : ℕ} (U : LatticeGaugeField G L) (x : Site L) (μ ν : Fin 4) : G :=
  U (x, μ) * U (siteShift x μ, ν) * (U (siteShift x ν, μ))⁻¹ * (U (x, ν))⁻¹

/-- Wilson plaquette energy `1 - Re tr ρ(U_{μν}(x)) / n`. -/
def plaquetteEnergy {n L : ℕ} (ρ : FaithfulUnitaryRep G n) (U : LatticeGaugeField G L)
    (x : Site L) (μ ν : Fin 4) : ℝ :=
  1 - (Matrix.trace ((ρ.toHom (plaquette U x μ ν) : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ)).re / n

/-- Lattice Lagrangian density `∑_{μ<ν} (1 - Re tr ρ(U_{μν}(x))/n)`; for small spacing it is a
positive multiple of `Tr F_{μν} F_{μν}(x)` plus higher-order terms. -/
def actionDensity {n L : ℕ} (ρ : FaithfulUnitaryRep G n) (U : LatticeGaugeField G L)
    (x : Site L) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then plaquetteEnergy ρ U x μ ν else 0

/-- Wilson action `S_β(U) = β ∑ₓ ∑_{μ<ν} (1 - Re tr ρ(U_{μν}(x))/n)`. -/
def wilsonAction {n L : ℕ} (ρ : FaithfulUnitaryRep G n) (β : ℝ) (U : LatticeGaugeField G L) : ℝ :=
  β * ∑ x : Site L, actionDensity ρ U x

variable (G) [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Normalised Haar measure on the compact group `G`. -/
def haarProb : Measure G := Measure.haarMeasure ⊤

/-- Product Haar measure on lattice gauge fields. -/
def latticeHaar (L : ℕ) : Measure (LatticeGaugeField G L) :=
  Measure.pi fun _ : Link L => haarProb G

variable {G}

/-- Expectation in the finite-volume Wilson measure `Z⁻¹ e^{-S_β(U)} ∏_ℓ dU_ℓ`. -/
def wilsonExpectation {n : ℕ} (ρ : FaithfulUnitaryRep G n) (L : ℕ) (β : ℝ)
    (Φ : LatticeGaugeField G L → ℝ) : ℝ :=
  (∫ U, Φ U * Real.exp (-wilsonAction ρ β U) ∂latticeHaar G L) /
    ∫ U, Real.exp (-wilsonAction ρ β U) ∂latticeHaar G L

/-- The point of `ℝ⁴` representing site `x` at spacing `ε`, in a periodic box centred at `0`. -/
def embedSite (ε : ℝ) {L : ℕ} (x : Site L) : E4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm fun μ => ε * (((x μ : ℕ) : ℝ) - (L : ℝ) / 2)

/-- Renormalised, vacuum-subtracted lattice Schwinger functions of the Lagrangian density smeared
with `F`: `E[ε^{4m} ∑_{x₁…xₘ} F(εx₁,…,εxₘ) ∏ᵢ Z (O(xᵢ) - E O(xᵢ))]`. -/
def latticeSchwinger {n : ℕ} (ρ : FaithfulUnitaryRep G n) (L : ℕ) (β ε Z : ℝ) (m : ℕ)
    (F : TestFn m) : ℝ :=
  wilsonExpectation ρ L β fun U =>
    ε ^ (4 * m) * ∑ xs : Fin m → Site L,
      F (fun i => embedSite ε (xs i)) *
        ∏ i, Z * (actionDensity ρ U (xs i) -
          wilsonExpectation ρ L β fun V => actionDensity ρ V (xs i))

variable (G)

/-- **Tie to Yang-Mills and to `G`.** `S` is the limit, along some sequence, of renormalised
Wilson lattice Schwinger functions of the Lagrangian density for `G` in a faithful unitary
representation, with spacing `εₖ → 0`, physical box size `(Lₖ + 1) εₖ → ∞`, and bare inverse
coupling `βₖ → ∞` (bare coupling `gₖ → 0`, the asymptotically free regime). -/
def IsWilsonLatticeLimit (S : SchwingerFamily) : Prop :=
  ∃ (n : ℕ) (ρ : FaithfulUnitaryRep G n) (L : ℕ → ℕ) (β ε Z : ℕ → ℝ),
    (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
    Tendsto (fun k => ε k * ((L k : ℝ) + 1)) atTop atTop ∧
    Tendsto β atTop atTop ∧
    ∀ (m : ℕ) (F : TestFn m), VanishesAtCoincidences F →
      Tendsto (fun k => latticeSchwinger ρ (L k) (β k) (ε k) (Z k) m F) atTop (𝓝 (S m F))

end Lattice

end YMStatement
