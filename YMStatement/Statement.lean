import Mathlib
import YMStatement.GaugeGroup
import YMStatement.Euclidean
import YMStatement.Lattice

/-!
# Yang-Mills existence and mass gap (prototype statement, v1)

Clay (Jaffe-Witten, section 4, clay_ym.txt lines 277-280): for every compact simple gauge group G,
prove that a non-trivial quantum Yang-Mills theory exists on R^4 with a mass gap, where existence
includes axiomatic properties at least as strong as Streater-Wightman [45] and
Osterwalder-Schrader [35].

Scope of v1 (see DESIGN.md): the field content is the Lagrangian density `Tr F²` only; the
short-distance clause is the leading logarithm of its two-point function; the construction route
is Wilson's lattice regularisation. These are documented narrowings and broadenings, not silent.
-/

namespace YMStatement

/-- A (Euclidean) quantum Yang-Mills theory for `G` with field content `Tr F²`. -/
structure IsQuantumYangMillsTheory (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (S : SchwingerFamily) : Prop where
  /-- Tie to Yang-Mills and to `G`: continuum limit of Wilson lattice gauge theory. -/
  lattice_limit : IsWilsonLatticeLimit G S
  /-- Axioms at least as strong as OS [35] (hence Wightman [45], by OS II). -/
  os : SatisfiesOS S
  /-- Short-distance agreement with asymptotic freedom (leading log). -/
  asymptotic_freedom : AgreesWithAsymptoticFreedom S

/-- **The prototype statement.** For every compact simple gauge group `G` there is a Euclidean
quantum Yang-Mills theory with finite mass `m < ∞` and a mass gap `Δ > 0`. -/
def YangMillsExistenceAndMassGap : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [ConnectedSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G],
    HasSimpleLieAlgebra G →
      ∃ S : SchwingerFamily, IsQuantumYangMillsTheory G S ∧ HasFiniteMass S ∧
        ∃ Δ : ℝ, 0 < Δ ∧ HasMassGap S Δ

section AntiToy

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The trivial theory is never a witness. -/
theorem trivial_not_witness :
    ¬ (IsQuantumYangMillsTheory G trivialSchwinger ∧ HasFiniteMass trivialSchwinger) :=
  fun h => trivialSchwinger_not_hasFiniteMass h.2

/-- A witness is never invariant along a spatial direction (so it is not a lower-dimensional
model extended trivially to `ℝ⁴`). -/
theorem witness_not_invariantAlong {S : SchwingerFamily} (h : IsQuantumYangMillsTheory G S)
    (hm : HasFiniteMass S) {v : E4} (hv0 : time v = 0) (hv : v ≠ 0) : ¬ IsInvariantAlong S v :=
  fun hinv => not_hasFiniteMass_of_invariantAlong h.os hv0 hv hinv hm

/-- A witness's two-point kernel is never bounded by `B ‖x‖^{-p}` with `p < 8` (free field,
Wick square of the Gaussian free field). -/
theorem witness_kernel_not_le {S : SchwingerFamily} (h : IsQuantumYangMillsTheory G S)
    {K : E4 → ℝ} (hK : IsTwoPointKernel S K) {B p : ℝ} (hp : p < 8) :
    ¬ (∀ᶠ x in nhdsWithin (0 : E4) {0}ᶜ, |K x| ≤ B * ‖x‖ ^ (-p)) :=
  fun hb => not_agreesWithAF_of_kernel_le hK hp hb h.asymptotic_freedom

/-- A witness's two-point kernel never satisfies the bounded-generator lower bound. -/
theorem witness_not_boundedTransfer {S : SchwingerFamily} (h : IsQuantumYangMillsTheory G S)
    {K : E4 → ℝ} (hK : IsTwoPointKernel S K) {M r₀ : ℝ} (hr₀ : 0 < r₀) :
    ¬ (∀ r s : ℝ, 0 < r → 0 ≤ s → r + s < r₀ →
      Real.exp (-M * s) * K (r • e0) ≤ K ((r + s) • e0)) :=
  fun hb => not_agreesWithAF_of_boundedTransfer hK hr₀ hb h.asymptotic_freedom

end AntiToy

/-- Abelian groups, in particular `U(1)`, are outside the quantifier domain. -/
theorem circle_outside_domain : ¬ HasSimpleLieAlgebra Circle :=
  not_hasSimpleLieAlgebra_of_comm fun a b => mul_comm a b

end YMStatement
