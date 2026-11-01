import Mathlib

/-!
# Compact simple gauge groups

Clay (Jaffe-Witten, section 4, clay_ym.txt lines 277-278) quantifies over every compact simple
gauge group G.

A compact Lie group has a faithful finite-dimensional unitary representation (Peter-Weyl), and
its Lie algebra is recovered from the image as `{X | ∀ t, exp (t X) ∈ ρ(G)}`. We use that
description so that "simple" means `LieAlgebra.IsSimple ℝ 𝔤` for a genuine matrix Lie algebra
with the commutator bracket, rather than an unconstrained type with no bracket (a defect of
earlier formalisations).
-/

noncomputable section

namespace YMStatement

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A faithful continuous unitary representation `ρ : G → U(n)`. -/
structure FaithfulUnitaryRep (G : Type*) [Group G] [TopologicalSpace G] (n : ℕ) where
  toHom : G →* Matrix.unitaryGroup (Fin n) ℂ
  continuous_toHom : Continuous toHom
  injective_toHom : Function.Injective toHom

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}

/-- The image `ρ(G)` as a set of complex `n × n` matrices. -/
def FaithfulUnitaryRep.image (ρ : FaithfulUnitaryRep G n) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  Set.range fun g : G => ((ρ.toHom g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)

/-- The real Lie algebra of the matrix group `ρ(G)`: all `X` with `exp (t • X) ∈ ρ(G)` for every
real `t`. -/
def FaithfulUnitaryRep.lieAlgebraCarrier (ρ : FaithfulUnitaryRep G n) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ ρ.image}

/-- The Lie algebra of `G`, read off a faithful unitary representation, is a simple real Lie
algebra. The existential over the Lie subalgebra `𝔤` only asserts closure under the commutator,
which holds for every closed subgroup of `U(n)`; it does not enlarge or shrink the class. -/
def HasSimpleLieAlgebra (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (n : ℕ) (ρ : FaithfulUnitaryRep G n) (𝔤 : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ)),
    (𝔤 : Set (Matrix (Fin n) (Fin n) ℂ)) = ρ.lieAlgebraCarrier ∧ LieAlgebra.IsSimple ℝ 𝔤

/-- A compact simple gauge group: a compact connected Hausdorff topological group whose Lie
algebra is simple. (Connectedness follows the standard convention for simple Lie groups.) -/
def IsCompactSimpleGaugeGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  IsTopologicalGroup G ∧ CompactSpace G ∧ ConnectedSpace G ∧ T2Space G ∧ HasSimpleLieAlgebra G

/-- If `exp (s • X)` and `exp (t • Y)` commute for all real `s, t`, then `X` and `Y` commute. -/
theorem commute_of_exp_commute {X Y : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ s t : ℝ, NormedSpace.exp (s • X) * NormedSpace.exp (t • Y) =
      NormedSpace.exp (t • Y) * NormedSpace.exp (s • X)) :
    X * Y = Y * X := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have step1 : ∀ t : ℝ, X * NormedSpace.exp (t • Y) = NormedSpace.exp (t • Y) * X := by
    intro t
    have d1 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * NormedSpace.exp (t • Y))
        (X * NormedSpace.exp ((0 : ℝ) • X) * NormedSpace.exp (t • Y)) 0 :=
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (0 : ℝ)).mul_const _
    have d2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (t • Y) * NormedSpace.exp (s • X))
        (NormedSpace.exp (t • Y) * (X * NormedSpace.exp ((0 : ℝ) • X))) 0 :=
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (0 : ℝ)).const_mul _
    have heq : (fun s : ℝ => NormedSpace.exp (s • X) * NormedSpace.exp (t • Y)) =
        (fun s : ℝ => NormedSpace.exp (t • Y) * NormedSpace.exp (s • X)) :=
      funext fun s => h s t
    rw [heq] at d1
    have := d1.unique d2
    simpa [NormedSpace.exp_zero] using this
  have d1 : HasDerivAt (fun t : ℝ => X * NormedSpace.exp (t • Y))
      (X * (Y * NormedSpace.exp ((0 : ℝ) • Y))) 0 :=
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (0 : ℝ)).const_mul _
  have d2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y) * X)
      (Y * NormedSpace.exp ((0 : ℝ) • Y) * X) 0 :=
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (0 : ℝ)).mul_const _
  have heq : (fun t : ℝ => X * NormedSpace.exp (t • Y)) =
      (fun t : ℝ => NormedSpace.exp (t • Y) * X) := funext step1
  rw [heq] at d1
  have := d1.unique d2
  simpa [NormedSpace.exp_zero, mul_assoc] using this

/-- **Anti-toy (U(1) and every abelian group).** A commutative group never has a simple Lie
algebra in the sense of `HasSimpleLieAlgebra`, for any faithful unitary representation. In
particular `U(1)` is excluded. -/
theorem not_hasSimpleLieAlgebra_of_comm (hcomm : ∀ a b : G, a * b = b * a) :
    ¬ HasSimpleLieAlgebra G := by
  rintro ⟨n, ρ, 𝔤, hcarrier, hsimple⟩
  apply hsimple.non_abelian
  have hcomm_img : ∀ A B : Matrix (Fin n) (Fin n) ℂ, A ∈ ρ.image → B ∈ ρ.image →
      A * B = B * A := by
    rintro _ _ ⟨g, rfl⟩ ⟨g', rfl⟩
    have e : ρ.toHom (g * g') = ρ.toHom (g' * g) := by rw [hcomm]
    have := congrArg (fun u : Matrix.unitaryGroup (Fin n) ℂ => (u : Matrix (Fin n) (Fin n) ℂ)) e
    simpa [map_mul] using this
  constructor
  intro x y
  have hx : (x : Matrix (Fin n) (Fin n) ℂ) ∈ ρ.lieAlgebraCarrier := by
    rw [← hcarrier]; exact x.2
  have hy : (y : Matrix (Fin n) (Fin n) ℂ) ∈ ρ.lieAlgebraCarrier := by
    rw [← hcarrier]; exact y.2
  have key : (x : Matrix (Fin n) (Fin n) ℂ) * y = y * x :=
    commute_of_exp_commute fun s t => hcomm_img _ _ (hx s) (hy t)
  apply Subtype.ext
  simp [LieSubalgebra.coe_bracket, Ring.lie_def, key]

theorem not_isCompactSimpleGaugeGroup_of_comm (hcomm : ∀ a b : G, a * b = b * a) :
    ¬ IsCompactSimpleGaugeGroup G :=
  fun h => not_hasSimpleLieAlgebra_of_comm hcomm h.2.2.2.2

/-- `U(1)` (the unit circle) is not a compact simple gauge group. -/
theorem circle_not_isCompactSimpleGaugeGroup : ¬ IsCompactSimpleGaugeGroup Circle :=
  not_isCompactSimpleGaugeGroup_of_comm fun a b => mul_comm a b

end YMStatement
