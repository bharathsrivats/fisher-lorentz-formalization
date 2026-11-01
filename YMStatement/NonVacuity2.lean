import Mathlib
import YMStatement.NonVacuity
import YMStatement.Statement

/-!
# Non-vacuity of the full gauge-group domain (attack A1, instances included)

`NonVacuity.lean` shows that the Lie-algebra predicate is satisfiable. Here we close the remaining
gap: the topological closure `SO3bar` of `SO3gen` in `U(3)` is a compact, connected Hausdorff
topological group whose Lie algebra is `so(3)`, so `IsCompactSimpleGaugeGroup SO3bar` holds and the
main statement specialises to a concrete existence claim for it.
-/

noncomputable section

namespace YMStatement

open scoped Matrix

/-- The defining representation of a subgroup of `U(3)`. -/
def subgroupRep (H : Subgroup (Matrix.unitaryGroup (Fin 3) ℂ)) : FaithfulUnitaryRep H 3 where
  toHom := H.subtype
  continuous_toHom := continuous_subtype_val
  injective_toHom := Subtype.val_injective

/-- Unitary matrices with real entries. -/
def realSubgroup : Subgroup (Matrix.unitaryGroup (Fin 3) ℂ) where
  carrier := {u | (u : M3)ᴴ = (u : M3)ᵀ}
  mul_mem' := by
    intro u v hu hv
    have hu' : (u : M3)ᴴ = (u : M3)ᵀ := hu
    have hv' : (v : M3)ᴴ = (v : M3)ᵀ := hv
    change ((u : M3) * (v : M3))ᴴ = ((u : M3) * (v : M3))ᵀ
    rw [Matrix.conjTranspose_mul, Matrix.transpose_mul, hu', hv']
  one_mem' := by
    change (1 : M3)ᴴ = (1 : M3)ᵀ
    simp
  inv_mem' := by
    intro u hu
    have hu' : (u : M3)ᴴ = (u : M3)ᵀ := hu
    change (star (u : M3))ᴴ = (star (u : M3))ᵀ
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    ext i j
    have h := congrFun (congrFun hu' j) i
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h ⊢
    exact h.symm

theorem isClosed_realSubgroup :
    IsClosed (realSubgroup : Set (Matrix.unitaryGroup (Fin 3) ℂ)) := by
  have hc : Continuous fun u : Matrix.unitaryGroup (Fin 3) ℂ => (u : M3) := continuous_subtype_val
  exact isClosed_eq (Continuous.matrix_conjTranspose hc) (Continuous.matrix_transpose hc)

theorem SO3gen_le_real : SO3gen ≤ realSubgroup :=
  fun _ hu => conjTranspose_eq_transpose_of_mem hu

/-- The closure of `SO3gen` in `U(3)` (mathematically `SO(3)`). -/
def SO3bar : Subgroup (Matrix.unitaryGroup (Fin 3) ℂ) := SO3gen.topologicalClosure

theorem SO3bar_le_real : SO3bar ≤ realSubgroup := by
  first
  | exact Subgroup.topologicalClosure_minimal SO3gen SO3gen_le_real isClosed_realSubgroup
  | exact Subgroup.topologicalClosure_minimal SO3gen_le_real isClosed_realSubgroup

theorem lieAlgebraCarrier_eq_so3 (H : Subgroup (Matrix.unitaryGroup (Fin 3) ℂ))
    (hlow : SO3gen ≤ H) (hreal : ∀ u ∈ H, (u : M3)ᴴ = (u : M3)ᵀ) :
    (subgroupRep H).lieAlgebraCarrier = so3Carrier := by
  ext X
  constructor
  · intro hX
    have key : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ unitary M3 ∧
        (NormedSpace.exp (t • X))ᴴ = (NormedSpace.exp (t • X))ᵀ := by
      intro t
      obtain ⟨g, hg⟩ := hX t
      have hg' : ((g : Matrix.unitaryGroup (Fin 3) ℂ) : M3) = NormedSpace.exp (t • X) := hg
      rw [← hg']
      exact ⟨(g : Matrix.unitaryGroup (Fin 3) ℂ).2, hreal _ g.2⟩
    have hct : ∀ t : ℝ, (t • X)ᴴ = t • Xᴴ := fun t => by
      rw [Matrix.conjTranspose_smul, star_trivial]
    have htt : ∀ t : ℝ, (t • X)ᵀ = t • Xᵀ := fun t => Matrix.transpose_smul t X
    refine ⟨eq_of_exp_smul_eq fun t => ?_, eq_of_exp_smul_eq fun t => ?_⟩
    · rw [← hct, ← htt, Matrix.exp_conjTranspose, Matrix.exp_transpose]
      exact (key t).2
    · obtain ⟨hu, -⟩ := key t
      have hsm : (NormedSpace.exp (t • X))ᴴ * NormedSpace.exp (t • X) = 1 := by
        have := (Unitary.mem_iff.mp hu).1
        rwa [Matrix.star_eq_conjTranspose] at this
      have hinv := Matrix.inv_eq_left_inv hsm
      rw [← hct, Matrix.exp_conjTranspose, ← hinv, ← Matrix.exp_neg, smul_neg]
  · intro hX t
    exact ⟨⟨⟨NormedSpace.exp (t • X), exp_mem_unitary_of_so3 (so3Carrier_smul hX t)⟩,
      hlow (Subgroup.subset_closure ⟨t • X, so3Carrier_smul hX t, rfl⟩)⟩, rfl⟩

theorem isCompact_unitary3 : IsCompact (unitary M3 : Set M3) := by
  have hclosed : IsClosed (unitary M3 : Set M3) := isClosed_unitary
  letI : NormedAddCommGroup M3 := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ M3 := Matrix.normedSpace
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_iff_subset_closedBall (0 : M3)).2 ⟨1, fun U hU => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Matrix.norm_le_iff zero_le_one).2 fun i j => entry_norm_bound_of_unitary hU i j

instance compactSpace_unitaryGroup3 : CompactSpace (Matrix.unitaryGroup (Fin 3) ℂ) := by
  have h := isCompact_iff_compactSpace.mp isCompact_unitary3
  exact h

instance compactSpace_SO3bar : CompactSpace SO3bar := by
  have h := isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure SO3gen).isCompact
  exact h

theorem continuous_exp_smul (X : M3) : Continuous fun s : ℝ => NormedSpace.exp (s • X) := by
  letI : NormedRing M3 := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ M3 := Matrix.linftyOpNormedAlgebra
  exact continuous_iff_continuousAt.2 fun s =>
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s).continuousAt

theorem isPreconnected_SO3gen : IsPreconnected (SO3gen : Set (Matrix.unitaryGroup (Fin 3) ℂ)) := by
  refine isPreconnected_of_forall 1 fun y hy => ?_
  have hy' : y ∈ Subgroup.closure so3Generators := hy
  clear hy
  induction hy' using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨X, hX, hux⟩ := hu
    let p : ℝ → Matrix.unitaryGroup (Fin 3) ℂ := fun s =>
      ⟨NormedSpace.exp (s • X), exp_mem_unitary_of_so3 (so3Carrier_smul hX s)⟩
    have hp : Continuous p := (continuous_exp_smul X).subtype_mk _
    refine ⟨p '' Set.Icc 0 1, ?_, ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩,
      isPreconnected_Icc.image p hp.continuousOn⟩
    · rintro _ ⟨s, -, rfl⟩
      exact Subgroup.subset_closure ⟨s • X, so3Carrier_smul hX s, rfl⟩
    · apply Subtype.ext
      simp [p]
    · apply Subtype.ext
      simp [p, hux]
  | one =>
    exact ⟨{1}, by simpa using SO3gen.one_mem, rfl, rfl, isPreconnected_singleton⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨tx, htx, h1x, hxx, hpx⟩ := ihx
    obtain ⟨ty, hty, h1y, hyy, hpy⟩ := ihy
    refine ⟨tx ∪ (fun z => x * z) '' ty, ?_, Or.inl h1x, Or.inr ⟨y, hyy, rfl⟩, ?_⟩
    · rintro z (hz | ⟨w, hw, rfl⟩)
      · exact htx hz
      · exact SO3gen.mul_mem hx (hty hw)
    · exact IsPreconnected.union x hxx ⟨1, h1y, mul_one x⟩ hpx
        (hpy.image _ (continuous_mul_left x).continuousOn)
  | inv x hx ihx =>
    obtain ⟨tx, htx, h1x, hxx, hpx⟩ := ihx
    refine ⟨(fun z => x⁻¹ * z) '' tx, ?_, ⟨x, hxx, inv_mul_cancel x⟩, ⟨1, h1x, mul_one x⁻¹⟩,
      hpx.image _ (continuous_mul_left x⁻¹).continuousOn⟩
    rintro _ ⟨w, hw, rfl⟩
    exact SO3gen.mul_mem (SO3gen.inv_mem hx) (htx hw)

instance connectedSpace_SO3bar : ConnectedSpace SO3bar := by
  have hconn : IsConnected (SO3gen : Set (Matrix.unitaryGroup (Fin 3) ℂ)) :=
    ⟨⟨1, SO3gen.one_mem⟩, isPreconnected_SO3gen⟩
  have h2 := hconn.closure
  rw [← Subgroup.topologicalClosure_coe] at h2
  exact isConnected_iff_connectedSpace.mp h2

/-- `SO3bar ≅ SO(3)` is a compact simple gauge group in the sense of the statement. -/
theorem SO3bar_isCompactSimpleGaugeGroup : IsCompactSimpleGaugeGroup SO3bar :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨3, subgroupRep SO3bar, so3, by
      rw [lieAlgebraCarrier_eq_so3 SO3bar (Subgroup.le_topologicalClosure SO3gen)
        (fun u hu => SO3bar_le_real hu)]
      rfl, so3_isSimple⟩⟩

/-- **Non-vacuity of the gauge-group domain.** -/
theorem exists_compactSimpleGaugeGroup :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G), IsCompactSimpleGaugeGroup G :=
  ⟨SO3bar, inferInstance, inferInstance, SO3bar_isCompactSimpleGaugeGroup⟩

/-- The main statement is not vacuous: it implies a concrete existence claim for `SO3bar`. -/
theorem specialize_SO3 (h : YangMillsExistenceAndMassGap) :
    letI : MeasurableSpace SO3bar := borel SO3bar
    haveI : BorelSpace SO3bar := ⟨rfl⟩
    ∃ S : SchwingerFamily, IsQuantumYangMillsTheory SO3bar S ∧ HasFiniteMass S ∧
      ∃ Δ : ℝ, 0 < Δ ∧ HasMassGap S Δ := by
  letI : MeasurableSpace SO3bar := borel SO3bar
  haveI : BorelSpace SO3bar := ⟨rfl⟩
  exact h SO3bar SO3bar_isCompactSimpleGaugeGroup.2.2.2.2

end YMStatement
