/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

The combinatorics of one slab. The spatial torus is a graph; a set `A` of vertical plaquettes
gives, for each time `t`, the subgraph of its bonds in slab `t`. Paths in the torus lift to sets
of vertical plaquettes, and the number of paths from `x` to `x + R e μ` is controlled by walks.
-/
import Confinement.Lattice
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Field.GeomSum

open Finset SimpleGraph

namespace Confinement

variable {n L Lt : ℕ}

section units

lemma e_apply_self (μ : Fin n) : (e μ : Space n L) μ = 1 := by simp [e]

lemma e_apply_ne {μ ν : Fin n} (h : ν ≠ μ) : (e μ : Space n L) ν = 0 := by simp [e, h]

lemma one_ne_zero_zmod (hL : 3 ≤ L) : (1 : ZMod L) ≠ 0 := by
  have : Fact (1 < L) := ⟨by omega⟩
  exact one_ne_zero

lemma two_ne_zero_zmod (hL : 3 ≤ L) : (1 : ZMod L) + 1 ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod L) = 0 := by push_cast; rw [← h]; norm_num
  have := (ZMod.natCast_eq_zero_iff 2 L).mp h2
  have := Nat.le_of_dvd (by norm_num) this
  omega

lemma e_ne_zero (hL : 3 ≤ L) (μ : Fin n) : (e μ : Space n L) ≠ 0 := by
  intro h
  have := congrFun h μ
  rw [e_apply_self] at this
  exact one_ne_zero_zmod hL this

lemma e_inj (hL : 3 ≤ L) {μ ν : Fin n} (h : (e μ : Space n L) = e ν) : μ = ν := by
  by_contra hne
  have := congrFun h μ
  rw [e_apply_self, e_apply_ne hne] at this
  exact one_ne_zero_zmod hL this

lemma e_add_e_ne_zero (hL : 3 ≤ L) (μ ν : Fin n) : (e μ : Space n L) + e ν ≠ 0 := by
  intro h
  have := congrFun h μ
  by_cases hμν : μ = ν
  · subst hμν
    simp only [Pi.add_apply, e_apply_self, Pi.zero_apply] at this
    exact two_ne_zero_zmod hL this
  · simp only [Pi.add_apply, e_apply_self, e_apply_ne hμν, add_zero, Pi.zero_apply] at this
    exact one_ne_zero_zmod hL this

end units

/-- The nearest-neighbour graph of the spatial torus. -/
def torusGraph (n L : ℕ) : SimpleGraph (Space n L) :=
  SimpleGraph.fromRel fun a b => ∃ μ, b = a + e μ

/-- The graph of the vertical plaquettes of `A` in slab `t`. -/
def bondGraph (A : Finset (VP n L Lt)) (t : ZMod Lt) : SimpleGraph (Space n L) :=
  SimpleGraph.fromRel fun a b => ∃ μ, (a, t, μ) ∈ A ∧ b = a + e μ

lemma bondGraph_le (A : Finset (VP n L Lt)) (t : ZMod Lt) : bondGraph A t ≤ torusGraph n L := by
  intro a b h
  rw [bondGraph, SimpleGraph.fromRel_adj] at h
  rw [torusGraph, SimpleGraph.fromRel_adj]
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨μ, -, hμ⟩ | ⟨μ, -, hμ⟩
  · exact Or.inl ⟨μ, hμ⟩
  · exact Or.inr ⟨μ, hμ⟩

/-- A plaquette of `A` joins its two legs in the bond graph. -/
lemma bondGraph_adj_of_mem (hL : 3 ≤ L) {A : Finset (VP n L Lt)} {v : Space n L} {t : ZMod Lt}
    {μ : Fin n} (h : (v, t, μ) ∈ A) : (bondGraph A t).Adj v (v + e μ) := by
  rw [bondGraph, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨μ, h, rfl⟩⟩
  intro hv
  apply e_ne_zero hL μ
  simpa using hv.symm

/-- An edge `{v, v + e μ}` of the bond graph comes from the plaquette `(v, t, μ)` itself. -/
lemma mem_of_bondGraph_adj (hL : 3 ≤ L) {A : Finset (VP n L Lt)} {v : Space n L} {t : ZMod Lt}
    {μ : Fin n} (h : (bondGraph A t).Adj v (v + e μ)) : (v, t, μ) ∈ A := by
  rw [bondGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨ν, hν, hνe⟩ | ⟨ν, -, hνe⟩
  · have : (e μ : Space n L) = e ν := by simpa using hνe
    rwa [e_inj hL this]
  · exfalso
    apply e_add_e_ne_zero hL μ ν
    have : v + (e μ + e ν) = v := by rw [← add_assoc]; exact hνe.symm
    simpa using this

variable [NeZero L] [NeZero Lt]

open Classical in
/-- The vertical plaquettes of slab `t` lying over the edges of a walk in the torus. -/
noncomputable def lift (t : ZMod Lt) {x y : Space n L} (γ : (torusGraph n L).Walk x y) :
    Finset (VP n L Lt) :=
  (Finset.univ : Finset (VP n L Lt)).filter
    fun p => p.2.1 = t ∧ s(p.1, p.1 + e p.2.2) ∈ γ.edges

lemma lift_disjoint {t t' : ZMod Lt} (h : t ≠ t') {x y : Space n L}
    (γ γ' : (torusGraph n L).Walk x y) : Disjoint (lift t γ) (lift t' γ') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  have h1 := (Finset.mem_filter.mp hp).2.1
  have h2 := (Finset.mem_filter.mp hp').2.1
  exact h (h1.symm.trans h2)

/-- A path of the bond graph lifts into `A`. -/
lemma lift_mapLe_subset (hL : 3 ≤ L) {A : Finset (VP n L Lt)} {t : ZMod Lt} {x y : Space n L}
    (γ : (bondGraph A t).Walk x y) : lift t (γ.mapLe (bondGraph_le A t)) ⊆ A := by
  classical
  intro p hp
  obtain ⟨-, hpt, hpe⟩ := Finset.mem_filter.mp hp
  obtain ⟨v, t', μ⟩ := p
  simp only at hpt hpe
  subst hpt
  rw [Walk.edges_mapLe_eq_edges] at hpe
  have := γ.edges_subset_edgeSet hpe
  exact mem_of_bondGraph_adj hL ((SimpleGraph.mem_edgeSet _).mp this)

/-- A path has at most as many edges as plaquettes over it. -/
lemma length_le_card_lift (t : ZMod Lt) {x y : Space n L} (γ : (torusGraph n L).Walk x y)
    (hγ : γ.IsPath) : γ.length ≤ (lift t γ).card := by
  classical
  have hnd : γ.edges.Nodup := hγ.isTrail.edges_nodup
  have hlen : γ.length = γ.edges.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, Walk.length_edges]
  rw [hlen]
  refine (Finset.card_le_card ?_).trans
    (Finset.card_image_le (s := lift t γ) (f := fun p : VP n L Lt => s(p.1, p.1 + e p.2.2)))
  intro ed hed
  have hed' : ed ∈ γ.edges := List.mem_toFinset.mp hed
  have hadj := γ.edges_subset_edgeSet hed'
  revert hed' hadj
  refine Sym2.inductionOn ed fun a b hed' hadj => ?_
  have hab := (SimpleGraph.mem_edgeSet _).mp hadj
  rw [torusGraph, SimpleGraph.fromRel_adj] at hab
  rcases hab.2 with ⟨μ, hμ⟩ | ⟨μ, hμ⟩
  · refine Finset.mem_image.mpr ⟨(a, t, μ), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, ?_⟩, ?_⟩
    · simpa [← hμ] using hed'
    · simp [← hμ]
  · refine Finset.mem_image.mpr ⟨(b, t, μ), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, ?_⟩, ?_⟩
    · have : s(b, a) ∈ γ.edges := by rw [Sym2.eq_swap]; exact hed'
      simpa [← hμ] using this
    · simp [← hμ, Sym2.eq_swap]

section counting

open Classical

/-- Every site of the torus has at most `2 n` neighbours. -/
lemma card_neighbors_le (u : Space n L) :
    Fintype.card ((torusGraph n L).neighborSet u) ≤ 2 * n := by
  have hsub : ((torusGraph n L).neighborFinset u) ⊆
      (Finset.univ.image fun μ : Fin n => u + e μ) ∪ (Finset.univ.image fun μ : Fin n => u - e μ) := by
    intro v hv
    have hv' := (SimpleGraph.mem_neighborFinset _ _ _).mp hv
    rw [torusGraph, SimpleGraph.fromRel_adj] at hv'
    rcases hv'.2 with ⟨μ, hμ⟩ | ⟨μ, hμ⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨μ, Finset.mem_univ _, hμ.symm⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨μ, Finset.mem_univ _, ?_⟩)
      rw [hμ]; simp
  have h1 : ((torusGraph n L).neighborFinset u).card ≤ n + n := by
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    refine add_le_add ?_ ?_ <;>
      exact Finset.card_image_le.trans (by simp)
  rw [SimpleGraph.card_neighborSet_eq_degree]
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
  omega

lemma adj_pow_le (k : ℕ) (x y : Space n L) :
    (((torusGraph n L).adjMatrix ℕ) ^ k) x y ≤ (2 * n) ^ k := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> omega
  | succ k ih =>
    rw [pow_succ', SimpleGraph.adjMatrix_mul_apply]
    calc ∑ w ∈ (torusGraph n L).neighborFinset x, (((torusGraph n L).adjMatrix ℕ) ^ k) w y
        ≤ ∑ _w ∈ (torusGraph n L).neighborFinset x, (2 * n) ^ k :=
          Finset.sum_le_sum fun w _ => ih w
      _ = ((torusGraph n L).neighborFinset x).card * (2 * n) ^ k := by simp
      _ ≤ (2 * n) * (2 * n) ^ k := by
          apply Nat.mul_le_mul_right
          have := card_neighbors_le (L := L) x
          rwa [SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree] at this
      _ = (2 * n) ^ (k + 1) := by ring

/-- The number of walks of length `k` between two sites is at most `(2 n) ^ k`. -/
lemma card_walks_le (k : ℕ) (x y : Space n L) :
    Fintype.card {p : (torusGraph n L).Walk x y | p.length = k} ≤ (2 * n) ^ k := by
  have hcard := SimpleGraph.adjMatrix_pow_apply_eq_card_walk (G := torusGraph n L) (α := ℕ) k x y
  rw [Nat.cast_id] at hcard
  rw [← hcard]
  exact adj_pow_le k x y

/-- **The path sum.** If every path from `x` to `y` has length at least `R`, and `q = 2 n p < 1`,
then the paths weighted by `p ^ length` sum to at most `q ^ R / (1 - q)`. -/
lemma path_sum_le {x y : Space n L} {p : ℝ} {R : ℕ} (hp0 : 0 ≤ p) (hq : 2 * (n : ℝ) * p < 1)
    (hR : ∀ γ : (torusGraph n L).Path x y, R ≤ (γ : (torusGraph n L).Walk x y).length) :
    ∑ γ : (torusGraph n L).Path x y, p ^ (γ : (torusGraph n L).Walk x y).length
      ≤ (2 * (n : ℝ) * p) ^ R / (1 - 2 * (n : ℝ) * p) := by
  have hq0 : 0 ≤ 2 * (n : ℝ) * p := by positivity
  have hmaps : ∀ γ ∈ (Finset.univ : Finset ((torusGraph n L).Path x y)),
      (fun γ : (torusGraph n L).Path x y => (γ : (torusGraph n L).Walk x y).length) γ
        ∈ Finset.Ico R (Fintype.card (Space n L)) := fun γ _ =>
    Finset.mem_Ico.mpr ⟨hR γ, γ.2.length_lt⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine (Finset.sum_le_sum fun k _ => ?_).trans (geom_sum_Ico_le_of_lt_one hq0 hq)
  set F := (Finset.univ : Finset ((torusGraph n L).Path x y)).filter
    (fun γ : (torusGraph n L).Path x y => γ.1.length = k) with hF
  change ∑ γ ∈ F, p ^ γ.1.length ≤ _
  have hcongr : ∑ γ ∈ F, p ^ γ.1.length = ∑ _γ ∈ F, p ^ k :=
    Finset.sum_congr rfl fun γ hγ => by rw [(Finset.mem_filter.mp hγ).2]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  have hcard : F.card ≤ (2 * n) ^ k := by
    refine le_trans ?_ (card_walks_le k x y)
    rw [← Fintype.card_coe]
    refine Fintype.card_le_of_injective
      (fun γ => ⟨(γ.1 : (torusGraph n L).Path x y).1, (Finset.mem_filter.mp γ.2).2⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => (z.1 : (torusGraph n L).Walk x y)) hab
  calc _ ≤ (((2 * n) ^ k : ℕ) : ℝ) * p ^ k :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hp0 k)
    _ = (2 * (n : ℝ) * p) ^ k := by push_cast; ring

end counting

/-- The first-coordinate displacement grows by at most one per step. -/
lemma displacement_le (hL : 3 ≤ L) (μ₀ : Fin n) (c : ZMod L) {a b : Space n L}
    (w : (torusGraph n L).Walk a b) :
    (b μ₀ - c).valMinAbs.natAbs ≤ (a μ₀ - c).valMinAbs.natAbs + w.length := by
  have hone : ((1 : ZMod L)).valMinAbs.natAbs ≤ 1 := by
    have : ((1 : ℕ) : ZMod L).valMinAbs = (1 : ℕ) :=
      ZMod.valMinAbs_natCast_of_le_half (by omega)
    simp only [Nat.cast_one] at this
    rw [this]; simp
  have hstep : ∀ (s δ : ZMod L), δ.valMinAbs.natAbs ≤ 1 →
      (s + δ).valMinAbs.natAbs ≤ s.valMinAbs.natAbs + 1 := by
    intro s δ hδ
    refine (ZMod.natAbs_valMinAbs_add_le s δ).trans ?_
    exact (Int.natAbs_add_le _ _).trans (by omega)
  have hδ : ∀ {u v : Space n L}, (torusGraph n L).Adj u v →
      ((v μ₀ - c).valMinAbs.natAbs ≤ (u μ₀ - c).valMinAbs.natAbs + 1) := by
    intro u v huv
    rw [torusGraph, SimpleGraph.fromRel_adj] at huv
    have hcases : ∃ δ : ZMod L, v μ₀ - c = (u μ₀ - c) + δ ∧ δ.valMinAbs.natAbs ≤ 1 := by
      rcases huv.2 with ⟨μ, hμ⟩ | ⟨μ, hμ⟩
      · refine ⟨e μ μ₀, by rw [hμ]; simp; ring, ?_⟩
        by_cases h : μ₀ = μ
        · subst h; rwa [e_apply_self]
        · rw [e_apply_ne h]; simp
      · refine ⟨-(e μ μ₀), by rw [hμ]; simp; ring, ?_⟩
        rw [ZMod.natAbs_valMinAbs_neg]
        by_cases h : μ₀ = μ
        · subst h; rwa [e_apply_self]
        · rw [e_apply_ne h]; simp
    obtain ⟨δ, h1, h2⟩ := hcases
    rw [h1]
    exact hstep _ _ h2
  induction w with
  | nil => simp
  | cons h p ih =>
    have := hδ h
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- A walk from `x` to `x + R e μ₀`, `R ≤ L / 2`, has length at least `R`. -/
lemma length_ge (hL : 3 ≤ L) (μ₀ : Fin n) (x : Space n L) {R : ℕ} (hR : R ≤ L / 2)
    (w : (torusGraph n L).Walk x (x + (R : ZMod L) • e μ₀)) : R ≤ w.length := by
  have h := displacement_le hL μ₀ (x μ₀) w
  have h1 : ((x + (R : ZMod L) • (e μ₀ : Space n L) : Space n L) μ₀) - x μ₀ = (R : ZMod L) := by
    simp [e_apply_self]
  rw [h1, ZMod.valMinAbs_natCast_of_le_half hR, sub_self] at h
  simpa using h

end Confinement
