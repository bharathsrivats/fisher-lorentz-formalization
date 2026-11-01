/-
Copyright (c) 2026 Bharath G. Srivats. Released under Apache 2.0.

**Exponential clustering in Euclidean time**, a mass gap in lattice units, for lattice gauge theory
with an arbitrary gauge group and arbitrary bounded local observables. No centre is needed.

The proof uses the same expansion as the area law, on two independent copies of the configuration.
Write `Cov (f, g) = ½ E [(f - f') (g - g')]`. Expand the product of the plaquette weights of both
copies over sets `A` of plaquettes. If `A` does not join the support of `f` to the support of `g`,
exchange the two copies on the cluster of the support of `f`. Every factor in the term is unchanged
except `f - f'`, which changes sign, so the term vanishes. The surviving `A` contain a chain of
plaquettes between the supports, and the pointwise bound counts those.
-/
import Confinement.AreaLaw
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Finset SimpleGraph

namespace Confinement

variable {n L Lt : ℕ} {G : Type*} [Group G]

/-! ### Plaquettes as one type -/

/-- Horizontal plaquettes, with `μ < ν` so that each is counted once. -/
abbrev HPlaq (n L Lt : ℕ) := {p : HP n L Lt // p.2.2.1 < p.2.2.2}

/-- All plaquettes of the torus. -/
abbrev Plaq (n L Lt : ℕ) := HPlaq n L Lt ⊕ VP n L Lt

/-- The holonomy of a plaquette. -/
def hol (U : Link n L Lt → G) : Plaq n L Lt → G
  | Sum.inl p => Qh U p.1
  | Sum.inr p => Qv U p

/-- The links of a plaquette. -/
def links : Plaq n L Lt → Finset (Link n L Lt)
  | Sum.inl ⟨(x, t, μ, ν), _⟩ =>
      {Sum.inl (x, t, μ), Sum.inl (x + e μ, t, ν), Sum.inl (x + e ν, t, μ), Sum.inl (x, t, ν)}
  | Sum.inr (x, t, μ) =>
      {Sum.inr (x, t), Sum.inl (x, t + 1, μ), Sum.inr (x + e μ, t), Sum.inl (x, t, μ)}

/-- A holonomy depends only on the links of its plaquette. -/
lemma hol_congr {U V : Link n L Lt → G} (p : Plaq n L Lt) (h : ∀ l ∈ links p, U l = V l) :
    hol U p = hol V p := by
  rcases p with ⟨⟨x, t, μ, ν⟩, hp⟩ | ⟨x, t, μ⟩
  · have h1 := h (Sum.inl (x, t, μ)) (by simp [links])
    have h2 := h (Sum.inl (x + e μ, t, ν)) (by simp [links])
    have h3 := h (Sum.inl (x + e ν, t, μ)) (by simp [links])
    have h4 := h (Sum.inl (x, t, ν)) (by simp [links])
    simp only [hol, Qh, hor, h1, h2, h3, h4]
  · have h1 := h (Sum.inr (x, t)) (by simp [links])
    have h2 := h (Sum.inl (x, t + 1, μ)) (by simp [links])
    have h3 := h (Sum.inr (x + e μ, t)) (by simp [links])
    have h4 := h (Sum.inl (x, t, μ)) (by simp [links])
    simp only [hol, Qv, hor, ver, h1, h2, h3, h4]

/-- The time coordinate of a link. -/
def linkTime : Link n L Lt → ZMod Lt
  | Sum.inl (_, t, _) => t
  | Sum.inr (_, t) => t

/-- The time coordinate of a plaquette. -/
def plaqTime : Plaq n L Lt → ZMod Lt
  | Sum.inl p => p.1.2.1
  | Sum.inr p => p.2.1

lemma linkTime_of_mem {p : Plaq n L Lt} {l : Link n L Lt} (h : l ∈ links p) :
    linkTime l = plaqTime p ∨ linkTime l = plaqTime p + 1 := by
  rcases p with ⟨⟨x, t, μ, ν⟩, hp⟩ | ⟨x, t, μ⟩
  · simp only [links, Finset.mem_insert, Finset.mem_singleton] at h
    left
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · simp only [links, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inl rfl

/-! ### The plaquette graph -/

/-- Two plaquettes are adjacent when they share a link. -/
def plaqGraph (n L Lt : ℕ) : SimpleGraph (Plaq n L Lt) :=
  SimpleGraph.fromRel fun p q => (links p ∩ links q).Nonempty

/-- The plaquette graph restricted to `A`. -/
def chainGraph (A : Finset (Plaq n L Lt)) : SimpleGraph (Plaq n L Lt) :=
  SimpleGraph.fromRel fun p q => p ∈ A ∧ q ∈ A ∧ (links p ∩ links q).Nonempty

lemma chainGraph_le (A : Finset (Plaq n L Lt)) : chainGraph A ≤ plaqGraph n L Lt := by
  intro a b h
  rw [chainGraph, SimpleGraph.fromRel_adj] at h
  rw [plaqGraph, SimpleGraph.fromRel_adj]
  refine ⟨h.1, ?_⟩
  rcases h.2 with ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact Or.inl h
  · exact Or.inr h

lemma exists_shared_link {p q : Plaq n L Lt} (h : (plaqGraph n L Lt).Adj p q) :
    ∃ l, l ∈ links p ∧ l ∈ links q := by
  rw [plaqGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨l, hl⟩ | ⟨l, hl⟩
  · exact ⟨l, (Finset.mem_inter.mp hl).1, (Finset.mem_inter.mp hl).2⟩
  · exact ⟨l, (Finset.mem_inter.mp hl).2, (Finset.mem_inter.mp hl).1⟩

lemma chain_mem_of_adj {A : Finset (Plaq n L Lt)} {p q : Plaq n L Lt}
    (h : (chainGraph A).Adj p q) : p ∈ A ∧ q ∈ A := by
  rw [chainGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

/-- Every vertex of a walk in the chain graph starting in `A` lies in `A`. -/
lemma support_subset_chain {A : Finset (Plaq n L Lt)} {a b : Plaq n L Lt}
    (w : (chainGraph A).Walk a b) (ha : a ∈ A) : ∀ v ∈ w.support, v ∈ A := by
  induction w with
  | nil => intro v hv; simp at hv; exact hv ▸ ha
  | cons h p ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact ih (chain_mem_of_adj h).2 v hv

/-- Time moves by at most one along an edge of the plaquette graph. -/
lemma natAbs_valMinAbs_one_le [NeZero Lt] : ((1 : ZMod Lt)).valMinAbs.natAbs ≤ 1 := by
  by_cases h : 2 ≤ Lt
  · have : ((1 : ℕ) : ZMod Lt).valMinAbs = (1 : ℕ) :=
      ZMod.valMinAbs_natCast_of_le_half (by omega)
    simp only [Nat.cast_one] at this
    rw [this]; simp
  · exact (ZMod.natAbs_valMinAbs_le (1 : ZMod Lt)).trans (by omega)

lemma step_le [NeZero Lt] (s δ : ZMod Lt) (hδ : δ.valMinAbs.natAbs ≤ 1) :
    (s + δ).valMinAbs.natAbs ≤ s.valMinAbs.natAbs + 1 :=
  (ZMod.natAbs_valMinAbs_add_le s δ).trans ((Int.natAbs_add_le _ _).trans (by omega))

lemma plaqTime_step [NeZero Lt] (c : ZMod Lt) {p q : Plaq n L Lt} (h : (plaqGraph n L Lt).Adj p q) :
    (plaqTime q - c).valMinAbs.natAbs ≤ (plaqTime p - c).valMinAbs.natAbs + 1 := by
  obtain ⟨l, hp, hq⟩ := exists_shared_link h
  have hone := natAbs_valMinAbs_one_le (Lt := Lt)
  have hcases : ∃ δ : ZMod Lt, plaqTime q - c = (plaqTime p - c) + δ ∧ δ.valMinAbs.natAbs ≤ 1 := by
    rcases linkTime_of_mem hp with h1 | h1 <;> rcases linkTime_of_mem hq with h2 | h2
    · refine ⟨0, ?_, by simp⟩
      have : plaqTime p = plaqTime q := h1.symm.trans h2
      rw [this]; ring
    · refine ⟨-1, ?_, by rwa [ZMod.natAbs_valMinAbs_neg]⟩
      have : plaqTime p = plaqTime q + 1 := h1.symm.trans h2
      rw [this]; ring
    · refine ⟨1, ?_, hone⟩
      have : plaqTime p + 1 = plaqTime q := h1.symm.trans h2
      rw [← this]; ring
    · refine ⟨0, ?_, by simp⟩
      have : plaqTime p + 1 = plaqTime q + 1 := h1.symm.trans h2
      have : plaqTime p = plaqTime q := add_right_cancel this
      rw [this]; ring
  obtain ⟨δ, h1, h2⟩ := hcases
  rw [h1]
  exact step_le _ _ h2

lemma plaqTime_walk [NeZero Lt] (c : ZMod Lt) {a b : Plaq n L Lt}
    (w : (plaqGraph n L Lt).Walk a b) :
    (plaqTime b - c).valMinAbs.natAbs ≤ (plaqTime a - c).valMinAbs.natAbs + w.length := by
  induction w with
  | nil => simp
  | cons h p ih =>
    have := plaqTime_step c h
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- A chain of plaquettes joining links at time distance `D` has length at least `D - 2`. -/
lemma length_ge_time [NeZero Lt] {a b : Plaq n L Lt} (w : (plaqGraph n L Lt).Walk a b)
    {x y : Link n L Lt} (hx : x ∈ links a) (hy : y ∈ links b) :
    (linkTime y - linkTime x).valMinAbs.natAbs ≤ w.length + 2 := by
  have hone := natAbs_valMinAbs_one_le (Lt := Lt)
  set c := linkTime x with hc
  have h1 := plaqTime_walk c w
  have h2 : (plaqTime a - c).valMinAbs.natAbs ≤ 1 := by
    rcases linkTime_of_mem hx with h | h
    · rw [hc, h, sub_self]; simp
    · rw [hc, h]
      have : plaqTime a - (plaqTime a + 1) = -1 := by ring
      rw [this, ZMod.natAbs_valMinAbs_neg]; exact hone
  have h3 : (linkTime y - c).valMinAbs.natAbs ≤ (plaqTime b - c).valMinAbs.natAbs + 1 := by
    rcases linkTime_of_mem hy with h | h
    · rw [h]; omega
    · rw [h]
      have : plaqTime b + 1 - c = (plaqTime b - c) + 1 := by ring
      rw [this]; exact step_le _ _ hone
  omega

/-! ### Counting -/

section counting

open Classical

variable [NeZero L] [NeZero Lt]

/-- The plaquettes containing a link. -/
noncomputable def incid (l : Link n L Lt) : Finset (Plaq n L Lt) :=
  Finset.univ.filter fun p => l ∈ links p

/-- A horizontal plaquette label in sorted order. -/
def sortHP (x : Space n L) (t : ZMod Lt) (μ ν : Fin n) : HP n L Lt :=
  if μ < ν then (x, t, μ, ν) else (x, t, ν, μ)

/-- The forgetful map from plaquettes to raw labels. -/
def toRaw : Plaq n L Lt → HP n L Lt ⊕ VP n L Lt
  | Sum.inl p => Sum.inl p.1
  | Sum.inr p => Sum.inr p

lemma toRaw_injective : Function.Injective (toRaw : Plaq n L Lt → _) := by
  rintro (p | p) (q | q) h
  · simp only [toRaw, Sum.inl.injEq] at h
    exact congrArg Sum.inl (Subtype.ext h)
  · simp [toRaw] at h
  · simp [toRaw] at h
  · simp only [toRaw, Sum.inr.injEq] at h
    exact congrArg Sum.inr h

/-- Each link lies in at most `2 n` plaquettes. -/
lemma card_incid_le (l : Link n L Lt) : (incid l).card ≤ 2 * n := by
  rw [← Finset.card_image_of_injective (incid l) toRaw_injective]
  rcases l with ⟨x, t, μ⟩ | ⟨x, t⟩
  · have hn : 1 ≤ n := by have := μ.2; omega
    set T : Finset (HP n L Lt ⊕ VP n L Lt) :=
      ({Sum.inr (x, t, μ), Sum.inr (x, t - 1, μ)} : Finset _) ∪
        (((Finset.univ.erase μ).image fun ν => Sum.inl (sortHP x t μ ν)) ∪
         ((Finset.univ.erase μ).image fun ν => Sum.inl (sortHP (x - e ν) t μ ν))) with hT
    have hsub : (incid (Sum.inl (x, t, μ))).image toRaw ⊆ T := by
      intro r hr
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
      have hmem := (Finset.mem_filter.mp hp).2
      rcases p with ⟨⟨v, t', α, β⟩, hαβ⟩ | ⟨v, t', α⟩
      · have hαβ' : α < β := hαβ
        simp only [links, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨β, Finset.mem_erase.mpr ⟨hαβ'.ne', Finset.mem_univ _⟩, ?_⟩))
          simp [toRaw, sortHP, hαβ']
        · refine Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨α, Finset.mem_erase.mpr ⟨hαβ'.ne, Finset.mem_univ _⟩, ?_⟩))
          simp [toRaw, sortHP, not_lt.mpr hαβ'.le]
        · refine Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨β, Finset.mem_erase.mpr ⟨hαβ'.ne', Finset.mem_univ _⟩, ?_⟩))
          simp [toRaw, sortHP, hαβ']
        · refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨α, Finset.mem_erase.mpr ⟨hαβ'.ne, Finset.mem_univ _⟩, ?_⟩))
          simp [toRaw, sortHP, not_lt.mpr hαβ'.le]
      · simp only [links, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq, reduceCtorEq,
          Prod.mk.injEq, false_or, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · refine Finset.mem_union_left _ ?_
          simp [toRaw]
        · refine Finset.mem_union_left _ ?_
          simp [toRaw]
    refine (Finset.card_le_card hsub).trans ?_
    have h1 : (({Sum.inr (x, t, μ), Sum.inr (x, t - 1, μ)} : Finset (HP n L Lt ⊕ VP n L Lt))).card ≤ 2 :=
      Finset.card_le_two
    have herase : (Finset.univ.erase μ).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have h2 : (((Finset.univ.erase μ).image fun ν =>
        (Sum.inl (sortHP x t μ ν) : HP n L Lt ⊕ VP n L Lt))).card ≤ n - 1 :=
      Finset.card_image_le.trans herase.le
    have h3 : (((Finset.univ.erase μ).image fun ν =>
        (Sum.inl (sortHP (x - e ν) t μ ν) : HP n L Lt ⊕ VP n L Lt))).card ≤ n - 1 :=
      Finset.card_image_le.trans herase.le
    have h4 := Finset.card_union_le ({Sum.inr (x, t, μ), Sum.inr (x, t - 1, μ)} :
      Finset (HP n L Lt ⊕ VP n L Lt)) (((Finset.univ.erase μ).image fun ν =>
        (Sum.inl (sortHP x t μ ν) : HP n L Lt ⊕ VP n L Lt)) ∪
        ((Finset.univ.erase μ).image fun ν =>
        (Sum.inl (sortHP (x - e ν) t μ ν) : HP n L Lt ⊕ VP n L Lt)))
    have h5 := Finset.card_union_le ((Finset.univ.erase μ).image fun ν =>
        (Sum.inl (sortHP x t μ ν) : HP n L Lt ⊕ VP n L Lt))
        ((Finset.univ.erase μ).image fun ν =>
        (Sum.inl (sortHP (x - e ν) t μ ν) : HP n L Lt ⊕ VP n L Lt))
    rw [hT]
    omega
  · set T : Finset (HP n L Lt ⊕ VP n L Lt) :=
      ((Finset.univ : Finset (Fin n)).image fun ν => Sum.inr (x, t, ν)) ∪
        ((Finset.univ : Finset (Fin n)).image fun ν => Sum.inr (x - e ν, t, ν)) with hT
    have hsub : (incid (Sum.inr (x, t))).image toRaw ⊆ T := by
      intro r hr
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
      have hmem := (Finset.mem_filter.mp hp).2
      rcases p with ⟨⟨v, t', α, β⟩, hαβ⟩ | ⟨v, t', α⟩
      · simp [links] at hmem
      · simp only [links, Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq, reduceCtorEq,
          Prod.mk.injEq, false_or, or_false] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨α, Finset.mem_univ _, rfl⟩)
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨α, Finset.mem_univ _, ?_⟩)
          simp [toRaw]
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    have h1 : (((Finset.univ : Finset (Fin n)).image fun ν =>
        (Sum.inr (x, t, ν) : HP n L Lt ⊕ VP n L Lt))).card ≤ n :=
      Finset.card_image_le.trans (by simp)
    have h2 : (((Finset.univ : Finset (Fin n)).image fun ν =>
        (Sum.inr (x - e ν, t, ν) : HP n L Lt ⊕ VP n L Lt))).card ≤ n :=
      Finset.card_image_le.trans (by simp)
    omega

lemma card_links_le (p : Plaq n L Lt) : (links p).card ≤ 4 := by
  rcases p with ⟨⟨x, t, μ, ν⟩, hp⟩ | ⟨x, t, μ⟩ <;> exact Finset.card_le_four

/-- The plaquette graph has degree at most `4 (2 n - 1)`. -/
lemma degree_plaq_le (p : Plaq n L Lt) :
    ((plaqGraph n L Lt).neighborFinset p).card ≤ 4 * (2 * n - 1) := by
  have hsub : (plaqGraph n L Lt).neighborFinset p ⊆
      (links p).biUnion fun l => (incid l).erase p := by
    intro q hq
    have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hq
    obtain ⟨l, h1, h2⟩ := exists_shared_link hadj
    exact Finset.mem_biUnion.mpr ⟨l, h1, Finset.mem_erase.mpr ⟨hadj.ne',
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ (2 * n - 1) ?_).trans
    (Nat.mul_le_mul_right _ (card_links_le p))
  intro l hl
  have hm : p ∈ incid l := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
  rw [Finset.card_erase_of_mem hm]
  have := card_incid_le l
  omega

/-- Walks in a graph of bounded degree. -/
lemma adj_pow_le_general {V : Type*} [Fintype V] (Γ : SimpleGraph V) {Δ : ℕ}
    (hdeg : ∀ v, (Γ.neighborFinset v).card ≤ Δ) (k : ℕ) (x y : V) :
    ((Γ.adjMatrix ℕ) ^ k) x y ≤ Δ ^ k := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> omega
  | succ k ih =>
    rw [pow_succ', SimpleGraph.adjMatrix_mul_apply]
    calc ∑ w ∈ Γ.neighborFinset x, ((Γ.adjMatrix ℕ) ^ k) w y
        ≤ ∑ _w ∈ Γ.neighborFinset x, Δ ^ k := Finset.sum_le_sum fun w _ => ih w
      _ = (Γ.neighborFinset x).card * Δ ^ k := by simp
      _ ≤ Δ * Δ ^ k := Nat.mul_le_mul_right _ (hdeg x)
      _ = Δ ^ (k + 1) := by ring

/-- Paths weighted by length, in a graph of bounded degree. -/
lemma path_sum_le_general {V : Type*} [Fintype V] (Γ : SimpleGraph V) {Δ : ℕ}
    (hdeg : ∀ v, (Γ.neighborFinset v).card ≤ Δ) {x y : V} {p : ℝ} {R : ℕ} (hp0 : 0 ≤ p)
    (hq : (Δ : ℝ) * p < 1) (hR : ∀ γ : Γ.Path x y, R ≤ (γ : Γ.Walk x y).length) :
    ∑ γ : Γ.Path x y, p ^ (γ : Γ.Walk x y).length ≤ ((Δ : ℝ) * p) ^ R / (1 - (Δ : ℝ) * p) := by
  have hq0 : 0 ≤ (Δ : ℝ) * p := by positivity
  have hmaps : ∀ γ ∈ (Finset.univ : Finset (Γ.Path x y)),
      (fun γ : Γ.Path x y => (γ : Γ.Walk x y).length) γ ∈ Finset.Ico R (Fintype.card V) :=
    fun γ _ => Finset.mem_Ico.mpr ⟨hR γ, γ.2.length_lt⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine (Finset.sum_le_sum fun k _ => ?_).trans (geom_sum_Ico_le_of_lt_one hq0 hq)
  set F := (Finset.univ : Finset (Γ.Path x y)).filter
    (fun γ : Γ.Path x y => γ.1.length = k) with hF
  change ∑ γ ∈ F, p ^ γ.1.length ≤ _
  have hcongr : ∑ γ ∈ F, p ^ γ.1.length = ∑ _γ ∈ F, p ^ k :=
    Finset.sum_congr rfl fun γ hγ => by rw [(Finset.mem_filter.mp hγ).2]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  have hwalk : Fintype.card {w : Γ.Walk x y | w.length = k} ≤ Δ ^ k := by
    have hcard := SimpleGraph.adjMatrix_pow_apply_eq_card_walk (G := Γ) (α := ℕ) k x y
    rw [Nat.cast_id] at hcard
    rw [← hcard]
    exact adj_pow_le_general Γ hdeg k x y
  have hcard : F.card ≤ Δ ^ k := by
    refine le_trans ?_ hwalk
    rw [← Fintype.card_coe]
    refine Fintype.card_le_of_injective
      (fun γ => ⟨(γ.1 : Γ.Path x y).1, (Finset.mem_filter.mp γ.2).2⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => (z.1 : Γ.Walk x y)) hab
  calc _ ≤ ((Δ ^ k : ℕ) : ℝ) * p ^ k :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hp0 k)
    _ = ((Δ : ℝ) * p) ^ k := by push_cast; ring

end counting

/-! ### Two copies -/

section dup

variable [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- A pair of configurations, stored link by link. -/
abbrev Dup (n L Lt : ℕ) (G : Type*) := Link n L Lt → G × G

/-- The first copy. -/
def fstC (ω : Dup n L Lt G) : Link n L Lt → G := fun l => (ω l).1

/-- The second copy. -/
def sndC (ω : Dup n L Lt G) : Link n L Lt → G := fun l => (ω l).2

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma measurable_fstC : Measurable (fstC : Dup n L Lt G → _) :=
  measurable_pi_lambda _ fun l => measurable_fst.comp (measurable_pi_apply l)

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma measurable_sndC : Measurable (sndC : Dup n L Lt G → _) :=
  measurable_pi_lambda _ fun l => measurable_snd.comp (measurable_pi_apply l)

/-- The law of two independent copies. -/
noncomputable def dupMeasure (μ₀ : Measure G) : Measure (Dup n L Lt G) :=
  Measure.pi fun _ => μ₀.prod μ₀

instance (μ₀ : Measure G) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (dupMeasure (n := n) (L := L) (Lt := Lt) μ₀) := by
  unfold dupMeasure; infer_instance

open Classical in
/-- Exchange the two copies on the links of `C`. -/
noncomputable def swapOn (C : Set (Link n L Lt)) (ω : Dup n L Lt G) : Dup n L Lt G :=
  fun l => if l ∈ C then (ω l).swap else ω l

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
open Classical in
lemma measurePreserving_swapOn (μ₀ : Measure G) [IsProbabilityMeasure μ₀]
    (C : Set (Link n L Lt)) :
    MeasurePreserving (swapOn C) (dupMeasure (n := n) (L := L) (Lt := Lt) μ₀) (dupMeasure μ₀) := by
  have : (swapOn C : Dup n L Lt G → Dup n L Lt G) =
      fun ω l => (if l ∈ C then Prod.swap else id) (ω l) := by
    funext ω l
    by_cases h : l ∈ C <;> simp [swapOn, h]
  rw [this]
  refine measurePreserving_pi (fun _ => μ₀.prod μ₀) (fun _ => μ₀.prod μ₀) fun l => ?_
  by_cases h : l ∈ C
  · simp only [h, if_true]
    exact Measure.measurePreserving_swap
  · simp only [h, if_false]
    exact MeasurePreserving.id _

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- Integrals of a product of functions of the two copies factorise. -/
lemma integral_dup_mul {𝕜 : Type*} [RCLike 𝕜] (μ₀ : Measure G) [IsProbabilityMeasure μ₀]
    (F F' : (Link n L Lt → G) → 𝕜) :
    ∫ ω, F (fstC ω) * F' (sndC ω) ∂(dupMeasure μ₀)
      = (∫ U, F U ∂(linkMeasure μ₀)) * ∫ U, F' U ∂(linkMeasure μ₀) := by
  have hmp := measurePreserving_arrowProdEquivProdArrow G G (Link n L Lt)
    (fun _ => μ₀) (fun _ => μ₀)
  have := hmp.integral_comp' (fun p : (Link n L Lt → G) × (Link n L Lt → G) => F p.1 * F' p.2)
  rw [show (∫ ω, F (fstC ω) * F' (sndC ω) ∂(dupMeasure μ₀))
      = ∫ ω, (fun p : (Link n L Lt → G) × (Link n L Lt → G) => F p.1 * F' p.2)
        (MeasurableEquiv.arrowProdEquivProdArrow G G (Link n L Lt) ω)
        ∂(Measure.pi fun _ => μ₀.prod μ₀) from rfl, this]
  exact integral_prod_mul F F'

/-- The exponent of a plaquette weight. -/
noncomputable def sP (χ : G → ℂ) (J : ℝ) (p : Plaq n L Lt) (U : Link n L Lt → G) : ℝ :=
  J * (χ (hol U p)).re + |J|

/-- The nonnegative part of the weight of a plaquette in both copies. -/
noncomputable def gP (χ : G → ℂ) (J : ℝ) (p : Plaq n L Lt) (ω : Dup n L Lt G) : ℝ :=
  Real.exp (sP χ J p (fstC ω) + sP χ J p (sndC ω)) - 1

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [NeZero L] [NeZero Lt] in
lemma sP_bounds {χ : G → ℂ} (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ) (p : Plaq n L Lt) (U) :
    0 ≤ sP χ J p U ∧ sP χ J p U ≤ 2 * |J| :=
  exponent_bounds hχ J (hol U p)

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [NeZero L] [NeZero Lt] in
lemma gP_nonneg {χ : G → ℂ} (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ) (p : Plaq n L Lt) (ω) :
    0 ≤ gP χ J p ω := by
  have h1 := (sP_bounds hχ J p (fstC ω)).1
  have h2 := (sP_bounds hχ J p (sndC ω)).1
  have := Real.one_le_exp (add_nonneg h1 h2)
  simp only [gP]; linarith

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [NeZero L] [NeZero Lt] in
lemma gP_le {χ : G → ℂ} (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ) (p : Plaq n L Lt) (ω) :
    gP χ J p ω ≤ Real.exp (4 * |J|) - 1 := by
  have h1 := (sP_bounds hχ J p (fstC ω)).2
  have h2 := (sP_bounds hχ J p (sndC ω)).2
  have := Real.exp_le_exp.mpr (show sP χ J p (fstC ω) + sP χ J p (sndC ω) ≤ 4 * |J| by linarith)
  simp only [gP]; linarith

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [NeZero L] [NeZero Lt] in
lemma gP_le_mul {χ : G → ℂ} (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ) (p : Plaq n L Lt) (ω) :
    gP χ J p ω ≤ (1 - Real.exp (-(4 * |J|))) * (1 + gP χ J p ω) := by
  have h1 := (sP_bounds hχ J p (fstC ω)).2
  have h2 := (sP_bounds hχ J p (sndC ω)).2
  set s := sP χ J p (fstC ω) + sP χ J p (sndC ω) with hs
  have hb : s ≤ 4 * |J| := by rw [hs]; linarith
  have h3 : Real.exp (s - 4 * |J|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h4 : Real.exp (-(4 * |J|)) * Real.exp s = Real.exp (s - 4 * |J|) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [gP, ← hs]
  nlinarith

omit [NeZero L] [NeZero Lt] [MeasurableMul₂ G] [MeasurableInv G] in
lemma measurable_hol [MeasurableMul₂ G] [MeasurableInv G] (p : Plaq n L Lt) :
    Measurable fun U : Link n L Lt → G => hol U p := by
  rcases p with p | p
  · exact measurable_Qh p.1
  · exact measurable_Qv p

lemma measurable_gP {χ : G → ℂ} (hχm : Measurable χ) (J : ℝ) (p : Plaq n L Lt) :
    Measurable (gP χ J p : Dup n L Lt G → ℝ) := by
  have hs : Measurable fun U : Link n L Lt → G => sP χ J p U :=
    ((Complex.measurable_re.comp (hχm.comp (measurable_hol p))).const_mul J).add_const _
  unfold gP
  exact ((hs.comp measurable_fstC).add (hs.comp measurable_sndC)).exp.sub_const _

/-- The chain-reachable plaquettes from `X`. -/
def reachSet (A : Finset (Plaq n L Lt)) (X : Finset (Link n L Lt)) : Set (Plaq n L Lt) :=
  {q | ∃ a ∈ A, (∃ x ∈ X, x ∈ links a) ∧ (chainGraph A).Reachable a q}

/-- The cluster of `X`. -/
def cluster (A : Finset (Plaq n L Lt)) (X : Finset (Link n L Lt)) : Set (Link n L Lt) :=
  {l | l ∈ X ∨ ∃ q ∈ reachSet A X, l ∈ links q}

omit [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [Group G] in
lemma reachSet_subset {A : Finset (Plaq n L Lt)} {X : Finset (Link n L Lt)} {q}
    (hq : q ∈ reachSet A X) : q ∈ A := by
  obtain ⟨a, ha, -, ⟨w⟩⟩ := hq
  exact support_subset_chain w ha q w.end_mem_support

omit [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [Group G] in
/-- A plaquette of `A` lies entirely inside the cluster or entirely outside it. -/
lemma plaq_in_or_out {A : Finset (Plaq n L Lt)} {X : Finset (Link n L Lt)} {p} (hp : p ∈ A) :
    (∀ l ∈ links p, l ∈ cluster A X) ∨ (∀ l ∈ links p, l ∉ cluster A X) := by
  by_cases hreach : p ∈ reachSet A X
  · exact Or.inl fun l hl => Or.inr ⟨p, hreach, hl⟩
  · refine Or.inr fun l hl hc => hreach ?_
    rcases hc with hX | ⟨q, hq, hlq⟩
    · exact ⟨p, hp, ⟨l, hX, hl⟩, SimpleGraph.Reachable.refl p⟩
    · by_cases hpq : q = p
      · exact hpq ▸ hq
      · obtain ⟨a, ha, htouch, hr⟩ := hq
        have hqA : q ∈ A := reachSet_subset ⟨a, ha, htouch, hr⟩
        refine ⟨a, ha, htouch, hr.trans (SimpleGraph.Adj.reachable ?_)⟩
        rw [chainGraph, SimpleGraph.fromRel_adj]
        exact ⟨hpq, Or.inl ⟨hqA, hp, ⟨l, Finset.mem_inter.mpr ⟨hlq, hl⟩⟩⟩⟩

open Classical in
omit [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma fstC_swapOn_mem (C : Set (Link n L Lt)) (ω : Dup n L Lt G) {l} (h : l ∈ C) :
    fstC (swapOn C ω) l = sndC ω l := by simp [fstC, sndC, swapOn, h]

open Classical in
omit [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma sndC_swapOn_mem (C : Set (Link n L Lt)) (ω : Dup n L Lt G) {l} (h : l ∈ C) :
    sndC (swapOn C ω) l = fstC ω l := by simp [fstC, sndC, swapOn, h]

open Classical in
omit [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma fstC_swapOn_not_mem (C : Set (Link n L Lt)) (ω : Dup n L Lt G) {l} (h : l ∉ C) :
    fstC (swapOn C ω) l = fstC ω l := by simp [fstC, swapOn, h]

open Classical in
omit [NeZero L] [NeZero Lt] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma sndC_swapOn_not_mem (C : Set (Link n L Lt)) (ω : Dup n L Lt G) {l} (h : l ∉ C) :
    sndC (swapOn C ω) l = sndC ω l := by simp [sndC, swapOn, h]

/-- The antisymmetrised observable. -/
noncomputable def covW (f g : (Link n L Lt → G) → ℂ) (ω : Dup n L Lt G) : ℂ :=
  (f (fstC ω) - f (sndC ω)) * (g (fstC ω) - g (sndC ω)) / 4

/-- **The exchange kills every term that does not join the supports.** -/
theorem term_vanish_swap (μ₀ : Measure G) [IsProbabilityMeasure μ₀]
    {χ : G → ℂ} (hχm : Measurable χ) (J : ℝ) (f g : (Link n L Lt → G) → ℂ)
    (hfm : Measurable f) (hgm : Measurable g)
    (X Y : Finset (Link n L Lt))
    (hfX : ∀ U V : Link n L Lt → G, (∀ l ∈ X, U l = V l) → f U = f V)
    (hgY : ∀ U V : Link n L Lt → G, (∀ l ∈ Y, U l = V l) → g U = g V)
    (A : Finset (Plaq n L Lt)) (hY : ∀ y ∈ Y, y ∉ cluster A X) :
    ∫ ω, covW f g ω * (((1 : ℝ) * ∏ p ∈ A, gP χ J p ω : ℝ) : ℂ)
      ∂(dupMeasure (n := n) (L := L) (Lt := Lt) μ₀) = 0 := by
  classical
  set C := cluster A X with hC
  set F : Dup n L Lt G → ℂ := fun ω => covW f g ω * (((1 : ℝ) * ∏ p ∈ A, gP χ J p ω : ℝ) : ℂ) with hF
  have hinv : ∀ ω, F (swapOn C ω) = -F ω := by
    intro ω
    have hg : ∀ p ∈ A, gP χ J p (swapOn C ω) = gP χ J p ω := by
      intro p hp
      rcases plaq_in_or_out (X := X) hp with hin | hout
      · have h1 : hol (fstC (swapOn C ω)) p = hol (sndC ω) p :=
          hol_congr p fun l hl => fstC_swapOn_mem C ω (hin l hl)
        have h2 : hol (sndC (swapOn C ω)) p = hol (fstC ω) p :=
          hol_congr p fun l hl => sndC_swapOn_mem C ω (hin l hl)
        simp only [gP, sP, h1, h2]
        congr 2
        ring
      · have h1 : hol (fstC (swapOn C ω)) p = hol (fstC ω) p :=
          hol_congr p fun l hl => fstC_swapOn_not_mem C ω (hout l hl)
        have h2 : hol (sndC (swapOn C ω)) p = hol (sndC ω) p :=
          hol_congr p fun l hl => sndC_swapOn_not_mem C ω (hout l hl)
        simp only [gP, sP, h1, h2]
    have hprod : ∏ p ∈ A, gP χ J p (swapOn C ω) = ∏ p ∈ A, gP χ J p ω := Finset.prod_congr rfl hg
    have hf1 : f (fstC (swapOn C ω)) = f (sndC ω) :=
      hfX _ _ fun l hl => fstC_swapOn_mem C ω (Or.inl hl)
    have hf2 : f (sndC (swapOn C ω)) = f (fstC ω) :=
      hfX _ _ fun l hl => sndC_swapOn_mem C ω (Or.inl hl)
    have hg1 : g (fstC (swapOn C ω)) = g (fstC ω) :=
      hgY _ _ fun l hl => fstC_swapOn_not_mem C ω (hY l hl)
    have hg2 : g (sndC (swapOn C ω)) = g (sndC ω) :=
      hgY _ _ fun l hl => sndC_swapOn_not_mem C ω (hY l hl)
    simp only [hF, covW, hprod, hf1, hf2, hg1, hg2]
    ring
  have hFm : Measurable F := by
    have hW : Measurable (covW f g : Dup n L Lt G → ℂ) := by
      unfold covW
      exact (((hfm.comp measurable_fstC).sub (hfm.comp measurable_sndC)).mul
        ((hgm.comp measurable_fstC).sub (hgm.comp measurable_sndC))).div_const _
    refine hW.mul (Complex.measurable_ofReal.comp ?_)
    exact measurable_const.mul (Finset.measurable_prod _ fun p _ => measurable_gP hχm J p)
  have hmp := measurePreserving_swapOn (n := n) (L := L) (Lt := Lt) μ₀ C
  have hmap : ∫ ω, F ω ∂(dupMeasure μ₀) = ∫ ω, F (swapOn C ω) ∂(dupMeasure μ₀) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hFm.aestronglyMeasurable
  have heq : ∫ ω, F ω ∂(dupMeasure μ₀) = -∫ ω, F ω ∂(dupMeasure μ₀) := by
    conv_lhs => rw [hmap]
    simp_rw [hinv]
    exact integral_neg _
  have h2 : (2 : ℂ) * ∫ ω, F ω ∂(dupMeasure μ₀) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [heq]
    ring
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

omit [MeasurableMul₂ G] [MeasurableInv G] in
lemma integrable_dup [MeasurableMul₂ G] [MeasurableInv G] (μ₀ : Measure G) [IsProbabilityMeasure μ₀]
    {F F' : (Link n L Lt → G) → ℂ} (hF : Measurable F) (hF' : Measurable F') {a b : ℝ}
    (hFb : ∀ U, ‖F U‖ ≤ a) (hFb' : ∀ U, ‖F' U‖ ≤ b) :
    Integrable (fun ω => F (fstC ω) * F' (sndC ω)) (dupMeasure (n := n) (L := L) (Lt := Lt) μ₀) := by
  refine Integrable.of_bound
    (((hF.comp measurable_fstC).mul (hF'.comp measurable_sndC)).aestronglyMeasurable)
    (a * b) (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul (hFb _) (hFb' _) (norm_nonneg _) ((norm_nonneg _).trans (hFb (fstC ω)))

/-- The total action is the sum over all plaquettes. -/
lemma sum_plaq_eq (χ : G → ℂ) (U : Link n L Lt → G) :
    ∑ p : Plaq n L Lt, (χ (hol U p)).re = actionH χ U + actionV χ U := by
  rw [Fintype.sum_sum_type]
  congr 1
  unfold actionH
  exact (Finset.sum_subtype _ (by simp) fun p : HP n L Lt => (χ (Qh U p)).re).symm

/-- The number of plaquettes, as a real number. -/
noncomputable def plaqCount (n L Lt : ℕ) [NeZero L] [NeZero Lt] : ℝ :=
  (Fintype.card (Plaq n L Lt) : ℝ)

lemma abs_action_le {χ : G → ℂ} (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ) (U : Link n L Lt → G) :
    |J * (actionH χ U + actionV χ U)| ≤ |J| * plaqCount n L Lt := by
  rw [← sum_plaq_eq, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ => (1 : ℝ))
    fun q _ => abs_le.mpr (re_bounds hχ _)).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, plaqCount]

lemma measurable_wilsonWeight {χ : G → ℂ} (hχm : Measurable χ) (J : ℝ) :
    Measurable (wilsonWeight χ J : (Link n L Lt → G) → ℝ) := by
  unfold wilsonWeight
  exact (((measurable_actionH hχm).add (measurable_actionV hχm)).const_mul J).exp

lemma wilsonWeight_le {χ : G → ℂ} (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ) (U : Link n L Lt → G) :
    wilsonWeight χ J U ≤ Real.exp (|J| * plaqCount n L Lt) :=
  Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_action_le hχ J U))

lemma wilsonWeight_ge {χ : G → ℂ} (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ) (U : Link n L Lt → G) :
    Real.exp (-(|J| * plaqCount n L Lt)) ≤ wilsonWeight χ J U :=
  Real.exp_le_exp.mpr (by linarith [(abs_le.mp (abs_action_le hχ J U)).1])

/-- The partition function is positive, for every bounded measurable `χ`. -/
theorem partition_pos_general (μ₀ : Measure G) [IsProbabilityMeasure μ₀] {χ : G → ℂ}
    (hχm : Measurable χ) (hχ : ∀ g, ‖χ g‖ ≤ 1) (J : ℝ) :
    0 < ∫ U : Link n L Lt → G, wilsonWeight χ J U ∂(linkMeasure μ₀) := by
  have hint : Integrable (wilsonWeight χ J : (Link n L Lt → G) → ℝ) (linkMeasure μ₀) := by
    refine Integrable.of_bound (measurable_wilsonWeight hχm J).aestronglyMeasurable
      (Real.exp (|J| * plaqCount n L Lt)) (Filter.Eventually.of_forall fun U => ?_)
    have h0 : 0 ≤ wilsonWeight χ J U := (Real.exp_pos _).le
    rw [Real.norm_of_nonneg h0]
    exact wilsonWeight_le hχ J U
  have hlow : ∫ _U : Link n L Lt → G, Real.exp (-(|J| * plaqCount n L Lt)) ∂(linkMeasure μ₀)
      ≤ ∫ U : Link n L Lt → G, wilsonWeight χ J U ∂(linkMeasure μ₀) :=
    integral_mono (integrable_const _) hint (wilsonWeight_ge hχ J)
  have hconst : ∫ _U : Link n L Lt → G, Real.exp (-(|J| * plaqCount n L Lt)) ∂(linkMeasure μ₀)
      = Real.exp (-(|J| * plaqCount n L Lt)) := by simp
  linarith [Real.exp_pos (-(|J| * plaqCount n L Lt))]

/-- Both copies' plaquette weights multiply to a constant times the two Wilson weights. -/
lemma prod_gP (χ : G → ℂ) (J : ℝ) (ω : Dup n L Lt G) :
    ∏ p : Plaq n L Lt, (1 + gP χ J p ω)
      = Real.exp (2 * (|J| * plaqCount n L Lt)) *
        (wilsonWeight χ J (fstC ω) * wilsonWeight χ J (sndC ω)) := by
  have h1 : ∀ p ∈ (Finset.univ : Finset (Plaq n L Lt)), 1 + gP χ J p ω
      = Real.exp (sP χ J p (fstC ω) + sP χ J p (sndC ω)) := fun p _ => by simp [gP]
  have hsum : ∀ U : Link n L Lt → G, ∑ p : Plaq n L Lt, sP χ J p U
      = J * (actionH χ U + actionV χ U) + |J| * plaqCount n L Lt := by
    intro U
    simp only [sP]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_plaq_eq, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, plaqCount, mul_comm (|J|)]
  rw [Finset.prod_congr rfl h1, ← Real.exp_sum, Finset.sum_add_distrib, hsum, hsum, wilsonWeight,
    wilsonWeight, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

open Classical in
/-- The plaquettes touching a set of links. -/
noncomputable def touch (X : Finset (Link n L Lt)) : Finset (Plaq n L Lt) := X.biUnion incid

open Classical in
lemma card_touch_le (X : Finset (Link n L Lt)) : (touch X).card ≤ X.card * (2 * n) :=
  Finset.card_biUnion_le_card_mul _ _ _ fun l _ => card_incid_le l

set_option maxHeartbeats 3200000 in
open Classical in
/-- **Exponential clustering in Euclidean time, for an arbitrary gauge group.** Let `f`, `g` be bounded
by one, depending on the links in `X` and `Y`, at time distance at least `D ≥ 1`. With
`p = 1 - exp (-4 |J|)` and `Δ = 4 (2 n - 1)`, if `Δ p < 1` then
`‖⟨f g⟩ - ⟨f⟩⟨g⟩‖ ≤ 2 (2 n |X|) (2 n |Y|) p (Δ p) ^ (D - 2) / (1 - Δ p)`.
The bound does not depend on the size of the torus. No centre and no invariance of the single-link
measure are used. -/
theorem clustering_general (μ₀ : Measure G) [IsProbabilityMeasure μ₀]
    {χ : G → ℂ} (hχm : Measurable χ) (hχ : ∀ g, ‖χ g‖ ≤ 1)
    (f g : (Link n L Lt → G) → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf1 : ∀ U, ‖f U‖ ≤ 1) (hg1 : ∀ U, ‖g U‖ ≤ 1)
    (X Y : Finset (Link n L Lt))
    (hfX : ∀ U V : Link n L Lt → G, (∀ l ∈ X, U l = V l) → f U = f V)
    (hgY : ∀ U V : Link n L Lt → G, (∀ l ∈ Y, U l = V l) → g U = g V)
    {D : ℕ} (hD1 : 1 ≤ D)
    (hD : ∀ x ∈ X, ∀ y ∈ Y, D ≤ (linkTime y - linkTime x).valMinAbs.natAbs)
    (J : ℝ) (hq : ((4 * (2 * n - 1) : ℕ) : ℝ) * (1 - Real.exp (-(4 * |J|))) < 1) :
    ‖gibbs μ₀ χ J (fun U => f U * g U) - gibbs μ₀ χ J f * gibbs μ₀ χ J g‖
      ≤ 2 * (((X.card * (2 * n) : ℕ) : ℝ) * ((Y.card * (2 * n) : ℕ) : ℝ)) *
        ((1 - Real.exp (-(4 * |J|))) *
          ((((4 * (2 * n - 1) : ℕ) : ℝ) * (1 - Real.exp (-(4 * |J|)))) ^ (D - 2) /
            (1 - ((4 * (2 * n - 1) : ℕ) : ℝ) * (1 - Real.exp (-(4 * |J|)))))) := by
  set p : ℝ := 1 - Real.exp (-(4 * |J|)) with hpdef
  set Δ : ℕ := 4 * (2 * n - 1) with hΔ
  have hp0 : 0 ≤ p := by
    have : Real.exp (-(4 * |J|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg J])
    linarith
  have hd0 : 0 < 1 - (Δ : ℝ) * p := by linarith
  set B : ℝ := ((Δ : ℝ) * p) ^ (D - 2) / (1 - (Δ : ℝ) * p) with hB
  have hB0 : 0 ≤ B := div_nonneg (pow_nonneg (by positivity) _) hd0.le
  -- the index of chains
  let TX := {a // a ∈ touch X}
  let TY := {b // b ∈ touch Y}
  let κ := Σ a : TX, Σ b : TY, (plaqGraph n L Lt).Path a.1 b.1
  let S : κ → Finset (Plaq n L Lt) := fun k =>
    ((k.2.2 : (plaqGraph n L Lt).Path k.1.1 k.2.1.1) :
      (plaqGraph n L Lt).Walk k.1.1 k.2.1.1).support.toFinset
  have hW : ∀ ω : Dup n L Lt G, ‖covW f g ω‖ ≤ 1 := by
    intro ω
    have h1 : ‖f (fstC ω) - f (sndC ω)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hf1 (fstC ω), hf1 (sndC ω)])
    have h2 : ‖g (fstC ω) - g (sndC ω)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hg1 (fstC ω), hg1 (sndC ω)])
    simp only [covW, norm_div, norm_mul]
    have h3 : ‖(4 : ℂ)‖ = 4 := by simp
    rw [h3, div_le_one (by norm_num)]
    nlinarith [norm_nonneg (f (fstC ω) - f (sndC ω)), norm_nonneg (g (fstC ω) - g (sndC ω))]
  have hWm : Measurable (covW f g : Dup n L Lt G → ℂ) := by
    unfold covW
    exact (((hfm.comp measurable_fstC).sub (hfm.comp measurable_sndC)).mul
      ((hgm.comp measurable_fstC).sub (hgm.comp measurable_sndC))).div_const _
  have hbound := expansion_bound (ν := dupMeasure (n := n) (L := L) (Lt := Lt) μ₀)
    (Finset.univ : Finset (Plaq n L Lt)) S (fun _ => Finset.subset_univ _)
    (fun q ω => gP χ J q ω) (fun _ => (1 : ℝ)) (covW f g) (p := p)
    (M := Real.exp (4 * |J|) - 1) (C := 1)
    (fun q _ => measurable_gP hχm J q) measurable_const hWm
    (fun q _ ω => gP_nonneg hχ J q ω) (fun q _ ω => gP_le hχ J q ω)
    (fun q _ ω => gP_le_mul hχ J q ω) (fun _ => zero_le_one) (fun _ => le_rfl) hW
    (by
      intro A _
      by_cases hy : ∃ y ∈ Y, y ∈ cluster A X
      · left
        obtain ⟨y, hyY, hyC⟩ := hy
        rcases hyC with hyX | ⟨q, hq', hyq⟩
        · have := hD y hyX y hyY
          simp at this
          omega
        · obtain ⟨a, haA, ⟨x, hxX, hxa⟩, ⟨w⟩⟩ := hq'
          have hta : a ∈ touch X := Finset.mem_biUnion.mpr
            ⟨x, hxX, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa⟩⟩
          have htq : q ∈ touch Y := Finset.mem_biUnion.mpr
            ⟨y, hyY, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyq⟩⟩
          let w' := w.toPath
          refine ⟨⟨⟨a, hta⟩, ⟨q, htq⟩, ⟨(w' : (chainGraph A).Walk a q).mapLe (chainGraph_le A),
            w'.2.mapLe _⟩⟩, ?_⟩
          intro v hv
          have hv' : v ∈ ((w' : (chainGraph A).Walk a q).mapLe (chainGraph_le A)).support :=
            List.mem_toFinset.mp hv
          have hv2 : v ∈ (w' : (chainGraph A).Walk a q).support := by
            simpa using hv'
          exact support_subset_chain _ haA v hv2
      · right
        have hY' : ∀ y ∈ Y, y ∉ cluster A X := fun y hyY hyC => hy ⟨y, hyY, hyC⟩
        exact term_vanish_swap μ₀ hχm J f g hfm hgm X Y hfX hgY A hY')
  -- the sum over chains
  have hsum : ∑ k, p ^ (S k).card ≤ (((touch X).card : ℝ) * ((touch Y).card : ℝ)) * (p * B) := by
    have hinner : ∀ (a : TX) (b : TY),
        ∑ γ : (plaqGraph n L Lt).Path a.1 b.1, p ^ ((γ : (plaqGraph n L Lt).Walk a.1 b.1).support.toFinset).card
          ≤ p * B := by
      intro a b
      have hcard : ∀ γ : (plaqGraph n L Lt).Path a.1 b.1,
          ((γ : (plaqGraph n L Lt).Walk a.1 b.1).support.toFinset).card
            = (γ : (plaqGraph n L Lt).Walk a.1 b.1).length + 1 := by
        intro γ
        rw [List.toFinset_card_of_nodup γ.2.support_nodup, SimpleGraph.Walk.length_support]
      simp_rw [hcard, pow_succ]
      rw [← Finset.sum_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ hp0
      refine path_sum_le_general (plaqGraph n L Lt) (fun v => degree_plaq_le v) hp0 hq ?_
      intro γ
      obtain ⟨x, hxX, hxa⟩ := Finset.mem_biUnion.mp a.2
      obtain ⟨y, hyY, hyb⟩ := Finset.mem_biUnion.mp b.2
      have h1 := hD x hxX y hyY
      have h2 := length_ge_time (γ : (plaqGraph n L Lt).Walk a.1 b.1)
        (Finset.mem_filter.mp hxa).2 (Finset.mem_filter.mp hyb).2
      omega
    calc ∑ k, p ^ (S k).card
        = ∑ a : TX, ∑ b : TY, ∑ γ : (plaqGraph n L Lt).Path a.1 b.1,
            p ^ ((γ : (plaqGraph n L Lt).Walk a.1 b.1).support.toFinset).card := by
          simp only [κ, S, Fintype.sum_sigma]
      _ ≤ ∑ _a : TX, ∑ _b : TY, p * B :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hinner a b
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, TX, TY, Fintype.card_coe]
          ring
  have hsum2 : ∑ k, p ^ (S k).card ≤
      (((X.card * (2 * n) : ℕ) : ℝ) * ((Y.card * (2 * n) : ℕ) : ℝ)) * (p * B) := by
    refine hsum.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hp0 hB0))
    exact mul_le_mul (by exact_mod_cast card_touch_le X) (by exact_mod_cast card_touch_le Y)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- back to the Gibbs state
  set w : (Link n L Lt → G) → ℝ := wilsonWeight χ J with hw
  have hwm : Measurable w := measurable_wilsonWeight hχm J
  set Bw : ℝ := Real.exp (|J| * plaqCount n L Lt) with hBw
  have hwb : ∀ U, ‖((w U : ℝ) : ℂ)‖ ≤ Bw := by
    intro U
    have h0 : 0 ≤ w U := (Real.exp_pos _).le
    rw [Complex.norm_real, Real.norm_of_nonneg h0]
    exact wilsonWeight_le hχ J U
  set Wc : (Link n L Lt → G) → ℂ := fun U => ((w U : ℝ) : ℂ) with hWc
  have hWcm : Measurable Wc := Complex.measurable_ofReal.comp hwm
  have hFf : Measurable fun U => f U * Wc U := hfm.mul hWcm
  have hFg : Measurable fun U => g U * Wc U := hgm.mul hWcm
  have hA : Measurable fun U => f U * g U * Wc U := (hfm.mul hgm).mul hWcm
  have hBw0 : 0 ≤ Bw := (Real.exp_pos _).le
  have bFf : ∀ U, ‖f U * Wc U‖ ≤ Bw := fun U => by
    rw [norm_mul]; nlinarith [hf1 U, hwb U, norm_nonneg (f U), norm_nonneg (Wc U)]
  have bFg : ∀ U, ‖g U * Wc U‖ ≤ Bw := fun U => by
    rw [norm_mul]; nlinarith [hg1 U, hwb U, norm_nonneg (g U), norm_nonneg (Wc U)]
  have bA : ∀ U, ‖f U * g U * Wc U‖ ≤ Bw := fun U => by
    rw [norm_mul, norm_mul]
    have h1 : ‖f U‖ * ‖g U‖ ≤ 1 := by nlinarith [hf1 U, hg1 U, norm_nonneg (f U), norm_nonneg (g U)]
    nlinarith [hwb U, norm_nonneg (Wc U), mul_nonneg (norm_nonneg (f U)) (norm_nonneg (g U))]
  set Z : ℝ := ∫ U, w U ∂(linkMeasure μ₀) with hZ
  have hZpos : 0 < Z := partition_pos_general μ₀ hχm hχ J
  have hZc : ∫ U, Wc U ∂(linkMeasure μ₀) = (Z : ℂ) := by
    simp only [hWc, hZ]
    exact integral_ofReal
  set If : ℂ := ∫ U, f U * Wc U ∂(linkMeasure μ₀) with hIf
  set Ig : ℂ := ∫ U, g U * Wc U ∂(linkMeasure μ₀) with hIg
  set Ifg : ℂ := ∫ U, f U * g U * Wc U ∂(linkMeasure μ₀) with hIfg
  set K : ℝ := Real.exp (2 * (|J| * plaqCount n L Lt)) with hK
  have hK0 : 0 < K := Real.exp_pos _
  -- the denominator
  have hden : ∫ ω, (1 : ℝ) * ∏ q : Plaq n L Lt, (1 + gP χ J q ω)
      ∂(dupMeasure (n := n) (L := L) (Lt := Lt) μ₀) = K * (Z * Z) := by
    simp_rw [one_mul, prod_gP, ← hK, ← hw]
    rw [integral_const_mul, integral_dup_mul μ₀ w w]
  -- the numerator
  have hnum : ∫ ω, covW f g ω * (((1 : ℝ) * ∏ q : Plaq n L Lt, (1 + gP χ J q ω) : ℝ) : ℂ)
      ∂(dupMeasure (n := n) (L := L) (Lt := Lt) μ₀)
      = (K : ℂ) * ((1 / 2 : ℂ) * ((Z : ℂ) * Ifg - If * Ig)) := by
    have hpt : ∀ ω : Dup n L Lt G,
        covW f g ω * (((1 : ℝ) * ∏ q : Plaq n L Lt, (1 + gP χ J q ω) : ℝ) : ℂ)
        = (K : ℂ) * ((1 / 4 : ℂ) * (
            ((f (fstC ω) * g (fstC ω) * Wc (fstC ω)) * Wc (sndC ω)
              - (f (fstC ω) * Wc (fstC ω)) * (g (sndC ω) * Wc (sndC ω)))
            - (g (fstC ω) * Wc (fstC ω)) * (f (sndC ω) * Wc (sndC ω))
            + Wc (fstC ω) * (f (sndC ω) * g (sndC ω) * Wc (sndC ω)))) := by
      intro ω
      rw [one_mul, prod_gP, ← hK, ← hw]
      simp only [covW, hWc]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_const_mul]
    have i1 : Integrable (fun ω : Dup n L Lt G =>
        f (fstC ω) * g (fstC ω) * Wc (fstC ω) * Wc (sndC ω)) (dupMeasure μ₀) :=
      integrable_dup μ₀ hA hWcm bA hwb
    have i2 : Integrable (fun ω : Dup n L Lt G =>
        f (fstC ω) * Wc (fstC ω) * (g (sndC ω) * Wc (sndC ω))) (dupMeasure μ₀) :=
      integrable_dup μ₀ hFf hFg bFf bFg
    have i3 : Integrable (fun ω : Dup n L Lt G =>
        g (fstC ω) * Wc (fstC ω) * (f (sndC ω) * Wc (sndC ω))) (dupMeasure μ₀) :=
      integrable_dup μ₀ hFg hFf bFg bFf
    have i4 : Integrable (fun ω : Dup n L Lt G =>
        Wc (fstC ω) * (f (sndC ω) * g (sndC ω) * Wc (sndC ω))) (dupMeasure μ₀) :=
      integrable_dup μ₀ hWcm hA hwb bA
    have i12 : Integrable (fun ω : Dup n L Lt G =>
        f (fstC ω) * g (fstC ω) * Wc (fstC ω) * Wc (sndC ω)
          - f (fstC ω) * Wc (fstC ω) * (g (sndC ω) * Wc (sndC ω))) (dupMeasure μ₀) := i1.sub i2
    have i123 : Integrable (fun ω : Dup n L Lt G =>
        f (fstC ω) * g (fstC ω) * Wc (fstC ω) * Wc (sndC ω)
          - f (fstC ω) * Wc (fstC ω) * (g (sndC ω) * Wc (sndC ω))
          - g (fstC ω) * Wc (fstC ω) * (f (sndC ω) * Wc (sndC ω))) (dupMeasure μ₀) := i12.sub i3
    have d1 : ∫ ω : Dup n L Lt G, f (fstC ω) * g (fstC ω) * Wc (fstC ω) * Wc (sndC ω) ∂(dupMeasure μ₀)
        = Ifg * (Z : ℂ) := by
      rw [← hZc]; exact integral_dup_mul μ₀ (fun U => f U * g U * Wc U) Wc
    have d2 : ∫ ω : Dup n L Lt G, f (fstC ω) * Wc (fstC ω) * (g (sndC ω) * Wc (sndC ω)) ∂(dupMeasure μ₀)
        = If * Ig := integral_dup_mul μ₀ (fun U => f U * Wc U) (fun U => g U * Wc U)
    have d3 : ∫ ω : Dup n L Lt G, g (fstC ω) * Wc (fstC ω) * (f (sndC ω) * Wc (sndC ω)) ∂(dupMeasure μ₀)
        = Ig * If := integral_dup_mul μ₀ (fun U => g U * Wc U) (fun U => f U * Wc U)
    have d4 : ∫ ω : Dup n L Lt G, Wc (fstC ω) * (f (sndC ω) * g (sndC ω) * Wc (sndC ω)) ∂(dupMeasure μ₀)
        = (Z : ℂ) * Ifg := by
      rw [← hZc]; exact integral_dup_mul μ₀ Wc (fun U => f U * g U * Wc U)
    rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2, d1, d2, d3, d4]
    ring
  -- combine
  rw [hnum, hden] at hbound
  have hbound2 : ‖(Z : ℂ) * Ifg - If * Ig‖ ≤ 2 * (∑ k, p ^ (S k).card) * (Z * Z) := by
    have hnorm : ‖(K : ℂ) * ((1 / 2 : ℂ) * ((Z : ℂ) * Ifg - If * Ig))‖
        = K * ((1 / 2) * ‖(Z : ℂ) * Ifg - If * Ig‖) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0.le]
      congr 2
      simp
    rw [hnorm] at hbound
    have h3 : K * ((1 / 2) * ‖(Z : ℂ) * Ifg - If * Ig‖)
        ≤ K * ((∑ k, p ^ (S k).card) * (Z * Z)) := by
      calc _ ≤ _ := hbound
        _ = _ := by ring
    have h4 := le_of_mul_le_mul_left h3 hK0
    linarith
  have hZcne : (Z : ℂ) ≠ 0 := by exact_mod_cast hZpos.ne'
  have hgibbs : gibbs μ₀ χ J (fun U => f U * g U) - gibbs μ₀ χ J f * gibbs μ₀ χ J g
      = ((Z : ℂ) * Ifg - If * Ig) / ((Z : ℂ) * (Z : ℂ)) := by
    have e1 : gibbs μ₀ χ J (fun U => f U * g U) = Ifg / (Z : ℂ) := rfl
    have e2 : gibbs μ₀ χ J f = If / (Z : ℂ) := rfl
    have e3 : gibbs μ₀ χ J g = Ig / (Z : ℂ) := rfl
    rw [e1, e2, e3]
    field_simp
  rw [hgibbs, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hZpos.le,
    div_le_iff₀ (mul_pos hZpos hZpos)]
  refine hbound2.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_pos hZpos hZpos).le
  have := hsum2
  nlinarith

end dup

end Confinement
