import Mathlib

/-!
# Tensor products of Schwartz functions on configuration spaces

Prerequisite for stating Osterwalder-Schrader positivity and clustering: Mathlib v4.33.0 has no
tensor product `𝓢(D₁, ℝ) × 𝓢(D₂, ℝ) → 𝓢(D₁ × D₂, ℝ)`. We construct it with an explicit
seminorm bound (Leibniz rule), and transport it to configurations `Fin (n + m) → E`.
-/

open scoped SchwartzMap

noncomputable section

namespace YMStatement

theorem natCast_le_infty (i : ℕ) : ((i : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  first
  | exact_mod_cast le_top
  | simp
  | exact WithTop.coe_le_coe.2 le_top

section ProdTensor

variable {D₁ D₂ : Type*} [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
  [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]

theorem norm_iteratedFDeriv_comp_fst_le (f : 𝓢(D₁, ℝ)) (z : D₁ × D₂) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z : D₁ × D₂ => f z.1) z‖ ≤ ‖iteratedFDeriv ℝ i f z.1‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.fst ℝ D₁ D₂)
    (f.smooth ⊤) z (natCast_le_infty i)
  have e : (fun z : D₁ × D₂ => f z.1) = (⇑f ∘ ⇑(ContinuousLinearMap.fst ℝ D₁ D₂)) := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ D₁ D₂‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ D₁ D₂)
  calc ‖iteratedFDeriv ℝ i (⇑f) ((ContinuousLinearMap.fst ℝ D₁ D₂) z)‖ *
        ∏ _j : Fin i, ‖ContinuousLinearMap.fst ℝ D₁ D₂‖
      ≤ ‖iteratedFDeriv ℝ i (⇑f) ((ContinuousLinearMap.fst ℝ D₁ D₂) z)‖ * 1 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ i f z.1‖ := by simp

theorem norm_iteratedFDeriv_comp_snd_le (g : 𝓢(D₂, ℝ)) (z : D₁ × D₂) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun z : D₁ × D₂ => g z.2) z‖ ≤ ‖iteratedFDeriv ℝ i g z.2‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.snd ℝ D₁ D₂)
    (g.smooth ⊤) z (natCast_le_infty i)
  have e : (fun z : D₁ × D₂ => g z.2) = (⇑g ∘ ⇑(ContinuousLinearMap.snd ℝ D₁ D₂)) := rfl
  rw [e, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _j : Fin i, ‖ContinuousLinearMap.snd ℝ D₁ D₂‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_snd_le ℝ D₁ D₂)
  calc ‖iteratedFDeriv ℝ i (⇑g) ((ContinuousLinearMap.snd ℝ D₁ D₂) z)‖ *
        ∏ _j : Fin i, ‖ContinuousLinearMap.snd ℝ D₁ D₂‖
      ≤ ‖iteratedFDeriv ℝ i (⇑g) ((ContinuousLinearMap.snd ℝ D₁ D₂) z)‖ * 1 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ i g z.2‖ := by simp

theorem prodTensor_decay (f : 𝓢(D₁, ℝ)) (g : 𝓢(D₂, ℝ)) (k l : ℕ) :
    ∃ C : ℝ, ∀ z : D₁ × D₂,
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ l (fun z : D₁ × D₂ => f z.1 * g z.2) z‖ ≤ C := by
  refine ⟨∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
      (SchwartzMap.seminorm ℝ k i f * SchwartzMap.seminorm ℝ 0 (l - i) g +
        SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ k (l - i) g), fun z => ?_⟩
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : D₁ × D₂ => f z.1) :=
    (f.smooth ⊤).comp contDiff_fst
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : D₁ × D₂ => g z.2) :=
    (g.smooth ⊤).comp contDiff_snd
  have hsum := norm_iteratedFDeriv_mul_le hf hg z (n := l) (natCast_le_infty l)
  have hz : ‖z‖ ^ k ≤ ‖z.1‖ ^ k + ‖z.2‖ ^ k := by
    rw [Prod.norm_def]
    rcases le_total ‖z.1‖ ‖z.2‖ with h | h
    · rw [max_eq_right h]
      have := pow_nonneg (norm_nonneg z.1) k
      linarith
    · rw [max_eq_left h]
      have := pow_nonneg (norm_nonneg z.2) k
      linarith
  have hzk : 0 ≤ ‖z‖ ^ k := by positivity
  calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ l (fun z : D₁ × D₂ => f z.1 * g z.2) z‖
      ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun z : D₁ × D₂ => f z.1) z‖ *
          ‖iteratedFDeriv ℝ (l - i) (fun z : D₁ × D₂ => g z.2) z‖ :=
        mul_le_mul_of_nonneg_left hsum hzk
    _ = ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) *
          (‖z‖ ^ k * ‖iteratedFDeriv ℝ i (fun z : D₁ × D₂ => f z.1) z‖ *
          ‖iteratedFDeriv ℝ (l - i) (fun z : D₁ × D₂ => g z.2) z‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ ≤ _ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have a1 := norm_iteratedFDeriv_comp_fst_le (D₂ := D₂) f z i
        have a2 := norm_iteratedFDeriv_comp_snd_le (D₁ := D₁) g z (l - i)
        have b1 := SchwartzMap.le_seminorm ℝ k i f z.1
        have b2 := SchwartzMap.le_seminorm ℝ k (l - i) g z.2
        have c1 := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f i z.1
        have c2 := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g (l - i) z.2
        have hA := norm_nonneg (iteratedFDeriv ℝ i (fun z : D₁ × D₂ => f z.1) z)
        have hB := norm_nonneg (iteratedFDeriv ℝ (l - i) (fun z : D₁ × D₂ => g z.2) z)
        have ha := norm_nonneg (iteratedFDeriv ℝ i f z.1)
        have hb := norm_nonneg (iteratedFDeriv ℝ (l - i) g z.2)
        have h1k : 0 ≤ ‖z.1‖ ^ k := by positivity
        have h2k : 0 ≤ ‖z.2‖ ^ k := by positivity
        have s1 := apply_nonneg (SchwartzMap.seminorm ℝ k i) f
        have s3 := apply_nonneg (SchwartzMap.seminorm ℝ 0 i) f
        calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ i (fun z : D₁ × D₂ => f z.1) z‖ *
              ‖iteratedFDeriv ℝ (l - i) (fun z : D₁ × D₂ => g z.2) z‖
            ≤ (‖z.1‖ ^ k + ‖z.2‖ ^ k) * ‖iteratedFDeriv ℝ i f z.1‖ *
              ‖iteratedFDeriv ℝ (l - i) g z.2‖ :=
              mul_le_mul (mul_le_mul hz a1 hA (by positivity)) a2 hB (by positivity)
          _ = (‖z.1‖ ^ k * ‖iteratedFDeriv ℝ i f z.1‖) * ‖iteratedFDeriv ℝ (l - i) g z.2‖ +
              ‖iteratedFDeriv ℝ i f z.1‖ * (‖z.2‖ ^ k * ‖iteratedFDeriv ℝ (l - i) g z.2‖) := by
              ring
          _ ≤ _ := add_le_add (mul_le_mul b1 c2 hb s1) (mul_le_mul c1 b2 (by positivity) s3)

/-- The tensor product `(f ⊗ g)(x, y) = f x * g y` of two real Schwartz functions. -/
def prodTensor (f : 𝓢(D₁, ℝ)) (g : 𝓢(D₂, ℝ)) : 𝓢(D₁ × D₂, ℝ) where
  toFun z := f z.1 * g z.2
  smooth' := ((f.smooth ⊤).comp contDiff_fst).mul ((g.smooth ⊤).comp contDiff_snd)
  decay' := prodTensor_decay f g

@[simp] theorem prodTensor_apply (f : 𝓢(D₁, ℝ)) (g : 𝓢(D₂, ℝ)) (z : D₁ × D₂) :
    prodTensor f g z = f z.1 * g z.2 := rfl

end ProdTensor

/-- Split a configuration of `n + m` points into its first `n` and its last `m` points. -/
def splitCLE (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n m : ℕ) :
    (Fin (n + m) → E) ≃L[ℝ] (Fin n → E) × (Fin m → E) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (n + m) => E) finSumFinEquiv).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin n) (Fin m) (fun _ => E))

section Config

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem splitCLE_apply (n m : ℕ) (x : Fin (n + m) → E) :
    splitCLE E n m x = (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j)) := by
  first
  | rfl
  | (ext <;> simp [splitCLE])

/-- Tensor product of a Schwartz function of `n` points with one of `m` points:
`(F ⊗ G)(x₁, …, x_{n+m}) = F(x₁, …, xₙ) · G(x_{n+1}, …, x_{n+m})`. -/
def tensor {n m : ℕ} (F : 𝓢(Fin n → E, ℝ)) (G : 𝓢(Fin m → E, ℝ)) :
    𝓢(Fin (n + m) → E, ℝ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (splitCLE E n m) (prodTensor F G)

@[simp] theorem tensor_apply {n m : ℕ} (F : 𝓢(Fin n → E, ℝ)) (G : 𝓢(Fin m → E, ℝ))
    (x : Fin (n + m) → E) :
    tensor F G x = F (fun i => x (Fin.castAdd m i)) * G (fun j => x (Fin.natAdd n j)) := by
  simp [tensor]

end Config

end YMStatement
