/-
Copyright (c) 2026 Zihua Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zihua Wu
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# The spectral-norm Eckart–Young theorem

For a linear map `T` between finite-dimensional inner product spaces, the best rank-`≤ k`
approximation of `T` in the operator (spectral) norm has error equal to the `(k)`-th singular
value `σ_k(T)`:
`IsLeast {r | ∃ S, finrank (range S) ≤ k ∧ r = ‖(T - S).toContinuousLinearMap‖} (σ_k T)`.

The proof diagonalizes the quadratic form `‖T z‖²` in the eigenbasis of `adjoint T ∘ₗ T`
(the right singular vectors), giving two one-sided bounds: a min–max lower bound on a
`(k+1)`-dimensional subspace, and a tail upper bound on the orthogonal complement of the
top-`k` right singular vectors. The achievable minimizer is the truncated SVD `T ∘ₗ P`,
where `P` is the orthogonal projection onto the span of the top-`k` right singular vectors.

## Main statements

- `LinearMap.eckart_young_spectral_lower`: every rank-`≤ k` operator has operator-norm error at
  least `σ_k(T)`.
- `LinearMap.eckart_young_spectral_achievable`: the truncated SVD attains error `σ_k(T)`.
- `LinearMap.eckart_young_spectral`: the minimum operator-norm error is `σ_k(T)`.
-/

public section

open Module InnerProductSpace Finset
open scoped ComplexConjugate

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Quadratic-form diagonalization**: `‖T z‖² = ∑ σ_i(T)² · ‖⟪bᵢ, z⟫‖²`, where `b` is the
eigenbasis of `adjoint T ∘ₗ T` (the right singular vectors of `T`). -/
private theorem norm_sq_apply_eq_sum_sq_singularValues (T : E →ₗ[𝕜] F) (z : E) :
    ‖T z‖ ^ 2
      = ∑ i : Fin (finrank 𝕜 E),
          (T.singularValues i) ^ 2
            * ‖(inner 𝕜 ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl) i) z : 𝕜)‖ ^ 2 := by
  classical
  set b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hb
  -- `‖T z‖² = re ⟪z, (adjoint T ∘ₗ T) z⟫`.
  have h1 : ‖T z‖ ^ 2 = RCLike.re (inner 𝕜 z ((adjoint T ∘ₗ T) z)) := by
    rw [LinearMap.comp_apply, adjoint_inner_right, inner_self_eq_norm_sq]
  -- Each eigen-coordinate of `(adjoint T ∘ₗ T) z`.
  have hcoord : ∀ i, (inner 𝕜 (b i) ((adjoint T ∘ₗ T) z) : 𝕜)
      = ((T.singularValues i ^ 2 : ℝ) : 𝕜) * inner 𝕜 (b i) z := by
    intro i
    have happ : (adjoint T ∘ₗ T) (b i)
        = (T.isSymmetric_adjoint_comp_self.eigenvalues rfl i : 𝕜) • b i := by
      rw [hb]; exact T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
    rw [← T.isSymmetric_adjoint_comp_self (b i) z, happ, inner_smul_left, RCLike.conj_ofReal,
      ← T.sq_singularValues_fin rfl i]
  rw [h1, ← b.sum_inner_mul_inner z ((adjoint T ∘ₗ T) z), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcoord i, ← inner_conj_symm z (b i), mul_left_comm, RCLike.conj_mul, ← RCLike.ofReal_pow,
    ← RCLike.ofReal_mul, RCLike.ofReal_re]

omit [FiniteDimensional 𝕜 E] in
/-- If `z ∈ span 𝕜 (b '' s)`, then for any `i ∉ s` the coordinate `⟪bᵢ, z⟫ = 0`. -/
private theorem inner_eq_zero_of_mem_span
    (b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) {s : Set (Fin (finrank 𝕜 E))} {z : E}
    (hz : z ∈ Submodule.span 𝕜 (b '' s)) {i : Fin (finrank 𝕜 E)} (hi : i ∉ s) :
    (inner 𝕜 (b i) z : 𝕜) = 0 := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination 𝕜).mp hz
  rw [inner_eq_zero_symm]
  exact b.orthonormal.inner_finsupp_eq_zero hi hl

/-- **Min–max lower bound.** If the eigen-coordinates of `z` vanish above index `k`, then
`σ_k(T) · ‖z‖ ≤ ‖T z‖`. -/
private theorem singularValues_mul_norm_le_norm_apply (T : E →ₗ[𝕜] F) (k : ℕ) {z : E}
    (hz : ∀ i : Fin (finrank 𝕜 E), k < (i : ℕ) →
          (inner 𝕜 ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl) i) z : 𝕜) = 0) :
    T.singularValues k * ‖z‖ ≤ ‖T z‖ := by
  have hsq : (T.singularValues k) ^ 2 * ‖z‖ ^ 2 ≤ ‖T z‖ ^ 2 := by
    rw [T.norm_sq_apply_eq_sum_sq_singularValues z,
      ← (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).sum_sq_norm_inner_right z,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hik : (i : ℕ) ≤ k
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (T.singularValues_nonneg _) (T.singularValues_antitone hik) 2)
        (by positivity)
    · rw [hz i (by omega)]; simp
  exact (sq_le_sq₀ (mul_nonneg (T.singularValues_nonneg k) (norm_nonneg z))
    (norm_nonneg _)).mp (by rw [mul_pow]; exact hsq)

/-- **Tail upper bound.** If the eigen-coordinates of `z` vanish below index `k`, then
`‖T z‖ ≤ σ_k(T) · ‖z‖`. -/
private theorem norm_apply_le_singularValues_mul_norm (T : E →ₗ[𝕜] F) (k : ℕ) {z : E}
    (hz : ∀ i : Fin (finrank 𝕜 E), (i : ℕ) < k →
          (inner 𝕜 ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl) i) z : 𝕜) = 0) :
    ‖T z‖ ≤ T.singularValues k * ‖z‖ := by
  have hsq : ‖T z‖ ^ 2 ≤ (T.singularValues k) ^ 2 * ‖z‖ ^ 2 := by
    rw [T.norm_sq_apply_eq_sum_sq_singularValues z,
      ← (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).sum_sq_norm_inner_right z,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hik : (i : ℕ) < k
    · rw [hz i hik]; simp
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (T.singularValues_nonneg _) (T.singularValues_antitone (by omega)) 2)
        (by positivity)
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (T.singularValues_nonneg k) (norm_nonneg z))).mp (by rw [mul_pow]; exact hsq)

/-- **Eckart–Young lower bound (spectral norm).** Every rank-`≤ k` operator `S` leaves
operator-norm error at least `σ_k(T)`. -/
theorem eckart_young_spectral_lower (T : E →ₗ[𝕜] F) (k : ℕ) (S : E →ₗ[𝕜] F)
    (hS : finrank 𝕜 (LinearMap.range S) ≤ k) :
    T.singularValues k ≤ ‖(T - S).toContinuousLinearMap‖ := by
  classical
  rcases lt_or_ge k (finrank 𝕜 E) with hkn | hkn
  · set b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hb
    set V : Submodule 𝕜 E :=
      Submodule.span 𝕜 (b '' {i : Fin (finrank 𝕜 E) | (i : ℕ) ≤ k}) with hV
    -- `finrank V = k + 1`.
    have hVdim : finrank 𝕜 V = k + 1 := by
      have himg : b '' {i : Fin (finrank 𝕜 E) | (i : ℕ) ≤ k}
          = Set.range (⇑b ∘ Fin.castLE hkn) := by
        rw [Set.range_comp, Fin.range_castLE]
        exact congrArg (b '' ·) (by ext i; simp only [Set.mem_setOf_eq]; omega)
      rw [hV, himg, finrank_span_eq_card
        (b.orthonormal.linearIndependent.comp _ (Fin.castLE_injective hkn)), Fintype.card_fin]
    -- `finrank (ker S) ≥ (finrank E) - k`, hence `V ⊓ ker S ≠ ⊥`.
    have hne : V ⊓ LinearMap.ker S ≠ ⊥ := fun hbot => by
      have hle := Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hbot)
      have h2 := S.finrank_range_add_finrank_ker
      rw [hVdim] at hle
      omega
    obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨hxV, hxker⟩ := Submodule.mem_inf.mp hxmem
    have hcoord : ∀ i : Fin (finrank 𝕜 E), k < (i : ℕ) →
        (inner 𝕜 ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl) i) x : 𝕜) = 0 := by
      intro i hik
      rw [← hb]
      exact inner_eq_zero_of_mem_span b (hV ▸ hxV)
        fun h => by simp only [Set.mem_setOf_eq] at h; omega
    refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hx0)
    calc T.singularValues k * ‖x‖
        ≤ ‖T x‖ := T.singularValues_mul_norm_le_norm_apply k hcoord
      _ = ‖(T - S).toContinuousLinearMap x‖ := by
          rw [coe_toContinuousLinearMap', LinearMap.sub_apply, LinearMap.mem_ker.mp hxker,
            sub_zero]
      _ ≤ ‖(T - S).toContinuousLinearMap‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
  · rw [T.singularValues_of_finrank_le hkn]
    exact norm_nonneg _

/-- **Eckart–Young achievability (spectral norm).** The truncated SVD — projecting onto the span
of the top-`k` right singular vectors — attains operator-norm error `σ_k(T)`. -/
theorem eckart_young_spectral_achievable (T : E →ₗ[𝕜] F) (k : ℕ) :
    ∃ S : E →ₗ[𝕜] F,
      finrank 𝕜 (LinearMap.range S) ≤ k ∧
      ‖(T - S).toContinuousLinearMap‖ = T.singularValues k := by
  classical
  set b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hb
  set s : Finset (Fin (finrank 𝕜 E)) := univ.filter (fun i => (i : ℕ) < k) with hs
  set U : Submodule 𝕜 E := Submodule.span 𝕜 (↑(s.image b) : Set E) with hU
  set P : E →ₗ[𝕜] E := (U.starProjection : E →ₗ[𝕜] E) with hP
  -- `range (T ∘ₗ P)` has rank `≤ k`.
  have hrank : finrank 𝕜 (LinearMap.range (T ∘ₗ P)) ≤ k := by
    rw [LinearMap.range_comp]
    refine (Submodule.finrank_map_le T (LinearMap.range P)).trans ?_
    rw [hP, Submodule.range_starProjection, hU]
    refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
    rw [hs, Fin.card_filter_val_lt]
    omega
  refine ⟨T ∘ₗ P, hrank, ?_⟩
  refine le_antisymm ?_ (T.eckart_young_spectral_lower k (T ∘ₗ P) hrank)
  refine ContinuousLinearMap.opNorm_le_bound _ (T.singularValues_nonneg k) fun x => ?_
  rw [coe_toContinuousLinearMap', show (T - T ∘ₗ P) x = T (x - P x) by
    simp [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]]
  have hnormle : ‖x - P x‖ ≤ ‖x‖ := by
    have hrw : x - P x = Uᗮ.starProjection x := by
      rw [hP, ContinuousLinearMap.coe_coe, sub_eq_iff_eq_add, add_comm]
      exact (U.starProjection_add_starProjection_orthogonal x).symm
    rw [hrw]; exact Uᗮ.norm_starProjection_apply_le x
  have hperp : x - P x ∈ (Submodule.span 𝕜 (b '' {j : Fin (finrank 𝕜 E) | (j : ℕ) < k}))ᗮ := by
    have hconv : (↑(s.image b) : Set E) = b '' {j : Fin (finrank 𝕜 E) | (j : ℕ) < k} := by
      ext y; simp [hs]
    rw [← hconv, ← hU, hP]
    exact U.sub_starProjection_mem_orthogonal x
  have hcoord : ∀ i : Fin (finrank 𝕜 E), (i : ℕ) < k →
      (inner 𝕜 ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl) i) (x - P x) : 𝕜) = 0 := by
    intro i hik
    rw [← hb]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_image_of_mem b hik)) hperp
  calc ‖T (x - P x)‖ ≤ T.singularValues k * ‖x - P x‖ :=
        T.norm_apply_le_singularValues_mul_norm k hcoord
    _ ≤ T.singularValues k * ‖x‖ :=
        mul_le_mul_of_nonneg_left hnormle (T.singularValues_nonneg k)

/-- **Eckart–Young theorem (spectral norm).** The minimum operator-norm error of a rank-`≤ k`
approximation of `T` is the `k`-th singular value `σ_k(T)`. -/
theorem eckart_young_spectral (T : E →ₗ[𝕜] F) (k : ℕ) :
    IsLeast {r : ℝ | ∃ S : E →ₗ[𝕜] F, finrank 𝕜 (LinearMap.range S) ≤ k ∧
      r = ‖(T - S).toContinuousLinearMap‖} (T.singularValues k) := by
  constructor
  · obtain ⟨S, hS, hEq⟩ := eckart_young_spectral_achievable T k
    exact ⟨S, hS, hEq.symm⟩
  · rintro r ⟨S, hS, rfl⟩
    exact eckart_young_spectral_lower T k S hS

end LinearMap
