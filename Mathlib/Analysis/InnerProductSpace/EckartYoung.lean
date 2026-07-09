/-
Copyright (c) 2026 Zihua Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zihua Wu
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.HilbertSchmidt

/-!
# Singular values and the Eckart–Young–Mirsky theorem (Hilbert–Schmidt norm)

For a linear map `T` between finite-dimensional inner product spaces, the sum of the squared
singular values equals the real part of the trace of `adjoint T ∘ₗ T`, i.e. the squared
Hilbert–Schmidt (Frobenius) norm of `T`. That norm is provided by
`Mathlib.Analysis.InnerProductSpace.HilbertSchmidt` (activated here with
`open scoped LinearMap.Norms.HilbertSchmidt`), so the main results below are stated in terms of
`‖·‖`.

This identity is the bridge that lets an Eckart–Young–Mirsky theorem (best rank-`k`
approximation) be stated in terms of `LinearMap.singularValues`.

## Main definitions

- `LinearMap.topSqSingularValues T k`: the sum of the top `k` squared singular values,
  `∑ i < k, σ_i²`.
- `LinearMap.tailSqSingularValues T k`: the squared best rank-`≤ k` approximation error,
  `∑ i ≥ k, σ_i²`.

## Main statements

- `LinearMap.hilbertSchmidt_norm_sq_eq_sum_sq_singularValues`:
  `‖T‖ ^ 2 = ∑ i, (T.singularValues i) ^ 2`.
- `LinearMap.kyFan_le`: **Ky Fan's maximal principle**, the `≤` direction — for a rank-`k`
  orthogonal projection `Q`, `re (trace (Q ∘ₗ adjoint T ∘ₗ T)) ≤ topSqSingularValues T k`.
- `LinearMap.eckart_young`: **Eckart–Young–Mirsky** — `tailSqSingularValues T k` is the
  least squared Frobenius error `‖T - S‖ ^ 2` over all `S` with `finrank (range S) ≤ k`.
- `LinearMap.sum_sq_singularValues_eq_re_trace`:
  `∑ i, (T.singularValues i) ^ 2 = re (trace (adjoint T ∘ₗ T))`.
-/

public section

open Module InnerProductSpace Finset
open scoped LinearMap.Norms.HilbertSchmidt

/-- **Bathtub / rearrangement bound** (the elementary combinatorial core of Ky Fan's maximal
principle). For a descending nonnegative sequence `lam` and weights `c ∈ [0,1]` summing to `k`,
the weighted sum `∑ lamᵢ cᵢ` is at most the sum of the top `k` values. -/
private lemma weighted_sum_le_top {N : ℕ} {lam : Fin N → ℝ} (hanti : Antitone lam)
    (hnn : ∀ i, 0 ≤ lam i) {c : Fin N → ℝ} (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    {k : ℕ} (hk : k ≤ N) (hsum : ∑ i, c i = (k : ℝ)) :
    ∑ i, lam i * c i ≤ ∑ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < k), lam i := by
  classical
  set e : Fin N → ℝ := fun i => (if (i : ℕ) < k then (1 : ℝ) else 0) - c i with he
  have hsum_e : ∑ i, e i = 0 := by
    simp [he, Finset.sum_sub_distrib, Fin.card_filter_val_lt, Nat.min_eq_right hk, hsum]
  rw [Finset.sum_filter, ← sub_nonneg, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun (i : Fin N) _ =>
      show (if (i : ℕ) < k then lam i else 0) - lam i * c i = lam i * e i by
        simp only [he, mul_sub, mul_ite, mul_one, mul_zero]]
  rcases Nat.lt_or_ge k N with hkN | hkN
  · -- shift by `τ = lam k`: each term `(lam i - τ) * e i` is nonneg by the sign pattern of `e`
    have hshift : ∑ i, lam i * e i = ∑ i, (lam i - lam ⟨k, hkN⟩) * e i := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_e, mul_zero, sub_zero]
    rw [hshift]
    refine Finset.sum_nonneg fun i _ => ?_
    rcases lt_or_ge (i : ℕ) k with h | h
    · simp only [he, if_pos h]
      exact mul_nonneg (sub_nonneg.mpr (hanti (Fin.le_def.mpr h.le))) (sub_nonneg.mpr (hc1 i))
    · simp only [he, if_neg (not_lt.mpr h)]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hanti (Fin.le_def.mpr h)))
        (sub_nonpos.mpr (hc0 i))
  · refine Finset.sum_nonneg fun i _ => ?_
    simp only [he, if_pos (lt_of_lt_of_le i.isLt hkN)]
    exact mul_nonneg (hnn i) (sub_nonneg.mpr (hc1 i))

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The sum of the squared singular values of `T` equals the real part of the trace of
`adjoint T ∘ₗ T` — the squared Hilbert–Schmidt (Frobenius) norm of `T`. -/
theorem sum_sq_singularValues_eq_re_trace (T : E →ₗ[𝕜] F) :
    ∑ i ∈ Finset.range (finrank 𝕜 E), T.singularValues i ^ 2
      = RCLike.re (LinearMap.trace 𝕜 E (adjoint T ∘ₗ T)) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => T.singularValues i ^ 2),
    (T.isSymmetric_adjoint_comp_self).re_trace_eq_sum_eigenvalues rfl]
  exact Finset.sum_congr rfl fun i _ => T.sq_singularValues_fin rfl i

/-- The sum of the top-`k` squared singular values over `Fin (finrank 𝕜 E)` (indices `< k`)
equals the natural `ℕ`-indexed sum over `Finset.range k`. Bridges the eigenbasis-side
`Fin`-sums to the `singularValues`-side `range`-sums. -/
private theorem sum_filter_sq_singularValues_eq_range (T : E →ₗ[𝕜] F) (k : ℕ) :
    ∑ i ∈ univ.filter (fun i : Fin (finrank 𝕜 E) => (i : ℕ) < k), (T.singularValues i) ^ 2
      = ∑ i ∈ Finset.range k, (T.singularValues i) ^ 2 := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range
    (fun i => if i < k then T.singularValues i ^ 2 else 0), ← Finset.sum_filter]
  refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr (Finset.mem_filter.mp hx).2)
    fun x hx hnx => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hx hnx
  rw [T.singularValues_of_finrank_le (by omega)]; ring

/-- The squared Hilbert–Schmidt (Frobenius) norm of `T` equals `∑ᵢ σ_i(T)²`. -/
theorem hilbertSchmidt_norm_sq_eq_sum_sq_singularValues (T : E →ₗ[𝕜] F) :
    ‖T‖ ^ 2 = ∑ i ∈ Finset.range (finrank 𝕜 E), (T.singularValues i) ^ 2 :=
  (hilbertSchmidt_norm_sq_eq_re_trace T).trans (sum_sq_singularValues_eq_re_trace T).symm

/-- Sum of the top `k` squared singular values of `T`, `∑ i < k, σ_i(T)²`. -/
@[expose] noncomputable def topSqSingularValues (T : E →ₗ[𝕜] F) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (T.singularValues i) ^ 2

theorem topSqSingularValues_eq_sum_range (T : E →ₗ[𝕜] F) (k : ℕ) :
    topSqSingularValues T k = ∑ i ∈ Finset.range k, (T.singularValues i) ^ 2 := rfl

/-- The squared Frobenius error of the best rank-`≤ k` approximation of `T` (Eckart–Young–Mirsky):
the tail sum of squared singular values, `∑ k ≤ i < finrank 𝕜 E, σ_i(T)²`. -/
@[expose] noncomputable def tailSqSingularValues (T : E →ₗ[𝕜] F) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico k (finrank 𝕜 E), (T.singularValues i) ^ 2

theorem tailSqSingularValues_eq_sum_Ico (T : E →ₗ[𝕜] F) (k : ℕ) :
    tailSqSingularValues T k = ∑ i ∈ Finset.Ico k (finrank 𝕜 E), (T.singularValues i) ^ 2 := rfl

theorem topSqSingularValues_nonneg (T : E →ₗ[𝕜] F) (k : ℕ) : 0 ≤ topSqSingularValues T k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem tailSqSingularValues_nonneg (T : E →ₗ[𝕜] F) (k : ℕ) : 0 ≤ tailSqSingularValues T k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem topSqSingularValues_mono (T : E →ₗ[𝕜] F) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    topSqSingularValues T k₁ ≤ topSqSingularValues T k₂ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) fun _ _ _ =>
    sq_nonneg _

/-- For `k ≥ finrank 𝕜 E` all singular values past the domain dimension vanish, so the top-`k`
sum is the full squared norm. -/
theorem topSqSingularValues_of_finrank_le (T : E →ₗ[𝕜] F) {k : ℕ} (h : finrank 𝕜 E ≤ k) :
    topSqSingularValues T k = ‖T‖ ^ 2 := by
  have hz : ∑ i ∈ Finset.Ico (finrank 𝕜 E) k, T.singularValues i ^ 2 = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp [T.singularValues_of_finrank_le (Finset.mem_Ico.mp hi).1]
  rw [hilbertSchmidt_norm_sq_eq_sum_sq_singularValues, topSqSingularValues,
    ← Finset.sum_range_add_sum_Ico (fun i => T.singularValues i ^ 2) h, hz, add_zero]

theorem topSqSingularValues_le_norm_sq (T : E →ₗ[𝕜] F) (k : ℕ) :
    topSqSingularValues T k ≤ ‖T‖ ^ 2 := by
  rw [← topSqSingularValues_of_finrank_le T (Nat.le_add_left (finrank 𝕜 E) k)]
  exact topSqSingularValues_mono T (Nat.le_add_right k (finrank 𝕜 E))

/-- The tail sum equals the total squared Hilbert–Schmidt norm minus the top-`k` sum. -/
theorem tailSqSingularValues_eq_norm_sq_sub (T : E →ₗ[𝕜] F) (k : ℕ) :
    tailSqSingularValues T k = ‖T‖ ^ 2 - topSqSingularValues T k := by
  rcases le_total k (finrank 𝕜 E) with h | h
  · rw [tailSqSingularValues_eq_sum_Ico, hilbertSchmidt_norm_sq_eq_sum_sq_singularValues,
      topSqSingularValues, Finset.sum_Ico_eq_sub _ h]
  · rw [tailSqSingularValues_eq_sum_Ico, Finset.Ico_eq_empty (not_lt.mpr h), Finset.sum_empty,
      topSqSingularValues_of_finrank_le T h, sub_self]

theorem topSqSingularValues_add_tailSqSingularValues (T : E →ₗ[𝕜] F) (k : ℕ) :
    topSqSingularValues T k + tailSqSingularValues T k = ‖T‖ ^ 2 := by
  rw [tailSqSingularValues_eq_norm_sq_sub]; ring

/-- **Ky Fan's maximal principle** (the `≤` direction, operator form). For an orthogonal
projection `Q` (symmetric projection) of rank `k` on `E`, the projected Gram sum
`re tr(Q ∘ₗ adjoint T ∘ₗ T)` is at most the sum of the top `k` squared singular values
of `T`. The combinatorial core is `weighted_sum_le_top`; the weights are the projection's
diagonal `cᵢ = ⟪qᵢ, Q qᵢ⟫ = ‖Q qᵢ‖²` in the eigenbasis `q` of `adjoint T ∘ₗ T`. -/
theorem kyFan_le (T : E →ₗ[𝕜] F) (Q : E →ₗ[𝕜] E) (hQ : Q.IsSymmetricProjection)
    {k : ℕ} (htr : finrank 𝕜 (LinearMap.range Q) = k) :
    RCLike.re (LinearMap.trace 𝕜 E (Q ∘ₗ (adjoint T ∘ₗ T))) ≤ topSqSingularValues T k := by
  classical
  have hk : k ≤ finrank 𝕜 E := htr ▸ Submodule.finrank_le _
  have hSsymm : (adjoint T ∘ₗ T).IsSymmetric := T.isSymmetric_adjoint_comp_self
  set b := hSsymm.eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) with hb
  have hQQ : ∀ x, Q (Q x) = Q x := fun x => LinearMap.congr_fun hQ.isIdempotentElem x
  have happ : ∀ i, (adjoint T ∘ₗ T) (b i)
      = (hSsymm.eigenvalues (rfl : finrank 𝕜 E = finrank 𝕜 E) i : 𝕜) • b i := fun i => by
    rw [hb]; exact hSsymm.apply_eigenvectorBasis rfl i
  have hinner : ∀ i, (inner 𝕜 (b i) (Q (b i)) : 𝕜) = (‖Q (b i)‖ : 𝕜) ^ 2 := fun i => by
    rw [← inner_self_eq_norm_sq_to_K, hQ.isSymmetric (b i) (Q (b i)), hQQ]
  have hc0 : ∀ i, 0 ≤ RCLike.re (inner 𝕜 (b i) (Q (b i))) := fun i => by
    rw [hinner i, RCLike.re_ofReal_pow]; positivity
  have hc1 : ∀ i, RCLike.re (inner 𝕜 (b i) (Q (b i))) ≤ 1 := fun i => by
    obtain ⟨_, hQeq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hQ
    rw [hinner i, RCLike.re_ofReal_pow, hQeq]
    exact pow_le_one₀ (norm_nonneg _)
      ((Submodule.norm_starProjection_apply_le _ _).trans_eq (b.orthonormal.1 i))
  have hsum_c : ∑ i, RCLike.re (inner 𝕜 (b i) (Q (b i))) = (k : ℝ) := by
    rw [← map_sum, ← LinearMap.trace_eq_sum_inner Q b,
      ((LinearMap.isProj_range_iff_isIdempotentElem Q).mpr hQ.isIdempotentElem).trace,
      RCLike.natCast_re, htr]
  have htrace : RCLike.re (LinearMap.trace 𝕜 E (Q ∘ₗ (adjoint T ∘ₗ T)))
      = ∑ i, hSsymm.eigenvalues (rfl : finrank 𝕜 E = finrank 𝕜 E) i
          * RCLike.re (inner 𝕜 (b i) (Q (b i))) := by
    rw [LinearMap.trace_eq_sum_inner (Q ∘ₗ (adjoint T ∘ₗ T)) b, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, happ i, map_smul, inner_smul_right, RCLike.re_ofReal_mul]
  rw [htrace, topSqSingularValues, ← sum_filter_sq_singularValues_eq_range,
    Finset.sum_congr rfl fun i _ => T.sq_singularValues_fin rfl i]
  exact weighted_sum_le_top (hSsymm.eigenvalues_antitone rfl)
    (fun i => by rw [← T.sq_singularValues_fin rfl i]; positivity) hc0 hc1 hk hsum_c

/-- Frobenius–Pythagoras identity: for a symmetric projection (orthogonal projection) `P`,
`‖M ∘ₗ P‖² = re tr(P ∘ₗ adjoint M ∘ₗ M)`. -/
theorem hilbertSchmidt_norm_sq_comp_proj (M : E →ₗ[𝕜] F) (P : E →ₗ[𝕜] E)
    (hP : P.IsSymmetricProjection) :
    ‖M ∘ₗ P‖ ^ 2 = RCLike.re (LinearMap.trace 𝕜 E (P ∘ₗ (adjoint M ∘ₗ M))) := by
  rw [hilbertSchmidt_norm_sq_eq_re_trace, LinearMap.adjoint_comp, hP.isSymmetric.adjoint_eq]
  congr 1
  change LinearMap.trace 𝕜 E (P ∘ₗ ((adjoint M ∘ₗ M) ∘ₗ P)) = _
  rw [LinearMap.trace_comp_comm' ((adjoint M ∘ₗ M) ∘ₗ P) P, LinearMap.comp_assoc,
    show P ∘ₗ P = P from hP.isIdempotentElem, LinearMap.trace_comp_comm' P (adjoint M ∘ₗ M)]

/-- The dropped Frobenius sum `re tr(P ∘ₗ adjoint M ∘ₗ M) = ‖M ∘ₗ P‖² ≥ 0`. -/
theorem re_trace_proj_comp_self_nonneg (M : E →ₗ[𝕜] F) (P : E →ₗ[𝕜] E)
    (hP : P.IsSymmetricProjection) :
    0 ≤ RCLike.re (LinearMap.trace 𝕜 E (P ∘ₗ (adjoint M ∘ₗ M))) :=
  hilbertSchmidt_norm_sq_comp_proj M P hP ▸ sq_nonneg _

/-- Frobenius–Pythagoras (identity form) for the complementary projection `1 - Q`. -/
theorem hilbertSchmidt_norm_sq_comp_one_sub_proj (M : E →ₗ[𝕜] F) (Q : E →ₗ[𝕜] E)
    (hQ : Q.IsSymmetricProjection) :
    ‖M ∘ₗ (1 - Q)‖ ^ 2
      = ‖M‖ ^ 2 - RCLike.re (LinearMap.trace 𝕜 E (Q ∘ₗ (adjoint M ∘ₗ M))) := by
  rw [hilbertSchmidt_norm_sq_comp_proj M (1 - Q)
      ⟨hQ.isIdempotentElem.one_sub, IsSymmetric.sub (fun _ _ => rfl) hQ.isSymmetric⟩,
    LinearMap.sub_comp, Module.End.one_eq_id, LinearMap.id_comp, map_sub, map_sub,
    hilbertSchmidt_norm_sq_eq_re_trace M]

/-- **Frobenius–Pythagoras inequality.** Composing with `1 - Q` for an orthogonal projection `Q`
can only shrink the squared Frobenius norm. -/
theorem hilbertSchmidt_norm_sq_comp_one_sub_proj_le (M : E →ₗ[𝕜] F) (Q : E →ₗ[𝕜] E)
    (hQ : Q.IsSymmetricProjection) :
    ‖M ∘ₗ (1 - Q)‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  rw [hilbertSchmidt_norm_sq_comp_one_sub_proj M Q hQ]
  linarith [re_trace_proj_comp_self_nonneg M Q hQ]

/-- **Eckart–Young–Mirsky lower bound.** Every rank-`≤ k` operator `S` leaves squared Frobenius
error at least the tail sum `∑_{i ≥ k} σ_i(T)²`. The witness is the orthogonal projection
`Q` onto `(ker S)ᗮ` (rank `= rank S ≤ k`, and `S ∘ₗ (1 - Q) = 0`), plus `kyFan_le` and
Frobenius–Pythagoras. -/
theorem eckart_young_lower (T : E →ₗ[𝕜] F) (k : ℕ) (S : E →ₗ[𝕜] F)
    (hS : finrank 𝕜 (LinearMap.range S) ≤ k) :
    tailSqSingularValues T k ≤ ‖T - S‖ ^ 2 := by
  classical
  set Q : E →ₗ[𝕜] E := (((LinearMap.ker S)ᗮ).starProjection : E →ₗ[𝕜] E) with hQ
  have hQP : Q.IsSymmetricProjection := Submodule.isSymmetricProjection_starProjection _
  have hrankQ : finrank 𝕜 (LinearMap.range Q) ≤ k := by
    rw [hQ, Submodule.range_starProjection]
    have h1 := (LinearMap.ker S).finrank_add_finrank_orthogonal
    have h2 := S.finrank_range_add_finrank_ker
    omega
  have hSQ : S ∘ₗ (1 - Q) = 0 := by
    ext x
    have hmem : x - Q x ∈ LinearMap.ker S := (LinearMap.ker S).orthogonal_orthogonal ▸
      ((LinearMap.ker S)ᗮ).sub_starProjection_mem_orthogonal x
    simpa using LinearMap.mem_ker.mp hmem
  have hTS : (T - S) ∘ₗ (1 - Q) = T ∘ₗ (1 - Q) := by rw [LinearMap.sub_comp, hSQ, sub_zero]
  have hky : RCLike.re (LinearMap.trace 𝕜 E (Q ∘ₗ (adjoint T ∘ₗ T))) ≤ topSqSingularValues T k :=
    (kyFan_le T Q hQP rfl).trans (topSqSingularValues_mono T hrankQ)
  calc tailSqSingularValues T k = ‖T‖ ^ 2 - topSqSingularValues T k :=
      tailSqSingularValues_eq_norm_sq_sub T k
    _ ≤ ‖T‖ ^ 2 - RCLike.re (LinearMap.trace 𝕜 E (Q ∘ₗ (adjoint T ∘ₗ T))) := by linarith
    _ = ‖T ∘ₗ (1 - Q)‖ ^ 2 := (hilbertSchmidt_norm_sq_comp_one_sub_proj T Q hQP).symm
    _ = ‖(T - S) ∘ₗ (1 - Q)‖ ^ 2 := by rw [hTS]
    _ ≤ ‖T - S‖ ^ 2 := hilbertSchmidt_norm_sq_comp_one_sub_proj_le (T - S) Q hQP

/-- **Eckart–Young–Mirsky achievability.** The truncated SVD — projecting onto the span of the
top-`k` right singular vectors — attains the tail sum `∑_{i ≥ k} σ_i(T)²`. -/
theorem eckart_young_achievable (T : E →ₗ[𝕜] F) (k : ℕ) :
    ∃ S : E →ₗ[𝕜] F, finrank 𝕜 (LinearMap.range S) ≤ k ∧
      ‖T - S‖ ^ 2 = tailSqSingularValues T k := by
  classical
  have hSsymm : (adjoint T ∘ₗ T).IsSymmetric := T.isSymmetric_adjoint_comp_self
  set b := hSsymm.eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) with hb
  set s : Finset (Fin (finrank 𝕜 E)) := univ.filter (fun i => (i : ℕ) < k) with hs
  set U : Submodule 𝕜 E := Submodule.span 𝕜 (↑(s.image b) : Set E) with hU
  set P : E →ₗ[𝕜] E := (U.starProjection : E →ₗ[𝕜] E) with hP
  have hPP : P.IsSymmetricProjection := Submodule.isSymmetricProjection_starProjection _
  have happ : ∀ i, (adjoint T ∘ₗ T) (b i)
      = (hSsymm.eigenvalues (rfl : finrank 𝕜 E = finrank 𝕜 E) i : 𝕜) • b i := fun i => by
    rw [hb]; exact hSsymm.apply_eigenvectorBasis rfl i
  -- P acts as the top-k indicator on the eigenbasis
  have hPb : ∀ i, P (b i) = if (i : ℕ) < k then b i else 0 := by
    intro i
    by_cases hik : (i : ℕ) < k
    · rw [if_pos hik, hP]
      exact Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem b (by simp [hs, hik]))))
    · rw [if_neg hik, hP]
      refine (Submodule.starProjection_apply_eq_zero_iff U).mpr ?_
      rw [hU]
      refine Submodule.isOrtho_span.mpr ?_ (Submodule.mem_span_singleton_self (b i))
      rintro u (rfl : u = b i) v hv
      obtain ⟨j, hjs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      exact b.orthonormal.2 (Fin.ne_of_val_ne (by simp [hs] at hjs; omega))
  -- the projected Gram sum equals the top squared singular-value sum
  have hPtr : RCLike.re (LinearMap.trace 𝕜 E (P ∘ₗ (adjoint T ∘ₗ T)))
      = topSqSingularValues T k := by
    rw [LinearMap.trace_eq_sum_inner (P ∘ₗ (adjoint T ∘ₗ T)) b, map_sum, topSqSingularValues,
      ← sum_filter_sq_singularValues_eq_range, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, happ i, map_smul, inner_smul_right, RCLike.re_ofReal_mul, hPb i]
    by_cases hik : (i : ℕ) < k
    · simp [if_pos hik, b.orthonormal.1 i, ← T.sq_singularValues_fin rfl i]
    · simp only [if_neg hik, inner_zero_right, map_zero, mul_zero]
  refine ⟨T ∘ₗ P, ?_, ?_⟩
  · -- rank (T ∘ₗ P) ≤ k
    rw [LinearMap.range_comp]
    refine (Submodule.finrank_map_le T (LinearMap.range P)).trans ?_
    rw [hP, Submodule.range_starProjection, hU]
    refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
    simp [hs, Fin.card_filter_val_lt]
  · -- ‖T - T ∘ₗ P‖² = tailSqSingularValues T k
    have hTS : T - T ∘ₗ P = T ∘ₗ (1 - P) := by
      rw [LinearMap.comp_sub, Module.End.one_eq_id, LinearMap.comp_id]
    rw [hTS, hilbertSchmidt_norm_sq_comp_one_sub_proj T P hPP, hPtr,
      ← tailSqSingularValues_eq_norm_sq_sub]

/-- **Eckart–Young–Mirsky (Frobenius / Hilbert–Schmidt).** The minimum squared Frobenius error of
a rank-`≤ k` approximation of `T` is the tail sum `∑_{i ≥ k} σ_i(T)²`. -/
theorem eckart_young (T : E →ₗ[𝕜] F) (k : ℕ) :
    IsLeast {r : ℝ | ∃ S : E →ₗ[𝕜] F, finrank 𝕜 (LinearMap.range S) ≤ k ∧ r = ‖T - S‖ ^ 2}
      (tailSqSingularValues T k) :=
  ⟨(eckart_young_achievable T k).imp fun _ h => ⟨h.1, h.2.symm⟩,
    fun _ ⟨S, hS, hr⟩ => hr.symm ▸ eckart_young_lower T k S hS⟩

end LinearMap
