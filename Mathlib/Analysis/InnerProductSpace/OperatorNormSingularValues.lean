/-
Copyright (c) 2026 Zihua Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zihua Wu
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The operator norm equals the largest singular value

For a linear map `T` between finite-dimensional inner product spaces, the operator (spectral) norm
of `T` equals its largest singular value:
`‖T.toContinuousLinearMap‖ = T.singularValues 0`.

The key step is that a positive self-adjoint operator's operator norm equals its largest eigenvalue.

## Main statements

- `LinearMap.IsPositive.norm_toContinuousLinearMap_eq_eigenvalues_zero`:
  `‖B.toContinuousLinearMap‖ = eigenvalues 0` for a positive `B`.
- `LinearMap.norm_toContinuousLinearMap_eq_singularValues_zero`:
  `‖T.toContinuousLinearMap‖ = T.singularValues 0`.
-/

public section

open Module InnerProductSpace Finset

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The operator norm of a positive operator equals its largest eigenvalue. -/
theorem IsPositive.norm_toContinuousLinearMap_eq_eigenvalues_zero
    {n : ℕ} {B : E →ₗ[𝕜] E} (hB : B.IsPositive) (hn : finrank 𝕜 E = n) (h0 : 0 < n) :
    ‖B.toContinuousLinearMap‖ = hB.isSymmetric.eigenvalues hn ⟨0, h0⟩ := by
  set hsym := hB.isSymmetric
  set b := hsym.eigenvectorBasis hn
  set l := hsym.eigenvalues hn
  have hl_nonneg : ∀ i, 0 ≤ l i := hB.nonneg_eigenvalues hn
  have hl_le : ∀ i, l i ≤ l ⟨0, h0⟩ := fun i =>
    hsym.eigenvalues_antitone hn (Fin.le_def.mpr (Nat.zero_le _))
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (hl_nonneg ⟨0, h0⟩) fun x => ?_
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hl_nonneg _) (norm_nonneg _)),
      coe_toContinuousLinearMap']
    have hrepr : ∀ y : E, ‖y‖ ^ 2 = ∑ i, ‖b.repr y i‖ ^ 2 := fun y => by
      simp only [b.repr_apply_apply]; exact (b.sum_sq_norm_inner_right y).symm
    rw [mul_pow, hrepr (B x), hrepr x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hsym.eigenvectorBasis_apply_self_apply hn x i, norm_mul, mul_pow,
      RCLike.norm_ofReal, sq_abs]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hl_nonneg i) (hl_le i) 2) (by positivity)
  · have happ : B (b ⟨0, h0⟩) = (l ⟨0, h0⟩ : 𝕜) • b ⟨0, h0⟩ :=
      hsym.apply_eigenvectorBasis hn ⟨0, h0⟩
    have hnorm_b : ‖b ⟨0, h0⟩‖ = 1 := b.orthonormal.1 ⟨0, h0⟩
    calc l ⟨0, h0⟩ = ‖B.toContinuousLinearMap (b ⟨0, h0⟩)‖ := by
          rw [coe_toContinuousLinearMap', happ, norm_smul, hnorm_b, mul_one, RCLike.norm_ofReal,
            abs_of_nonneg (hl_nonneg _)]
      _ ≤ ‖B.toContinuousLinearMap‖ * ‖b ⟨0, h0⟩‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖B.toContinuousLinearMap‖ := by rw [hnorm_b, mul_one]

/-- The operator norm of `T` equals its largest singular value `σ₀`. -/
theorem norm_toContinuousLinearMap_eq_singularValues_zero (T : E →ₗ[𝕜] F) :
    ‖T.toContinuousLinearMap‖ = T.singularValues 0 := by
  rcases Nat.eq_zero_or_pos (finrank 𝕜 E) with hn0 | hpos
  · have hE : Subsingleton E := Module.finrank_zero_iff.mp hn0
    rw [T.singularValues_of_finrank_le hn0.le, norm_eq_zero]
    exact ContinuousLinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp
  · haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    haveI : CompleteSpace F := FiniteDimensional.complete 𝕜 F
    have hcomp : (T.toContinuousLinearMap).adjoint ∘L T.toContinuousLinearMap
        = (adjoint T ∘ₗ T).toContinuousLinearMap := ContinuousLinearMap.ext fun x => by
      simp [← adjoint_toContinuousLinearMap, coe_toContinuousLinearMap']
    have key : ‖T.toContinuousLinearMap‖ ^ 2 = T.singularValues 0 ^ 2 := by
      rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self, hcomp,
        (T.isPositive_adjoint_comp_self).norm_toContinuousLinearMap_eq_eigenvalues_zero rfl hpos]
      exact (T.sq_singularValues_fin rfl ⟨0, hpos⟩).symm
    exact (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg 0)).mp key

end LinearMap
