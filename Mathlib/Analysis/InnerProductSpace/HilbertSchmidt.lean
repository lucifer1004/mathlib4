/-
Copyright (c) 2026 Zihua Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zihua Wu
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Lp.WithLp

/-!
# The Hilbert–Schmidt inner product on finite-dimensional operators

For linear maps `S T : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the
**Hilbert–Schmidt** (Frobenius) inner product is
`⟪S, T⟫ = trace (adjoint S ∘ₗ T) = ∑ᵢ ⟪S eᵢ, T eᵢ⟫` for any orthonormal basis `e` of `E`,
with norm `‖T‖ = √(∑ᵢ ‖T eᵢ‖²)`.

Since `E →ₗ[𝕜] F` should not carry a canonical norm, the norm and inner product are registered
as *global* instances on the type synonym `WithLp 2 (E →ₗ[𝕜] F)`, following the `PiLp`/`ProdLp`
pattern; statements are phrased through `WithLp.toLp 2`. This is an alternative to the
scoped-instance design used by the matrix Frobenius norm (`Matrix.frobeniusNormedAddCommGroup`,
scoped in `Matrix.Norms.Frobenius`).

## Main definitions

- `LinearMap.hilbertSchmidtCore`: the `InnerProductSpace.Core` on `WithLp 2 (E →ₗ[𝕜] F)`.
- The global `NormedAddCommGroup (WithLp 2 (E →ₗ[𝕜] F))` and
  `InnerProductSpace 𝕜 (WithLp 2 (E →ₗ[𝕜] F))` instances it induces.

## Main statements

- `LinearMap.hilbertSchmidt_inner_toLp_toLp`:
  `⟪toLp 2 S, toLp 2 T⟫ = trace (adjoint S ∘ₗ T)`.
- `LinearMap.hilbertSchmidt_norm_sq_toLp_eq_re_trace`:
  `‖toLp 2 T‖ ^ 2 = re (trace (adjoint T ∘ₗ T))`.
- `LinearMap.hilbertSchmidt_norm_sq_toLp_eq_sum_norm_sq`:
  `‖toLp 2 T‖ ^ 2 = ∑ i, ‖T (b i)‖ ^ 2` for any orthonormal basis `b`.
-/

@[expose] public section

open Module ComplexConjugate
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- `trace (adjoint S ∘ₗ T) = ∑ᵢ ⟪S eᵢ, T eᵢ⟫` for any orthonormal basis `e` of `E`. -/
theorem trace_adjoint_comp_eq_sum_inner {ι : Type*} [Fintype ι]
    (S T : E →ₗ[𝕜] F) (b : OrthonormalBasis ι 𝕜 E) :
    LinearMap.trace 𝕜 E (adjoint S ∘ₗ T) = ∑ i, inner 𝕜 (S (b i)) (T (b i)) := by
  simp [LinearMap.trace_eq_sum_inner _ b, adjoint_inner_right]

/-- The Hilbert–Schmidt inner product core `⟪S, T⟫ = trace (adjoint S ∘ₗ T)` on the type
synonym `WithLp 2 (E →ₗ[𝕜] F)`. -/
@[implicit_reducible] noncomputable def hilbertSchmidtCore :
    InnerProductSpace.Core 𝕜 (WithLp 2 (E →ₗ[𝕜] F)) where
  inner S T := LinearMap.trace 𝕜 E (adjoint (WithLp.ofLp S) ∘ₗ WithLp.ofLp T)
  conj_inner_symm S T := by
    simp [trace_adjoint_comp_eq_sum_inner _ _ (stdOrthonormalBasis 𝕜 E), map_sum]
  re_inner_nonneg T := by
    rw [trace_adjoint_comp_eq_sum_inner _ _ (stdOrthonormalBasis 𝕜 E), map_sum]
    exact Finset.sum_nonneg fun i _ => inner_self_nonneg
  add_left S T U := by
    rw [WithLp.ofLp_add, map_add, LinearMap.add_comp, map_add]
  smul_left S T r := by
    rw [WithLp.ofLp_smul, map_smulₛₗ, LinearMap.smul_comp, map_smul, smul_eq_mul]
  definite T h := by
    have hre : ∑ i, ‖WithLp.ofLp T (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 = 0 := by
      simpa [trace_adjoint_comp_eq_sum_inner _ _ (stdOrthonormalBasis 𝕜 E), map_sum,
        inner_self_eq_norm_sq] using congrArg RCLike.re h
    refine WithLp.ofLp_injective 2 (Basis.ext (stdOrthonormalBasis 𝕜 E).toBasis fun i => ?_)
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp hre i
      (Finset.mem_univ i)

/-- The Hilbert–Schmidt (Frobenius) norm, as a global instance on the type synonym
`WithLp 2 (E →ₗ[𝕜] F)`. -/
noncomputable instance : NormedAddCommGroup (WithLp 2 (E →ₗ[𝕜] F)) :=
  hilbertSchmidtCore.toNormedAddCommGroup

/-- The Hilbert–Schmidt (Frobenius) inner product, as a global instance on the type synonym
`WithLp 2 (E →ₗ[𝕜] F)`. -/
noncomputable instance : InnerProductSpace 𝕜 (WithLp 2 (E →ₗ[𝕜] F)) :=
  letI := hilbertSchmidtCore (𝕜 := 𝕜) (E := E) (F := F)
  InnerProductSpace.ofCore _

theorem hilbertSchmidt_inner_toLp_toLp (S T : E →ₗ[𝕜] F) :
    inner 𝕜 (WithLp.toLp 2 S) (WithLp.toLp 2 T)
      = LinearMap.trace 𝕜 E (LinearMap.adjoint S ∘ₗ T) := rfl

/-- The defining identity of the Hilbert–Schmidt norm:
`‖toLp 2 T‖² = re (trace (adjoint T ∘ₗ T))`. -/
theorem hilbertSchmidt_norm_sq_toLp_eq_re_trace (T : E →ₗ[𝕜] F) :
    ‖WithLp.toLp 2 T‖ ^ 2 = RCLike.re (LinearMap.trace 𝕜 E (LinearMap.adjoint T ∘ₗ T)) :=
  (inner_self_eq_norm_sq (𝕜 := 𝕜) _).symm

/-- The Hilbert–Schmidt norm via any orthonormal basis:
`‖toLp 2 T‖ ^ 2 = ∑ i, ‖T (b i)‖ ^ 2`. -/
theorem hilbertSchmidt_norm_sq_toLp_eq_sum_norm_sq {ι : Type*} [Fintype ι] (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis ι 𝕜 E) : ‖WithLp.toLp 2 T‖ ^ 2 = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [hilbertSchmidt_norm_sq_toLp_eq_re_trace, trace_adjoint_comp_eq_sum_inner T T b, map_sum]
  exact Finset.sum_congr rfl fun i _ => inner_self_eq_norm_sq _

end LinearMap
