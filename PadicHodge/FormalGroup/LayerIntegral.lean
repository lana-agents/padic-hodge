/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.LayerHopf
import PadicHodge.FormalGroup.Filtration
import PadicHodge.GroupScheme.HopfTrace

/-!
# An integral of `F[p^v]` (Cramer's rule)

For a `p`-divisible formal group law `F` of dimension `d` over a complete local ring `R`, write
`[p^v]_F(T)_i = ∑_j t_j b_{ij}` (`FGL.exists_eq_sum_X_mul`), with `b_{ij}(0) = p^v δ_{ij}`
([Hong, Lemma 2.2.14]: the linear part of `[p^v]` is `p^v T`). By Cramer's rule
(`adj(b) b = det(b) · 1`), `det(b) t_k = ∑_i adj(b)_{ki} [p^v]_i ∈ J_v`, so the image
`Λ = det b ∈ A_v = R[[T]]/J_v` is killed by the augmentation ideal `(t_1, …, t_d)`, i.e. it is an
**integral** of `A_v` (`PDivFGL.isIntegral_layerDet`), with `ε(Λ) = det(p^v · 1) = (p^v)^d`
(`PDivFGL.counit_layerDet`). This is the source of the factor `p^{dv}` in [Hong, Prop. 3.5.1]
(it plays the role of the Jacobian `det(∂[p^v]_i/∂T_j)` in [Haines, §2.3.2],
[Lipnowski, App., Claim 2]).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Lemma 2.2.14, Prop. 3.5.1.
-/

noncomputable section

open MvPowerSeries IsLocalRing

namespace PadicHodge

universe u

namespace PDivFGL

section Cramer

variable {R : Type u} [CommRing R] {d p : ℕ} (P : PDivFGL R d p)

/-- The coefficient matrix `b` with `[p^v]_i = ∑_j t_j b_{ij}`. -/
def layerMat (v : ℕ) : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) R) := fun i =>
  (FGL.exists_eq_sum_X_mul (P.F.constantCoeff_mulPS (p ^ v) i)).choose

theorem mulPS_eq_sum (v : ℕ) (i : Fin d) :
    P.F.mulPS (p ^ v) i = ∑ j, X j * P.layerMat v i j :=
  (FGL.exists_eq_sum_X_mul (P.F.constantCoeff_mulPS (p ^ v) i)).choose_spec.1

theorem constantCoeff_layerMat (v : ℕ) (i j : Fin d) :
    constantCoeff (P.layerMat v i j) = if i = j then ((p ^ v : ℕ) : R) else 0 := by
  rw [layerMat, (FGL.exists_eq_sum_X_mul (P.F.constantCoeff_mulPS (p ^ v) i)).choose_spec.2 j,
    P.F.coeff_single_mulPS]

/-- **Cramer's rule**: `det(b) t_k ∈ J_v`. -/
theorem X_mul_det_mem (v : ℕ) (k : Fin d) :
    X k * (P.layerMat v).det ∈ P.F.layerIdeal p v := by
  have h1 : (P.layerMat v).det * X k =
      ∑ i, (P.layerMat v).adjugate k i * P.F.mulPS (p ^ v) i := by
    have h2 := congrFun (Matrix.mulVec_mulVec (fun j => (X j : MvPowerSeries (Fin d) R))
      (P.layerMat v).adjugate (P.layerMat v)) k
    rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul] at h2
    rw [← h2]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [P.mulPS_eq_sum v i]
    simp_rw [mul_comm (X _)]
  rw [mul_comm, h1]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (P.F.mulPS_mem_layerIdeal p v i)

/-- The integral `Λ = det(b) ∈ A_v`. -/
def layerDet (v : ℕ) : P.A v := Ideal.Quotient.mk _ (P.layerMat v).det

end Cramer

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d p : ℕ} [hp : Fact p.Prime] (P : PDivFGL R d p)

theorem counit_mk (v : ℕ) (f : MvPowerSeries (Fin d) R) :
    letI := P.hopfAlgebra v
    Coalgebra.counit (R := R) (Ideal.Quotient.mk (P.F.layerIdeal p v) f) = constantCoeff f := by
  letI := P.hopfAlgebra v
  change (P.counit v).toLinearMap (Ideal.Quotient.mk _ f) = _
  rw [AlgHom.toLinearMap_apply, counit, liftL_mk]
  rfl

/-- **`Λ = det b` is an integral of `A_v`**. -/
theorem isIntegral_layerDet (v : ℕ) : (P.groupScheme v).IsIntegral (P.layerDet v) := by
  intro a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hc := P.counit_mk v f
  erw [hc]
  rw [← sub_eq_zero, ← sub_mul, layerDet, ← Ideal.Quotient.mk_algebraMap, ← map_sub,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hf : f - algebraMap R _ (constantCoeff f) ∈
      Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R)) := by
    refine FGL.mem_span_X ?_
    rw [map_sub, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      constantCoeff_C, sub_self]
  refine Submodule.span_induction (p := fun g _ => g * (P.layerMat v).det ∈
    P.F.layerIdeal p v) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨k, rfl⟩
    exact P.X_mul_det_mem v k
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Ideal.add_mem _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ hx

/-- **`ε(Λ) = (p^v)^d`**. -/
theorem counit_layerDet (v : ℕ) :
    letI := P.hopfAlgebra v
    Coalgebra.counit (R := R) (P.layerDet v) = ((p ^ v : ℕ) : R) ^ d := by
  rw [layerDet, counit_mk, RingHom.map_det]
  have : (constantCoeff (R := R) (σ := Fin d)).mapMatrix (P.layerMat v) =
      Matrix.diagonal fun _ => ((p ^ v : ℕ) : R) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_layerMat, Matrix.diagonal_apply]
  rw [this, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end PDivFGL

end PadicHodge
