/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.HopfTrace
import PadicHodge.GroupScheme.Cartier

/-!
# Discriminants of finite group schemes via integrals

Let `G = Spec A` be a finite flat commutative group scheme of order `N` over a domain `R`,
`Λ ∈ A` an integral (`a Λ = ε(a) Λ`) and `c = ε(Λ) ≠ 0`. Suppose the trace formula
`(Tr ⊗ id)((x ⊗ 1) Δ(Λ)) = c S(x)` holds (`trL_mul_comul_integral`, e.g. when the generic fibre
is étale). Then:

* `fourier_comp_traceForm`: the trace form `t : A → A^∨`, `x ↦ Tr(x ·)`, composed with the
  **Fourier map** `F : A^∨ → A`, `φ ↦ (φ ⊗ id) Δ(Λ)`, is `c S`;
* **`discIdeal_eq_of_trace_eq_smul`**: if moreover `Tr_{A/R} = c λ` for some `λ : A → R`, then
  `disc(A/R) = (c^N)`: indeed `t = c m_λ` with `m_λ(x) = λ(x ·)`, so
  `c^N det(S) = det(F) c^N det(m_λ)`; `S² = 1` makes `det S` a unit, hence `det m_λ` is a unit
  and `disc = det t = c^N det m_λ`;
* `trace_eq_smul_of_dual_integral`: such a `λ` exists if there is an integral `λ` of the Cartier
  dual `A^∨` (`(id ⊗ λ) Δ(a) = λ(a)`, e.g. `G.dual.IsIntegral λ`, `rid_lTensor_comul_of_isIntegral`)
  with `c λ(1) = N`: then `c λ(S x) = λ(Λ) Tr(x)`, `λ(Λ) = 1` and `Tr = c (λ ∘ S)`.

This is the route to [Hong, Prop. 3.5.1] used here (instead of Tate's trace formula for
complete intersections [Lipnowski, App., Claim 2'], which rests on [Tate, Thm. A.3 in the
appendix to Mazur–Roberts], not available): for `G = F[p^∞]`, `Λ = det(b_{ij})` where
`[p^v]_i = ∑_j b_{ij} t_j` (Cramer), `ε(Λ) = p^{dv}`, and the dual integral comes from the
connected part of the Cartier dual, of dimension `d' = h − d` (`DiscFormula.lean`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.5.1.
* [Haines] T. Haines, *Notes on Tate's p-divisible groups*, §2.3 (Lemma 2.3.3 is the linear
  algebra `disc = N(τ)` behind `discIdeal_eq_of_trace_eq_smul`).
-/

noncomputable section

open Module TensorProduct Coalgebra HopfAlgebra WithConv

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (G : FFGroupScheme R)

/-- **The Fourier map** `A^∨ → A`, `φ ↦ (φ ⊗ id) Δ(Λ)`. -/
def fourier (Λ : G.A) : Module.Dual R G.A →ₗ[R] G.A where
  toFun φ := TensorProduct.lid R G.A (φ.rTensor G.A (comul (R := R) Λ))
  map_add' φ ψ := by simp [LinearMap.rTensor_add]
  map_smul' c φ := by simp [LinearMap.rTensor_smul]

theorem rTensor_trace_mul (x : G.A) (w : G.A ⊗[R] G.A) :
    (Algebra.trace R G.A).rTensor G.A ((x ⊗ₜ 1) * w) =
      (Algebra.traceForm R G.A x).rTensor G.A w := by
  induction w with
  | zero => simp
  | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz]
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem fourier_traceForm (Λ x : G.A) :
    G.fourier Λ (Algebra.traceForm R G.A x) = G.trL ((x ⊗ₜ 1) * comul (R := R) Λ) := by
  simp only [fourier, trL, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp,
    Function.comp_apply, rTensor_trace_mul]
  rfl

/-- **The discriminant from an integral**: if `(Tr ⊗ id)((x ⊗ 1) Δ(Λ)) = c S(x)` with
`c ≠ 0`, `S² = 1` and `Tr_{A/R} = c λ`, then `disc(A/R) = (c^N)`, `N = rk A`. -/
theorem discIdeal_eq_of_trace_eq_smul [IsDomain R] {Λ : G.A} {c : R} (hc : c ≠ 0)
    (h1 : ∀ x : G.A, G.trL ((x ⊗ₜ 1) * comul (R := R) Λ) = c • antipode R x)
    (hS : ∀ x : G.A, antipode R (antipode R x) = x)
    {l : G.A →ₗ[R] R} (hTr : Algebra.trace R G.A = c • l) :
    discIdeal R G.A = Ideal.span {c ^ finrank R G.A} := by
  classical
  let b := Module.finBasis R G.A
  rw [discIdeal_eq_span_discr b]
  let m : G.A →ₗ[R] Module.Dual R G.A := (LinearMap.mul R G.A).compr₂ l
  have htm : (Algebra.traceForm R G.A : G.A →ₗ[R] Module.Dual R G.A) = c • m := by
    ext x y
    simp [m, hTr]
  let Sl : G.A →ₗ[R] G.A := antipode R
  have hcomp : (G.fourier Λ) ∘ₗ (Algebra.traceForm R G.A : G.A →ₗ[R] Module.Dual R G.A) =
      c • Sl := by
    ext x
    simp [fourier_traceForm, h1, Sl]
  have hdisc : Algebra.discr R b =
      (LinearMap.toMatrix b b.dualBasis (Algebra.traceForm R G.A)).det := by
    rw [Algebra.discr_def]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply, Algebra.traceMatrix_apply, mul_comm]
  have hdet : (LinearMap.toMatrix b b (c • Sl)).det =
      (LinearMap.toMatrix b.dualBasis b (G.fourier Λ)).det *
        (LinearMap.toMatrix b b.dualBasis (Algebra.traceForm R G.A)).det := by
    rw [← hcomp, LinearMap.toMatrix_comp _ b.dualBasis, Matrix.det_mul]
  rw [htm] at hdet hdisc
  simp only [map_smul, Matrix.det_smul, Fintype.card_fin] at hdet hdisc
  have hSu : IsUnit (LinearMap.toMatrix b b Sl).det := by
    rw [LinearMap.det_toMatrix]
    have : Sl ∘ₗ Sl = LinearMap.id := LinearMap.ext hS
    exact IsUnit.of_mul_eq_one (LinearMap.det Sl)
      (by rw [← LinearMap.det_comp, this, LinearMap.det_id])
  have hcN : c ^ finrank R G.A ≠ 0 := pow_ne_zero _ hc
  have hmu : IsUnit (LinearMap.toMatrix b b.dualBasis m).det := by
    have h2 : (LinearMap.toMatrix b b Sl).det =
        (LinearMap.toMatrix b.dualBasis b (G.fourier Λ)).det *
          (LinearMap.toMatrix b b.dualBasis m).det :=
      mul_left_cancel₀ hcN (by rw [hdet]; ring)
    rw [h2] at hSu
    exact isUnit_of_mul_isUnit_right hSu
  rw [hdisc]
  exact Ideal.span_singleton_mul_right_unit hmu _

theorem trace_trL (l : G.A →ₗ[R] R) (w : G.A ⊗[R] G.A) :
    l (G.trL w) = Algebra.trace R G.A (TensorProduct.rid R G.A (l.lTensor G.A w)) := by
  induction w with
  | zero => simp
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add, map_add]
  | tmul a b => simp [trL_tmul, mul_comm]

theorem rid_lTensor_mul (l : G.A →ₗ[R] R) (x : G.A) (w : G.A ⊗[R] G.A) :
    TensorProduct.rid R G.A (l.lTensor G.A ((x ⊗ₜ 1) * w)) =
      x * TensorProduct.rid R G.A (l.lTensor G.A w) := by
  induction w with
  | zero => simp
  | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz, map_add, map_add, mul_add]
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- **The trace from a dual integral**: if `(id ⊗ λ) Δ(a) = λ(a)` for all `a` and
`c λ(1) = N ≠ 0`, then `Tr_{A/R} = c (λ ∘ S)` (`λ(Λ) = 1`). -/
theorem trace_eq_smul_of_dual_integral [IsDomain R] {Λ : G.A} {c : R}
    (h1 : ∀ x : G.A, G.trL ((x ⊗ₜ 1) * comul (R := R) Λ) = c • antipode R x)
    (l : G.A →ₗ[R] R)
    (hl : ∀ a, TensorProduct.rid R G.A (l.lTensor G.A (comul (R := R) a)) = algebraMap R G.A (l a))
    (hN : c * l 1 = finrank R G.A) (hN0 : (finrank R G.A : R) ≠ 0) :
    Algebra.trace R G.A = c • (l ∘ₗ antipode R) := by
  have key : ∀ x, c * l (antipode R x) = l Λ * Algebra.trace R G.A x := by
    intro x
    have := congrArg l (h1 x)
    rw [map_smul, smul_eq_mul, trace_trL, rid_lTensor_mul, hl, mul_comm x, ← Algebra.smul_def,
      map_smul, smul_eq_mul] at this
    exact this.symm
  have h0 : l Λ = 1 := by
    have := key 1
    rw [HopfAlgebra.antipode_one, hN, ← map_one (algebraMap R G.A), Algebra.trace_algebraMap,
      nsmul_eq_mul, mul_one] at this
    have h3 : l Λ * (finrank R G.A : R) = 1 * (finrank R G.A : R) := by
      rw [one_mul]; exact this.symm
    exact mul_right_cancel₀ hN0 h3
  ext x
  rw [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, key, h0, one_mul]

/-- An integral `λ` of the Cartier dual `A^∨` satisfies `(id ⊗ λ) Δ(a) = λ(a)`. -/
theorem rid_lTensor_comul_of_isIntegral {l : Cartier.Dual R G.A} (hl : G.dual.IsIntegral l)
    (a : G.A) :
    TensorProduct.rid R G.A ((ofConv l).lTensor G.A (comul (R := R) a)) =
      algebraMap R G.A (ofConv l a) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff R _).mp fun f => ?_
  rw [map_sub, sub_eq_zero]
  have h2 : ofConv (toConv f * l) a =
      ofConv (algebraMap R (Cartier.Dual R G.A) (counit (R := R) (toConv f : G.dual.A)) * l) a :=
    congrArg (fun g : Cartier.Dual R G.A => ofConv g a) (hl (toConv f))
  have e1 : ∀ w : G.A ⊗[R] G.A, f (TensorProduct.rid R G.A ((ofConv l).lTensor G.A w)) =
      LinearMap.mul' R R (TensorProduct.map f (ofConv l) w) := by
    intro w
    induction w with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add, map_add]
    | tmul x y => simp [mul_comm]
  rw [e1, ← LinearMap.convMul_apply, h2, ← Algebra.smul_def]
  rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  change Cartier.counitD R G.A (toConv f) * ofConv l a = _
  simp [Cartier.counitD, mul_comm]

/-- A linear form with values in `(c)`, `c ≠ 0`, over a domain is `c` times a linear form. -/
theorem exists_eq_smul_of_mem_span {M : Type*} [AddCommGroup M] [Module R M] [IsDomain R]
    {c : R} (hc : c ≠ 0) (f : M →ₗ[R] R) (hf : ∀ x, f x ∈ Ideal.span {c}) :
    ∃ g : M →ₗ[R] R, f = c • g := by
  choose g hg using fun x => Ideal.mem_span_singleton'.mp (hf x)
  refine ⟨{ toFun := g, map_add' := fun x y => ?_, map_smul' := fun r x => ?_ }, ?_⟩
  · refine mul_right_cancel₀ hc ?_
    rw [add_mul, hg, hg, hg, map_add]
  · refine mul_right_cancel₀ hc ?_
    rw [RingHom.id_apply, smul_eq_mul, mul_assoc, hg, hg, map_smul, smul_eq_mul]
  · ext x
    simp [← hg x, mul_comm]


/-! ### Over a base with étale generic fibre -/

section Etale

variable {G} [IsDomain R] {Ω : Type u} [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
  (hinj : Function.Injective (algebraMap R Ω)) (hG : (G.baseChange Ω).IsEtale)
include hinj hG

/-- **The trace from integrals of `A` and `A^∨`**: `Tr = ε(Λ) (λ ∘ S)` if `ε(Λ) λ(1) = N ≠ 0`. -/
theorem trace_eq_smul_of_integrals {Λ : G.A} (hΛ : G.IsIntegral Λ) {l : Cartier.Dual R G.A}
    (hl : G.dual.IsIntegral l) (hN : counit (R := R) Λ * ofConv l 1 = finrank R G.A)
    (hN0 : (finrank R G.A : R) ≠ 0) :
    Algebra.trace R G.A = counit (R := R) Λ • (ofConv l ∘ₗ antipode R) :=
  G.trace_eq_smul_of_dual_integral (G.trL_mul_comul_integral hinj hG hΛ) (ofConv l)
    (G.rid_lTensor_comul_of_isIntegral hl) hN hN0

/-- **The discriminant from an integral** `Λ` with `Tr_{A/R}(A) ⊆ (ε(Λ))`, `ε(Λ) ≠ 0`:
`disc(A/R) = (ε(Λ)^N)`. -/
theorem discIdeal_eq_of_integral_of_trace_mem {Λ : G.A} (hΛ : G.IsIntegral Λ)
    (hc : counit (R := R) Λ ≠ 0)
    (hTr : ∀ x, Algebra.trace R G.A x ∈ Ideal.span {counit (R := R) Λ}) :
    discIdeal R G.A = Ideal.span {counit (R := R) Λ ^ finrank R G.A} := by
  obtain ⟨l, hl⟩ := exists_eq_smul_of_mem_span hc _ hTr
  exact G.discIdeal_eq_of_trace_eq_smul hc (G.trL_mul_comul_integral hinj hG hΛ)
    (G.antipode_antipode hinj hG) hl

end Etale

end FFGroupScheme

end PadicHodge
