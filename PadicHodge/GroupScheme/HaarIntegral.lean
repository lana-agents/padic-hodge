/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Cartier

/-!
# Existence of integrals of finite flat group schemes (Larson–Sweedler)

Let `K = Spec E` be a finite flat commutative group scheme over a commutative ring `R`
(`FFGroupScheme R`: `E` a finite free commutative and cocommutative Hopf algebra). For a linear
form `l : E → R` write `l ⇀ u = (l ⊗ id)(Δ u)` (`FFGroupScheme.hit`). We prove, over an
arbitrary base ring, the part of the fundamental theorem of Hopf modules
([Farnsteiner, *Hopf modules and integrals: the fundamental theorem*, Theorem = [Larson–Sweedler,
Prop. 1]], applied to the Hopf module `E ≅ (E^∨)^∨`) that is needed for quotients:

* `haarProj b f = ∑ₖ bₖ^* ⇀ (bₖ f)` (for a basis `b` of `E`) is an **integral** of `E`:
  `e · haarProj b f = ε(e) haarProj b f` (`mul_haarProj`). This is the projection `φ` of
  [Farnsteiner, proof of the Theorem] onto the coinvariants of the Hopf module `E`.
* `∑ⱼ (bⱼ^* ∘ S) ⇀ haarProj b (bⱼ) = 1` (`sum_hit_haarProj`): `μ ∘ Φ = id` in
  [Farnsteiner, proof of the Theorem], evaluated at `1`.

Applied to the Cartier dual `H^∨` of `H = Spec C` this gives (`exists_invariant_forms`):
**`H`-invariant linear forms `tᵢ : C → R` (`(id ⊗ tᵢ) Δ = tᵢ(·) 1`, "Haar measures") and
`Λᵢ ∈ C` with `∑ᵢ tᵢ(Λᵢ x) = ε(x)`.** These are the input of the quotient construction
`G/H` in `GroupScheme/Quotient.lean` (the dual basis of `O(G)` over the invariants).

## References

* R. Farnsteiner, *Hopf modules and integrals: the fundamental theorem*, lecture notes
  (Bielefeld, 2006), Theorem ([Larson–Sweedler, Amer. J. Math. 91 (1969)], Prop. 1) and its proof.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (K : FFGroupScheme R)

/-! ### The Fourier operators `l ⇀ u = (l ⊗ id)(Δ u)` -/

/-- `l ⇀ u = (l ⊗ id)(Δ u)`. -/
def hit (l : K.A →ₗ[R] R) : K.A →ₗ[R] K.A :=
  (TensorProduct.lid R K.A).toLinearMap ∘ₗ l.rTensor K.A ∘ₗ comul

theorem hit_apply (l : K.A →ₗ[R] R) (u : K.A) :
    K.hit l u = TensorProduct.lid R K.A (l.rTensor K.A (comul u)) := rfl

/-- `l ↦ (l ⇀ ·)` is linear. -/
def hitL : (K.A →ₗ[R] R) →ₗ[R] K.A →ₗ[R] K.A where
  toFun := K.hit
  map_add' l l' := by
    ext u
    simp [hit_apply, LinearMap.rTensor_add]
  map_smul' r l := by
    ext u
    simp [hit_apply, LinearMap.rTensor_smul]

theorem hitL_apply (l : K.A →ₗ[R] R) : K.hitL l = K.hit l := rfl

theorem hit_counit (u : K.A) : K.hit counit u = u := by
  rw [hit_apply, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

theorem mul_lid_rTensor (l : K.A →ₗ[R] R) (e : K.A) (w : K.A ⊗[R] K.A) :
    e * TensorProduct.lid R K.A (l.rTensor K.A w) =
      TensorProduct.lid R K.A (l.rTensor K.A ((1 ⊗ₜ e) * w)) := by
  induction w with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, mul_add, hx, hy, mul_add, map_add, map_add]
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem lid_rTensor_mul_left (l : K.A →ₗ[R] R) (a : K.A) (w : K.A ⊗[R] K.A) :
    TensorProduct.lid R K.A (l.rTensor K.A ((a ⊗ₜ 1) * w)) =
      TensorProduct.lid R K.A ((l ∘ₗ LinearMap.mulLeft R a).rTensor K.A w) := by
  induction w with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, map_add, map_add]
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- `∑ S(e₁) ⊗ 1 · Δ(e₂) = 1 ⊗ e`: in the group `K(E ⊗ E)`, `i₁⁻¹ (i₁ i₂) = i₂`. -/
theorem lift_antipode_comul (e : K.A) :
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : K.A →ₐ[R] K.A ⊗[R] K.A).comp
        (HopfAlgebra.antipodeAlgHom R K.A))
      (Bialgebra.comulAlgHom R K.A) (fun _ _ => .all _ _) (comul e) = 1 ⊗ₜ e := by
  let i₁ : K.points (K.A ⊗[R] K.A) := toConv Algebra.TensorProduct.includeLeft
  let i₂ : K.points (K.A ⊗[R] K.A) := toConv Algebra.TensorProduct.includeRight
  have hΔ : i₁ * i₂ = toConv (Bialgebra.comulAlgHom R K.A) := by
    apply WithConv.ofConv_injective
    ext x
    rw [AlgHom.convMul_apply]
    simp only [i₁, i₂, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply,
      Bialgebra.comulAlgHom_apply]
  have h : i₁⁻¹ * toConv (Bialgebra.comulAlgHom R K.A) = i₂ := by
    rw [← hΔ, inv_mul_cancel_left]
  have h' := congrArg (fun f : K.points (K.A ⊗[R] K.A) => (ofConv f : K.A →ₐ[R] _) e) h
  rw [AlgHom.convMul_apply] at h'
  exact h'

/-! ### Transport along a basis -/

/-- `∑ₖ Q(bₖ^* ∘ φ, bₖ) = ∑ₖ Q(bₖ^*, φ bₖ)` for a bilinear `Q` (both sides are `Q` applied to the
canonical element of `End(E)`). -/
theorem sum_coord_comp {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R M) (Q : (M →ₗ[R] R) →ₗ[R] M →ₗ[R] N)
    (φ : M →ₗ[R] M) :
    ∑ k, Q (b.coord k ∘ₗ φ) (b k) = ∑ k, Q (b.coord k) (φ (b k)) := by
  classical
  have hc : ∀ k, b.coord k ∘ₗ φ = ∑ j, b.coord k (φ (b j)) • b.coord j := by
    intro k
    refine b.ext fun i => ?_
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  simp_rw [hc, map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [← b.sum_repr (φ (b j)), map_sum]
  simp only [map_smul, Module.Basis.coord_apply]

/-! ### The integral `haarProj` -/

variable {K} {ι : Type*} [Fintype ι] (b : Module.Basis ι R K.A)

/-- `haarProj b f = ∑ₖ bₖ^* ⇀ (bₖ f)`, an integral of `E` ([Farnsteiner, proof of the Theorem]:
the projection `φ` onto the coinvariants of the Hopf module `E`). -/
def haarProj (f : K.A) : K.A := ∑ k, K.hit (b.coord k) (b k * f)

include b in
theorem sum_lid_shear (f : K.A) (w : K.A ⊗[R] K.A) :
    ∑ k, TensorProduct.lid R K.A ((b.coord k).rTensor K.A
      (Algebra.TensorProduct.lift
        ((Algebra.TensorProduct.includeLeft : K.A →ₐ[R] K.A ⊗[R] K.A).comp
          (HopfAlgebra.antipodeAlgHom R K.A))
        (Bialgebra.comulAlgHom R K.A) (fun _ _ => .all _ _) w * comul (b k * f))) =
    ∑ k, K.hit (b.coord k)
      (LinearMap.mul' R K.A ((antipode R).rTensor K.A w) * (b k * f)) := by
  induction w with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, hx, hy]
  | tmul a c =>
    simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      Algebra.TensorProduct.includeLeft_apply, HopfAlgebra.antipodeAlgHom_apply,
      Bialgebra.comulAlgHom_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply]
    have h1 : ∀ k, ((antipode R a ⊗ₜ[R] (1 : K.A)) * comul c) * comul (b k * f) =
        (antipode R a ⊗ₜ[R] (1 : K.A)) * comul (c * (b k * f)) := by
      intro k
      rw [mul_assoc, ← Bialgebra.comulAlgHom_apply, ← Bialgebra.comulAlgHom_apply,
        ← Bialgebra.comulAlgHom_apply]
      simp only [map_mul]
    simp_rw [h1, K.lid_rTensor_mul_left]
    let Q : (K.A →ₗ[R] R) →ₗ[R] K.A →ₗ[R] K.A :=
      (LinearMap.lcomp R K.A (LinearMap.mulLeft R c ∘ₗ LinearMap.mulRight R f)).comp K.hitL
    have := sum_coord_comp b Q (LinearMap.mulLeft R (antipode R a))
    simp only [Q, LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, hitL_apply] at this
    refine Eq.trans ?_ (this.trans ?_)
    · exact Finset.sum_congr rfl fun k _ => rfl
    · refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      ring

/-- **`haarProj b f` is an integral**: `e · haarProj b f = ε(e) haarProj b f`. -/
theorem mul_haarProj (f e : K.A) :
    e * haarProj b f = algebraMap R K.A (counit (R := R) e) * haarProj b f := by
  rw [haarProj, Finset.mul_sum]
  simp_rw [hit_apply, K.mul_lid_rTensor, ← K.lift_antipode_comul e]
  rw [sum_lid_shear b f (comul e), mul_antipode_rTensor_comul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_mul_assoc, one_mul]
  rfl

/-! ### The Fourier inversion `∑ⱼ (bⱼ^* ∘ S) ⇀ haarProj b (bⱼ) = 1` -/

/-- The convolution `l * μ = (l ⊗ μ) ∘ Δ` of linear forms. -/
def convForm (l μ : K.A →ₗ[R] R) : K.A →ₗ[R] R :=
  LinearMap.mul' R R ∘ₗ TensorProduct.map l μ ∘ₗ comul

omit [Fintype ι] in
theorem hit_hit (l μ : K.A →ₗ[R] R) (u : K.A) :
    K.hit μ (K.hit l u) = K.hit (convForm l μ) u := by
  have h1 : ∀ w : K.A ⊗[R] K.A, K.hit μ (TensorProduct.lid R K.A (l.rTensor K.A w)) =
      TensorProduct.lid R K.A (l.rTensor K.A
        (((TensorProduct.lid R K.A).toLinearMap ∘ₗ μ.rTensor K.A).lTensor K.A
          (comul.lTensor K.A w))) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [hit_apply]
  have h2 : ∀ v : (K.A ⊗[R] K.A) ⊗[R] K.A,
      TensorProduct.lid R K.A (l.rTensor K.A
        (((TensorProduct.lid R K.A).toLinearMap ∘ₗ μ.rTensor K.A).lTensor K.A
          (TensorProduct.assoc R K.A K.A K.A v))) =
      TensorProduct.lid R K.A ((LinearMap.mul' R R ∘ₗ TensorProduct.map l μ).rTensor K.A v) := by
    intro v
    induction v with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x z =>
      induction x with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | tmul x y => simp [mul_smul, smul_comm (μ y)]
  rw [K.hit_apply l, h1, ← coassoc_apply, h2, hit_apply, convForm]
  simp only [LinearMap.rTensor_comp, LinearMap.comp_apply]

theorem sum_coord_mul_convForm (l : ι) (w : K.A ⊗[R] K.A) :
    ∑ j, ∑ k, b.coord l (b k * b j) *
        LinearMap.mul' R R (TensorProduct.map (b.coord k) (b.coord j ∘ₗ antipode R) w) =
      b.coord l (LinearMap.mul' R K.A ((antipode R).lTensor K.A w)) := by
  induction w with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, mul_add, Finset.sum_add_distrib, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.lTensor_tmul,
      LinearMap.comp_apply]
    conv_rhs => rw [← b.sum_repr x, ← b.sum_repr (antipode R y), Finset.sum_mul_sum]
    rw [map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_mul_smul_comm, map_smul, smul_eq_mul, Module.Basis.coord_apply]
    ring

/-- **Fourier inversion at `1`**: `∑ⱼ (bⱼ^* ∘ S) ⇀ haarProj b (bⱼ) = 1`. -/
theorem sum_hit_haarProj :
    ∑ j, K.hit (b.coord j ∘ₗ antipode R) (haarProj b (b j)) = 1 := by
  have key : ∀ l, ∑ j, ∑ k, b.coord l (b k * b j) • convForm (b.coord k) (b.coord j ∘ₗ antipode R)
      = b.coord l 1 • (counit : K.A →ₗ[R] R) := by
    intro l
    ext v
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      convForm, LinearMap.comp_apply]
    rw [sum_coord_mul_convForm, mul_antipode_lTensor_comul_apply, Algebra.algebraMap_eq_smul_one,
      map_smul, smul_eq_mul, mul_comm]
  have e1 : ∀ j k, K.hit (convForm (b.coord k) (b.coord j ∘ₗ antipode R)) (b k * b j) =
      ∑ l, b.coord l (b k * b j) • K.hit (convForm (b.coord k) (b.coord j ∘ₗ antipode R))
        (b l) := by
    intro j k
    conv_lhs => rw [← b.sum_repr (b k * b j)]
    rw [map_sum]
    simp [Module.Basis.coord_apply]
  have e2 : ∀ l, K.hit (∑ j, ∑ k, b.coord l (b k * b j) •
      convForm (b.coord k) (b.coord j ∘ₗ antipode R)) (b l) =
      ∑ j, ∑ k, b.coord l (b k * b j) •
        K.hit (convForm (b.coord k) (b.coord j ∘ₗ antipode R)) (b l) := by
    intro l
    simp only [← hitL_apply, map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply]
  simp_rw [haarProj, map_sum, hit_hit, e1]
  calc _ = ∑ l, ∑ j, ∑ k, b.coord l (b k * b j) •
        K.hit (convForm (b.coord k) (b.coord j ∘ₗ antipode R)) (b l) := by
          exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm
    _ = ∑ l, K.hit (b.coord l 1 • (counit : K.A →ₗ[R] R)) (b l) := by
          simp_rw [← e2, key]
    _ = 1 := by
          simp_rw [← hitL_apply, map_smul, LinearMap.smul_apply, hitL_apply,
            hit_counit]
          exact b.sum_repr 1

/-! ### Haar measures on `H` from integrals of `H^∨` -/

variable (H : FFGroupScheme R)

/-- An integral `T` of the Cartier dual (`e T = ε(e) T`) is an `H`-invariant linear form on
`O(H)`: `(id ⊗ T)(Δ y) = T(y) · 1`. -/
theorem rid_lTensor_comul_of_mul_eq {T : Cartier.Dual R H.A}
    (hT : ∀ e : Cartier.Dual R H.A,
      e * T = algebraMap R (Cartier.Dual R H.A) (counit (R := R) e) * T) (y : H.A) :
    TensorProduct.rid R H.A ((ofConv T).lTensor H.A (comul (R := R) y)) =
      algebraMap R H.A (ofConv T y) := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff R _).mp fun f => ?_
  rw [map_sub, sub_eq_zero]
  have h2 : ofConv ((toConv f : Cartier.Dual R H.A) * T) y =
      ofConv (algebraMap R (Cartier.Dual R H.A)
        (counit (R := R) (toConv f : Cartier.Dual R H.A)) * T) y :=
    congrArg (fun g : Cartier.Dual R H.A => ofConv g y) (hT (toConv f))
  have e1 : ∀ w : H.A ⊗[R] H.A, f (TensorProduct.rid R H.A ((ofConv T).lTensor H.A w)) =
      LinearMap.mul' R R (TensorProduct.map f (ofConv T) w) := by
    intro w
    induction w with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add, map_add]
    | tmul x y => simp [mul_comm]
  rw [e1, ← LinearMap.convMul_apply]
  change ofConv ((toConv f : Cartier.Dual R H.A) * T) y = _
  rw [h2, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  change Cartier.counitD R H.A (toConv f) * ofConv T y = _
  simp [Cartier.counitD, mul_comm]

theorem ofConv_lid_rTensor_eval (z x : H.A) (w : Cartier.Dual R H.A ⊗[R] Cartier.Dual R H.A) :
    ofConv (TensorProduct.lid R (Cartier.Dual R H.A)
      ((LinearMap.applyₗ (R := R) z ∘ₗ Cartier.lc (R := R) (A := H.A)).rTensor
        (Cartier.Dual R H.A) w)) x =
      Cartier.ev2 R H.A w (z ⊗ₜ x) := by
  induction w with
  | zero => simp
  | add y w hy hw => simp only [map_add, ofConv_add, LinearMap.add_apply, hy, hw]
  | tmul f g => simp

/-- **Haar measures on `H` with Fourier inversion** ([Larson–Sweedler]): there are `H`-invariant
linear forms `tᵢ : O(H) → R` (`(id ⊗ tᵢ)(Δ y) = tᵢ(y) · 1`) and elements `Λᵢ ∈ O(H)` with
`∑ᵢ tᵢ(Λᵢ x) = ε(x)` for all `x`. -/
theorem exists_invariant_forms :
    ∃ (ι : Type u) (_ : Fintype ι) (t : ι → (H.A →ₗ[R] R)) (Λ : ι → H.A),
      (∀ i y, TensorProduct.rid R H.A ((t i).lTensor H.A (comul (R := R) y)) =
        algebraMap R H.A (t i y)) ∧ ∀ x, ∑ i, t i (Λ i * x) = counit (R := R) x := by
  let c := Module.Free.chooseBasis R H.A
  let bE : Module.Basis _ R H.dual.A :=
    c.dualBasis.map (WithConv.linearEquiv R (H.A →ₗ[R] R)).symm
  let dv : H.dual.A → H.A →ₗ[R] R := fun g => ofConv (show Cartier.Dual R H.A from g)
  have hcoord : ∀ j (g : H.dual.A), bE.coord j g = dv g (c j) := by
    intro j g
    simp [bE, dv, Module.Basis.coord_apply, Module.Basis.map_repr]
    rfl
  refine ⟨_, inferInstance, fun j => dv (haarProj bE (bE j)), fun j => antipode R (c j),
    fun j y => H.rid_lTensor_comul_of_mul_eq (fun e => mul_haarProj bE _ e) y, fun x => ?_⟩
  have hS : ∀ j, bE.coord j ∘ₗ antipode R =
      LinearMap.applyₗ (R := R) (antipode R (c j)) ∘ₗ Cartier.lc (R := R) (A := H.A) := by
    intro j
    ext g
    rw [LinearMap.comp_apply, hcoord]
    rfl
  have h := congrArg (fun g : H.dual.A => dv g x) (sum_hit_haarProj bE)
  change ofConv (∑ j, (show Cartier.Dual R H.A from
    H.dual.hit (bE.coord j ∘ₗ antipode R) (haarProj bE (bE j)))) x =
    ofConv (1 : Cartier.Dual R H.A) x at h
  rw [ofConv_sum, LinearMap.coe_sum, Finset.sum_apply, LinearMap.convOne_apply,
    Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hS, hit_apply]
  exact ((H.ofConv_lid_rTensor_eval _ _ _).trans (Cartier.ev2_comulD_tmul _ _ _)).symm

end FFGroupScheme

end PadicHodge
