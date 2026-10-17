/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.CartierPairing
import Mathlib.LinearAlgebra.Contraction

/-!
# The Cartier pairing over an `R`-algebra `S`

For `G = Spec A` finite flat over `R` and a commutative `R`-algebra `S`, the **Cartier pairing**
`G(S) × G^∨(S) → S`, `⟨φ, ψ⟩ = ∑_i φ(e_i) ψ(e_i^*)` for a basis `(e_i)` of `A` with dual basis
`(e_i^*)` of `A^∨` ([BC, Exercise 12.5.3]; [Stix, §11.2.2] uses it levelwise for `p`-divisible
groups). Basis-free construction, written up here:

* `Cartier.theta : A^∨ ⊗_R S ≃ Hom_R(A, S)`, `f ⊗ s ↦ (a ↦ f(a) s)` (Mathlib's
  `dualTensorHomEquiv`), turns the tensor product algebra structure into convolution
  (`theta_mul`, `theta_one`); so a point `φ ∈ G(S)` gives `φ̂ = θ⁻¹(φ)` with `(φφ')^ = φ̂ φ̂'`
  (`hat_mul`).
* `cartierPairingBase φ ψ = (ψ ⊗ id_S)(φ̂)`: multiplicative in `φ` since `ψ ⊗ id_S` is an
  algebra map; `pairing_eq_sum`: `= ∑_i φ(e_i) ψ(e_i^*)` for every basis.
* `pairing_symm`: `⟨φ, ψ⟩_G = ⟨ψ, φ ∘ ev⁻¹⟩_{G^∨}` (double duality `A ≅ A^∨∨`, the dual basis of
  `(e_i^*)` is `(ev e_i)`); hence multiplicativity in `ψ` follows from multiplicativity in the
  first variable for `G^∨`.
* `cartierPairingBase : G(S) →* G^∨(S) →* S` (`FFGroupScheme.cartierPairingBase`), with
  `cartierPairingBase_pow_eq_one`: if `G` is killed by `n`, the pairing takes values in the
  `n`-th roots of unity.
* naturality (`cartierPairingBase_comp`): for a homomorphism `f : G → H` (a bialgebra map
  `f^* : O(H) → O(G)`), `⟨f(φ), ψ⟩_H = ⟨φ, ψ ∘ (f^*)^∨⟩_G`, where `(f^*)^∨ : A_G^∨ → A_H^∨`,
  `F ↦ F ∘ f^*` is an algebra map for the convolution products (`Cartier.transposeAlgHom`).
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u v

namespace Cartier

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  (S : Type v) [CommRing S] [Algebra R S]

section Theta

variable [Module.Free R A] [Module.Finite R A]

variable (A) in
/-- `θ : A^∨ ⊗_R S ≃ Hom_R(A, S)`, `f ⊗ s ↦ (a ↦ f(a) s)`. -/
def theta : Dual R A ⊗[R] S ≃ₗ[R] (A →ₗ[R] S) :=
  (TensorProduct.congr (WithConv.linearEquiv R (A →ₗ[R] R)) (LinearEquiv.refl R S)).trans
    (dualTensorHomEquiv R A S)

@[simp]
theorem theta_tmul (f : Dual R A) (s : S) (a : A) : theta A S (f ⊗ₜ s) a = f a • s := by
  simp [theta, dualTensorHom_apply]

theorem theta_mul (x y : Dual R A ⊗[R] S) :
    theta A S (x * y) = ofConv (toConv (theta A S x) * toConv (theta A S y)) := by
  induction x with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, toConv_add, add_mul, ofConv_add, hx, hx']
  | tmul f s =>
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [mul_add, map_add, toConv_add, mul_add, ofConv_add, hy, hy']
    | tmul g t =>
      ext a
      rw [Algebra.TensorProduct.tmul_mul_tmul, theta_tmul, LinearMap.convMul_apply,
        LinearMap.convMul_apply]
      generalize comul (R := R) a = z
      induction z with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, add_smul, hz, hz']
      | tmul a₁ a₂ =>
        rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
          LinearMap.mul'_apply, theta_tmul, theta_tmul]
        exact (smul_mul_smul_comm _ _ _ _).symm

theorem theta_one : theta A S 1 = ofConv (1 : WithConv (A →ₗ[R] S)) := by
  ext a
  rw [Algebra.TensorProduct.one_def, theta_tmul, LinearMap.convOne_apply]
  change (algebraMap R R (counit a)) • (1 : S) = _
  simp [Algebra.algebraMap_eq_smul_one]

end Theta

/-- The transpose `F ↦ F ∘ f` of a coalgebra map `f : B → A`, an algebra map `A^∨ → B^∨` for the
convolution products. -/
def transposeAlgHom {B : Type u} [CommRing B] [HopfAlgebra R B] (f : B →ₗc[R] A) :
    Dual R A →ₐ[R] Dual R B where
  toFun F := toConv ((ofConv F).comp f.toLinearMap)
  map_one' := by
    apply WithConv.ofConv_injective
    ext b
    simp [LinearMap.convOne_apply, CoalgHomClass.counit_comp_apply]
  map_mul' F F' := by
    apply WithConv.ofConv_injective
    exact LinearMap.convMul_comp_coalgHom_distrib F F' f
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' r := by
    apply WithConv.ofConv_injective
    ext b
    change (algebraMap R (Dual R A) r) (f b) = (algebraMap R (Dual R B) r) b
    simp [Algebra.algebraMap_eq_smul_one, LinearMap.convOne_apply,
      CoalgHomClass.counit_comp_apply]

@[simp]
theorem transposeAlgHom_apply {B : Type u} [CommRing B] [HopfAlgebra R B] (f : B →ₗc[R] A)
    (F : Dual R A) (b : B) : transposeAlgHom f F b = F (f b) := rfl

end Cartier

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (G : FFGroupScheme R) (S : Type v) [CommRing S] [Algebra R S]

/-- `φ̂ = θ⁻¹(φ) ∈ A^∨ ⊗_R S` for a point `φ ∈ G(S)`. -/
def hat (φ : G.points S) : Cartier.Dual R G.A ⊗[R] S :=
  (Cartier.theta G.A S).symm (ofConv φ).toLinearMap

theorem theta_hat (φ : G.points S) : Cartier.theta G.A S (G.hat S φ) = (ofConv φ).toLinearMap :=
  LinearEquiv.apply_symm_apply _ _

theorem hat_mul (φ φ' : G.points S) : G.hat S (φ * φ') = G.hat S φ * G.hat S φ' := by
  apply (Cartier.theta G.A S).injective
  rw [Cartier.theta_mul, theta_hat, theta_hat, theta_hat]
  rfl

theorem hat_one : G.hat S 1 = 1 := by
  apply (Cartier.theta G.A S).injective
  rw [Cartier.theta_one, theta_hat]
  rfl

/-- `φ̂ = ∑_i e_i^* ⊗ φ(e_i)` for any basis `(e_i)` of `A`. -/
theorem hat_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι R G.A) (φ : G.points S) :
    G.hat S φ = ∑ i, toConv (b.coord i) ⊗ₜ ofConv φ (b i) := by
  apply (Cartier.theta G.A S).injective
  rw [theta_hat]
  refine b.ext fun j => ?_
  simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply, Cartier.theta_tmul]
  change _ = ∑ i, (b.coord i (b j)) • ofConv φ (b i)
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi.symm])
    (by simp)]
  simp

/-- `ψ ⊗ id : A^∨ ⊗_R S → S` for a point `ψ ∈ G^∨(S)`. -/
def evalDual (ψ : G.dual.points S) : Cartier.Dual R G.A ⊗[R] S →ₐ[R] S :=
  Algebra.TensorProduct.productMap (ofConv ψ) (AlgHom.id R S)

/-- The Cartier pairing over `S`, as a function. -/
def pairing (φ : G.points S) (ψ : G.dual.points S) : S := G.evalDual S ψ (G.hat S φ)

theorem pairing_mul_left (φ φ' : G.points S) (ψ : G.dual.points S) :
    G.pairing S (φ * φ') ψ = G.pairing S φ ψ * G.pairing S φ' ψ := by
  rw [pairing, hat_mul, map_mul]
  rfl

theorem pairing_one_left (ψ : G.dual.points S) : G.pairing S 1 ψ = 1 := by
  rw [pairing, hat_one, map_one]

/-- `⟨φ, ψ⟩ = ∑_i φ(e_i) ψ(e_i^*)` for any basis `(e_i)` of `A`. -/
theorem pairing_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι R G.A) (φ : G.points S)
    (ψ : G.dual.points S) :
    G.pairing S φ ψ = ∑ i, ofConv φ (b i) * ofConv ψ (toConv (b.coord i)) := by
  rw [pairing, hat_eq_sum G S b, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [evalDual, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply]
  exact mul_comm _ _

/-- The point `φ ∘ ev⁻¹ ∈ G^∨∨(S)` corresponding to `φ ∈ G(S)`. -/
def toDualDual (φ : G.points S) : G.dual.dual.points S :=
  toConv ((ofConv φ).comp (G.dualDualIso.symm.toBialgHom : G.dual.dual.A →ₐ[R] G.A))

theorem toDualDual_mul (φ φ' : G.points S) :
    G.toDualDual S (φ * φ') = G.toDualDual S φ * G.toDualDual S φ' := by
  apply WithConv.ofConv_injective
  exact AlgHom.convMul_comp_bialgHom_distrib φ φ' G.dualDualIso.symm.toBialgHom

/-- The dual basis `(e_i^*)` of `A^∨`, as a basis of `Cartier.Dual R A`. -/
def dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R G.A) :
    Module.Basis ι R G.dual.A :=
  b.dualBasis.map (WithConv.linearEquiv R (G.A →ₗ[R] R)).symm

theorem dualBasis_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R G.A)
    (i : ι) : G.dualBasis b i = toConv (b.coord i) := by
  simp [dualBasis]
  rfl

theorem dualBasis_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R G.A)
    (i : ι) : toConv ((G.dualBasis b).coord i) = Cartier.evLin R G.A (b i) := by
  apply WithConv.ofConv_injective
  refine (G.dualBasis b).ext fun j => ?_
  change (G.dualBasis b).coord i (G.dualBasis b j) =
    (ofConv (G.dualBasis b j : Cartier.Dual R G.A)) (b i)
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, dualBasis_apply]
  change Finsupp.single j 1 i = b.coord j (b i)
  rw [Module.Basis.coord_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

/-- **Symmetry of the Cartier pairing** under double duality. -/
theorem pairing_symm (φ : G.points S) (ψ : G.dual.points S) :
    G.pairing S φ ψ = G.dual.pairing S ψ (G.toDualDual S φ) := by
  classical
  let b := Module.Free.chooseBasis R G.A
  rw [pairing_eq_sum G S b, pairing_eq_sum G.dual S (G.dualBasis b)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dualBasis_coord, dualBasis_apply, mul_comm]
  congr 1
  exact congrArg (fun a => (ofConv φ) a) (G.dualDualIso.symm_apply_apply (b i)).symm

theorem pairing_mul_right (φ : G.points S) (ψ ψ' : G.dual.points S) :
    G.pairing S φ (ψ * ψ') = G.pairing S φ ψ * G.pairing S φ ψ' := by
  rw [G.pairing_symm S φ (ψ * ψ'), G.pairing_symm S φ ψ, G.pairing_symm S φ ψ',
    pairing_mul_left]

theorem pairing_one_right (φ : G.points S) : G.pairing S φ 1 = 1 := by
  rw [pairing_symm, pairing_one_left]

/-- **The Cartier pairing** `G(S) × G^∨(S) → S` over an `R`-algebra `S`, multiplicative in both
variables. -/
def cartierPairingBase : G.points S →* G.dual.points S →* S where
  toFun φ :=
    { toFun := G.pairing S φ
      map_one' := G.pairing_one_right S φ
      map_mul' := G.pairing_mul_right S φ }
  map_one' := by ext ψ; exact G.pairing_one_left S ψ
  map_mul' φ φ' := by ext ψ; exact G.pairing_mul_left S φ φ' ψ

theorem cartierPairingBase_apply (φ : G.points S) (ψ : G.dual.points S) :
    G.cartierPairingBase S φ ψ = G.pairing S φ ψ := rfl

/-- If `n` kills `G(S)`, the Cartier pairing takes values in the `n`-th roots of unity. -/
theorem cartierPairingBase_pow_eq_one {n : ℕ} (φ : G.points S) (hφ : φ ^ n = 1)
    (ψ : G.dual.points S) : G.cartierPairingBase S φ ψ ^ n = 1 := by
  rw [← MonoidHom.pow_apply, ← map_pow, hφ, map_one, MonoidHom.one_apply]

/-- **Naturality** of the Cartier pairing: `⟨f(φ), ψ⟩_H = ⟨φ, f^∨(ψ)⟩_G`, with
`f^∨(ψ) = ψ ∘ (F ↦ F ∘ f^*)`. -/
theorem pairing_mapPoints {H : FFGroupScheme R} (f : Hom G H) (φ : G.points S)
    (ψ : H.dual.points S) :
    H.pairing S (f.mapPoints S φ) ψ =
      G.pairing S φ (toConv ((ofConv ψ).comp (Cartier.transposeAlgHom (f : H.A →ₗc[R] G.A)))) := by
  classical
  let b := Module.Free.chooseBasis R H.A
  let c := Module.Free.chooseBasis R G.A
  rw [pairing_eq_sum H S b, pairing_eq_sum G S c]
  -- both sides are `∑_{i,j} c_j^*(f e_i) φ(c_j) ψ(e_i^*)`
  have hf : ∀ i, ofConv (f.mapPoints S φ) (b i) =
      ∑ j, c.coord j (f (b i)) • ofConv φ (c j) := by
    intro i
    change ofConv φ (f (b i)) = _
    conv_lhs => rw [← c.sum_repr (f (b i))]
    simp only [map_sum, map_smul, Module.Basis.coord_apply]
  have hg : ∀ j, (Cartier.transposeAlgHom (f : H.A →ₗc[R] G.A) (toConv (c.coord j))) =
      ∑ i, (c.coord j (f (b i))) • toConv (b.coord i) := by
    intro j
    apply WithConv.ofConv_injective
    refine b.ext fun k => ?_
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have hg' : ∀ j, ofConv (toConv ((ofConv ψ).comp
      (Cartier.transposeAlgHom (f : H.A →ₗc[R] G.A)))) (toConv (c.coord j)) =
      ∑ i, (c.coord j (f (b i))) • ofConv ψ (toConv (b.coord i)) := by
    intro j
    change ofConv ψ (Cartier.transposeAlgHom (f : H.A →ₗc[R] G.A) (toConv (c.coord j))) = _
    rw [hg j]
    exact (map_sum (ofConv ψ) _ _).trans
      (Finset.sum_congr rfl fun i _ => map_smul (ofConv ψ) _ _)
  refine (Finset.sum_congr rfl fun i _ => by rw [hf i, Finset.sum_mul]).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => ?_))
  refine Eq.trans ?_ (congrArg (fun y => ofConv φ (c j) * y) (hg' j)).symm
  exact (Finset.sum_congr rfl fun i _ =>
    (smul_mul_assoc _ _ _).trans (mul_smul_comm _ _ _).symm).trans (Finset.mul_sum _ _ _).symm

end FFGroupScheme

end PadicHodge
