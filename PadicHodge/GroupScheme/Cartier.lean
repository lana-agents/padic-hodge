/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.FiniteFlat
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Cartier duality: the dual Hopf algebra

Let `A` be a commutative and cocommutative Hopf algebra over a commutative ring `R` which is
finite free as an `R`-module (the coordinate ring of a finite flat commutative group scheme
`G = Spec A`). Following [BC, Exercise 12.5.3 (3), (4)], the `R`-linear dual
`A^∨ = Hom_R(A, R)` is again such a Hopf algebra, by transposing all structure maps:

* multiplication: the transpose of the comultiplication, i.e. the convolution product
  `(f g)(a) = (f ⊗ g)(Δ a)` (Mathlib's `WithConv`), with unit the counit `ε`;
* comultiplication: the transpose of the multiplication, `Δ^∨ f = f ∘ m`, read in
  `A^∨ ⊗ A^∨ ≅ (A ⊗ A)^∨` (`TensorProduct.dualDistribEquiv`, `A` finite free);
* counit `f ↦ f(1)`, antipode `f ↦ f ∘ S`.

`Spec A^∨` is the Cartier dual `G^∨` of `G`.

## Main definitions

* `Cartier.Dual R A = WithConv (A →ₗ[R] R)`, its `HopfAlgebra` and `IsCocomm` instances;
* `Cartier.ev2 : A^∨ ⊗ A^∨ →ₗ (A ⊗ A)^∨` (injective, `ev2_injective`) with
  `ev2 (Δ^∨ f) = f ∘ m` (`ev2_comul`) and `ev2 (x * y) = ev2 x ⋆ ev2 y` (`ev2_mul`);
* `FFGroupScheme.dual G` (the Cartier dual) with `order_dual : G^∨.order = G.order`.

The proofs reduce every identity in `A^∨ ⊗ A^∨` (resp. `A^∨ ⊗ (A^∨ ⊗ A^∨)`) to an identity of
functionals on `A ⊗ A` (resp. `A ⊗ (A ⊗ A)`) via the injective evaluation maps `ev2`, `ev3`,
where it becomes the corresponding axiom of `A`.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace Cartier

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]

/-- The `R`-linear dual `A^∨ = Hom_R(A, R)` with the convolution product. -/
abbrev Dual : Type u := WithConv (A →ₗ[R] R)

variable {R A}

/-- `ofConv` as a linear map `A^∨ → Hom_R(A, R)`. -/
abbrev lc : Dual R A →ₗ[R] (A →ₗ[R] R) := (WithConv.linearEquiv R (A →ₗ[R] R)).toLinearMap

variable (R A) in
/-- The evaluation `A^∨ ⊗ A^∨ → (A ⊗ A)^∨`, `f ⊗ g ↦ (a ⊗ b ↦ f(a) g(b))`. -/
def ev2 : Dual R A ⊗[R] Dual R A →ₗ[R] (A ⊗[R] A →ₗ[R] R) :=
  TensorProduct.dualDistrib R A A ∘ₗ TensorProduct.map lc lc

@[simp]
theorem ev2_tmul_tmul (f g : Dual R A) (a b : A) :
    ev2 R A (f ⊗ₜ g) (a ⊗ₜ b) = f a * g b := rfl

theorem ev2_tmul (f g : Dual R A) :
    ev2 R A (f ⊗ₜ g) = LinearMap.mul' R R ∘ₗ TensorProduct.map (ofConv f) (ofConv g) := by
  ext a b
  simp

variable (R A) in
/-- The counit of `A^∨`: evaluation at `1`. -/
def counitD : Dual R A →ₗ[R] R where
  toFun f := f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem counitD_apply (f : Dual R A) : counitD R A f = f 1 := rfl

variable [Module.Free R A] [Module.Finite R A]

theorem ev2_injective : Function.Injective (ev2 R A) := by
  have h1 : Function.Injective (TensorProduct.dualDistrib R A A) :=
    (TensorProduct.dualDistribEquiv R A A).injective
  have h2 : Function.Injective (TensorProduct.map (lc (R := R) (A := A)) lc) :=
    (TensorProduct.congr (WithConv.linearEquiv R (A →ₗ[R] R))
      (WithConv.linearEquiv R (A →ₗ[R] R))).injective
  exact h1.comp h2

theorem ev2_surjective : Function.Surjective (ev2 R A) := by
  have h1 : Function.Surjective (TensorProduct.dualDistrib R A A) :=
    (TensorProduct.dualDistribEquiv R A A).surjective
  have h2 : Function.Surjective (TensorProduct.map (lc (R := R) (A := A)) lc) :=
    (TensorProduct.congr (WithConv.linearEquiv R (A →ₗ[R] R))
      (WithConv.linearEquiv R (A →ₗ[R] R))).surjective
  exact h1.comp h2

variable (R A) in
/-- `ev2` as a linear equivalence. -/
def ev2Equiv : Dual R A ⊗[R] Dual R A ≃ₗ[R] (A ⊗[R] A →ₗ[R] R) :=
  LinearEquiv.ofBijective (ev2 R A) ⟨ev2_injective, ev2_surjective⟩

variable (R A) in
/-- The comultiplication of `A^∨`: the transpose of the multiplication of `A`. -/
def comulD : Dual R A →ₗ[R] Dual R A ⊗[R] Dual R A :=
  (ev2Equiv R A).symm.toLinearMap ∘ₗ (LinearMap.mul' R A).dualMap ∘ₗ lc

@[simp]
theorem ev2_comulD (f : Dual R A) : ev2 R A (comulD R A f) = ofConv f ∘ₗ LinearMap.mul' R A := by
  change ev2Equiv R A ((ev2Equiv R A).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem ev2_comulD_tmul (f : Dual R A) (a b : A) :
    ev2 R A (comulD R A f) (a ⊗ₜ b) = f (a * b) := by
  simp

/-! ### Counit laws -/

omit [Module.Free R A] [Module.Finite R A] in
theorem lid_rTensor_counitD (x : Dual R A ⊗[R] Dual R A) (a : A) :
    TensorProduct.lid R (Dual R A) ((counitD R A).rTensor _ x) a = ev2 R A x (1 ⊗ₜ a) := by
  induction x with
  | zero => simp
  | tmul f g => simp
  | add x y hx hy => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply] at *; rw [hx, hy]

omit [Module.Free R A] [Module.Finite R A] in
theorem rid_lTensor_counitD (x : Dual R A ⊗[R] Dual R A) (a : A) :
    TensorProduct.rid R (Dual R A) ((counitD R A).lTensor _ x) a = ev2 R A x (a ⊗ₜ 1) := by
  induction x with
  | zero => simp
  | tmul f g => simp [mul_comm]
  | add x y hx hy => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply] at *; rw [hx, hy]

theorem rTensor_counitD_comulD (f : Dual R A) :
    (counitD R A).rTensor _ (comulD R A f) = 1 ⊗ₜ f := by
  apply (TensorProduct.lid R (Dual R A)).injective
  ext a
  rw [lid_rTensor_counitD, ev2_comulD_tmul, one_mul]
  simp

theorem lTensor_counitD_comulD (f : Dual R A) :
    (counitD R A).lTensor _ (comulD R A f) = f ⊗ₜ 1 := by
  apply (TensorProduct.rid R (Dual R A)).injective
  ext a
  rw [rid_lTensor_counitD, ev2_comulD_tmul, mul_one]
  simp

/-! ### Coassociativity -/

variable (R A) in
/-- The evaluation `A^∨ ⊗ (A^∨ ⊗ A^∨) → (A ⊗ (A ⊗ A))^∨`. -/
def ev3 : Dual R A ⊗[R] (Dual R A ⊗[R] Dual R A) →ₗ[R] (A ⊗[R] (A ⊗[R] A) →ₗ[R] R) :=
  TensorProduct.dualDistrib R A (A ⊗[R] A) ∘ₗ TensorProduct.map lc (ev2 R A)

omit [Module.Free R A] [Module.Finite R A] in
@[simp]
theorem ev3_tmul_tmul (f : Dual R A) (y : Dual R A ⊗[R] Dual R A) (a : A) (z : A ⊗[R] A) :
    ev3 R A (f ⊗ₜ y) (a ⊗ₜ z) = f a * ev2 R A y z := rfl

theorem ev3_injective : Function.Injective (ev3 R A) := by
  have h1 : Function.Injective (TensorProduct.dualDistrib R A (A ⊗[R] A)) :=
    (TensorProduct.dualDistribEquiv R A (A ⊗[R] A)).injective
  have h2 : Function.Injective (TensorProduct.map (lc (R := R) (A := A)) (ev2 R A)) :=
    (TensorProduct.congr (WithConv.linearEquiv R (A →ₗ[R] R)) (ev2Equiv R A)).injective
  exact h1.comp h2

omit [Module.Free R A] [Module.Finite R A] in
theorem ext3 {φ ψ : A ⊗[R] (A ⊗[R] A) →ₗ[R] R}
    (h : ∀ a b c, φ (a ⊗ₜ (b ⊗ₜ c)) = ψ (a ⊗ₜ (b ⊗ₜ c))) : φ = ψ := by
  refine TensorProduct.ext' fun a z => ?_
  induction z with
  | zero => rw [tmul_zero, map_zero, map_zero]
  | tmul b c => exact h a b c
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

theorem ev3_lTensor_comulD (x : Dual R A ⊗[R] Dual R A) (a b c : A) :
    ev3 R A ((comulD R A).lTensor _ x) (a ⊗ₜ (b ⊗ₜ c)) = ev2 R A x (a ⊗ₜ (b * c)) := by
  induction x with
  | zero => simp
  | tmul f g => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply] at *; rw [hx, hy]

omit [Module.Free R A] [Module.Finite R A] in
theorem ev3_assoc (z : Dual R A ⊗[R] Dual R A) (g : Dual R A) (a b c : A) :
    ev3 R A (TensorProduct.assoc R _ _ _ (z ⊗ₜ g)) (a ⊗ₜ (b ⊗ₜ c)) =
      ev2 R A z (a ⊗ₜ b) * g c := by
  induction z with
  | zero => rw [zero_tmul, LinearEquiv.map_zero, map_zero, LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply, zero_mul]
  | tmul f h => simp [mul_assoc]
  | add x y hx hy =>
    rw [add_tmul, LinearEquiv.map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply, add_mul]

theorem ev3_assoc_rTensor_comulD (y : Dual R A ⊗[R] Dual R A) (a b c : A) :
    ev3 R A (TensorProduct.assoc R _ _ _ ((comulD R A).rTensor _ y)) (a ⊗ₜ (b ⊗ₜ c)) =
      ev2 R A y ((a * b) ⊗ₜ c) := by
  induction y with
  | zero => rw [map_zero, LinearEquiv.map_zero, map_zero, map_zero, LinearMap.zero_apply,
      LinearMap.zero_apply]
  | tmul f g => rw [LinearMap.rTensor_tmul, ev3_assoc, ev2_comulD_tmul]; rfl
  | add x y hx hy =>
    rw [map_add, LinearEquiv.map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply]

theorem coassoc_comulD (f : Dual R A) :
    TensorProduct.assoc R _ _ _ ((comulD R A).rTensor _ (comulD R A f)) =
      (comulD R A).lTensor _ (comulD R A f) := by
  apply ev3_injective
  refine ext3 fun a b c => ?_
  rw [ev3_assoc_rTensor_comulD, ev3_lTensor_comulD, ev2_comulD_tmul, ev2_comulD_tmul, mul_assoc]

/-- The coalgebra structure on `A^∨`. -/
instance instCoalgebra : Coalgebra R (Dual R A) where
  comul := comulD R A
  counit := counitD R A
  coassoc := by ext f; exact coassoc_comulD f
  rTensor_counit_comp_comul := by ext f; exact rTensor_counitD_comulD f
  lTensor_counit_comp_comul := by ext f; exact lTensor_counitD_comulD f

@[simp] theorem counit_dual_apply (f : Dual R A) :
    Coalgebra.counit (R := R) f = f 1 := rfl

/-! ### The bialgebra structure -/

omit [Module.Free R A] [Module.Finite R A] in
/-- `ev2` is multiplicative: the tensor product of convolution algebras maps to the convolution
algebra of the tensor product coalgebra. -/
theorem ev2_mul (x y : Dual R A ⊗[R] Dual R A) :
    ev2 R A (x * y) = ofConv (toConv (ev2 R A x) * toConv (ev2 R A y)) := by
  induction x with
  | zero => simp
  | add x x' hx hx' => simp only [add_mul, map_add, toConv_add, ofConv_add, hx, hx']
  | tmul f g =>
    induction y with
    | zero => simp
    | add y y' hy hy' => simp only [mul_add, map_add, toConv_add, ofConv_add, hy, hy']
    | tmul f' g' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, ev2_tmul, ev2_tmul, ev2_tmul,
        ← Algebra.TensorProduct.lmul'_toLinearMap]
      have h := LinearMap.nonUnitalAlgHom_comp_convMul_distrib
        ((Algebra.TensorProduct.lmul' R : R ⊗[R] R →ₐ[R] R) : R ⊗[R] R →ₙₐ[R] R)
        (toConv (TensorProduct.map (ofConv f) (ofConv g)))
        (toConv (TensorProduct.map (ofConv f') (ofConv g')))
      rw [TensorProduct.map_convMul_map] at h
      exact h

omit [Module.Free R A] [Module.Finite R A] in
theorem counitD_one : counitD R A 1 = 1 := by
  simp

omit [Module.Free R A] [Module.Finite R A] in
theorem counitD_mul (f g : Dual R A) : counitD R A (f * g) = counitD R A f * counitD R A g := by
  simp [LinearMap.convMul_apply, Algebra.TensorProduct.one_def]

theorem comulD_one : comulD R A 1 = 1 := by
  apply ev2_injective
  rw [ev2_comulD, Algebra.TensorProduct.one_def]
  ext a b
  simp

theorem comulD_mul (f g : Dual R A) : comulD R A (f * g) = comulD R A f * comulD R A g := by
  apply ev2_injective
  rw [ev2_mul, ev2_comulD, ev2_comulD, ev2_comulD]
  exact LinearMap.convMul_comp_coalgHom_distrib f g (Bialgebra.mulCoalgHom R A)

/-- The bialgebra structure on `A^∨`. -/
instance instBialgebra : Bialgebra R (Dual R A) :=
  Bialgebra.mk' R (Dual R A) counitD_one (counitD_mul _ _) comulD_one (comulD_mul _ _)

/-! ### The antipode -/

variable (R A) in
/-- The antipode of `A^∨`: `f ↦ f ∘ S`. -/
def antipodeD : Dual R A →ₗ[R] Dual R A where
  toFun f := toConv (ofConv f ∘ₗ antipode R)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Module.Free R A] [Module.Finite R A] in
theorem mul'_apply_eq_ev2 (x : Dual R A ⊗[R] Dual R A) (a : A) :
    LinearMap.mul' R (Dual R A) x a = ev2 R A x (comul a) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, ofConv_add, LinearMap.add_apply, hx, hy]
  | tmul f g => rw [LinearMap.mul'_apply, LinearMap.convMul_apply, ev2_tmul]; rfl

omit [Module.Free R A] [Module.Finite R A] in
theorem ev2_rTensor_antipodeD (x : Dual R A ⊗[R] Dual R A) :
    ev2 R A ((antipodeD R A).rTensor _ x) = ev2 R A x ∘ₗ (antipode R).rTensor A := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]
  | tmul f g => ext a b; simp [antipodeD]

omit [Module.Free R A] [Module.Finite R A] in
theorem ev2_lTensor_antipodeD (x : Dual R A ⊗[R] Dual R A) :
    ev2 R A ((antipodeD R A).lTensor _ x) = ev2 R A x ∘ₗ (antipode R).lTensor A := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]
  | tmul f g => ext a b; simp [antipodeD]

/-- The Hopf algebra structure on `A^∨`. -/
instance instHopfAlgebra : HopfAlgebra R (Dual R A) where
  antipode := antipodeD R A
  mul_antipode_rTensor_comul := by
    ext f a
    change LinearMap.mul' R (Dual R A) ((antipodeD R A).rTensor _ (comulD R A f)) a = _
    rw [mul'_apply_eq_ev2, ev2_rTensor_antipodeD, LinearMap.comp_apply, ev2_comulD,
      LinearMap.comp_apply, HopfAlgebra.mul_antipode_rTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
  mul_antipode_lTensor_comul := by
    ext f a
    change LinearMap.mul' R (Dual R A) ((antipodeD R A).lTensor _ (comulD R A f)) a = _
    rw [mul'_apply_eq_ev2, ev2_lTensor_antipodeD, LinearMap.comp_apply, ev2_comulD,
      LinearMap.comp_apply, HopfAlgebra.mul_antipode_lTensor_comul_apply]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]

omit [Module.Free R A] [Module.Finite R A] in
theorem ev2_comm (x : Dual R A ⊗[R] Dual R A) (a b : A) :
    ev2 R A (TensorProduct.comm R _ _ x) (a ⊗ₜ b) = ev2 R A x (b ⊗ₜ a) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul f g => simp [mul_comm]

/-- `A^∨` is cocommutative since `A` is commutative. -/
instance instIsCocomm : Coalgebra.IsCocomm R (Dual R A) where
  comm_comp_comul := by
    ext f
    apply ev2_injective
    ext a b
    change ev2 R A (TensorProduct.comm R _ _ (comulD R A f)) (a ⊗ₜ b) = _
    rw [ev2_comm]
    change _ = ev2 R A (comulD R A f) (a ⊗ₜ b)
    rw [ev2_comulD_tmul, ev2_comulD_tmul, mul_comm]

instance instFree : Module.Free R (Dual R A) :=
  Module.Free.of_equiv (WithConv.linearEquiv R (A →ₗ[R] R)).symm

instance instFinite : Module.Finite R (Dual R A) :=
  Module.Finite.equiv (WithConv.linearEquiv R (A →ₗ[R] R)).symm

theorem finrank_dual [Nontrivial R] : Module.finrank R (Dual R A) = Module.finrank R A :=
  (WithConv.linearEquiv R (A →ₗ[R] R)).finrank_eq.trans (Module.finrank_linearMap_self R R A)

end Cartier

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

/-- The Cartier dual `G^∨ = Spec A^∨` of a finite flat commutative group scheme `G = Spec A`
([BC, Exercise 12.5.3]). -/
def dual (G : FFGroupScheme R) : FFGroupScheme R where
  A := Cartier.Dual R G.A

theorem order_dual [Nontrivial R] (G : FFGroupScheme R) : G.dual.order = G.order :=
  Cartier.finrank_dual

end FFGroupScheme

end PadicHodge
