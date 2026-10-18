/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.BaseChange
import PadicHodge.GroupScheme.TatePairing
import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Cartier duality commutes with base change (on points)

For `G = Spec A` finite flat over `R` and an `R`-algebra `S`, the base change of linear forms
`f ↦ f_S` (`f_S(s ⊗ a) = f(a) s`, Mathlib's `Module.Dual.baseChange`) is an `R`-algebra map
`A^∨ → (S ⊗_R A)^∨` for the convolution products (`dualBC_one`, `dualBC_mul`), compatible with
the comultiplications (`comulD_dualBC`), and `(S ⊗_R A)^∨` is the base change of `A^∨`
(`IsBaseChange.dual`, `A` finite free). Hence, for every `S`-algebra `T`:

* **`dualBaseChangePointsEquiv : (G_S)^∨(T) ≃* G^∨(T)`**, `ψ ↦ ψ ∘ (·)_S`;
* naturality in homomorphisms (`dualBaseChangePointsEquiv_mapPoints`);
* for a `p`-divisible group `G` over `R`: **`DualTate (G_S) T ≃* DualTate G T`**
  (`PDivGroup.dualTateBaseChangeEquiv`). For `R = ℤ_p`, `S = ℚ_p` this identifies the Tate module
  of the Cartier dual of `G` with that of `G_{ℚ_p}`, which is `T_p(G_{ℚ_p}^∨)` (`dualPDiv`).
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] (G : FFGroupScheme R)

/-- `f ↦ f_S`, `f_S(s ⊗ a) = f(a) s`. -/
def dualBC (f : Cartier.Dual R G.A) : Cartier.Dual S (S ⊗[R] G.A) :=
  toConv (Module.Dual.baseChange S (ofConv f))

@[simp] theorem dualBC_tmul (f : Cartier.Dual R G.A) (s : S) (a : G.A) :
    ofConv (G.dualBC f) (s ⊗ₜ a) = f a • s := rfl

theorem dualBC_ext {F F' : Cartier.Dual S (S ⊗[R] G.A)}
    (h : ∀ a : G.A, ofConv F (1 ⊗ₜ a) = ofConv F' (1 ⊗ₜ a)) : F = F' := by
  apply WithConv.ofConv_injective
  refine TensorProduct.AlgebraTensorModule.ext fun s a => ?_
  rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul, h]

theorem dualBC_add (f g : Cartier.Dual R G.A) :
    G.dualBC (S := S) (f + g) = G.dualBC f + G.dualBC g :=
  G.dualBC_ext fun a => by simp [add_smul]

theorem dualBC_smul (r : R) (f : Cartier.Dual R G.A) :
    G.dualBC (S := S) (r • f) = algebraMap R S r • G.dualBC f :=
  G.dualBC_ext fun a => by
    simp only [dualBC_tmul, ofConv_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    ring

theorem dualBC_one : G.dualBC (S := S) 1 = 1 :=
  G.dualBC_ext fun a => by
    simp [Algebra.smul_def]

theorem dualBC_mul (f g : Cartier.Dual R G.A) :
    G.dualBC (S := S) (f * g) = G.dualBC f * G.dualBC g := by
  refine G.dualBC_ext fun a => ?_
  change (ofConv (f * g) : G.A →ₗ[R] R) a • (1 : S) =
    (ofConv (G.dualBC (S := S) f * G.dualBC g) : S ⊗[R] G.A →ₗ[S] S) ((1 : S) ⊗ₜ[R] a)
  rw [LinearMap.convMul_apply, LinearMap.convMul_apply, TensorProduct.comul_tmul]
  have h1 : comul (R := S) (1 : S) = 1 ⊗ₜ 1 := rfl
  rw [h1]
  induction comul (R := R) a with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, add_smul, hx, hy, tmul_add, map_add, map_add, map_add]
  | tmul a₁ a₂ =>
    simp [Algebra.smul_def, mul_comm]

/-- `f ⊗ g ↦ f_S ⊗ g_S`, `A^∨ ⊗_R A^∨ → (S ⊗ A)^∨ ⊗_S (S ⊗ A)^∨`. -/
def dualBC2 : Cartier.Dual R G.A ⊗[R] Cartier.Dual R G.A →+
    Cartier.Dual S (S ⊗[R] G.A) ⊗[S] Cartier.Dual S (S ⊗[R] G.A) :=
  TensorProduct.liftAddHom
    { toFun := fun f =>
        { toFun := fun g => G.dualBC f ⊗ₜ[S] G.dualBC g
          map_zero' := by
            rw [show G.dualBC (S := S) 0 = 0 from G.dualBC_ext fun a => by simp]
            exact tmul_zero _ _
          map_add' := fun g g' => by rw [dualBC_add, tmul_add] }
      map_zero' := by
        ext g
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
        rw [show G.dualBC (S := S) 0 = 0 from G.dualBC_ext fun a => by simp]
        exact zero_tmul _ _
      map_add' := fun f f' => by
        ext g
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
        rw [dualBC_add, add_tmul] }
    fun r f g => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [dualBC_smul, dualBC_smul, smul_tmul]

@[simp] theorem dualBC2_tmul (f g : Cartier.Dual R G.A) :
    G.dualBC2 (S := S) (f ⊗ₜ g) = G.dualBC f ⊗ₜ[S] G.dualBC g := rfl

theorem tmul_eq_smul_one_tmul (s : S) (a : G.A) : (s ⊗ₜ[R] a : S ⊗[R] G.A) = s • (1 ⊗ₜ a) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- `S`-linear maps on `(S ⊗ A) ⊗_S (S ⊗ A)` are determined on `(1 ⊗ a) ⊗ (1 ⊗ b)`. -/
theorem ext2 {M : Type*} [AddCommGroup M] [Module S M]
    {L L' : (S ⊗[R] G.A) ⊗[S] (S ⊗[R] G.A) →ₗ[S] M}
    (h : ∀ a b : G.A, L ((1 ⊗ₜ a) ⊗ₜ (1 ⊗ₜ b)) = L' ((1 ⊗ₜ a) ⊗ₜ (1 ⊗ₜ b))) : L = L' := by
  refine TensorProduct.ext' fun x y => ?_
  induction x with
  | zero => simp
  | add x x' hx hx' => rw [add_tmul, map_add, map_add, hx, hx']
  | tmul s a =>
    induction y with
    | zero => simp
    | add y y' hy hy' => rw [tmul_add, map_add, map_add, hy, hy']
    | tmul s' b =>
      have key : ((s ⊗ₜ[R] a) ⊗ₜ[S] (s' ⊗ₜ[R] b) : (S ⊗[R] G.A) ⊗[S] (S ⊗[R] G.A)) =
          (s * s') • (((1 : S) ⊗ₜ[R] a) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b)) := by
        rw [← smul_tmul_smul, ← tmul_eq_smul_one_tmul, ← tmul_eq_smul_one_tmul]
      rw [key, map_smul, map_smul, h]

theorem ev2_dualBC2 (x : Cartier.Dual R G.A ⊗[R] Cartier.Dual R G.A) (a b : G.A) :
    Cartier.ev2 S (S ⊗[R] G.A) (G.dualBC2 x) ((1 ⊗ₜ a) ⊗ₜ (1 ⊗ₜ b)) =
      algebraMap R S (Cartier.ev2 R G.A x (a ⊗ₜ b)) := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply, map_add]
  | tmul f g =>
    rw [dualBC2_tmul, Cartier.ev2_tmul_tmul, Cartier.ev2_tmul_tmul, dualBC_tmul, dualBC_tmul,
      map_mul, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one]

/-- **`(f_S)` is compatible with the comultiplications.** -/
theorem comulD_dualBC (f : Cartier.Dual R G.A) :
    Cartier.comulD S (S ⊗[R] G.A) (G.dualBC f) = G.dualBC2 (Cartier.comulD R G.A f) := by
  apply Cartier.ev2_injective
  refine G.ext2 fun a b => ?_
  rw [Cartier.ev2_comulD_tmul, ev2_dualBC2, Cartier.ev2_comulD_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, dualBC_tmul, Algebra.smul_def, mul_one]

theorem dualBC_zero : G.dualBC (S := S) 0 = 0 := G.dualBC_ext fun a => by simp

/-! ### Points -/

variable {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- `ψ ↦ ψ ∘ (·)_S`, `(G_S)^∨(T) → G^∨(T)`. -/
def dualBCPoint (ψ : (G.baseChange S).dual.points T) : G.dual.points T :=
  let φ : Cartier.Dual S (S ⊗[R] G.A) →ₐ[S] T := ofConv ψ
  toConv (show Cartier.Dual R G.A →ₐ[R] T from
    { toFun := fun f => φ (G.dualBC f)
      map_one' := by
        change φ (G.dualBC 1) = 1
        rw [dualBC_one, map_one]
      map_mul' := fun f g => by
        change φ (G.dualBC (f * g)) = φ (G.dualBC f) * φ (G.dualBC g)
        rw [dualBC_mul, map_mul]
      map_zero' := by
        change φ (G.dualBC 0) = 0
        rw [dualBC_zero, map_zero]
      map_add' := fun f g => by
        change φ (G.dualBC (f + g)) = φ (G.dualBC f) + φ (G.dualBC g)
        rw [dualBC_add, map_add]
      commutes' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one, dualBC_smul, dualBC_one, map_smul, map_one,
          Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply] })

@[simp] theorem dualBCPoint_apply (ψ : (G.baseChange S).dual.points T) (f : Cartier.Dual R G.A) :
    ofConv (G.dualBCPoint ψ) f = ofConv ψ (G.dualBC f) := rfl

theorem dualBCPoint_mul (ψ ψ' : (G.baseChange S).dual.points T) :
    G.dualBCPoint (ψ * ψ') = G.dualBCPoint ψ * G.dualBCPoint ψ' := by
  apply WithConv.ofConv_injective
  ext f
  let φ : Cartier.Dual S (S ⊗[R] G.A) →ₗ[S] T := (ofConv ψ).toLinearMap
  let φ' : Cartier.Dual S (S ⊗[R] G.A) →ₗ[S] T := (ofConv ψ').toLinearMap
  let χ : Cartier.Dual R G.A →ₗ[R] T := (ofConv (G.dualBCPoint ψ)).toLinearMap
  let χ' : Cartier.Dual R G.A →ₗ[R] T := (ofConv (G.dualBCPoint ψ')).toLinearMap
  change LinearMap.mul' S T (TensorProduct.map φ φ' (Cartier.comulD S (S ⊗[R] G.A)
    (G.dualBC f))) = LinearMap.mul' R T (TensorProduct.map χ χ' (Cartier.comulD R G.A f))
  rw [comulD_dualBC]
  induction Cartier.comulD R G.A f with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]
  | tmul g h => rfl

/-- The base change `IsBaseChange` structure of `f ↦ f_S` (Mathlib's `IsBaseChange.dual`). -/
theorem isBaseChange_dual :
    IsBaseChange S (TensorProduct.isBaseChange R G.A S).toDual :=
  (TensorProduct.isBaseChange R G.A S).dual

theorem toDual_eq (f : Module.Dual R G.A) :
    (TensorProduct.isBaseChange R G.A S).toDual f = ofConv (G.dualBC (toConv f)) := by
  refine TensorProduct.AlgebraTensorModule.ext fun s a => ?_
  rw [G.tmul_eq_smul_one_tmul s a, map_smul, map_smul]
  congr 1
  rw [show ((1 : S) ⊗ₜ[R] a) = TensorProduct.mk R S G.A 1 a from rfl,
    IsBaseChange.toDual_comp_apply]
  change _ = f a • (1 : S)
  rw [Algebra.smul_def, mul_one]

/-- The extension of a point `χ ∈ G^∨(T)` to `(S ⊗ A)^∨ → T`, `S`-linearly. -/
def dualBCLift (χ : G.dual.points T) : Module.Dual S (S ⊗[R] G.A) →ₗ[S] T :=
  G.isBaseChange_dual.lift ((ofConv χ).toLinearMap ∘ₗ
    (WithConv.linearEquiv R (G.A →ₗ[R] R)).symm.toLinearMap)

theorem dualBCLift_dualBC (χ : G.dual.points T) (f : Cartier.Dual R G.A) :
    G.dualBCLift χ (ofConv (G.dualBC (S := S) f)) = ofConv χ f := by
  have h := G.toDual_eq (S := S) (ofConv f)
  rw [toConv_ofConv] at h
  rw [← h, dualBCLift, IsBaseChange.lift_eq]
  rfl

theorem dualBCLift_mul (χ : G.dual.points T) (F F' : Cartier.Dual S (S ⊗[R] G.A)) :
    G.dualBCLift χ (ofConv (F * F')) = G.dualBCLift χ (ofConv F) * G.dualBCLift χ (ofConv F') := by
  have key : ∀ x y : Module.Dual S (S ⊗[R] G.A),
      G.dualBCLift χ (ofConv (toConv x * toConv y)) =
        G.dualBCLift χ x * G.dualBCLift χ y := by
    intro x y
    refine G.isBaseChange_dual.inductionOn x _ ?_ ?_ ?_ ?_
    · simp
    · intro f
      refine G.isBaseChange_dual.inductionOn y _ ?_ ?_ ?_ ?_
      · simp
      · intro g
        rw [G.toDual_eq, G.toDual_eq, toConv_ofConv, toConv_ofConv, ← dualBC_mul,
          dualBCLift_dualBC, dualBCLift_dualBC, dualBCLift_dualBC]
        exact map_mul (ofConv χ) _ _
      · intro s n hn
        rw [toConv_smul, mul_smul_comm, ofConv_smul, map_smul, map_smul, hn, mul_smul_comm]
      · intro n₁ n₂ h₁ h₂
        rw [toConv_add, mul_add, ofConv_add, map_add, map_add, h₁, h₂, mul_add]
    · intro s n hn
      rw [toConv_smul, smul_mul_assoc, ofConv_smul, map_smul, map_smul, hn, smul_mul_assoc]
    · intro n₁ n₂ h₁ h₂
      rw [toConv_add, add_mul, ofConv_add, map_add, map_add, h₁, h₂, add_mul]
  exact key (ofConv F) (ofConv F')

/-- The inverse: `χ ↦` the `S`-algebra map `(S ⊗ A)^∨ → T` extending `χ`. -/
def dualBCPointInv (χ : G.dual.points T) : (G.baseChange S).dual.points T :=
  have h1 : ofConv χ (1 : Cartier.Dual R G.A) = 1 := map_one (ofConv χ)
  toConv (show Cartier.Dual S (S ⊗[R] G.A) →ₐ[S] T from
    { toFun := fun F => G.dualBCLift χ (ofConv F)
      map_one' := by
        change G.dualBCLift χ (ofConv (1 : Cartier.Dual S (S ⊗[R] G.A))) = 1
        rw [← G.dualBC_one (S := S), dualBCLift_dualBC, h1]
      map_mul' := fun F F' => G.dualBCLift_mul χ F F'
      map_zero' := by
        change G.dualBCLift χ (ofConv (0 : Cartier.Dual S (S ⊗[R] G.A))) = 0
        rw [ofConv_zero, map_zero]
      map_add' := fun F F' => by
        change G.dualBCLift χ (ofConv (F + F')) =
          G.dualBCLift χ (ofConv F) + G.dualBCLift χ (ofConv F')
        rw [ofConv_add, map_add]
      commutes' := fun s => by
        rw [Algebra.algebraMap_eq_smul_one, ofConv_smul, map_smul, ← G.dualBC_one (S := S),
          dualBCLift_dualBC, h1, Algebra.smul_def, mul_one] })

/-- **`(G_S)^∨(T) ≃* G^∨(T)`.** -/
def dualBaseChangePointsEquiv : (G.baseChange S).dual.points T ≃* G.dual.points T where
  toFun := G.dualBCPoint
  invFun := G.dualBCPointInv
  left_inv ψ := by
    apply WithConv.ofConv_injective
    apply AlgHom.toLinearMap_injective
    have h := G.isBaseChange_dual.algHom_ext
      (G.dualBCLift (G.dualBCPoint ψ))
      ((ofConv ψ).toLinearMap.restrictScalars S ∘ₗ
        (WithConv.linearEquiv S (Module.Dual S (S ⊗[R] G.A))).symm.toLinearMap)
      fun f => by
        rw [G.toDual_eq, dualBCLift_dualBC]
        rfl
    ext F
    exact LinearMap.congr_fun h (ofConv F)
  right_inv χ := by
    apply WithConv.ofConv_injective
    ext f
    exact G.dualBCLift_dualBC χ f
  map_mul' := G.dualBCPoint_mul

theorem dualBaseChangePointsEquiv_apply (ψ : (G.baseChange S).dual.points T)
    (f : Cartier.Dual R G.A) :
    ofConv (G.dualBaseChangePointsEquiv ψ) f = ofConv ψ (G.dualBC f) := rfl

/-- Naturality: `(f_S)^∨` corresponds to `f^∨`. -/
theorem dualBaseChangePointsEquiv_mapPoints {H : FFGroupScheme R} (f : Hom G H)
    (ψ : (H.baseChange S).dual.points T) :
    G.dualBaseChangePointsEquiv ((baseChangeHom S f).dual.mapPoints T ψ) =
      f.dual.mapPoints T (H.dualBaseChangePointsEquiv ψ) := by
  apply WithConv.ofConv_injective
  ext F
  change ofConv ψ ((baseChangeHom S f).dual (G.dualBC F)) = ofConv ψ (H.dualBC (f.dual F))
  congr 1
  refine H.dualBC_ext fun a => ?_
  rfl

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} (G : PDivGroup R p) {S : Type u}
  [CommRing S] [Algebra R S] [Nontrivial S] (T : Type u) [CommRing T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

/-- **`T_p((G_S)^∨)(T) ≃* T_p(G^∨)(T)`** (as limits of the `G_v^∨(T)` along the `i_v^∨`). -/
def dualTateBaseChangeEquiv : (G.baseChange S).DualTate T ≃* G.DualTate T where
  toFun y := ⟨fun v => (G.G v).dualBaseChangePointsEquiv (y.1 v), fun v =>
    (congrArg ((G.G v).dualBaseChangePointsEquiv (S := S) (T := T)) (y.2 v)).trans
      ((G.G v).dualBaseChangePointsEquiv_mapPoints (G.incl v) _)⟩
  invFun z := ⟨fun v => ((G.G v).dualBaseChangePointsEquiv (S := S)).symm (z.1 v), fun v =>
    (G.G v).dualBaseChangePointsEquiv.injective <|
      ((G.G v).dualBaseChangePointsEquiv.apply_symm_apply (z.1 v)).trans <| (z.2 v).trans <|
        Eq.trans (congrArg _ ((G.G (v + 1)).dualBaseChangePointsEquiv.apply_symm_apply
          (z.1 (v + 1))).symm)
          ((G.G v).dualBaseChangePointsEquiv_mapPoints (G.incl v) _).symm⟩
  left_inv _ := Subtype.ext (funext fun _ => MulEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (funext fun _ => MulEquiv.apply_symm_apply _ _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)

end PDivGroup

end PadicHodge
