/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Cartier

/-!
# Cartier double duality

For a finite free commutative cocommutative Hopf algebra `A`, evaluation `a ↦ (f ↦ f(a))` is an
isomorphism of Hopf algebras `A ≅ A^∨∨` ([BC, Exercise 12.5.3 (6)], "double duality"): it is
bijective since `A` is finite free (`Module.evalEquiv`), multiplicative because the
comultiplication of `A^∨` is the transpose of the multiplication of `A`, and compatible with the
comultiplications because the multiplication of `A^∨` is the transpose of that of `A`.

* `Cartier.evEquiv : A ≃ₐc[R] A^∨∨`; `FFGroupScheme.dualDualIso : G ≅ G^∨∨`.
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace Cartier

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A] [Module.Free R A] [Module.Finite R A]

variable (R A) in
/-- Evaluation `A → A^∨∨`, `a ↦ (f ↦ f(a))`. -/
def evLin : A →ₗ[R] Dual R (Dual R A) where
  toFun a := toConv
    { toFun := fun f => f a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := WithConv.ext <| LinearMap.ext fun f => map_add (ofConv f) a b
  map_smul' c a := WithConv.ext <| LinearMap.ext fun f => map_smul (ofConv f) c a

@[simp]
theorem evLin_apply (a : A) (f : Dual R A) : evLin R A a f = f a := rfl

theorem mul'_map_evLin (x : Dual R A ⊗[R] Dual R A) (a b : A) :
    LinearMap.mul' R R (TensorProduct.map (ofConv (evLin R A a)) (ofConv (evLin R A b)) x) =
      ev2 R A x (a ⊗ₜ b) := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_apply]
  | tmul f g => simp

theorem ev2_map_evLin (z : A ⊗[R] A) (f g : Dual R A) :
    ev2 R (Dual R A) (TensorProduct.map (evLin R A) (evLin R A) z) (f ⊗ₜ g) =
      LinearMap.mul' R R (TensorProduct.map (ofConv f) (ofConv g) z) := by
  induction z with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, map_add]
  | tmul a b => simp

variable (R A) in
/-- Evaluation as an algebra map. -/
def evAlg : A →ₐ[R] Dual R (Dual R A) :=
  AlgHom.ofLinearMap (evLin R A)
    (WithConv.ext <| LinearMap.ext fun f => by simp)
    (fun a b => WithConv.ext <| LinearMap.ext fun F => by
      rw [LinearMap.convMul_apply]
      change F (a * b) = LinearMap.mul' R R (TensorProduct.map (ofConv (evLin R A a))
        (ofConv (evLin R A b)) (comulD R A F))
      rw [mul'_map_evLin, ev2_comulD_tmul])

variable (R A) in
/-- Evaluation as a bialgebra map. -/
def evBialg : A →ₐc[R] Dual R (Dual R A) :=
  BialgHom.ofAlgHom (evAlg R A)
    (AlgHom.ext fun a => by
      change (1 : Dual R A) a = counit (R := R) a
      simp)
    (AlgHom.ext fun a => by
      change TensorProduct.map (evLin R A) (evLin R A) (comul a) = comulD R (Dual R A) _
      apply ev2_injective
      refine TensorProduct.ext' fun f g => ?_
      rw [ev2_comulD_tmul, ev2_map_evLin]
      change _ = (f * g) a
      rw [LinearMap.convMul_apply])

theorem evBialg_bijective : Function.Bijective (evBialg R A) := by
  have he := (Module.evalEquiv R A).bijective
  refine ⟨fun a b h => he.1 ?_, fun Φ => ?_⟩
  · ext f
    exact congrArg (fun F : Dual R (Dual R A) => F (toConv f)) h
  · obtain ⟨a, ha⟩ := he.2 (ofConv Φ ∘ₗ (WithConv.linearEquiv R (A →ₗ[R] R)).symm.toLinearMap)
    refine ⟨a, WithConv.ext <| LinearMap.ext fun f => ?_⟩
    have h := LinearMap.congr_fun ha (ofConv f)
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, WithConv.symm_linearEquiv_apply] at h
    exact h

variable (R A) in
/-- **Cartier double duality** `A ≅ A^∨∨`. -/
def evEquiv : A ≃ₐc[R] Dual R (Dual R A) :=
  BialgEquiv.ofBijective (evBialg R A) evBialg_bijective

end Cartier

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

/-- Double duality `G ≅ G^∨∨` (on coordinate rings). -/
def dualDualIso (G : FFGroupScheme R) : G.A ≃ₐc[R] G.dual.dual.A :=
  Cartier.evEquiv R G.A

end FFGroupScheme

end PadicHodge
