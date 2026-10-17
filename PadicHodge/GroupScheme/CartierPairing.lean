/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.CartierDouble
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-!
# Points of the Cartier dual and the Cartier pairing

For `G = Spec A` finite flat over `R` ([BC, Exercise 12.5.3 (5), (6)], over the base ring):

* an `R`-linear functional `f : A → R` is an algebra map iff it is a group-like element of the
  coalgebra `A^∨` (`isGroupLikeElem_dual_iff`: `Δ^∨ f = f ∘ m` is `f ⊗ f` iff `f` is
  multiplicative); hence `G(R) ≃* GroupLike(A^∨)` (`pointsEquivGroupLike`);
* dually, by double duality, `G^∨(R) ≃* GroupLike(A)` (`dualPointsEquivGroupLike`): the
  `R`-points of the Cartier dual are the characters `G → 𝔾_m` (group-like elements of `A`, i.e.
  Hopf algebra maps `R[t, t⁻¹] → A`);
* the **Cartier pairing** `G(R) × G^∨(R) → R`, `⟨φ, ψ⟩ = ψ(φ)` (`cartierPairing`), which is
  bimultiplicative.
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (G : FFGroupScheme R)

/-- A functional `f ∈ A^∨` is group-like iff it is an algebra map `A → R`. -/
theorem isGroupLikeElem_dual_iff (f : Cartier.Dual R G.A) :
    IsGroupLikeElem R f ↔ f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b := by
  rw [isGroupLikeElem_iff]
  refine and_congr Iff.rfl ⟨fun h a b => ?_, fun h => ?_⟩
  · have h' := congrArg (fun x => Cartier.ev2 R G.A x (a ⊗ₜ b)) h
    rw [show comul f = Cartier.comulD R G.A f from rfl, Cartier.ev2_comulD_tmul,
      Cartier.ev2_tmul_tmul] at h'
    exact h'
  · apply Cartier.ev2_injective
    refine TensorProduct.ext' fun a b => ?_
    rw [show comul f = Cartier.comulD R G.A f from rfl, Cartier.ev2_comulD_tmul,
      Cartier.ev2_tmul_tmul, h]

/-- `G(R) ≃* GroupLike(A^∨)`. -/
def pointsEquivGroupLike : G.points R ≃* GroupLike R G.dual.A where
  toFun φ := ⟨toConv (ofConv φ).toLinearMap,
    (G.isGroupLikeElem_dual_iff _).2 ⟨map_one (ofConv φ), map_mul (ofConv φ)⟩⟩
  invFun g := toConv (AlgHom.ofLinearMap (ofConv (g.val : Cartier.Dual R G.A))
    ((G.isGroupLikeElem_dual_iff g.val).1 g.2).1
    ((G.isGroupLikeElem_dual_iff g.val).1 g.2).2)
  left_inv φ := rfl
  right_inv g := rfl
  map_mul' φ ψ := by
    apply GroupLike.ext
    change toConv (ofConv (φ * ψ)).toLinearMap =
      toConv (ofConv φ).toLinearMap * toConv (ofConv ψ).toLinearMap
    apply WithConv.ext
    refine LinearMap.ext fun a => ?_
    rw [LinearMap.convMul_apply]
    change (ofConv (φ * ψ)) a = _
    rw [AlgHom.convMul_apply]
    generalize comul (R := R) a = x
    induction x with
    | zero => simp
    | tmul b c => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

@[simp]
theorem pointsEquivGroupLike_apply (φ : G.points R) (a : G.A) :
    (show Cartier.Dual R G.A from (G.pointsEquivGroupLike φ).val) a = ofConv φ a := rfl

/-- `G^∨(R) ≃* GroupLike(A)`: the `R`-points of the Cartier dual are the characters of `G`. -/
def dualPointsEquivGroupLike : G.dual.points R ≃* GroupLike R G.A :=
  G.dual.pointsEquivGroupLike.trans
    { toFun := fun g => ⟨(Cartier.evEquiv R G.A).symm g.val,
        (isGroupLikeElem_map_equiv (Cartier.evEquiv R G.A).symm).2 g.2⟩
      invFun := fun g => ⟨Cartier.evEquiv R G.A g.val,
        (isGroupLikeElem_map_equiv (Cartier.evEquiv R G.A)).2 g.2⟩
      left_inv := fun g => GroupLike.ext (by simp)
      right_inv := fun g => GroupLike.ext (by simp)
      map_mul' := fun g h => GroupLike.ext (by
        simp only [GroupLike.val_mul]
        exact map_mul (Cartier.evEquiv R G.A).symm _ _) }

/-- The **Cartier pairing** `⟨φ, ψ⟩ = ψ(φ)` for `φ ∈ G(R)`, `ψ ∈ G^∨(R)`, multiplicative in
both variables. -/
def cartierPairing : G.points R →* G.dual.points R →* R where
  toFun φ :=
    { toFun := fun ψ => ofConv ψ ((G.pointsEquivGroupLike φ).val : Cartier.Dual R G.A)
      map_one' := by
        change algebraMap R R (counit (R := R) (G.pointsEquivGroupLike φ).val) = 1
        rw [(G.pointsEquivGroupLike φ).2.counit_eq_one, map_one]
      map_mul' := fun ψ ψ' => by
        change ((ofConv (ψ * ψ')) _ : R) = _
        rw [AlgHom.convMul_apply, (G.pointsEquivGroupLike φ).2.comul_eq_tmul_self]
        simp }
  map_one' := by
    ext ψ
    change ofConv ψ ((G.pointsEquivGroupLike 1).val : Cartier.Dual R G.A) = 1
    rw [map_one, GroupLike.val_one, map_one]
  map_mul' φ φ' := by
    ext ψ
    change ofConv ψ ((G.pointsEquivGroupLike (φ * φ')).val : Cartier.Dual R G.A) =
      ofConv ψ (G.pointsEquivGroupLike φ).val * ofConv ψ (G.pointsEquivGroupLike φ').val
    rw [map_mul, GroupLike.val_mul, map_mul]

theorem cartierPairing_apply (φ : G.points R) (ψ : G.dual.points R) :
    G.cartierPairing φ ψ = ofConv ψ ((G.pointsEquivGroupLike φ).val : Cartier.Dual R G.A) :=
  rfl

end FFGroupScheme

end PadicHodge
