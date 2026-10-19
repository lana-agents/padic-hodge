/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Closure
import PadicHodge.GroupScheme.QuotientGroup
import PadicHodge.GroupScheme.PDivisibleHom

/-!
# Functoriality of scheme-theoretic closures and their points over the generic fibre

Let `R` be a PID with fraction field `K` and `j : H̃ ↪ G_K`, `j' : H̃' ↪ G'_K` closed immersions
of finite flat group schemes over `K` ([Hong, proof of Prop. 3.5.3]).

* `Hom.closureInduced`: a homomorphism `f : G → G'` with `f_K(H̃) ⊆ H̃'` (through
  `g : H̃ → H̃'`) restricts to the closures `H → H'` (`mapPoints_closureInduced`: compatible with
  `f` on points; surjective if `f` is a closed immersion);
* `Hom.closurePtEquiv`: for a `K`-algebra `Ω`, the points of the closure are those of the generic
  fibre, `H̃(Ω) ≃* H(Ω)` (`closureHom_closurePt`: compatible with `j` and `H → G`;
  `closureInduced_closurePt`: compatible with `closureInduced`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, proof of Prop. 3.5.3.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {K : Type u} [Field K]
  [Algebra R K] [IsFractionRing R K]

attribute [local instance] algebraBase

namespace Hom

variable {G G' : FFGroupScheme R} {H H' : FFGroupScheme K}

/-! ### Functoriality -/

section Functoriality

variable (j : Hom H (G.baseChange K)) (j' : Hom H' (G'.baseChange K)) (f : Hom G G')
  (g : Hom H H') (h : ∀ a, j (1 ⊗ₜ f a) = g (j' (1 ⊗ₜ a)))

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] in
include h in
theorem closureIdeal_le_comap :
    j'.closureIdeal ≤ j.closureIdeal.comap (f : G'.A →ₐ[R] G.A) := by
  intro a ha
  rw [Ideal.mem_comap, mem_closureIdeal]
  change j (1 ⊗ₜ f a) = 0
  rw [h, ← closureMap_apply, (mem_closureIdeal j').mp ha, map_zero]

/-- The algebra map `A'/I' → A/I` induced by `f`. -/
def closureInducedAlg : j'.closure.A →ₐ[R] j.closure.A :=
  Ideal.quotientMapₐ j.closureIdeal (f : G'.A →ₐ[R] G.A) (closureIdeal_le_comap j j' f g h)

theorem closureInducedAlg_mk (a : G'.A) :
    closureInducedAlg j j' f g h (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) := rfl

theorem closureHom_mapPoints_closureInducedAlg {T : Type*} [CommRing T] [Algebra R T]
    (x : j.closure.points T) :
    j'.closureHom.mapPoints T (toConv ((ofConv x).comp (closureInducedAlg j j' f g h))) =
      f.mapPoints T (j.closureHom.mapPoints T x) := rfl

/-- **The homomorphism of closures `H → H'` induced by `f : G → G'`** (with `f_K(H̃) ⊆ H̃'`). -/
def closureInduced : Hom j.closure j'.closure :=
  homOfPoints (closureInducedAlg j j' f g h)
    (fun S _ _ φ ψ => by
      apply mapPoints_injective_of_surjective j'.closureHom_surjective
      rw [map_mul, closureHom_mapPoints_closureInducedAlg, closureHom_mapPoints_closureInducedAlg,
        closureHom_mapPoints_closureInducedAlg, map_mul, map_mul])
    (by
      apply mapPoints_injective_of_surjective j'.closureHom_surjective
      rw [closureHom_mapPoints_closureInducedAlg, map_one, map_one, map_one])

theorem closureInduced_mk (a : G'.A) :
    closureInduced j j' f g h (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f a) := rfl

/-- `H → H' → G'` is `H → G → G'` on points. -/
theorem mapPoints_closureInduced {T : Type*} [CommRing T] [Algebra R T]
    (x : j.closure.points T) :
    j'.closureHom.mapPoints T ((closureInduced j j' f g h).mapPoints T x) =
      f.mapPoints T (j.closureHom.mapPoints T x) := rfl

theorem closureInduced_surjective (hf : Function.Surjective f) :
    Function.Surjective (closureInduced j j' f g h) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨b, rfl⟩ := hf a
  exact ⟨Ideal.Quotient.mk _ b, rfl⟩

end Functoriality

/-! ### Points of the closure over the generic fibre -/

section Points

variable (j : Hom H (G.baseChange K)) (Ω : Type*) [CommRing Ω] [Algebra K Ω] [Algebra R Ω]
  [IsScalarTower R K Ω]

/-- The point `y ∘ (A/I ↪ C̃)` of the closure attached to a point `y` of `H̃`. -/
def closurePt (y : H.points Ω) : j.closure.points Ω :=
  toConv (((ofConv y).restrictScalars R).comp j.closureEmb)

theorem closurePt_mk (y : H.points Ω) (a : G.A) :
    ofConv (j.closurePt Ω y) (Ideal.Quotient.mk _ a) = ofConv y (j (1 ⊗ₜ a)) := rfl

/-- `H̃(Ω) → H(Ω) → G(Ω)` is `j` on points. -/
theorem closureHom_closurePt (y : H.points Ω) :
    j.closureHom.mapPoints Ω (j.closurePt Ω y) =
      G.baseChangePointsEquiv Ω (j.mapPoints Ω y) := rfl

/-- `y ↦ y ∘ (A/I ↪ C̃)` as a group homomorphism `H̃(Ω) → H(Ω)`. -/
def closurePtHom : H.points Ω →* j.closure.points Ω where
  toFun := j.closurePt Ω
  map_one' := by
    apply mapPoints_injective_of_surjective j.closureHom_surjective
    rw [closureHom_closurePt, map_one, map_one, map_one]
  map_mul' y y' := by
    apply mapPoints_injective_of_surjective j.closureHom_surjective
    rw [map_mul, closureHom_closurePt, closureHom_closurePt, closureHom_closurePt, map_mul,
      map_mul]

theorem closurePtHom_apply (y : H.points Ω) : j.closurePtHom Ω y = j.closurePt Ω y := rfl

theorem closurePt_bijective (hj : Function.Surjective j) :
    Function.Bijective (j.closurePt Ω) := by
  constructor
  · intro y y' hyy
    apply WithConv.ofConv_injective
    have h1 : ((ofConv y).restrictScalars R).comp j.closureEmb =
        ((ofConv y').restrictScalars R).comp j.closureEmb :=
      congrArg ofConv hyy
    have h2 : (ofConv y).comp (j.closureGeneric hj).toAlgHom =
        (ofConv y').comp (j.closureGeneric hj).toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro k q
      change ofConv y (algebraMap K H.A k * j.closureEmb q) =
        ofConv y' (algebraMap K H.A k * j.closureEmb q)
      rw [map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
      exact congrArg (algebraMap K Ω k * ·) (AlgHom.congr_fun h1 q)
    ext c
    obtain ⟨t, rfl⟩ := (j.closureGeneric hj).surjective c
    exact AlgHom.congr_fun h2 t
  · intro x
    refine ⟨toConv ((Algebra.TensorProduct.lift (Algebra.ofId K Ω) (ofConv x)
      (fun _ _ => .all _ _)).comp (j.closureGeneric hj).symm.toAlgHom), ?_⟩
    apply WithConv.ofConv_injective
    ext q
    have hq : (j.closureGeneric hj).symm (j.closureEmb q) = 1 ⊗ₜ q := by
      rw [AlgEquiv.symm_apply_eq]
      change j.closureEmb q = algebraMap K H.A 1 * j.closureEmb q
      rw [map_one, one_mul]
    change Algebra.TensorProduct.lift (Algebra.ofId K Ω) (ofConv x) (fun _ _ => .all _ _)
      ((j.closureGeneric hj).symm (j.closureEmb q)) = ofConv x q
    rw [hq]
    exact (Algebra.TensorProduct.lift_tmul (Algebra.ofId K Ω) (ofConv x) _ 1 q).trans (by simp)

/-- **`H̃(Ω) ≃* H(Ω)`**: the closure has the points of the generic fibre. -/
def closurePtEquiv (hj : Function.Surjective j) : H.points Ω ≃* j.closure.points Ω :=
  MulEquiv.ofBijective (j.closurePtHom Ω) (j.closurePt_bijective Ω hj)

theorem closurePtEquiv_apply (hj : Function.Surjective j) (y : H.points Ω) :
    j.closurePtEquiv Ω hj y = j.closurePt Ω y := rfl

/-- `closureInduced` is `g` on the points of the generic fibre. -/
theorem closureInduced_closurePt (j' : Hom H' (G'.baseChange K)) (f : Hom G G') (g : Hom H H')
    (h : ∀ a, j (1 ⊗ₜ f a) = g (j' (1 ⊗ₜ a))) (y : H.points Ω) :
    (closureInduced j j' f g h).mapPoints Ω (j.closurePt Ω y) =
      j'.closurePt Ω (g.mapPoints Ω y) := by
  apply WithConv.ofConv_injective
  refine Ideal.Quotient.algHom_ext R (AlgHom.ext fun a => ?_)
  change ofConv y (j (1 ⊗ₜ f a)) = ofConv y (g (j' (1 ⊗ₜ a)))
  rw [h]

end Points

end Hom

end FFGroupScheme

end PadicHodge
