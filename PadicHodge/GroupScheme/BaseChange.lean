/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.PDivisibleHom
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Base change of finite flat group schemes and `p`-divisible groups

For an `R`-algebra `S`:

* `FFGroupScheme.baseChange S G = G_S = Spec (S ⊗_R A)` (Mathlib's Hopf algebra structure on
  `S ⊗_R A`), of the same order (`order_baseChange`);
* `baseChangePointsEquiv : G_S(T) ≃* G(T)` for every `S`-algebra `T` (restriction along
  `A → S ⊗_R A`, inverse `g ↦ (s ⊗ a ↦ s g(a))`), natural in homomorphisms
  (`baseChangeHom`, `baseChangePointsEquiv_mapPoints`);
* `PDivGroup.baseChange S G = G_S`, a `p`-divisible group over `S` of the same height
  (the kernel condition is transported along `baseChangePointsEquiv`), with
  `PDivGroup.baseChangeTateEquiv : T_p(G_S)(T) ≃* T_p(G)(T)`, and base change of morphisms
  `PDivGroup.Hom.baseChange`.
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

/-- The base change `G_S = Spec (S ⊗_R A)`. -/
abbrev baseChange (G : FFGroupScheme R) : FFGroupScheme S where
  A := S ⊗[R] G.A

theorem order_baseChange [Nontrivial R] [Nontrivial S] (G : FFGroupScheme R) :
    (G.baseChange S).order = G.order :=
  Module.finrank_baseChange

/-- The base change `f_S : G_S → H_S` of a homomorphism. -/
def baseChangeHom {G H : FFGroupScheme R} (f : Hom G H) :
    Hom (G.baseChange S) (H.baseChange S) :=
  Bialgebra.TensorProduct.map (BialgHom.id S S) f

theorem baseChangeHom_tmul {G H : FFGroupScheme R} (f : Hom G H) (s : S) (a : H.A) :
    baseChangeHom S f (s ⊗ₜ a) = s ⊗ₜ f a := rfl

variable {S} (G : FFGroupScheme R) (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

/-- **Points of the base change**: `G_S(T) ≃* G(T)` for an `S`-algebra `T`. -/
def baseChangePointsEquiv : (G.baseChange S).points T ≃* G.points T where
  toFun f := toConv (((ofConv f).restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : G.A →ₐ[R] S ⊗[R] G.A))
  invFun g := toConv (Algebra.TensorProduct.lift (Algebra.ofId S T) (ofConv g)
    (fun _ _ => .all _ _))
  left_inv f := by
    apply WithConv.ofConv_injective
    apply Algebra.TensorProduct.ext'
    intro s a
    change algebraMap S T s * ofConv f (1 ⊗ₜ a) = ofConv f (s ⊗ₜ a)
    rw [← AlgHom.commutes (ofConv f) s, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_self, RingHom.id_apply, mul_one,
      one_mul]
  right_inv g := by
    apply WithConv.ofConv_injective
    ext a
    simp
  map_mul' f f' := by
    apply WithConv.ofConv_injective
    ext a
    change (ofConv (f * f')) (1 ⊗ₜ a) = _
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
    rw [TensorProduct.comul_tmul]
    have h1 : comul (R := S) (1 : S) = 1 ⊗ₜ 1 := rfl
    rw [h1]
    induction comul (R := R) a with
    | zero => simp
    | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy, map_add]
    | tmul a₁ a₂ => simp

theorem baseChangePointsEquiv_apply (f : (G.baseChange S).points T) (a : G.A) :
    ofConv (G.baseChangePointsEquiv T f) a = ofConv f (1 ⊗ₜ a) := rfl

/-- Naturality of `baseChangePointsEquiv`. -/
theorem baseChangePointsEquiv_mapPoints {H : FFGroupScheme R} (f : Hom G H)
    (x : (G.baseChange S).points T) :
    H.baseChangePointsEquiv T ((baseChangeHom S f).mapPoints T x) =
      f.mapPoints T (G.baseChangePointsEquiv T x) := rfl

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} (S : Type u) [CommRing S] [Algebra R S]
  [Nontrivial S]

omit [Nontrivial R] [Nontrivial S] in
theorem baseChange_incl_surjective (G : PDivGroup R p) (v : ℕ) :
    Function.Surjective (baseChangeHom S (G.incl v)) := by
  intro x
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective S
    (g := (G.incl v : (G.G (v + 1)).A →ₗ[R] (G.G v).A)) (G.incl_surjective v) x
  exact ⟨y, hy⟩

omit [Nontrivial R] [Nontrivial S] in
theorem baseChange_range_eq (G : PDivGroup R p) (v : ℕ) (T : Type u) [CommRing T] [Algebra S T]
    (y : ((G.G (v + 1)).baseChange S).points T) :
    (∃ x, (baseChangeHom S (G.incl v)).mapPoints T x = y) ↔ y ^ (p ^ v) = 1 := by
  letI : Algebra R T := Algebra.compHom T (algebraMap R S)
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key := G.range_eq v T ((G.G (v + 1)).baseChangePointsEquiv T y)
  rw [← map_pow, MulEquiv.map_eq_one_iff] at key
  rw [← key]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(G.G v).baseChangePointsEquiv T x,
      ((G.G v).baseChangePointsEquiv_mapPoints T (G.incl v) x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨((G.G v).baseChangePointsEquiv T).symm x, ?_⟩
    apply ((G.G (v + 1)).baseChangePointsEquiv T).injective
    rw [(G.G v).baseChangePointsEquiv_mapPoints T (G.incl v), MulEquiv.apply_symm_apply, hx]

/-- **Base change of a `p`-divisible group** to an `R`-algebra `S`. -/
def baseChange (G : PDivGroup R p) : PDivGroup S p where
  height := G.height
  G v := (G.G v).baseChange S
  order_eq v := by rw [order_baseChange]; exact G.order_eq v
  incl v := baseChangeHom S (G.incl v)
  incl_surjective := baseChange_incl_surjective S G
  range_eq := baseChange_range_eq S G

theorem baseChange_height (G : PDivGroup R p) : (G.baseChange S).height = G.height := rfl

variable {S} (G : PDivGroup R p) (T : Type u) [CommRing T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

/-- `T_p(G_S)(T) ≃* T_p(G)(T)`. -/
def baseChangeTateEquiv : (G.baseChange S).TateModule T ≃* G.TateModule T where
  toFun x := ⟨fun v => (G.G v).baseChangePointsEquiv T (x.1 v), fun v =>
    ((G.G v).baseChangePointsEquiv_mapPoints T (G.incl v) (x.1 v)).symm.trans
      ((congrArg ((G.G (v + 1)).baseChangePointsEquiv T) (x.2 v)).trans (map_pow _ _ _))⟩
  invFun y := ⟨fun v => ((G.G v).baseChangePointsEquiv T).symm (y.1 v), fun v => by
    apply ((G.G (v + 1)).baseChangePointsEquiv T).injective
    refine ((G.G v).baseChangePointsEquiv_mapPoints T (G.incl v) _).trans ?_
    refine (congrArg ((G.incl v).mapPoints T)
      (MulEquiv.apply_symm_apply ((G.G v).baseChangePointsEquiv T) (y.1 v))).trans ?_
    refine (y.2 v).trans ?_
    refine Eq.trans ?_ (map_pow _ _ _).symm
    exact congrArg (· ^ p)
      (MulEquiv.apply_symm_apply ((G.G (v + 1)).baseChangePointsEquiv T) (y.1 (v + 1))).symm⟩
  left_inv x := Subtype.ext (funext fun v => MulEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (funext fun v => MulEquiv.apply_symm_apply _ _)
  map_mul' x y := Subtype.ext (funext fun v => map_mul _ _ _)

/-- Base change of a morphism of `p`-divisible groups. -/
def Hom.baseChange {G H : PDivGroup R p} (φ : Hom G H) : Hom (G.baseChange S) (H.baseChange S)
    where
  f v := baseChangeHom S (φ.f v)
  comm v := by
    refine DFunLike.ext _ _ fun (x : S ⊗[R] (H.G (v + 1)).A) => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul s a =>
      have := congrArg (fun g : (H.G (v + 1)).A →ₐc[R] (G.G v).A => g a) (φ.comm v)
      change s ⊗ₜ (G.incl v) (φ.f (v + 1) a) = s ⊗ₜ (φ.f v) (H.incl v a)
      exact congrArg (s ⊗ₜ ·) this
    | add x y hx hy => exact ((map_add _ x y).trans (congrArg₂ _ hx hy)).trans (map_add _ x y).symm

theorem Hom.baseChange_mapTate {H : PDivGroup R p} (φ : Hom G H)
    (x : (G.baseChange S).TateModule T) :
    H.baseChangeTateEquiv T ((φ.baseChange (S := S)).mapTate T x) =
      φ.mapTate T (G.baseChangeTateEquiv T x) := rfl

end PDivGroup

end PadicHodge
