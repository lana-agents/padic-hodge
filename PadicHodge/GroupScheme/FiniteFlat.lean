/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Finite flat commutative group schemes (affine, Hopf-algebra form)

Over a commutative ring `R`, a finite flat commutative group scheme `G = Spec A` is given by a
commutative and cocommutative `R`-Hopf algebra `A` that is finite free as an `R`-module
([BC, Def. 7.1.6]: `f_* O_G` locally free of constant rank; over a local ring such as `O_K`
locally free is free). Its points in a commutative `R`-algebra `S` form the commutative group
`G(S) = Hom_{R-alg}(A, S)` under convolution (Mathlib's `HopfAlgebra.convGroup`), and a
homomorphism `G → H` is a bialgebra map `O(H) → O(G)`.

* `FFGroupScheme R`, `FFGroupScheme.order`, `FFGroupScheme.points`, `FFGroupScheme.Hom`,
  `FFGroupScheme.Hom.mapPoints` (a group homomorphism `G(S) → H(S)`);
* `FFGroupScheme.diag M`: the diagonalizable group scheme `D(M) = Spec R[M]` of a finite abelian
  group `M` (e.g. `μ_n = D(ℤ/n)`, [BC, Example 7.1.7(2)]), of order `|M|`;
* `FFGroupScheme.diagPointsEquiv`: `D(M)(S) ≃* Hom(M, Sˣ)`.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv

namespace PadicHodge

universe u

/-- A finite flat commutative group scheme over `R`, given by its Hopf algebra of functions. -/
structure FFGroupScheme (R : Type u) [CommRing R] where
  /-- The coordinate ring. -/
  A : Type u
  [commRing : CommRing A]
  [hopfAlgebra : HopfAlgebra R A]
  [isCocomm : IsCocomm R A]
  [free : Module.Free R A]
  [finite : Module.Finite R A]

namespace FFGroupScheme

attribute [instance] commRing hopfAlgebra isCocomm free finite

variable {R : Type u} [CommRing R]

/-- The order (rank of the coordinate ring). -/
def order (G : FFGroupScheme R) : ℕ := Module.finrank R G.A

/-- The `S`-valued points `G(S) = Hom_{R-alg}(A, S)`, a commutative group under convolution. -/
abbrev points (G : FFGroupScheme R) (S : Type*) [CommRing S] [Algebra R S] : Type _ :=
  WithConv (G.A →ₐ[R] S)

/-- The group structure on `G(S)`: convolution, with inverse given by the antipode. (Mathlib's
`AlgHom.convGroup` asks for a bialgebra structure on the target; we only need `S` commutative.) -/
instance pointsCommGroup (G : FFGroupScheme R) (S : Type*) [CommRing S] [Algebra R S] :
    CommGroup (G.points S) where
  __ := (inferInstance : CommMonoid (WithConv (G.A →ₐ[R] S)))
  inv f := toConv <| (ofConv f).comp (HopfAlgebra.antipodeAlgHom R G.A)
  inv_mul_cancel f := by
    have H : (Algebra.TensorProduct.lmul' R).comp
        (Algebra.TensorProduct.map (ofConv f) (ofConv f)) =
        (ofConv f).comp (Algebra.TensorProduct.lmul' R) := by ext <;> simp
    trans toConv <| ((Algebra.TensorProduct.lmul' R).comp
      (Algebra.TensorProduct.map (ofConv f) (ofConv f))).comp
      ((Algebra.TensorProduct.map
      (HopfAlgebra.antipodeAlgHom R G.A) (.id _ _)).comp (Bialgebra.comulAlgHom R G.A))
    · rw [AlgHom.comp_assoc,
        ← AlgHom.comp_assoc (Algebra.TensorProduct.map (ofConv f) (ofConv f)),
        ← Algebra.TensorProduct.map_comp]; rfl
    rw [H, AlgHom.comp_assoc, WithConv.ext_iff, ← AlgHom.toLinearMap_injective.eq_iff]
    change (ofConv f).toLinearMap.comp
        (toConv (antipode R (A := G.A)) * toConv LinearMap.id).ofConv =
      ofConv (1 : WithConv <| G.A →ₗ[R] S)
    rw [LinearMap.antipode_mul_id]
    ext
    simp

/-- Homomorphisms of finite flat group schemes `G → H`: bialgebra maps `O(H) → O(G)`. -/
abbrev Hom (G H : FFGroupScheme R) : Type u := H.A →ₐc[R] G.A

/-- The group homomorphism `G(S) → H(S)` induced by a homomorphism `G → H`. -/
def Hom.mapPoints {G H : FFGroupScheme R} (f : Hom G H) (S : Type*) [CommRing S] [Algebra R S] :
    G.points S →* H.points S where
  toFun φ := toConv ((ofConv φ).comp (f : H.A →ₐ[R] G.A))
  map_one' := by
    apply WithConv.ofConv_injective
    ext a
    simp [AlgHom.convOne_apply]
  map_mul' φ ψ := by
    apply WithConv.ofConv_injective
    rw [← AlgHom.convMul_comp_bialgHom_distrib]

/-! ### Diagonalizable group schemes -/

variable (R) in
/-- The diagonalizable group scheme `D(M) = Spec R[M]` of a finite commutative group `M`
(written multiplicatively). For `M = ℤ/n` this is `μ_n`. -/
def diag (M : Type) [CommGroup M] [Fintype M] : FFGroupScheme R where
  A := MonoidAlgebra R M

theorem order_diag (M : Type) [CommGroup M] [Fintype M] [Nontrivial R] :
    (diag R M).order = Fintype.card M := by
  rw [order]
  change Module.finrank R (MonoidAlgebra R M) = _
  rw [(MonoidAlgebra.coeffLinearEquiv (R := R) (S := R) (M := M)).finrank_eq]
  exact Module.finrank_finsupp_self (R := R) (ι := M)

/-- The points of `D(M)` are the characters of `M`: `D(M)(S) ≃* Hom(M, S)`. -/
def diagPointsEquiv (M : Type) [CommGroup M] [Fintype M] (S : Type*) [CommRing S]
    [Algebra R S] : (diag R M).points S ≃* (M →* S) where
  toFun φ := (MonoidAlgebra.lift R S M).symm (ofConv φ)
  invFun F := toConv (MonoidAlgebra.lift R S M F)
  left_inv φ := by simp
  right_inv F := by simp
  map_mul' φ ψ := by
    ext m
    change (ofConv (φ * ψ)) (MonoidAlgebra.single m 1) =
      (ofConv φ) (MonoidAlgebra.single m 1) * (ofConv ψ) (MonoidAlgebra.single m 1)
    rw [AlgHom.convMul_apply]
    have hc : Coalgebra.comul (R := R) (A := MonoidAlgebra R M) (MonoidAlgebra.single m 1) =
        MonoidAlgebra.single m 1 ⊗ₜ[R] MonoidAlgebra.single m 1 := by
      rw [MonoidAlgebra.comul_single]; simp
    erw [hc]
    exact Algebra.TensorProduct.lift_tmul _ _ _ _ _


end FFGroupScheme

end PadicHodge
