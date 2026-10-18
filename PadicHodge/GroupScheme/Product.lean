/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.PDivisibleHom
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Products of finite flat group schemes and of `p`-divisible groups

* `FFGroupScheme.prod G H = G × H = Spec (A ⊗_R B)` (Mathlib's Hopf structure on `A ⊗_R B`),
  `order_prod`, `prodPointsEquiv : (G × H)(S) ≃* G(S) × H(S)` (`x ↦ (x ∘ inl, x ∘ inr)`),
  the projections `fst`, `snd` and `prodMap`;
* `PDivGroup.prod G H` (layers `G_v × H_v`, height `h_G + h_H`), the projections
  `PDivGroup.fst`, `PDivGroup.snd`, and `prodTateEquiv : T_p(G × H)(S) ≃* T_p G(S) × T_p H(S)`.

Products are used for the graph of a homomorphism in [Hong, proof of Thm. 3.5.4].

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, proof of Thm. 3.5.4.
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

/-- **The product** `G × H = Spec (A ⊗_R B)`. -/
abbrev prod (G H : FFGroupScheme R) : FFGroupScheme R where
  A := G.A ⊗[R] H.A

theorem order_prod [Nontrivial R] (G H : FFGroupScheme R) :
    (G.prod H).order = G.order * H.order :=
  Module.finrank_tensorProduct

variable (G H : FFGroupScheme R) (S : Type*) [CommRing S] [Algebra R S]

theorem comul_tmul_one (a : G.A) :
    comul (R := R) (a ⊗ₜ[R] (1 : H.A)) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (S := R))
        (Algebra.TensorProduct.includeLeft (S := R)) (comul (R := R) a) := by
  rw [TensorProduct.comul_tmul]
  have h1 : comul (R := R) (1 : H.A) = 1 ⊗ₜ 1 := Bialgebra.comul_one
  rw [h1]
  induction comul (R := R) a with
  | zero => simp
  | add x y hx hy => rw [add_tmul, map_add, map_add, hx, hy]
  | tmul a₁ a₂ => rfl

theorem comul_one_tmul (b : H.A) :
    comul (R := R) ((1 : G.A) ⊗ₜ[R] b) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight)
        (Algebra.TensorProduct.includeRight) (comul (R := R) b) := by
  rw [TensorProduct.comul_tmul]
  have h1 : comul (R := R) (1 : G.A) = 1 ⊗ₜ 1 := Bialgebra.comul_one
  rw [h1]
  induction comul (R := R) b with
  | zero => simp
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
  | tmul b₁ b₂ => rfl

/-- **Points of a product**: `(G × H)(S) ≃* G(S) × H(S)`. -/
def prodPointsEquiv : (G.prod H).points S ≃* G.points S × H.points S where
  toFun x := (toConv ((ofConv x).comp Algebra.TensorProduct.includeLeft),
    toConv ((ofConv x).comp Algebra.TensorProduct.includeRight))
  invFun y := toConv (Algebra.TensorProduct.lift (ofConv y.1) (ofConv y.2)
    (fun _ _ => .all _ _))
  left_inv x := by
    apply WithConv.ofConv_injective
    apply Algebra.TensorProduct.ext'
    intro a b
    change ofConv x (a ⊗ₜ 1) * ofConv x (1 ⊗ₜ b) = ofConv x (a ⊗ₜ b)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  right_inv y := by
    ext a
    · change ofConv y.1 a * ofConv y.2 1 = _
      rw [map_one, mul_one]
    · change ofConv y.1 1 * ofConv y.2 a = _
      rw [map_one, one_mul]
  map_mul' x y := by
    ext a
    · change ofConv (x * y) (a ⊗ₜ 1) = _
      rw [Prod.fst_mul, AlgHom.convMul_apply, AlgHom.convMul_apply, comul_tmul_one]
      induction comul (R := R) a with
      | zero => simp
      | add u w hu hw => rw [map_add, map_add, hu, hw, map_add]
      | tmul a₁ a₂ => rfl
    · change ofConv (x * y) (1 ⊗ₜ a) = _
      rw [Prod.snd_mul, AlgHom.convMul_apply, AlgHom.convMul_apply, comul_one_tmul]
      induction comul (R := R) a with
      | zero => simp
      | add u w hu hw => rw [map_add, map_add, hu, hw, map_add]
      | tmul a₁ a₂ => rfl

theorem prodPointsEquiv_symm_apply (x : G.points S) (y : H.points S) (a : G.A) (b : H.A) :
    ofConv ((G.prodPointsEquiv H S).symm (x, y)) (a ⊗ₜ b) = ofConv x a * ofConv y b := rfl

variable {G H}

/-- The product of two homomorphisms `G × H → G' × H'`. -/
def prodMap {G' H' : FFGroupScheme R} (f : Hom G G') (g : Hom H H') : Hom (G.prod H) (G'.prod H') :=
  Bialgebra.TensorProduct.map f g

theorem prodPointsEquiv_mapPoints {G' H' : FFGroupScheme R} (f : Hom G G') (g : Hom H H')
    (x : (G.prod H).points S) :
    (G'.prodPointsEquiv H' S) ((prodMap f g).mapPoints S x) =
      (f.mapPoints S (G.prodPointsEquiv H S x).1, g.mapPoints S (G.prodPointsEquiv H S x).2) := by
  ext a
  · change ofConv x (prodMap f g (a ⊗ₜ 1)) = ofConv x (f a ⊗ₜ 1)
    rw [prodMap, Bialgebra.TensorProduct.map_tmul, map_one]
  · change ofConv x (prodMap f g (1 ⊗ₜ a)) = ofConv x (1 ⊗ₜ g a)
    rw [prodMap, Bialgebra.TensorProduct.map_tmul, map_one]

variable (G H) in
/-- The first projection `G × H → G` (`a ↦ a ⊗ 1`). -/
def fst : Hom (G.prod H) G :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeLeft (S := R))
    (AlgHom.ext fun a => by
      change counit (R := R) (a ⊗ₜ[R] (1 : H.A)) = counit (R := R) a
      rw [TensorProduct.counit_tmul, Bialgebra.counit_one, one_smul])
    (AlgHom.ext fun a => (comul_tmul_one G H a).symm)

variable (G H) in
/-- The second projection `G × H → H` (`b ↦ 1 ⊗ b`). -/
def snd : Hom (G.prod H) H :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeRight)
    (AlgHom.ext fun b => by
      change counit (R := R) ((1 : G.A) ⊗ₜ[R] b) = counit (R := R) b
      rw [TensorProduct.counit_tmul, Bialgebra.counit_one, smul_eq_mul, mul_one])
    (AlgHom.ext fun b => (comul_one_tmul G H b).symm)

variable (G H) in
theorem fst_apply (a : G.A) : fst G H a = a ⊗ₜ 1 := rfl

variable (G H) in
theorem snd_apply (b : H.A) : snd G H b = 1 ⊗ₜ b := rfl

theorem mapPoints_fst (x : (G.prod H).points S) :
    (fst G H).mapPoints S x = (G.prodPointsEquiv H S x).1 := rfl

theorem mapPoints_snd (x : (G.prod H).points S) :
    (snd G H).mapPoints S x = (G.prodPointsEquiv H S x).2 := rfl

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} (G H : PDivGroup R p)

/-- **The product of `p`-divisible groups** `G × H = (G_v × H_v)`. -/
def prod : PDivGroup R p where
  height := G.height + H.height
  G v := (G.G v).prod (H.G v)
  order_eq v := by
    rw [order_prod, G.order_eq, H.order_eq, ← pow_add, add_mul]
  incl v := prodMap (G.incl v) (H.incl v)
  incl_surjective v := by
    have h := Algebra.TensorProduct.map_surjective
      (f := (G.incl v : (G.G (v + 1)).A →ₐ[R] (G.G v).A))
      (g := (H.incl v : (H.G (v + 1)).A →ₐ[R] (H.G v).A)) (G.incl_surjective v)
      (H.incl_surjective v)
    rw [← Bialgebra.TensorProduct.map_toAlgHom] at h
    exact h
  range_eq v S _ _ y := by
    let E := (G.G (v + 1)).prodPointsEquiv (H.G (v + 1)) S
    let E' := (G.G v).prodPointsEquiv (H.G v) S
    constructor
    · rintro ⟨x, rfl⟩
      apply E.injective
      rw [map_pow, map_one, prodPointsEquiv_mapPoints, Prod.pow_def, Prod.ext_iff]
      exact ⟨(G.range_eq v S _).mp ⟨_, rfl⟩, (H.range_eq v S _).mp ⟨_, rfl⟩⟩
    · intro hy
      have h1 := congrArg E hy
      rw [map_pow, map_one, Prod.pow_def, Prod.ext_iff] at h1
      obtain ⟨x1, hx1⟩ := (G.range_eq v S _).mpr h1.1
      obtain ⟨x2, hx2⟩ := (H.range_eq v S _).mpr h1.2
      refine ⟨E'.symm (x1, x2), E.injective ?_⟩
      rw [prodPointsEquiv_mapPoints, MulEquiv.apply_symm_apply, hx1, hx2]

theorem prod_height : (G.prod H).height = G.height + H.height := rfl

/-- The first projection `G × H → G`. -/
def fst : Hom (G.prod H) G where
  f v := FFGroupScheme.fst (G.G v) (H.G v)
  comm v := BialgHom.ext fun a => by
    change prodMap (G.incl v) (H.incl v) (a ⊗ₜ 1) = G.incl v a ⊗ₜ 1
    rw [prodMap, Bialgebra.TensorProduct.map_tmul, map_one]

/-- The second projection `G × H → H`. -/
def snd : Hom (G.prod H) H where
  f v := FFGroupScheme.snd (G.G v) (H.G v)
  comm v := BialgHom.ext fun b => by
    change prodMap (G.incl v) (H.incl v) (1 ⊗ₜ b) = 1 ⊗ₜ H.incl v b
    rw [prodMap, Bialgebra.TensorProduct.map_tmul, map_one]

/-- **Tate modules of products**: `T_p(G × H)(S) ≃* T_p G(S) × T_p H(S)`. -/
def prodTateEquiv (S : Type u) [CommRing S] [Algebra R S] :
    (G.prod H).TateModule S ≃* G.TateModule S × H.TateModule S where
  toFun x := ((fst G H).mapTate S x, (snd G H).mapTate S x)
  invFun y := ⟨fun v => ((G.G v).prodPointsEquiv (H.G v) S).symm (y.1.1 v, y.2.1 v), fun v => by
    apply ((G.G (v + 1)).prodPointsEquiv (H.G (v + 1)) S).injective
    change (G.G (v + 1)).prodPointsEquiv (H.G (v + 1)) S
        ((prodMap (G.incl v) (H.incl v)).mapPoints S _) = _
    rw [prodPointsEquiv_mapPoints, MulEquiv.apply_symm_apply]
    change _ = (G.G (v + 1)).prodPointsEquiv (H.G (v + 1)) S
      ((((G.G (v + 1)).prodPointsEquiv (H.G (v + 1)) S).symm (y.1.1 (v + 1), y.2.1 (v + 1))) ^ p)
    rw [map_pow, MulEquiv.apply_symm_apply, Prod.pow_mk, ← y.1.2 v, ← y.2.2 v]⟩
  left_inv x := Subtype.ext (funext fun v => by
    change ((G.G v).prodPointsEquiv (H.G v) S).symm
      ((((G.G v).prodPointsEquiv (H.G v) S) (x.1 v)).1,
        (((G.G v).prodPointsEquiv (H.G v) S) (x.1 v)).2) = x.1 v
    rw [Prod.mk.eta, MulEquiv.symm_apply_apply])
  right_inv y := Prod.ext (Subtype.ext (funext fun v => by
      change (((G.G v).prodPointsEquiv (H.G v) S)
        (((G.G v).prodPointsEquiv (H.G v) S).symm (y.1.1 v, y.2.1 v))).1 = y.1.1 v
      rw [MulEquiv.apply_symm_apply]))
    (Subtype.ext (funext fun v => by
      change (((G.G v).prodPointsEquiv (H.G v) S)
        (((G.G v).prodPointsEquiv (H.G v) S).symm (y.1.1 v, y.2.1 v))).2 = y.2.1 v
      rw [MulEquiv.apply_symm_apply]))
  map_mul' x y := Prod.ext (map_mul _ x y) (map_mul _ x y)

theorem prodTateEquiv_apply (S : Type u) [CommRing S] [Algebra R S]
    (x : (G.prod H).TateModule S) :
    G.prodTateEquiv H S x = ((fst G H).mapTate S x, (snd G H).mapTate S x) := rfl

end PDivGroup

end PadicHodge
