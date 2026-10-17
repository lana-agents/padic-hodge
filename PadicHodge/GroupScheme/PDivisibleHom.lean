/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.PDivisible

/-!
# Morphisms of `p`-divisible groups, the quotient maps `G_{v+1} → G_v`, Tate modules

For a `p`-divisible group `G = (G_v, i_v)` over `R`:

* `PDivGroup.pow_eq_one`: `G_v` is killed by `p^v` (on points);
* `PDivGroup.quot v : G_{v+1} → G_v`, the homomorphism with `i_v ∘ quot_v = [p]` on `G_{v+1}`
  (`incl_quot`), i.e. `[p] : G_{v+1} → G_{v+1}` factors through the closed immersion `i_v`
  ([BC, Def. 7.2.1]; [Stix, §11.2.2] calls these `j`). Construction (Yoneda): the universal
  point `id ∈ G_{v+1}(A_{v+1})` satisfies `(id^p)^{p^v} = 1`, so `id^p = i_v(x)` for a unique
  `x ∈ G_v(A_{v+1})`, an algebra map `A_v → A_{v+1}`; it is a bialgebra map because
  `y ↦ y ∘ x` is the group homomorphism `y ↦ i_v⁻¹(y^p)` on points, tested on the two
  projections `A_{v+1} → A_{v+1} ⊗ A_{v+1}`;
* `TateModule.val_eq_quot`: a point of the Tate module is a compatible system for the maps
  `quot_v` (`x_v = quot_v(x_{v+1})`);
* `PDivGroup.Hom G H`: families `f_v : G_v → H_v` compatible with the `i_v`; identity and
  composition; the induced homomorphism of Tate modules `Hom.mapTate`, functorial
  (`mapTate_id`, `mapTate_comp`); compatibility with the quotient maps (`Hom.quot_comm`).
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

/-- Postcomposition with an algebra map `S → S'`, a group homomorphism `G(S) → G(S')`. -/
def postComp (G : FFGroupScheme R) {S S' : Type*} [CommRing S] [Algebra R S] [CommRing S']
    [Algebra R S'] (φ : S →ₐ[R] S') : G.points S →* G.points S' where
  toFun f := toConv (φ.comp (ofConv f))
  map_one' := by
    apply WithConv.ofConv_injective
    ext a
    simp [AlgHom.convOne_apply]
  map_mul' f g := by
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib φ f g

/-- The universal point `id ∈ G(A)`. -/
def univPt (G : FFGroupScheme R) : G.points G.A := toConv (AlgHom.id R G.A)

/-- In `G(A ⊗ A)`, the product of the two projections is the comultiplication. -/
theorem inl_mul_inr (G : FFGroupScheme R) :
    toConv (Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] G.A) *
      toConv (Algebra.TensorProduct.includeRight : G.A →ₐ[R] G.A ⊗[R] G.A) =
      (toConv (Bialgebra.comulAlgHom R G.A) : G.points (G.A ⊗[R] G.A)) := by
  rw [AlgHom.convMul_def]
  congr 1
  have : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] G.A)
      (Algebra.TensorProduct.includeRight : G.A →ₐ[R] G.A ⊗[R] G.A)) = AlgHom.id R _ :=
    Algebra.TensorProduct.ext' fun a b => by simp
  rw [← AlgHom.comp_assoc, this, AlgHom.id_comp]

/-- An algebra map `f : O(H) → O(G)` inducing group homomorphisms on all points is a
homomorphism of group schemes (Yoneda). -/
def homOfPoints {G H : FFGroupScheme R} (f : H.A →ₐ[R] G.A)
    (hf : ∀ (S : Type u) [CommRing S] [Algebra R S] (φ ψ : G.points S),
      toConv ((ofConv (φ * ψ)).comp f) = toConv ((ofConv φ).comp f) * toConv ((ofConv ψ).comp f))
    (h1 : toConv ((ofConv (1 : G.points R)).comp f) = (1 : H.points R)) : Hom G H :=
  BialgHom.ofAlgHom f
    (by
      have h := congrArg ofConv h1
      simp only [AlgHom.convOne_def] at h
      ext a
      have := congrArg (fun F : H.A →ₐ[R] R => F a) h
      simpa using this)
    (by
      have hm : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map
          ((Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] G.A).comp f)
          ((Algebra.TensorProduct.includeRight : G.A →ₐ[R] G.A ⊗[R] G.A).comp f)) =
          Algebra.TensorProduct.map f f :=
        Algebra.TensorProduct.ext' fun a b => by simp
      have h := hf (G.A ⊗[R] G.A) (toConv Algebra.TensorProduct.includeLeft)
        (toConv Algebra.TensorProduct.includeRight)
      rw [inl_mul_inr, AlgHom.convMul_def] at h
      have h' := congrArg ofConv h
      refine Eq.trans ?_ h'.symm
      change _ = ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map
          ((Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] G.A).comp f)
          ((Algebra.TensorProduct.includeRight : G.A →ₐ[R] G.A ⊗[R] G.A).comp f))).comp
        (Bialgebra.comulAlgHom R H.A)
      rw [hm])

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] {p : ℕ} (G : PDivGroup R p)

/-- `G_v` is killed by `p^v`. -/
theorem pow_eq_one (v : ℕ) (S : Type u) [CommRing S] [Algebra R S] (x : (G.G v).points S) :
    x ^ (p ^ v) = 1 := by
  have h := (G.range_eq v S ((G.incl v).mapPoints S x)).mp ⟨x, rfl⟩
  rw [← map_pow] at h
  apply G.mapPoints_injective v S
  rw [h, map_one]

theorem exists_incl_eq_pow (v : ℕ) (S : Type u) [CommRing S] [Algebra R S]
    (y : (G.G (v + 1)).points S) : ∃ x, (G.incl v).mapPoints S x = y ^ p := by
  refine (G.range_eq v S (y ^ p)).mpr ?_
  rw [← pow_mul, ← pow_succ']
  exact G.pow_eq_one (v + 1) S y

/-- The algebra map `A_v → A_{v+1}` underlying `quot_v`. -/
def quotAlg (v : ℕ) : (G.G v).A →ₐ[R] (G.G (v + 1)).A :=
  ofConv (G.exists_incl_eq_pow v _ (G.G (v + 1)).univPt).choose

theorem incl_quotAlg (v : ℕ) :
    (G.incl v).mapPoints _ (toConv (G.quotAlg v)) = (G.G (v + 1)).univPt ^ p :=
  (G.exists_incl_eq_pow v _ (G.G (v + 1)).univPt).choose_spec

/-- `i_v(y ∘ quot_v) = y^p` for every point `y` of `G_{v+1}`. -/
theorem incl_comp_quotAlg (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (y : (G.G (v + 1)).points S) :
    (G.incl v).mapPoints S (toConv ((ofConv y).comp (G.quotAlg v))) = y ^ p := by
  have h : (G.G (v + 1)).postComp (ofConv y)
      ((G.incl v).mapPoints _ (toConv (G.quotAlg v))) =
      (G.G (v + 1)).postComp (ofConv y) ((G.G (v + 1)).univPt ^ p) := by
    rw [G.incl_quotAlg v]
  rw [map_pow] at h
  exact h

theorem quotAlg_mul (v : ℕ) (S : Type u) [CommRing S] [Algebra R S]
    (y y' : (G.G (v + 1)).points S) :
    toConv ((ofConv (y * y')).comp (G.quotAlg v)) =
      toConv ((ofConv y).comp (G.quotAlg v)) * toConv ((ofConv y').comp (G.quotAlg v)) := by
  apply G.mapPoints_injective v S
  rw [map_mul, G.incl_comp_quotAlg, G.incl_comp_quotAlg, G.incl_comp_quotAlg, mul_pow]

theorem quotAlg_one (v : ℕ) :
    toConv ((ofConv (1 : (G.G (v + 1)).points R)).comp (G.quotAlg v)) = 1 := by
  apply G.mapPoints_injective v R
  rw [G.incl_comp_quotAlg, one_pow, map_one]

/-- **The quotient map** `quot_v : G_{v+1} → G_v` with `i_v ∘ quot_v = [p]`. -/
def quot (v : ℕ) : FFGroupScheme.Hom (G.G (v + 1)) (G.G v) :=
  homOfPoints (G.quotAlg v) (G.quotAlg_mul v) (G.quotAlg_one v)

theorem quot_apply (v : ℕ) (a : (G.G v).A) : G.quot v a = G.quotAlg v a := rfl

/-- `i_v ∘ quot_v = [p]` on points. -/
theorem incl_quot (v : ℕ) {S : Type*} [CommRing S] [Algebra R S] (y : (G.G (v + 1)).points S) :
    (G.incl v).mapPoints S ((G.quot v).mapPoints S y) = y ^ p :=
  G.incl_comp_quotAlg v y

/-- A point of the Tate module is a compatible system for the quotient maps. -/
theorem TateModule.val_eq_quot {S : Type u} [CommRing S] [Algebra R S] (x : G.TateModule S)
    (v : ℕ) : x.1 v = (G.quot v).mapPoints S (x.1 (v + 1)) := by
  apply G.mapPoints_injective v S
  rw [G.incl_quot]
  exact x.2 v

/-! ### Morphisms -/

/-- A homomorphism of `p`-divisible groups: homomorphisms `f_v : G_v → H_v` compatible with the
inclusions `i_v`. -/
structure Hom (G H : PDivGroup R p) where
  /-- the levels -/
  f : ∀ v, FFGroupScheme.Hom (G.G v) (H.G v)
  /-- compatibility with the inclusions: `i_v^H ∘ f_v = f_{v+1} ∘ i_v^G` -/
  comm : ∀ v, BialgHom.comp (G.incl v) (f (v + 1)) = BialgHom.comp (f v) (H.incl v)

namespace Hom

variable {G} {H K : PDivGroup R p}

theorem incl_mapPoints (φ : Hom G H) (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (x : (G.G v).points S) :
    (H.incl v).mapPoints S ((φ.f v).mapPoints S x) =
      (φ.f (v + 1)).mapPoints S ((G.incl v).mapPoints S x) := by
  apply WithConv.ofConv_injective
  change (ofConv x).comp ((φ.f v : (H.G v).A →ₐ[R] (G.G v).A).comp
      (H.incl v : (H.G (v + 1)).A →ₐ[R] (H.G v).A)) =
    (ofConv x).comp ((G.incl v : (G.G (v + 1)).A →ₐ[R] (G.G v).A).comp
      (φ.f (v + 1) : (H.G (v + 1)).A →ₐ[R] (G.G (v + 1)).A))
  congr 1
  have := congrArg (fun g : (H.G (v + 1)).A →ₐc[R] (G.G v).A =>
    (g : (H.G (v + 1)).A →ₐ[R] (G.G v).A)) (φ.comm v)
  exact this.symm

/-- The identity. -/
protected def id (G : PDivGroup R p) : Hom G G where
  f _ := BialgHom.id R _
  comm _ := by ext; rfl

/-- Composition. -/
def comp (ψ : Hom H K) (φ : Hom G H) : Hom G K where
  f v := (φ.f v).comp (ψ.f v)
  comm v := by
    rw [← BialgHom.comp_assoc, φ.comm v, BialgHom.comp_assoc, ψ.comm v, BialgHom.comp_assoc]

/-- The induced homomorphism of Tate modules `T_p G(S) → T_p H(S)`. -/
def mapTate (φ : Hom G H) (S : Type u) [CommRing S] [Algebra R S] :
    G.TateModule S →* H.TateModule S where
  toFun x := ⟨fun v => (φ.f v).mapPoints S (x.1 v), fun v => by
    rw [φ.incl_mapPoints, x.2 v, map_pow]⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ => map_mul _ _ _)

theorem mapTate_apply (φ : Hom G H) (S : Type u) [CommRing S] [Algebra R S] (x : G.TateModule S)
    (v : ℕ) : (φ.mapTate S x).1 v = (φ.f v).mapPoints S (x.1 v) := rfl

theorem mapTate_id (S : Type u) [CommRing S] [Algebra R S] (x : G.TateModule S) :
    (Hom.id G).mapTate S x = x := rfl

theorem mapTate_comp (ψ : Hom H K) (φ : Hom G H) (S : Type u) [CommRing S] [Algebra R S]
    (x : G.TateModule S) : (ψ.comp φ).mapTate S x = ψ.mapTate S (φ.mapTate S x) := rfl

/-- Morphisms commute with the quotient maps: `quot_v^H ∘ f_{v+1} = f_v ∘ quot_v^G`. -/
theorem quot_comm (φ : Hom G H) (v : ℕ) {S : Type*} [CommRing S] [Algebra R S]
    (y : (G.G (v + 1)).points S) :
    (H.quot v).mapPoints S ((φ.f (v + 1)).mapPoints S y) =
      (φ.f v).mapPoints S ((G.quot v).mapPoints S y) := by
  -- check after the universal case: both sides are `i_v^H`-preimages of `f_{v+1}(y)^p`
  have key : ∀ (T : Type u) [CommRing T] [Algebra R T] (z : (G.G (v + 1)).points T),
      (H.quot v).mapPoints T ((φ.f (v + 1)).mapPoints T z) =
        (φ.f v).mapPoints T ((G.quot v).mapPoints T z) := by
    intro T _ _ z
    apply H.mapPoints_injective v T
    rw [H.incl_quot, φ.incl_mapPoints, G.incl_quot, map_pow]
  have h : (H.G v).postComp (ofConv y)
      ((H.quot v).mapPoints _ ((φ.f (v + 1)).mapPoints _ (G.G (v + 1)).univPt)) =
      (H.G v).postComp (ofConv y)
        ((φ.f v).mapPoints _ ((G.quot v).mapPoints _ (G.G (v + 1)).univPt)) := by
    rw [key]
  exact h

end Hom

end PDivGroup

end PadicHodge
