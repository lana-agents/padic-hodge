/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.QuotientMap
import PadicHodge.GroupScheme.EtalePoints

/-!
# Quotients of finite flat group schemes: universal points, lifts, points over a field

Complements to [Hong, Thm. 1.1.9] (`QuotientGroup.lean`, `QuotientMap.lean`) used in
[Hong, proof of Prop. 3.5.3]:

* `Hom.ext_univPt`: homomorphisms agreeing on the universal point are equal;
  `postComp_univPt`: every point is a push-forward of the universal point;
* `KilledBy`: `G` is killed by `n` (`univPt^n = 1`); then so are all points
  (`KilledBy.pow_eq_one`), quotients (`KilledBy.quotient`), base changes; over a separably
  closed field `Ω` with `n ≠ 0` in `Ω`, `G_Ω` is étale and `#G(Ω) = |G|`
  (`KilledBy.card_points`);
* `Hom.quotientLift`: a homomorphism `G → X` trivial on `H` factors through `G/H`;
* `Hom.surjective_quotientMap_of_comp`: `H/K → G/K` is a closed immersion for any
  presentation of `K → G` as `K → H → G`;
* `Hom.quotientHom_mapPoints_surjective`: `G(Ω) → (G/H)(Ω)` is onto when the three groups of
  points have the expected orders.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

/-! ### Universal points -/

theorem postComp_univPt (G : FFGroupScheme R) {S : Type*} [CommRing S] [Algebra R S]
    (x : G.points S) : G.postComp (ofConv x) G.univPt = x := rfl

theorem Hom.mapPoints_postComp {G H : FFGroupScheme R} (f : Hom G H) {S S' : Type*} [CommRing S]
    [Algebra R S] [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (x : G.points S) :
    f.mapPoints S' (G.postComp φ x) = H.postComp φ (f.mapPoints S x) := rfl

/-- **Homomorphisms agreeing on the universal point are equal.** -/
theorem Hom.ext_univPt {G H : FFGroupScheme R} {f g : Hom G H}
    (h : f.mapPoints G.A G.univPt = g.mapPoints G.A G.univPt) : f = g :=
  BialgHom.ext fun a => congrArg (fun z : H.points G.A => ofConv z a) h

/-- Homomorphisms agreeing on all points are equal. -/
theorem Hom.ext_points {G H : FFGroupScheme R} {f g : Hom G H}
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] (x : G.points S),
      f.mapPoints S x = g.mapPoints S x) : f = g :=
  Hom.ext_univPt (h G.A G.univPt)

theorem postComp_injective (G : FFGroupScheme R) {S S' : Type*} [CommRing S] [Algebra R S]
    [CommRing S'] [Algebra R S'] {φ : S →ₐ[R] S'} (hφ : Function.Injective φ) :
    Function.Injective (G.postComp φ) := by
  intro x y hxy
  apply WithConv.ofConv_injective
  ext a
  exact hφ (congrArg (fun z : G.points S' => ofConv z a) hxy)

/-- A homomorphism with bijective algebra map is bijective on points. -/
theorem Hom.mapPoints_bijective {G H : FFGroupScheme R} (f : Hom G H)
    (hf : Function.Bijective f) (S : Type*) [CommRing S] [Algebra R S] :
    Function.Bijective (f.mapPoints S) := by
  let e : H.A ≃ₐ[R] G.A := AlgEquiv.ofBijective (f : H.A →ₐ[R] G.A) hf
  refine ⟨fun x y hxy => ?_, fun y => ⟨toConv ((ofConv y).comp (e.symm : G.A →ₐ[R] H.A)), ?_⟩⟩
  · apply WithConv.ofConv_injective
    ext a
    obtain ⟨b, rfl⟩ := hf.2 a
    exact congrArg (fun z : H.points S => ofConv z b) hxy
  · apply WithConv.ofConv_injective
    ext b
    change ofConv y (e.symm (e b)) = ofConv y b
    rw [AlgEquiv.symm_apply_apply]

/-! ### Group schemes killed by `n` -/

/-- `G` is killed by `n`: `univPt^n = 1`. -/
def KilledBy (G : FFGroupScheme R) (n : ℕ) : Prop := G.univPt ^ n = 1

namespace KilledBy

variable {G : FFGroupScheme R} {n : ℕ}

theorem pow_eq_one (hG : G.KilledBy n) {S : Type*} [CommRing S] [Algebra R S]
    (x : G.points S) : x ^ n = 1 := by
  have := congrArg (G.postComp (ofConv x)) hG
  rwa [map_pow, map_one] at this

theorem of_pow_eq_one (h : ∀ (S : Type u) [CommRing S] [Algebra R S] (x : G.points S),
    x ^ n = 1) : G.KilledBy n := h G.A G.univPt

/-- A closed subgroup of a group killed by `n` is killed by `n`. -/
theorem of_injective {H : FFGroupScheme R} (f : Hom H G)
    (hf : ∀ (S : Type u) [CommRing S] [Algebra R S], Function.Injective (f.mapPoints S))
    (hG : G.KilledBy n) : H.KilledBy n :=
  of_pow_eq_one fun S _ _ x => hf S (by rw [map_pow, map_one, hG.pow_eq_one])

/-- **A quotient of a group killed by `n` is killed by `n`.** -/
theorem quotient {H : FFGroupScheme R} (i : Hom H G) [IsDomain R] [IsPrincipalIdealRing R]
    (hG : G.KilledBy n) : i.quotient.KilledBy n := by
  apply i.quotient.postComp_injective (φ := (i.quotientHom : i.quotient.A →ₐ[R] G.A))
    (Hom.quotientHom_injective i)
  rw [map_pow, map_one]
  change (i.quotientHom.mapPoints G.A G.univPt) ^ n = 1
  rw [← map_pow, hG, map_one]

theorem baseChange (S : Type u) [CommRing S] [Algebra R S] (hG : G.KilledBy n) :
    (G.baseChange S).KilledBy n := by
  apply (G.baseChangePointsEquiv (S := S) (S ⊗[R] G.A)).injective
  rw [map_pow, map_one, hG.pow_eq_one]

/-- Over a separably closed field `Ω` with `n ≠ 0` in `Ω`, a group killed by `n` has `|G|`
points (`G_Ω` is étale). -/
theorem isEtale_baseChange (Ω : Type u) [Field Ω] [Algebra R Ω] (hG : G.KilledBy n)
    (hn : (n : Ω) ≠ 0) : (G.baseChange Ω).IsEtale :=
  (G.baseChange Ω).isEtale_of_univPt_pow_eq_one (isUnit_iff_ne_zero.mpr hn) (hG.baseChange Ω)

theorem card_points [Nontrivial R] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
    (hG : G.KilledBy n) (hn : (n : Ω) ≠ 0) : Nat.card (G.points Ω) = G.order := by
  rw [← Nat.card_congr (G.baseChangePointsEquiv (S := Ω) Ω).toEquiv,
    card_points_of_isEtale _ (hG.isEtale_baseChange Ω hn), order_baseChange]

end KilledBy

namespace Hom

variable {G H X : FFGroupScheme R}

/-! ### Lifting along `G → G/H` -/

/-- A homomorphism `f : G → X` trivial on `H` maps `O(X)` into the invariants. -/
theorem mem_invariants_of_trivial (i : Hom H G) (f : Hom G X)
    (h : ∀ x, i (f x) = algebraMap R H.A (counit (R := R) x)) (x : X.A) :
    f x ∈ i.invariants := by
  rw [mem_invariants, coact_apply]
  have hf : comul (R := R) (f x) = TensorProduct.map (f : X.A →ₗ[R] G.A)
      (f : X.A →ₗ[R] G.A) (comul x) :=
    (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) x).symm
  have key : ∀ w : X.A ⊗[R] X.A, TensorProduct.map LinearMap.id (i : G.A →ₗ[R] H.A)
      (TensorProduct.map (f : X.A →ₗ[R] G.A) (f : X.A →ₗ[R] G.A) w) =
      TensorProduct.map (f : X.A →ₗ[R] G.A) (Algebra.linearMap R H.A)
        ((counit (R := R) (A := X.A)).lTensor X.A w) := by
    intro w
    induction w with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul y z => simp [h]
  rw [hf, key, Coalgebra.lTensor_counit_comul]
  simp

theorem incl2_map_of_mem {i : Hom H G} [IsDomain R] [IsPrincipalIdealRing R]
    (φ : X.A →ₐ[R] i.invariants) (f : X.A →ₐ[R] G.A) (hφ : ∀ b, (φ b : G.A) = f b)
    (w : X.A ⊗[R] X.A) :
    i.incl2 (Algebra.TensorProduct.map φ φ w) = Algebra.TensorProduct.map f f w := by
  induction w with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [hφ]

/-- **The homomorphism `G/H → X` induced by `f : G → X` trivial on `H`.** -/
def quotientLift [IsDomain R] [IsPrincipalIdealRing R] (i : Hom H G) (f : Hom G X)
    (h : ∀ x, i (f x) = algebraMap R H.A (counit (R := R) x)) : Hom i.quotient X :=
  let φ : X.A →ₐ[R] i.invariants :=
    (f : X.A →ₐ[R] G.A).codRestrict i.invariants (mem_invariants_of_trivial i f h)
  BialgHom.ofAlgHom (A := X.A) (B := i.invariants) φ
    (AlgHom.ext fun b => by
      change counit (R := R) (f b) = counit (R := R) b
      exact CoalgHomClass.counit_comp_apply f _)
    (AlgHom.ext fun b => i.incl2_injective (by
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
      rw [incl2_map_of_mem φ (f : X.A →ₐ[R] G.A) (fun _ => rfl), comul_Q, i.incl2_comulQ]
      exact (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) b)))

theorem quotientLift_apply [IsDomain R] [IsPrincipalIdealRing R] (i : Hom H G) (f : Hom G X)
    (h : ∀ x, i (f x) = algebraMap R H.A (counit (R := R) x)) (b : X.A) :
    Subtype.val (show i.invariants from quotientLift i f h b) = f b := rfl

/-- `G → G/H → X` is `f`. -/
theorem quotientLift_mapPoints [IsDomain R] [IsPrincipalIdealRing R] (i : Hom H G) (f : Hom G X)
    (h : ∀ x, i (f x) = algebraMap R H.A (counit (R := R) x)) {S : Type*} [CommRing S]
    [Algebra R S] (z : G.points S) :
    (quotientLift i f h).mapPoints S (i.quotientHom.mapPoints S z) = f.mapPoints S z := rfl

/-- The triviality condition of `quotientLift` from points: `f ∘ i = 1` on all points. -/
theorem trivial_of_mapPoints (i : Hom H G) (f : Hom G X)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] (z : H.points S),
      f.mapPoints S (i.mapPoints S z) = 1) (x : X.A) :
    i (f x) = algebraMap R H.A (counit (R := R) x) :=
  (mapPoints_eq_one_iff f (i.mapPoints H.A H.univPt)).mp (h H.A H.univPt) x

/-- On points, `G → G/H` followed by `quotientMap` is `f` followed by `G' → G'/H'`. -/
theorem quotientMap_mapPoints [IsDomain R] [IsPrincipalIdealRing R] {G' H' : FFGroupScheme R}
    (i : Hom H G) (i' : Hom H' G') (f : Hom G G') (g : Hom H H')
    (h : ∀ a, i (f a) = g (i' a)) {S : Type*} [CommRing S] [Algebra R S] (z : G.points S) :
    (quotientMap i i' f g h).mapPoints S (i.quotientHom.mapPoints S z) =
      i'.quotientHom.mapPoints S (f.mapPoints S z) := rfl

/-- Homomorphisms out of `G/H` agreeing after `G → G/H` are equal. -/
theorem ext_quotient [IsDomain R] [IsPrincipalIdealRing R] (i : Hom H G) {f g : Hom i.quotient X}
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] (z : G.points S),
      f.mapPoints S (i.quotientHom.mapPoints S z) = g.mapPoints S (i.quotientHom.mapPoints S z)) :
    f = g :=
  BialgHom.ext fun a => Hom.quotientHom_injective i
    (congrArg (fun z : X.points G.A => ofConv z a) (h G.A G.univPt))

/-! ### `H/K → G/K` for `K → G` factoring through `H` -/

theorem surjective_quotientMap_of_comp [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    {K : FFGroupScheme R} {i : Hom H G} {k : Hom K H} {k' : Hom K G}
    (hi : Function.Surjective i) (hk : Function.Surjective k)
    (h : ∀ a, k (i a) = (BialgHom.id R K.A) (k' a)) :
    Function.Surjective (quotientMap k k' i (BialgHom.id R K.A) h) := by
  have e : k' = k.comp i := BialgHom.ext fun a => (h a).symm
  subst e
  exact surjective_subQuot hi hk

/-! ### Points of the quotient over a field -/

/-- **`G(Ω) → (G/H)(Ω)` is onto** if `#G(Ω) = |G|`, `#H(Ω) = |H|`, `#(G/H)(Ω) = |G/H|`. -/
theorem quotientHom_mapPoints_surjective [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    {i : Hom H G} (hi : Function.Surjective i) (Ω : Type*) [CommRing Ω] [Algebra R Ω]
    (hG : Nat.card (G.points Ω) = G.order) (hH : Nat.card (H.points Ω) = H.order)
    (hQ : Nat.card (i.quotient.points Ω) = i.quotient.order) (h0 : G.order ≠ 0) :
    Function.Surjective (i.quotientHom.mapPoints Ω) := by
  set φ := i.quotientHom.mapPoints Ω
  have hker : φ.ker = (i.mapPoints Ω).range := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    exact mapPoints_quotientHom_eq_one_iff hi g
  have hcard_ker : Nat.card φ.ker = H.order := by
    rw [hker, ← hH]
    exact Nat.card_congr (MonoidHom.ofInjective
      (mapPoints_injective_of_surjective hi (T := Ω))).toEquiv.symm
  have h1 := φ.ker.card_mul_index
  rw [Subgroup.index_ker φ, hcard_ker, hG, order_eq_mul hi] at h1
  have hH0 : H.order ≠ 0 := by
    intro hH0
    rw [order_eq_mul hi, hH0, zero_mul] at h0
    exact h0 rfl
  have h2 : Nat.card φ.range = Nat.card (i.quotient.points Ω) := by
    rw [hQ]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hH0) h1
  have : Finite (i.quotient.points Ω) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hQ]
    intro hQ0
    rw [order_eq_mul hi, hQ0, mul_zero] at h0
    exact h0 rfl
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ h2

end Hom

end FFGroupScheme

end PadicHodge
