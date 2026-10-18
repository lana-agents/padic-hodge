/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.EtaleQuotientOrder
import PadicHodge.GroupScheme.PDivisiblePoints
import PadicHodge.GroupScheme.SerreTateEss
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The connected part `G⁰ = (G_v⁰)_v` of a `p`-divisible group

Let `R` be a complete local principal ideal domain (e.g. `ℤ_p`, `O_K`) and `G = (G_v, i_v)` a
`p`-divisible group of height `h` over `R`. We show that the connected components `G_v⁰` form a
`p`-divisible group `G⁰` (`PDivGroup.connPart`), with the closed immersion `G⁰ → G`
(`PDivGroup.connPartHom`). This is the first half of the connected–étale sequence
`0 → G⁰ → G → G^{et} → 0` of [Hong, Prop. 2.1.10].

## Functoriality of the connected component

For a homomorphism `f : G → H` of finite flat group schemes over a complete local ring, the
idempotents of the identity components satisfy `e_G · f^*(e_H) = e_G` (`idemConn_mul_map`), so
`f^*` maps `(1 - e_H)` into `(1 - e_G)` and induces `f⁰ : G⁰ → H⁰`
(`FFGroupScheme.connectedComponentMap`); if `f^*` is surjective then `f^*(e_H) = e_G`
(`map_idemConn_of_surjective`, uniqueness of point idempotents).

## The transition maps (`connIncl`)

`i_v⁰ : G_v⁰ → G_{v+1}⁰` is a closed immersion, and a point `y ∈ G_{v+1}⁰(S)` with `p^v y = 0`
comes from `G_v(S)` (as `G` is `p`-divisible) by a point killing `i_v^*(1 - e_{v+1}) = 1 - e_v`,
i.e. from `G_v⁰(S)` (`connIncl_range_eq`).

## The orders (standard argument, written up here)

Write `c_v = |G_v⁰|` and `n_v = #G_v(Ω)` for an algebraically closed field `Ω` over the residue
field of `R`.

* `|G| = |G⁰| · #G(Ω)` (`order_eq_mul_card_points`): `|G| = |G⁰| · |G^{et}|`
  (`order_eq_mul`), `G(Ω) → G^{et}(Ω)` is injective (its kernel is `G⁰(Ω) = 1`) and surjective
  (`A` is free over `A^{et}`, so `Ω ⊗_{A^{et}} A ≠ 0` has an `Ω`-point), and the étale `G^{et}`
  has `|G^{et}|` points over `Ω` (`card_points_of_isEtale`).
* `n_{v+1} ≤ n_1 n_v` (`card_ker_mul_card_range_quot`).
* `c_{v+1} ≤ c_1 c_v`: Nakayama (`order_le_mul_of_surjective`) for
  `[p^v]⁰ : G_{v+1}⁰ → G_1⁰` (`quotOne`), whose kernel is a closed subscheme of `G_v⁰`.
* Since `c_v n_v = p^{hv}`, both inequalities are equalities, so `c_v = c_1^v`, and `c_1 ∣ p^h`
  is a power `p^{h⁰}` (`exists_order_connectedComponent`).

## Main definitions and results

* `FFGroupScheme.connectedComponentMap`, `FFGroupScheme.order_le_mul_of_surjective`,
  `FFGroupScheme.order_eq_mul_card_points`;
* `PDivGroup.connPart G : PDivGroup R p` with layers `(G.G v).connectedComponent`, all connected
  (`isConnected_connPart`), and `PDivGroup.connPartHom : Hom G.connPart G`, a closed immersion
  in every layer (`connPartHom_surjective`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 2.1.10.
-/

noncomputable section

open Coalgebra HopfAlgebra IsLocalRing TensorProduct WithConv Module

namespace PadicHodge

universe u

namespace FFGroupScheme

/-! ### Functoriality of the connected component -/

section Functor

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]

theorem counitAlgHom_map_idemConn {G H : FFGroupScheme R} (f : Hom G H) :
    Bialgebra.counitAlgHom R G.A (f H.idemConn) = 1 :=
  (CoalgHomClass.counit_comp_apply f H.idemConn).trans H.counit_idemConn

/-- `e_G · f^*(e_H) = e_G`: the identity component of `G` maps into that of `H`. -/
theorem idemConn_mul_map {G H : FFGroupScheme R} (f : Hom G H) :
    G.idemConn * f H.idemConn = G.idemConn := by
  have he := G.isPointIdempotent_idemConn
  have hf : IsIdempotentElem (f H.idemConn) :=
    H.isPointIdempotent_idemConn.isIdempotentElem.map f
  have hg : IsIdempotentElem (G.idemConn * (1 - f H.idemConn)) :=
    he.isIdempotentElem.mul hf.one_sub
  have h0 := he.eq_zero_of_mul_eq hg (by rw [mul_right_comm, he.isIdempotentElem.eq]) (by
    rw [map_mul, map_sub, map_one, he.apply_eq_one, counitAlgHom_map_idemConn, sub_self,
      mul_zero])
  rw [mul_sub, mul_one, sub_eq_zero] at h0
  exact h0.symm

theorem map_one_sub_idemConn_mem {G H : FFGroupScheme R} (f : Hom G H) :
    f (1 - H.idemConn) ∈ G.connIdeal := by
  refine Ideal.mem_span_singleton'.mpr ⟨f (1 - H.idemConn), ?_⟩
  have := idemConn_mul_map f
  rw [map_sub, map_one]
  linear_combination this

theorem connIdeal_le_comap {G H : FFGroupScheme R} (f : Hom G H) :
    H.connIdeal ≤ G.connIdeal.comap (f : H.A →ₐ[R] G.A) :=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (map_one_sub_idemConn_mem f))

/-- The homomorphism `f⁰ : G⁰ → H⁰` induced by `f : G → H`. -/
def connectedComponentMap {G H : FFGroupScheme R} (f : Hom G H) :
    Hom G.connectedComponent H.connectedComponent :=
  (BialgHom.ofAlgHom (Ideal.quotientMapₐ G.connIdeal (f : H.A →ₐ[R] G.A) (connIdeal_le_comap f))
    (Ideal.Quotient.algHom_ext R (AlgHom.ext fun a => by
      change counit (R := R) (Ideal.Quotient.mk G.connIdeal (f a)) =
        counit (R := R) (Ideal.Quotient.mk H.connIdeal a)
      exact CoalgHomClass.counit_comp_apply f a))
    (Ideal.Quotient.algHom_ext R (AlgHom.ext fun a => by
      change Algebra.TensorProduct.map (Ideal.quotientMapₐ G.connIdeal (f : H.A →ₐ[R] G.A)
          (connIdeal_le_comap f)) (Ideal.quotientMapₐ G.connIdeal (f : H.A →ₐ[R] G.A)
          (connIdeal_le_comap f)) (comul (R := R) (Ideal.Quotient.mk H.connIdeal a)) =
        comul (R := R) (Ideal.Quotient.mk G.connIdeal (f a))
      rw [Bialgebra.Quotient.comul_mk, Bialgebra.Quotient.comul_mk,
        ← CoalgHomClass.map_comp_comul_apply f a]
      induction comul (R := R) a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add, hx, hy])) :
    (H.A ⧸ H.connIdeal) →ₐc[R] (G.A ⧸ G.connIdeal))

theorem connectedComponentMap_mk {G H : FFGroupScheme R} (f : Hom G H) (a : H.A) :
    connectedComponentMap f (Ideal.Quotient.mk H.connIdeal a) =
      Ideal.Quotient.mk G.connIdeal (f a) := rfl

/-- `G⁰ → H⁰ → H` equals `G⁰ → G → H`. -/
theorem connectedComponentMap_comp {G H : FFGroupScheme R} (f : Hom G H) :
    (connectedComponentMap f).comp H.connectedComponentHom = G.connectedComponentHom.comp f :=
  DFunLike.ext _ _ fun _ => rfl

theorem mapPoints_connectedComponentMap {G H : FFGroupScheme R} (f : Hom G H) (S : Type*)
    [CommRing S] [Algebra R S] (y : G.connectedComponent.points S) :
    H.connectedComponentHom.mapPoints S ((connectedComponentMap f).mapPoints S y) =
      f.mapPoints S (G.connectedComponentHom.mapPoints S y) :=
  WithConv.ofConv_injective (AlgHom.ext fun _ => rfl)

/-- For surjective `f^*`, `f^*(e_H) = e_G`. -/
theorem map_idemConn_of_surjective {G H : FFGroupScheme R} (f : Hom G H)
    (hf : Function.Surjective f) : f H.idemConn = G.idemConn := by
  have hH := H.isPointIdempotent_idemConn
  refine IsPointIdempotent.unique (φ := Bialgebra.counitAlgHom R G.A) ⟨hH.isIdempotentElem.map f,
    counitAlgHom_map_idemConn f, fun b => ?_⟩ G.isPointIdempotent_idemConn
  obtain ⟨a, rfl⟩ := hf b
  have h := map_mem_radical_fiberIdeal (f : H.A →ₐ[R] G.A) (hH.mul_sub_mem a)
  have hc : Bialgebra.counitAlgHom R G.A (f a) = Bialgebra.counitAlgHom R H.A a :=
    CoalgHomClass.counit_comp_apply f a
  rw [hc]
  simp only [map_sub, map_mul, map_smul] at h
  exact h

/-- A point `x ∈ G(S)` with `x(1 - e₀) = 0` lies in `G⁰(S)`. -/
theorem exists_connectedComponentHom_mapPoints_eq (G : FFGroupScheme R) {S : Type*} [CommRing S]
    [Algebra R S] (x : G.points S) (hx : ofConv x (1 - G.idemConn) = 0) :
    ∃ y, G.connectedComponentHom.mapPoints S y = x := by
  refine ⟨toConv (Ideal.Quotient.liftₐ G.connIdeal (ofConv x) fun a ha => ?_), ?_⟩
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx, mul_zero]
  · exact WithConv.ofConv_injective (AlgHom.ext fun _ => rfl)

end Functor

/-! ### Nakayama -/

section Nakayama

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- **Nakayama**: let `f : G → H` be a homomorphism with `H` connected and let `Q` be a finite flat
group scheme with a surjection `O(Q) ↠ O(ker f) = O(G) / f^*(I_H)` (i.e. `ker f ⊆ Q` as closed
subschemes). Then `|G| ≤ |H| · |Q|`: lifts of generators of `O(ker f)` generate `O(G)` over
the local ring `O(H)`. -/
theorem order_le_mul_of_surjective {G H Q : FFGroupScheme R} (f : Hom G H) (hH : H.IsConnected)
    (ψ : Q.A →ₐ[R] G.A ⧸ (RingHom.ker (Bialgebra.counitAlgHom R H.A)).map
      (f : H.A →ₐ[R] G.A))
    (hψ : Function.Surjective ψ) : G.order ≤ H.order * Q.order := by
  classical
  haveI : IsLocalRing H.A := hH
  letI : Algebra H.A G.A := (f : H.A →ₐ[R] G.A).toRingHom.toAlgebra
  haveI : IsScalarTower R H.A G.A :=
    IsScalarTower.of_algebraMap_eq fun r => ((f : H.A →ₐ[R] G.A).commutes r).symm
  let J := RingHom.ker (Bialgebra.counitAlgHom R H.A)
  let I := J.map (f : H.A →ₐ[R] G.A)
  have hJ : J ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    refine IsLocalRing.le_maximalIdeal fun h => ?_
    have h1 : (1 : H.A) ∈ J := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI : Module.Finite H.A G.A := Module.Finite.of_restrictScalars_finite R H.A G.A
  let bQ := Module.finBasis R Q.A
  let s : Fin (finrank R Q.A) → G.A := fun j => (Ideal.Quotient.mk_surjective (ψ (bQ j))).choose
  have hs : ∀ j, Ideal.Quotient.mk I (s j) = ψ (bQ j) :=
    fun j => (Ideal.Quotient.mk_surjective (ψ (bQ j))).choose_spec
  have htop : (⊤ : Submodule H.A G.A) ≤ Submodule.span H.A (Set.range s) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJ ?_
    intro a _
    obtain ⟨q, hq⟩ := hψ (Ideal.Quotient.mk I a)
    let y : G.A := ∑ j, bQ.repr q j • s j
    have hy : y ∈ Submodule.span H.A (Set.range s) :=
      Submodule.sum_mem _ fun j _ =>
        Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hmk : Ideal.Quotient.mkₐ R I y = Ideal.Quotient.mkₐ R I a := by
      calc Ideal.Quotient.mkₐ R I y = ψ (∑ j, bQ.repr q j • bQ j) := by
            simp only [y, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk, hs]
        _ = Ideal.Quotient.mk I a := by rw [bQ.sum_repr]; exact hq
    have hay : a - y ∈ J • (⊤ : Submodule H.A G.A) := by
      rw [Ideal.smul_top_eq_map]
      exact Ideal.Quotient.eq.mp hmk.symm
    have := Submodule.add_mem_sup hy hay
    rwa [add_sub_cancel] at this
  let bH := Module.finBasis R H.A
  have hspan : Submodule.span R (Set.range fun q : Fin (finrank R H.A) × Fin (finrank R Q.A) =>
      bH q.1 • s q.2) = ⊤ := by
    rw [← Set.range_smul_range, Submodule.span_smul_of_span_eq_top bH.span_eq,
      eq_top_iff.mpr htop, Submodule.restrictScalars_top]
  have := finrank_range_le_card (R := R)
    (fun q : Fin (finrank R H.A) × Fin (finrank R Q.A) => bH q.1 • s q.2)
  unfold Set.finrank at this
  rw [hspan, finrank_top, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
  exact this

end Nakayama

/-! ### Points over an algebraically closed field: `|G| = |G⁰| · #G(Ω)` -/

section Points

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  (G : FFGroupScheme R) {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- `G⁰(Ω) = 1` if `m_R` maps to `0` in the field `Ω`. -/
theorem connectedComponent_points_eq_one (hΩ : ∀ r ∈ maximalIdeal R, algebraMap R Ω r = 0)
    (y : G.connectedComponent.points Ω) : y = 1 := by
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun a => ?_
  change ofConv y a = algebraMap R Ω (counit (R := R) a)
  have hb : Bialgebra.counitAlgHom R _
      (a - algebraMap R G.connectedComponent.A (counit (R := R) a)) = 0 := by
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    exact sub_self _
  have hbm : a - algebraMap R G.connectedComponent.A (counit (R := R) a) ∈
      maximalIdeal G.connectedComponent.A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (Bialgebra.counitAlgHom R G.connectedComponent.A)
    rw [hb] at this
    exact not_isUnit_zero this
  have h1 := map_mem_radical_fiberIdeal (ofConv y)
    (maximalIdeal_le_radical_fiberIdeal (R := R) hbm)
  have hfib : fiberIdeal R Ω = ⊥ := by
    rw [eq_bot_iff, fiberIdeal, Ideal.map_le_iff_le_comap]
    intro r hr
    exact Ideal.mem_comap.mpr (Ideal.mem_bot.mpr (hΩ r hr))
  rw [hfib] at h1
  obtain ⟨n, hn⟩ := h1
  have h0 := eq_zero_of_pow_eq_zero (Ideal.mem_bot.mp hn)
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
  exact h0

variable [IsDomain R] [IsPrincipalIdealRing R]

theorem mapPoints_etaleQuotientHom_injective
    (hΩ : ∀ r ∈ maximalIdeal R, algebraMap R Ω r = 0) :
    Function.Injective (G.etaleQuotientHom.mapPoints Ω) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨y, rfl⟩ := (G.mapPoints_etaleQuotientHom_eq_one_iff x).mp hx
  rw [G.connectedComponent_points_eq_one hΩ y, map_one]

theorem mapPoints_etaleQuotientHom_surjective [IsAlgClosed Ω] :
    Function.Surjective (G.etaleQuotientHom.mapPoints Ω) := by
  intro φ
  obtain ⟨b⟩ := G.nonempty_basis_etaleInvariants
  haveI : Nontrivial G.A := (Bialgebra.counitAlgHom R G.A).toRingHom.domain_nontrivial
  obtain ⟨i⟩ := b.index_nonempty
  letI : Algebra G.etaleInvariants Ω := (ofConv φ : G.etaleInvariants →ₐ[R] Ω).toRingHom.toAlgebra
  let b' := Algebra.TensorProduct.basis Ω b
  haveI : Nontrivial (Ω ⊗[G.etaleInvariants] G.A) := ⟨⟨b' i, 0, b'.ne_zero i⟩⟩
  haveI : Module.Finite Ω (Ω ⊗[G.etaleInvariants] G.A) := Module.Finite.of_basis b'
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Ω ⊗[G.etaleInvariants] G.A)
  letI := Ideal.Quotient.field M
  haveI : Module.Finite Ω ((Ω ⊗[G.etaleInvariants] G.A) ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ Ω M).toLinearMap Ideal.Quotient.mk_surjective
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω)
    (K := (Ω ⊗[G.etaleInvariants] G.A) ⧸ M)
  let χ : (Ω ⊗[G.etaleInvariants] G.A) →ₐ[Ω] Ω :=
    (AlgEquiv.ofBijective (Algebra.ofId Ω _) hbij).symm.toAlgHom.comp (Ideal.Quotient.mkₐ Ω M)
  let ψ : G.A →ₐ[G.etaleInvariants] Ω :=
    (χ.restrictScalars G.etaleInvariants).comp Algebra.TensorProduct.includeRight
  have hψ : ∀ e : G.etaleInvariants, ψ e = ofConv φ e := fun e => ψ.commutes e
  let x : G.A →ₐ[R] Ω :=
    { ψ.toRingHom with
      commutes' := fun r => by
        change ψ (algebraMap R G.A r) = algebraMap R Ω r
        rw [IsScalarTower.algebraMap_apply R G.etaleInvariants G.A r]
        exact (ψ.commutes _).trans ((ofConv φ).commutes r) }
  refine ⟨toConv x, WithConv.ofConv_injective (AlgHom.ext fun e => ?_)⟩
  exact hψ e

/-- An étale quotient has `|G^{et}|` points over an algebraically closed field. -/
theorem card_points_etaleQuotient [IsAlgClosed Ω] :
    Nat.card (G.etaleQuotient.points Ω) = G.etaleQuotient.order := by
  have h1 : (G.etaleQuotient.baseChange Ω).IsEtale := by
    have : Algebra.Etale R G.etaleQuotient.A := G.isEtale_etaleQuotient
    exact (inferInstance : Algebra.Etale Ω (Ω ⊗[R] G.etaleQuotient.A))
  rw [← order_baseChange Ω G.etaleQuotient, ← card_points_of_isEtale _ h1]
  exact Nat.card_congr (G.etaleQuotient.baseChangePointsEquiv (S := Ω) Ω).toEquiv.symm

/-- **`#G(Ω) = |G^{et}|`** for an algebraically closed field `Ω` over the residue field. -/
theorem card_points_eq_order_etaleQuotient [IsAlgClosed Ω]
    (hΩ : ∀ r ∈ maximalIdeal R, algebraMap R Ω r = 0) :
    Nat.card (G.points Ω) = G.etaleQuotient.order :=
  (Nat.card_congr (Equiv.ofBijective _ ⟨G.mapPoints_etaleQuotientHom_injective hΩ,
    G.mapPoints_etaleQuotientHom_surjective⟩)).trans G.card_points_etaleQuotient

/-- **`|G| = |G⁰| · #G(Ω)`**. -/
theorem order_eq_mul_card_points [IsAlgClosed Ω]
    (hΩ : ∀ r ∈ maximalIdeal R, algebraMap R Ω r = 0) :
    G.order = G.connectedComponent.order * Nat.card (G.points Ω) := by
  rw [G.card_points_eq_order_etaleQuotient hΩ, G.order_eq_mul]

end Points

end FFGroupScheme

/-! ### The connected part of a `p`-divisible group -/

namespace PDivGroup

open FFGroupScheme

section Quot

variable {R : Type u} [CommRing R] {p : ℕ} (G : PDivGroup R p)

/-- The iterated quotient map `[p^v] : G_{v+1} → G_1`. -/
def quotOne : ∀ v : ℕ, FFGroupScheme.Hom (G.G (v + 1)) (G.G 1)
  | 0 => BialgHom.id R (G.G 1).A
  | v + 1 => (G.quot (v + 1)).comp (quotOne v)

theorem mapPoints_quotOne_zero (S : Type*) [CommRing S] [Algebra R S] (y : (G.G (0 + 1)).points S) :
    (G.quotOne 0).mapPoints S y = y :=
  WithConv.ofConv_injective (AlgHom.ext fun _ => rfl)

theorem mapPoints_quotOne_succ (v : ℕ) (S : Type*) [CommRing S] [Algebra R S]
    (y : (G.G (v + 1 + 1)).points S) :
    (G.quotOne (v + 1)).mapPoints S y =
      (G.quotOne v).mapPoints S ((G.quot (v + 1)).mapPoints S y) :=
  WithConv.ofConv_injective (AlgHom.ext fun _ => rfl)

theorem quotOne_mapPoints_eq_one_iff (v : ℕ) (S : Type u) [CommRing S] [Algebra R S] :
    ∀ y : (G.G (v + 1)).points S, (G.quotOne v).mapPoints S y = 1 ↔ y ^ (p ^ v) = 1 := by
  induction v with
  | zero => intro y; rw [mapPoints_quotOne_zero, pow_zero, pow_one]
  | succ v ih =>
    intro y
    rw [mapPoints_quotOne_succ, ih, ← map_pow, ← MonoidHom.mem_ker, G.ker_quot S (v + 1),
      MonoidHom.mem_ker, powMonoidHom_apply, ← pow_mul, pow_succ]

end Quot

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {p : ℕ} (G : PDivGroup R p)

/-- The transition maps `i_v⁰ : G_v⁰ → G_{v+1}⁰`. -/
def connIncl (v : ℕ) :
    FFGroupScheme.Hom (G.G v).connectedComponent (G.G (v + 1)).connectedComponent :=
  connectedComponentMap (G.incl v)

theorem connIncl_surjective (v : ℕ) : Function.Surjective (G.connIncl v) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := G.incl_surjective v a
  exact ⟨Ideal.Quotient.mk _ b, rfl⟩

theorem incl_idemConn (v : ℕ) : G.incl v (G.G (v + 1)).idemConn = (G.G v).idemConn :=
  map_idemConn_of_surjective (G.incl v) (G.incl_surjective v)

/-- `G_v⁰ ≅ G_{v+1}⁰[p^v]` on points. -/
theorem connIncl_range_eq (v : ℕ) (S : Type u) [CommRing S] [Algebra R S]
    (y : (G.G (v + 1)).connectedComponent.points S) :
    (∃ x, (G.connIncl v).mapPoints S x = y) ↔ y ^ (p ^ v) = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ (p ^ v) = 1 := by
      apply (G.G v).mapPoints_connectedComponentHom_injective S
      rw [map_pow, G.pow_eq_one v S, map_one]
    rw [this, map_one]
  · intro hy
    set z := (G.G (v + 1)).connectedComponentHom.mapPoints S y
    have hz : z ^ (p ^ v) = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨x₀, hx₀⟩ := (G.range_eq v S z).mpr hz
    have hk : ofConv x₀ (1 - (G.G v).idemConn) = 0 := by
      rw [← G.incl_idemConn v, ← map_one (G.incl v), ← map_sub]
      change ofConv ((G.incl v).mapPoints S x₀) (1 - (G.G (v + 1)).idemConn) = 0
      rw [hx₀]
      change ofConv y ((G.G (v + 1)).connectedComponentHom (1 - (G.G (v + 1)).idemConn)) = 0
      rw [map_sub, map_one, connectedComponentHom_idemConn, sub_self, map_zero]
    obtain ⟨x, hx⟩ := (G.G v).exists_connectedComponentHom_mapPoints_eq x₀ hk
    refine ⟨x, (G.G (v + 1)).mapPoints_connectedComponentHom_injective S ?_⟩
    exact (mapPoints_connectedComponentMap (G.incl v) S x).trans (by rw [hx, hx₀])

section Order

variable [IsDomain R] [IsPrincipalIdealRing R]

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- **`c_{v+1} ≤ c_1 c_v`** (Nakayama for `[p^v]⁰ : G_{v+1}⁰ → G_1⁰`, whose kernel lies in
`G_v⁰`). -/
theorem order_connectedComponent_succ_le (v : ℕ) :
    (G.G (v + 1)).connectedComponent.order ≤
      (G.G 1).connectedComponent.order * (G.G v).connectedComponent.order := by
  let I := (RingHom.ker (Bialgebra.counitAlgHom R (G.G 1).connectedComponent.A)).map
      (connectedComponentMap (G.quotOne v) :
        (G.G 1).connectedComponent.A →ₐ[R] (G.G (v + 1)).connectedComponent.A)
  let S := (G.G (v + 1)).connectedComponent.A ⧸ I
  let y : (G.G (v + 1)).connectedComponent.points S := toConv (Ideal.Quotient.mkₐ R I)
  have hφy : (connectedComponentMap (G.quotOne v)).mapPoints S y = 1 := by
    apply WithConv.ofConv_injective
    refine AlgHom.ext fun a => ?_
    change Ideal.Quotient.mk I (connectedComponentMap (G.quotOne v) a) =
      algebraMap R S (counit (R := R) a)
    have hmem : a - algebraMap R _ (counit (R := R) a) ∈
        RingHom.ker (Bialgebra.counitAlgHom R (G.G 1).connectedComponent.A) := by
      rw [RingHom.mem_ker]
      simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      exact sub_self _
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem
      (connectedComponentMap (G.quotOne v) :
        (G.G 1).connectedComponent.A →ₐ[R] (G.G (v + 1)).connectedComponent.A) hmem)
    rw [map_sub, AlgHom.commutes, map_sub, sub_eq_zero] at h0
    rw [← Ideal.Quotient.mk_algebraMap]
    exact h0
  have hy : y ^ (p ^ v) = 1 := by
    apply (G.G (v + 1)).mapPoints_connectedComponentHom_injective S
    rw [map_pow, map_one, ← G.quotOne_mapPoints_eq_one_iff v S,
      ← mapPoints_connectedComponentMap, hφy, map_one]
  obtain ⟨x, hx⟩ := (G.connIncl_range_eq v S y).mpr hy
  refine order_le_mul_of_surjective (connectedComponentMap (G.quotOne v))
    (G.G 1).isConnected_connectedComponent (ofConv x) fun t => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact ⟨G.connIncl v b,
    congrArg (fun z : (G.G (v + 1)).connectedComponent.points S => ofConv z b) hx⟩

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]

/-- **`n_{v+1} ≤ n_1 n_v`** for `n_w = #G_w(Ω)`. -/
theorem card_points_succ_le [hp : Fact p.Prime]
    (hΩ : ∀ r ∈ maximalIdeal R, algebraMap R Ω r = 0) (v : ℕ) :
    Nat.card ((G.G (v + 1)).points Ω) ≤
      Nat.card ((G.G 1).points Ω) * Nat.card ((G.G v).points Ω) := by
  have hfin : Finite ((G.G v).points Ω) := Nat.finite_of_card_ne_zero fun h => by
    have := ((G.G v).order_eq_mul_card_points hΩ).symm.trans (G.order_eq v)
    rw [h, mul_zero] at this
    exact (pow_pos hp.out.pos _).ne' this.symm
  rw [← G.card_ker_mul_card_range_quot Ω v]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)

/-- **`|G_v⁰| = |G_1⁰|^v`**. -/
theorem order_connectedComponent_eq_pow [hp : Fact p.Prime] (v : ℕ) :
    (G.G v).connectedComponent.order = (G.G 1).connectedComponent.order ^ v := by
  let Ω := AlgebraicClosure (ResidueField R)
  have hΩ : ∀ r ∈ maximalIdeal R, algebraMap R Ω r = 0 := fun r hr => by
    rw [IsScalarTower.algebraMap_apply R (ResidueField R) Ω, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff r).mpr hr, map_zero]
  have hord : ∀ w, (G.G w).connectedComponent.order * Nat.card ((G.G w).points Ω) =
      p ^ (G.height * w) := fun w =>
    ((G.G w).order_eq_mul_card_points hΩ).symm.trans (G.order_eq w)
  have hpos : ∀ w, 0 < Nat.card ((G.G w).points Ω) := fun w => Nat.pos_of_ne_zero fun h => by
    have := hord w
    rw [h, mul_zero] at this
    exact (pow_pos hp.out.pos _).ne' this.symm
  induction v with
  | zero =>
    have := hord 0
    rw [mul_zero, pow_zero, mul_eq_one] at this
    rw [pow_zero]
    exact this.1
  | succ v ih =>
    have hc := G.order_connectedComponent_succ_le v
    have hn := G.card_points_succ_le Ω hΩ v
    have key : (G.G (v + 1)).connectedComponent.order * Nat.card ((G.G (v + 1)).points Ω) =
        ((G.G 1).connectedComponent.order * (G.G v).connectedComponent.order) *
          (Nat.card ((G.G 1).points Ω) * Nat.card ((G.G v).points Ω)) := by
      rw [hord (v + 1), mul_mul_mul_comm, hord 1, hord v, ← pow_add]
      congr 1
      ring
    have h1 := Nat.mul_le_mul_left (G.G (v + 1)).connectedComponent.order hn
    have h2 := Nat.mul_le_mul_right (Nat.card ((G.G 1).points Ω) * Nat.card ((G.G v).points Ω))
      hc
    have heq := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (hpos 1) (hpos v))
      (le_antisymm h2 (by rw [← key]; exact h1))
    rw [heq, ih, pow_succ, mul_comm]

/-- **The order of `G_v⁰` is `p^{h⁰ v}`** for some `h⁰ ≤ h`. -/
theorem exists_order_connectedComponent [hp : Fact p.Prime] :
    ∃ h₀ ≤ G.height, ∀ v, (G.G v).connectedComponent.order = p ^ (h₀ * v) := by
  have hdvd : (G.G 1).connectedComponent.order ∣ p ^ G.height := by
    have := (G.G 1).order_eq_mul
    rw [G.order_eq 1, mul_one] at this
    exact ⟨_, this⟩
  obtain ⟨h₀, hle, he⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  exact ⟨h₀, hle, fun v => by rw [G.order_connectedComponent_eq_pow v, he, ← pow_mul]⟩

variable [Fact p.Prime]

/-- The height `h⁰` of the connected part. -/
def connHeight : ℕ := G.exists_order_connectedComponent.choose

theorem connHeight_le : G.connHeight ≤ G.height :=
  G.exists_order_connectedComponent.choose_spec.1

/-- **The connected part `G⁰ = (G_v⁰)_v`**, a `p`-divisible group of height `h⁰`
([Hong, Prop. 2.1.10]). -/
def connPart : PDivGroup R p where
  height := G.connHeight
  G v := (G.G v).connectedComponent
  order_eq := G.exists_order_connectedComponent.choose_spec.2
  incl := G.connIncl
  incl_surjective := G.connIncl_surjective
  range_eq := G.connIncl_range_eq

theorem connPart_height : G.connPart.height = G.connHeight := rfl

theorem connPart_G (v : ℕ) : G.connPart.G v = (G.G v).connectedComponent := rfl

/-- All layers of `G⁰` are connected. -/
theorem isConnected_connPart (v : ℕ) : (G.connPart.G v).IsConnected :=
  (G.G v).isConnected_connectedComponent

/-- The closed immersion `G⁰ → G`. -/
def connPartHom : PDivGroup.Hom G.connPart G where
  f v := (G.G v).connectedComponentHom
  comm _ := DFunLike.ext _ _ fun _ => rfl

theorem connPartHom_surjective (v : ℕ) : Function.Surjective (G.connPartHom.f v) :=
  (G.G v).connectedComponentHom_surjective

theorem connPartHom_mapPoints_injective (v : ℕ) (S : Type u) [CommRing S] [Algebra R S] :
    Function.Injective ((G.connPartHom.f v).mapPoints S) :=
  (G.G v).mapPoints_connectedComponentHom_injective S

/-- A connected `p`-divisible group has connected part of the same height. -/
theorem connHeight_eq_of_isConnected (hG : ∀ v, (G.G v).IsConnected) :
    G.connHeight = G.height := by
  have h := G.exists_order_connectedComponent.choose_spec.2 1
  have h1 : (G.G 1).connectedComponent.order = (G.G 1).order := by
    rw [(G.G 1).order_eq_mul, (G.G 1).order_etaleQuotient_of_isConnected (hG 1), mul_one]
  rw [h1, G.order_eq 1, mul_one, mul_one] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm

end Order

end PDivGroup

/-! ### Serre–Tate: `G⁰ ≅ F[p^∞]` over `ℤ_p` -/

section SerreTate

variable {p : ℕ} [Fact p.Prime]

theorem isPrincipalIdealRing_zpD : IsPrincipalIdealRing (ZpD p) :=
  inferInstanceAs (IsPrincipalIdealRing ℤ_[p])

attribute [local instance] SerreTate.isDomain_zpD isPrincipalIdealRing_zpD

/-- **`G⁰ ≅ F[p^∞]`** ([Hong, Prop. 2.1.10, Thm. 2.2.16, Def. 2.2.17]): the connected part of a
`p`-divisible group `G` over `ℤ_p` is isomorphic to `F[p^∞]` for a `p`-divisible formal group
law `F` in some number `d` of variables (the dimension of `G`). -/
theorem PDivGroup.exists_connPart_iso (G : PDivGroup (ZpD p) p) :
    ∃ (d : ℕ) (P : PDivFGL (ZpD p) d p) (φ : PDivGroup.Hom G.connPart P.pdivGroup)
      (ψ : PDivGroup.Hom P.pdivGroup G.connPart),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ :=
  PDivGroup.exists_pdivFGL_iso G.connPart G.isConnected_connPart

end SerreTate

end PadicHodge
