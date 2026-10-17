/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.FiniteFlat
import PadicHodge.GroupScheme.ConnectedIdempotent
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.LocalRing.Module

/-!
# The connected component of a finite flat group scheme

Let `R` be a complete local ring (see `GroupScheme/ConnectedIdempotent.lean` for why complete
rather than henselian) and `G = Spec A` a finite flat commutative group scheme over `R`. The
identity section `ε : A → R` has a point idempotent `e₀ ∈ A` (`ε(e₀) = 1`, `A e₀` is `R e₀`
plus elements nilpotent modulo `m_R`). Then `G⁰ = Spec (A / (1 - e₀)) = Spec (A e₀)` is a closed
subgroup scheme, the *connected component of the identity*.

Proof that `(1 - e₀)` is a Hopf ideal (standard argument, written up here): `e₀ ⊗ e₀` is a point
idempotent of `A ⊗ A` for `ε ⊗ ε` (`IsPointIdempotent.tmul`), and `g = (e₀ ⊗ e₀) Δ(1 - e₀)` is
an idempotent below `e₀ ⊗ e₀` with `(ε ⊗ ε)(g) = ε(1 - e₀) = 0`, hence `g ≡ 0` modulo the radical
of `m_R (A ⊗ A)`, hence `g = 0` (`A ⊗ A` is finite over `R`, so this radical lies in the
Jacobson radical). So `Δ(1 - e₀) ↦ 0` in `A/(1 - e₀) ⊗ A/(1 - e₀)`. Likewise `e₀ S(1 - e₀) = 0`.

* `isHopfIdeal_span_one_sub`: `(1 - e₀)` is a Hopf ideal;
* `isLocalRing_quotient_span_one_sub`, `free_quotient_span_one_sub`: `A / (1 - e₀)` is local and
  finite free (a direct summand of `A`, projective over a local ring);
* `FFGroupScheme.connectedComponent G` (`G⁰`), `FFGroupScheme.connectedComponentHom : G⁰ → G`
  (a closed immersion: `connectedComponentHom_surjective`), `G⁰` is connected
  (`isConnected_connectedComponent`), and `G⁰ = G` if `G` is connected
  (`connectedComponentHom_bijective`).

Here a finite flat group scheme over a local ring is *connected* (`FFGroupScheme.IsConnected`)
if its coordinate ring is local; over a field this is [BC, Example 7.1.7(4)]'s notion
(`G` connected iff `G_red = Spec k`, i.e. `A` local with residue field `k`).
-/

noncomputable section

open Coalgebra HopfAlgebra IsLocalRing TensorProduct

namespace PadicHodge

universe u

/-! ### The Hopf ideal of a point idempotent of the counit -/

section HopfIdeal

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]

theorem productMap_counit_comul (a : A) :
    Algebra.TensorProduct.productMap (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R A)
      (comul a) = counit a := by
  have H : (Algebra.TensorProduct.productMap (Bialgebra.counitAlgHom R A)
      (Bialgebra.counitAlgHom R A)).toLinearMap =
      (counit : A →ₗ[R] R) ∘ₗ (TensorProduct.lid R A).toLinearMap ∘ₗ
        (counit : A →ₗ[R] R).rTensor A := by
    ext x y
    simp [Algebra.TensorProduct.productMap_apply_tmul]
  have := LinearMap.congr_fun H (comul a)
  simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at this
  rw [this, Coalgebra.rTensor_counit_comul]
  simp

theorem mk_eq_one_of_span_one_sub (e : A) :
    Ideal.Quotient.mk (Ideal.span {1 - e}) e = 1 := by
  rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
  have : e - 1 = -(1 - e) := by ring
  rw [this]
  exact neg_mem (Ideal.subset_span rfl)

variable [IsLocalRing R] [Module.Finite R A] {e : A}

theorem IsPointIdempotent.tmul_mul_comul_one_sub
    (he : IsPointIdempotent (Bialgebra.counitAlgHom R A) e) :
    (e ⊗ₜ[R] e) * comul (R := R) (1 - e) = 0 := by
  have hE := he.tmul he
  have hg : IsIdempotentElem ((e ⊗ₜ[R] e) * comul (R := R) (1 - e)) := by
    refine hE.isIdempotentElem.mul ?_
    simpa using he.isIdempotentElem.one_sub.map (Bialgebra.comulAlgHom R A)
  refine hE.eq_zero_of_mul_eq hg (by rw [mul_right_comm, hE.isIdempotentElem.eq]) ?_
  have h1 : counit (R := R) e = 1 := he.apply_eq_one
  rw [map_mul, hE.apply_eq_one, one_mul, productMap_counit_comul, map_sub, h1,
    Bialgebra.counit_one, sub_self]

theorem IsPointIdempotent.mul_antipode_one_sub
    (he : IsPointIdempotent (Bialgebra.counitAlgHom R A) e) :
    e * antipode R (1 - e) = 0 := by
  have hg : IsIdempotentElem (e * antipode R (1 - e)) := by
    refine he.isIdempotentElem.mul ?_
    simpa using he.isIdempotentElem.one_sub.map (antipodeAlgHom R A)
  refine he.eq_zero_of_mul_eq hg (by rw [mul_right_comm, he.isIdempotentElem.eq]) ?_
  have h1 : counit (R := R) e = 1 := he.apply_eq_one
  change counit (R := R) (e * antipode R (1 - e)) = 0
  rw [Bialgebra.counit_mul, counit_antipode, map_sub, h1, Bialgebra.counit_one, sub_self,
    mul_zero]

/-- `(1 - e₀)` is a Hopf ideal. -/
theorem isHopfIdeal_span_one_sub (he : IsPointIdempotent (Bialgebra.counitAlgHom R A) e) :
    (Ideal.span {1 - e}).IsHopfIdeal R where
  counit_eq_zero := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    change Bialgebra.counitAlgHom R A (y * (1 - e)) = 0
    rw [map_mul, map_sub, map_one, he.apply_eq_one, sub_self, mul_zero]
  map_mkQ_comul_eq_zero := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    set π := Ideal.Quotient.mkₐ R (Ideal.span {1 - e})
    change Algebra.TensorProduct.map π π (Bialgebra.comulAlgHom R A (y * (1 - e))) = 0
    have h1 : Algebra.TensorProduct.map π π (e ⊗ₜ[R] e) = 1 := by
      rw [Algebra.TensorProduct.map_tmul]
      simp only [π, Ideal.Quotient.mkₐ_eq_mk, mk_eq_one_of_span_one_sub]
      rfl
    have h2 : Algebra.TensorProduct.map π π (Bialgebra.comulAlgHom R A (1 - e)) = 0 := by
      rw [← one_mul (Algebra.TensorProduct.map π π _), ← h1, ← map_mul]
      erw [he.tmul_mul_comul_one_sub, map_zero]
    rw [map_mul, map_mul, h2, mul_zero]
  antipode_mem := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    change antipodeAlgHom R A (y * (1 - e)) ∈ _
    rw [map_mul]
    refine Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton'.mpr ⟨antipode R (1 - e), ?_⟩)
    have := he.mul_antipode_one_sub
    rw [mul_sub, mul_one, mul_comm, this, sub_zero]
    rfl

end HopfIdeal

/-! ### The quotient `A / (1 - e)` -/

section Quotient

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

theorem projective_quotient_span_one_sub [Module.Projective R A] {e : A}
    (he : IsIdempotentElem e) : Module.Projective R (A ⧸ Ideal.span {1 - e}) := by
  set I := Ideal.span {1 - e}
  let i : (A ⧸ I) →ₗ[R] A := (I.restrictScalars R).liftQ (LinearMap.mulLeft R e) (by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, mul_left_comm, mul_sub, mul_one, he.eq,
      sub_self, mul_zero])
  refine Module.Projective.of_split i (Ideal.Quotient.mkₐ R I).toLinearMap ?_
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk I (e * a) = Ideal.Quotient.mk I a
  rw [map_mul, mk_eq_one_of_span_one_sub, one_mul]

theorem free_quotient_span_one_sub [IsLocalRing R] [Module.Free R A] [Module.Finite R A] {e : A}
    (he : IsIdempotentElem e) : Module.Free R (A ⧸ Ideal.span {1 - e}) := by
  have := projective_quotient_span_one_sub (R := R) he
  exact Module.free_of_flat_of_isLocalRing

/-- The quotient by `1 - e` for a point idempotent `e` is local. -/
theorem isLocalRing_quotient_span_one_sub [IsLocalRing R] [Module.Finite R A] {φ : A →ₐ[R] R}
    {e : A} (he : IsPointIdempotent φ e) : IsLocalRing (A ⧸ Ideal.span {1 - e}) := by
  set I := Ideal.span {1 - e}
  set π := Ideal.Quotient.mkₐ R I
  have hπe : π e = 1 := mk_eq_one_of_span_one_sub e
  have hφI : ∀ x ∈ I, φ x = 0 := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_sub, map_one, he.apply_eq_one, sub_self, mul_zero]
  have : Nontrivial (A ⧸ I) := (Ideal.Quotient.liftₐ I φ hφI).toRingHom.domain_nontrivial
  have key : ∀ a : A, π a - algebraMap R _ (φ a) ∈ Ideal.jacobson ⊥ := by
    intro a
    have h1 := map_mem_radical_fiberIdeal π (he.mul_sub_mem a)
    rw [map_sub, map_mul, map_smul, hπe, mul_one, Algebra.smul_def, mul_one] at h1
    exact radical_fiberIdeal_le_jacobson h1
  have unit_of : ∀ r : R, IsUnit r → ∀ y : A ⧸ I, y - algebraMap R _ r ∈ Ideal.jacobson ⊥ →
      IsUnit y := by
    rintro r ⟨u, rfl⟩ y hy
    have h2 := Ideal.mem_jacobson_bot.mp hy (algebraMap R _ ↑u⁻¹)
    have hu : algebraMap R (A ⧸ I) ↑u * algebraMap R (A ⧸ I) ↑u⁻¹ = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h' : y = algebraMap R _ ↑u *
        ((y - algebraMap R _ ↑u) * algebraMap R _ ↑u⁻¹ + 1) := by
      linear_combination (-(y - algebraMap R (A ⧸ I) ↑u)) * hu
    rw [h']
    exact (u.isUnit.map _).mul h2
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (φ a) with h | h
  · exact Or.inl (unit_of _ h _ (key a))
  · refine Or.inr (unit_of _ h _ ?_)
    have := neg_mem (key a)
    convert this using 1
    simp only [π, Ideal.Quotient.mkₐ_eq_mk, map_sub, map_one]
    ring

end Quotient

/-- The quotient of a cocommutative Hopf algebra by a Hopf ideal is cocommutative. -/
instance isCocomm_quotient {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    [IsCocomm R A] (I : Ideal A) [I.IsHopfIdeal R] : IsCocomm R (A ⧸ I) where
  comm_comp_comul := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Bialgebra.Quotient.comul_mk]
    conv_rhs => rw [← comm_comul (R := R) a]
    induction comul (R := R) a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]

/-! ### The connected component of a finite flat group scheme -/

namespace FFGroupScheme

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A finite flat group scheme over a local ring is connected if its coordinate ring is local. -/
def IsConnected (G : FFGroupScheme R) : Prop := IsLocalRing G.A

variable [IsAdicComplete (maximalIdeal R) R] (G : FFGroupScheme R)

/-- The idempotent `e₀ ∈ A` of the identity component. -/
def idemConn : G.A := (exists_isPointIdempotent (Bialgebra.counitAlgHom R G.A)).choose

theorem isPointIdempotent_idemConn :
    IsPointIdempotent (Bialgebra.counitAlgHom R G.A) G.idemConn :=
  (exists_isPointIdempotent (Bialgebra.counitAlgHom R G.A)).choose_spec

/-- The Hopf ideal `(1 - e₀)` cutting out `G⁰`. -/
def connIdeal : Ideal G.A := Ideal.span {1 - G.idemConn}

instance : G.connIdeal.IsHopfIdeal R := isHopfIdeal_span_one_sub G.isPointIdempotent_idemConn

instance : Module.Free R (G.A ⧸ G.connIdeal) :=
  free_quotient_span_one_sub G.isPointIdempotent_idemConn.isIdempotentElem

instance : Module.Finite R (G.A ⧸ G.connIdeal) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ R G.connIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

/-- The connected component of the identity `G⁰ = Spec (A / (1 - e₀))`. -/
def connectedComponent : FFGroupScheme R where
  A := G.A ⧸ G.connIdeal

/-- The closed immersion `G⁰ → G`. -/
def connectedComponentHom : Hom G.connectedComponent G :=
  Bialgebra.Quotient.mkBialgHom G.connIdeal

theorem connectedComponentHom_apply (a : G.A) :
    G.connectedComponentHom a = Ideal.Quotient.mk G.connIdeal a := rfl

theorem connectedComponentHom_surjective : Function.Surjective G.connectedComponentHom :=
  Ideal.Quotient.mk_surjective

instance : IsLocalRing (G.A ⧸ G.connIdeal) :=
  isLocalRing_quotient_span_one_sub G.isPointIdempotent_idemConn

instance : IsLocalRing G.connectedComponent.A :=
  inferInstanceAs (IsLocalRing (G.A ⧸ G.connIdeal))

theorem isConnected_connectedComponent : G.connectedComponent.IsConnected :=
  inferInstanceAs (IsLocalRing (G.A ⧸ G.connIdeal))

/-- A connected `G` equals its connected component. -/
theorem idemConn_eq_one (hG : G.IsConnected) : G.idemConn = 1 := by
  have he := G.isPointIdempotent_idemConn
  have : IsLocalRing G.A := hG
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self G.idemConn with h | h
  · exact h.mul_left_cancel (he.isIdempotentElem.eq.trans (mul_one _).symm)
  · have h0 : G.idemConn * (1 - G.idemConn) = 0 := by
      rw [mul_sub, mul_one, he.isIdempotentElem.eq, sub_self]
    have := he.apply_eq_one
    rw [h.mul_left_eq_zero.mp h0, map_zero] at this
    exact absurd this zero_ne_one

theorem connectedComponentHom_bijective (hG : G.IsConnected) :
    Function.Bijective G.connectedComponentHom := by
  refine ⟨fun a b hab => ?_, G.connectedComponentHom_surjective⟩
  replace hab : Ideal.Quotient.mk G.connIdeal a = Ideal.Quotient.mk G.connIdeal b := hab
  rw [Ideal.Quotient.eq, connIdeal,
    G.idemConn_eq_one hG, sub_self, Ideal.span_singleton_eq_bot.mpr rfl] at hab
  exact sub_eq_zero.mp hab

end FFGroupScheme

end PadicHodge
