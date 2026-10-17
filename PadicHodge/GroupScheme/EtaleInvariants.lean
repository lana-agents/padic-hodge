/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Connected
import PadicHodge.GroupScheme.Constant
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Towards the étale quotient `G^{et} = G / G⁰`

Let `G = Spec A` be a finite flat commutative group scheme over a complete local ring `R`, with
connected component `π : A → A⁰` (`GroupScheme/Connected.lean`). The coordinate ring of the
étale quotient `G^{et} = G / G⁰` should be the ring of `G⁰`-invariant functions
`A^{et} = {a | (id ⊗ π)(Δ a) = a ⊗ 1}` (`FFGroupScheme.etaleInvariants`). Here:

* `FFGroupScheme.IsEtale G`: `A` is an étale `R`-algebra;
* `comul_antipode`: `Δ ∘ S = (S ⊗ S) ∘ Δ` (for commutative and cocommutative `A`; proved in the
  commutative group `G(A ⊗ A)`: `Δ = i₁ * i₂` and `Δ ∘ S = Δ⁻¹ = i₁⁻¹ i₂⁻¹`);
* `etaleInvariants`: `A^{et}`, an `R`-subalgebra of `A`, stable under the antipode
  (`antipode_mem_etaleInvariants`) — i.e. closed under the algebra and antipode operations of a
  sub-Hopf algebra;
* `connectedComponentHom_of_mem_etaleInvariants`: `π(a) = ε(a)` on `A^{et}`, i.e. the composite
  `G⁰ → G → G^{et}` is trivial;
* `etaleInvariants_eq_bot`: if `G` is connected, then `A^{et} = R` (`G^{et}` trivial);
* `etaleInvariants_eq_top`, `order_connectedComponent_eq_one`: if `G⁰` is trivial (`π = ε`),
  then `A^{et} = A` and `|G⁰| = 1`;
* `connectedComponentHom_eq_of_isEtale`: **for étale `G`, `G⁰` is trivial** (so `A^{et} = A`,
  `etaleInvariants_eq_top_of_isEtale`): `A⁰` is finite, local and unramified over `R` with residue
  field `k`, so `m_R A⁰ = m_{A⁰}` (Mathlib `FormallyUnramified.map_maximalIdeal`), `A⁰ = R + m_R A⁰`
  and `A⁰ = R` by Nakayama;
* constant groups: `e₀ = e_1` (`const_idemConn`), `A^{et} = A` (`etaleInvariants_const`) and
  `|M_R⁰| = 1` (`order_connectedComponent_const`).

Over a complete local PID, `GroupScheme/EtaleQuotient.lean` shows `Δ(A^{et}) ⊆ A^{et} ⊗ A^{et}`,
that `A^{et}` is a finite free sub-Hopf algebra, and defines `G^{et}`. **Open**: that `A^{et}` is
étale over `R`, that `A` is faithfully flat over `A^{et}` with `A ⊗_{A^{et}} R = A⁰`, and hence
the exact sequence `0 → G⁰ → G → G^{et} → 0`.
-/

noncomputable section

open Coalgebra HopfAlgebra IsLocalRing TensorProduct WithConv

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

/-- A finite flat group scheme is étale if its coordinate ring is an étale `R`-algebra. -/
def IsEtale (G : FFGroupScheme R) : Prop := Algebra.Etale R G.A

/-- `Δ ∘ S = (S ⊗ S) ∘ Δ` for a commutative cocommutative Hopf algebra. -/
theorem comul_antipode (G : FFGroupScheme R) (a : G.A) :
    comul (R := R) (antipode R a) = TensorProduct.map (antipode R) (antipode R) (comul a) := by
  let i₁ : G.points (G.A ⊗[R] G.A) := toConv Algebra.TensorProduct.includeLeft
  let i₂ : G.points (G.A ⊗[R] G.A) := toConv Algebra.TensorProduct.includeRight
  have hΔ : i₁ * i₂ = toConv (Bialgebra.comulAlgHom R G.A) := by
    apply WithConv.ofConv_injective
    ext x
    rw [AlgHom.convMul_apply]
    simp only [i₁, i₂, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply,
      Bialgebra.comulAlgHom_apply]
  have h := mul_inv i₁ i₂
  rw [hΔ] at h
  have h' := congrArg (fun f : G.points (G.A ⊗[R] G.A) => (ofConv f : G.A →ₐ[R] _) a) h
  change comul (R := R) (antipode R a) = ofConv (i₁⁻¹ * i₂⁻¹) a at h'
  rw [h', AlgHom.convMul_apply]
  induction comul (R := R) a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [Algebra.TensorProduct.lift_tmul]
    change (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := G.A) (B := G.A)
      (antipode R x)) * Algebra.TensorProduct.includeRight (R := R) (A := G.A) (antipode R y) = _
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (G : FFGroupScheme R)

/-- The coaction `A → A ⊗ A⁰`, `a ↦ (id ⊗ π)(Δ a)`, of `G⁰` on `G` by translation. -/
def coactConn : G.A →ₐ[R] G.A ⊗[R] G.connectedComponent.A :=
  (Algebra.TensorProduct.map (AlgHom.id R G.A)
    (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A)).comp
    (Bialgebra.comulAlgHom R G.A)

/-- `A^{et}`: the `G⁰`-invariant functions `{a | (id ⊗ π)(Δ a) = a ⊗ 1}`. -/
def etaleInvariants : Subalgebra R G.A :=
  AlgHom.equalizer G.coactConn Algebra.TensorProduct.includeLeft

theorem mem_etaleInvariants {a : G.A} :
    a ∈ G.etaleInvariants ↔ G.coactConn a = a ⊗ₜ[R] 1 :=
  AlgHom.mem_equalizer _ _ a

/-- On `A^{et}`, `π = ε`: the composite `G⁰ → G → G^{et}` is trivial. -/
theorem connectedComponentHom_of_mem_etaleInvariants {a : G.A} (ha : a ∈ G.etaleInvariants) :
    G.connectedComponentHom a = algebraMap R _ (counit (R := R) a) := by
  set π : G.A →ₗ[R] G.connectedComponent.A :=
    (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A).toLinearMap
  have key : ∀ x : G.A ⊗[R] G.A,
      TensorProduct.lid R _ ((counit (R := R) (A := G.A)).rTensor _
        (TensorProduct.map LinearMap.id π x)) =
      π (TensorProduct.lid R _ ((counit (R := R) (A := G.A)).rTensor _ x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have h := congrArg (fun z => TensorProduct.lid R _ ((counit (R := R) (A := G.A)).rTensor _ z))
    ((G.mem_etaleInvariants).mp ha)
  change TensorProduct.lid R _ ((counit (R := R) (A := G.A)).rTensor _
    (TensorProduct.map LinearMap.id π (comul a))) = _ at h
  rw [key, Coalgebra.rTensor_counit_comul] at h
  simp only [TensorProduct.lid_tmul, one_smul, LinearMap.rTensor_tmul] at h
  rw [Algebra.algebraMap_eq_smul_one]
  exact h

theorem antipode_mem_etaleInvariants {a : G.A} (ha : a ∈ G.etaleInvariants) :
    antipode R a ∈ G.etaleInvariants := by
  rw [mem_etaleInvariants] at ha ⊢
  set π : G.A →ₗ[R] G.connectedComponent.A :=
    (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A).toLinearMap
  have hπS : π ∘ₗ antipode R = antipode R ∘ₗ π :=
    (HopfAlgebra.Quotient.antipode_comp_mkₐ G.connIdeal).symm
  change TensorProduct.map LinearMap.id π (comul (antipode R a)) = _
  change TensorProduct.map LinearMap.id π (comul a) = _ at ha
  rw [comul_antipode]
  have : ∀ x : G.A ⊗[R] G.A, TensorProduct.map LinearMap.id π
      (TensorProduct.map (antipode R) (antipode R) x) =
      TensorProduct.map (antipode R) (antipode R) (TensorProduct.map LinearMap.id π x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply]
      rw [← LinearMap.comp_apply π (antipode R) y, hπS, LinearMap.comp_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this, ha, TensorProduct.map_tmul, HopfAlgebra.antipode_one]

/-- If `G` is connected, `A^{et} = R`. -/
theorem etaleInvariants_eq_bot (hG : G.IsConnected) : G.etaleInvariants = ⊥ := by
  refine eq_bot_iff.mpr fun a ha => ?_
  have h := G.connectedComponentHom_of_mem_etaleInvariants ha
  have h2 : G.connectedComponentHom (algebraMap R G.A (counit (R := R) a)) =
      algebraMap R _ (counit (R := R) a) :=
    (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A).commutes _
  rw [(G.connectedComponentHom_bijective hG).1 (h.trans h2.symm)]
  exact Subalgebra.algebraMap_mem _ _

/-- A sufficient condition for `G⁰` to be trivial: `a e₀ = ε(a) e₀` for all `a`. -/
theorem connectedComponentHom_eq_of_mul_idemConn
    (h : ∀ a : G.A, a * G.idemConn = counit (R := R) a • G.idemConn) (a : G.A) :
    G.connectedComponentHom a = algebraMap R _ (counit (R := R) a) := by
  have h1 : G.connectedComponentHom G.idemConn = 1 := mk_eq_one_of_span_one_sub _
  have := congrArg G.connectedComponentHom (h a)
  rw [map_mul, h1, mul_one, map_smul, h1] at this
  rw [this, Algebra.algebraMap_eq_smul_one]

/-- If `G⁰` is trivial (`π = ε`), then `A^{et} = A`. -/
theorem etaleInvariants_eq_top
    (h : ∀ a : G.A, G.connectedComponentHom a = algebraMap R _ (counit (R := R) a)) :
    G.etaleInvariants = ⊤ := by
  refine eq_top_iff.mpr fun a _ => (G.mem_etaleInvariants).mpr ?_
  change TensorProduct.map LinearMap.id
    (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A).toLinearMap (comul a) = _
  have key : ∀ x : G.A ⊗[R] G.A, TensorProduct.map LinearMap.id
      (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A).toLinearMap x =
      TensorProduct.rid R G.A ((counit (R := R) (A := G.A)).lTensor _ x) ⊗ₜ[R] 1 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [h, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, TensorProduct.add_tmul]
  rw [key, Coalgebra.lTensor_counit_comul]
  simp

/-- If `G⁰` is trivial (`π = ε`), then `G⁰` has order `1`. -/
theorem order_connectedComponent_eq_one
    (h : ∀ a : G.A, G.connectedComponentHom a = algebraMap R _ (counit (R := R) a)) :
    G.connectedComponent.order = 1 := by
  let ε := Bialgebra.counitAlgHom R G.connectedComponent.A
  have hε : Function.Bijective ε := by
    refine ⟨fun x y hxy => ?_, fun r => ⟨algebraMap R _ r, ε.commutes r⟩⟩
    obtain ⟨a, rfl⟩ := G.connectedComponentHom_surjective x
    obtain ⟨b, rfl⟩ := G.connectedComponentHom_surjective y
    rw [h, h, ε.commutes, ε.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      RingHom.id_apply] at hxy
    rw [h, h, hxy]
  rw [order, (LinearEquiv.ofBijective ε.toLinearMap hε).finrank_eq, Module.finrank_self]

/-- **An étale `G` has trivial connected component**: `π = ε`. (`A⁰` is a finite local
unramified `R`-algebra with residue field `k`, so `m_R A⁰ = m_{A⁰}` and `A⁰ = R + m_R A⁰`,
hence `A⁰ = R` by Nakayama.) -/
theorem connectedComponentHom_eq_of_isEtale (hG : G.IsEtale) (a : G.A) :
    G.connectedComponentHom a = algebraMap R _ (counit (R := R) a) := by
  have : Algebra.Etale R G.A := hG
  set A₀ := G.connectedComponent.A
  have : Algebra.FormallyUnramified R A₀ :=
    Algebra.FormallyUnramified.of_surjective (G.connectedComponentHom : G.A →ₐ[R] A₀)
      G.connectedComponentHom_surjective
  have : IsLocalHom (algebraMap R A₀) := ⟨fun r hr => by
    simpa using hr.map (Bialgebra.counitAlgHom R A₀)⟩
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := A₀)
  have key : (⊤ : Submodule R A₀) ≤ Submodule.span R {1} ⊔ maximalIdeal R • ⊤ := by
    intro x _
    have hx : x - algebraMap R A₀ (counit (R := R) x) ∈ maximalIdeal A₀ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have := hu.map (Bialgebra.counitAlgHom R A₀)
      simp at this
    rw [← hm] at hx
    rw [Ideal.smul_top_eq_map]
    have hx' : x = algebraMap R A₀ (counit (R := R) x) +
        (x - algebraMap R A₀ (counit (R := R) x)) := by ring
    rw [hx']
    refine Submodule.add_mem_sup ?_ hx
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self 1)
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge key
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hle (Submodule.mem_top (x :=
    G.connectedComponentHom a)))
  have hr' := congrArg (Bialgebra.counitAlgHom R A₀) hr
  rw [map_smul, map_one, smul_eq_mul, mul_one] at hr'
  change r = counit (R := R) a at hr'
  rw [← hr, hr', Algebra.algebraMap_eq_smul_one]

theorem etaleInvariants_eq_top_of_isEtale (hG : G.IsEtale) : G.etaleInvariants = ⊤ :=
  G.etaleInvariants_eq_top (G.connectedComponentHom_eq_of_isEtale hG)

theorem order_connectedComponent_of_isEtale (hG : G.IsEtale) : G.connectedComponent.order = 1 :=
  G.order_connectedComponent_eq_one (G.connectedComponentHom_eq_of_isEtale hG)

/-! ### Constant groups -/

variable (M : Type) [CommGroup M] [Fintype M] [DecidableEq M]

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [Fintype M] in
theorem const_mul_e_one (f : M → R) : f * ConstGS.e R M 1 = f 1 • ConstGS.e R M 1 := by
  ext x
  simp only [Pi.mul_apply, ConstGS.e_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with hx
  · rw [hx]
  · simp

/-- For a constant group `M_R`, `e₀ = e_1` (the indicator of the identity). -/
theorem const_idemConn : (const R M).idemConn = eA (R := R) (M := M) 1 := by
  refine (const R M).isPointIdempotent_idemConn.unique ⟨?_, ?_, fun f => ?_⟩
  · change ConstGS.e R M 1 * ConstGS.e R M 1 = ConstGS.e R M 1
    rw [ConstGS.e_mul_e, if_pos rfl]
  · change ConstGS.counit R M (ConstGS.e R M 1) = 1
    rw [ConstGS.counit_e, if_pos rfl]
  · change f * eA (R := R) (M := M) 1 - counit (R := R) f • eA (R := R) (M := M) 1 ∈ _
    rw [show f * eA (R := R) (M := M) 1 = counit (R := R) f • eA (R := R) (M := M) 1 from
      const_mul_e_one M f, sub_self]
    exact zero_mem _

/-- The constant group is its own étale quotient: `A^{et} = A`. -/
theorem etaleInvariants_const : (const R M).etaleInvariants = ⊤ :=
  etaleInvariants_eq_top _ <| connectedComponentHom_eq_of_mul_idemConn _ fun a => by
    rw [const_idemConn]; exact const_mul_e_one M a

/-- The connected component of a constant group is trivial. -/
theorem order_connectedComponent_const : (const R M).connectedComponent.order = 1 :=
  order_connectedComponent_eq_one _ <| connectedComponentHom_eq_of_mul_idemConn _ fun a => by
    rw [const_idemConn]; exact const_mul_e_one M a

end FFGroupScheme

end PadicHodge
