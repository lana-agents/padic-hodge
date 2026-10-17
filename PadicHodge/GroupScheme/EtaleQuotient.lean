/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.EtaleInvariants
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.Basic

/-!
# The étale quotient `G^{et}` of a finite flat group scheme

Let `G = Spec A` be a finite flat commutative group scheme over a complete local principal ideal
domain `R` (e.g. `O_K`, `ℤ_p`), with connected component `π : A → A⁰` and `G⁰`-invariants
`A^{et} = {a | (id ⊗ π)(Δ a) = a ⊗ 1}` (`GroupScheme/EtaleInvariants.lean`). We show that `A^{et}`
is a sub-Hopf algebra of `A`, finite free over `R`, and define the étale quotient
`G^{et} = Spec A^{et}` with the homomorphism `G → G^{et}`. Standard argument, written up here:

1. `A^{et} ⊆ A` is torsion free and finite over the PID `R`, hence free, hence flat; `A` and
   `A ⊗ A⁰` are free, hence flat.
2. `A^{et} = ker f` for `f = (id ⊗ π) ∘ Δ - (· ⊗ 1) : A → A ⊗ A⁰`. For `x ∈ A ⊗ A` with
   `(id ⊗ f)(x) = 0` and `(f ⊗ id)(x) = 0`, flatness (exactness of `A ⊗ -`, `A^{et} ⊗ -`,
   `- ⊗ A`, injectivity of `- ⊗ (A ⊗ A⁰)`) gives `x ∈ A^{et} ⊗ A^{et}`
   (`mem_range_map_of_lTensor_eq_zero_of_rTensor_eq_zero`).
3. For `a ∈ A^{et}`, coassociativity gives `(id ⊗ f)(Δ a) = 0` and cocommutativity then
   `(f ⊗ id)(Δ a) = 0`, so `Δ a ∈ A^{et} ⊗ A^{et}` (`comul_mem_range_incl2`).
4. Since `A^{et} ⊗ A^{et} → A ⊗ A` and `A^{et} ⊗ (A^{et} ⊗ A^{et}) → A ⊗ (A ⊗ A)` are injective
   (flatness), the Hopf algebra axioms for `A^{et}` follow from those of `A`.

## Main definitions and results

* `FFGroupScheme.comulEt`: the comultiplication `A^{et} → A^{et} ⊗ A^{et}` restricting `Δ`
  (`incl2_comulEt`);
* instances `HopfAlgebra R A^{et}`, `IsCocomm`, `Module.Free`, `Module.Finite`;
* `FFGroupScheme.etaleQuotient G = G^{et}` and `etaleQuotientHom : Hom G G^{et}` (the inclusion
  `A^{et} → A`, injective: `etaleQuotientHom_injective`);
* `connectedComponentHom_etaleQuotientHom`: the composite `G⁰ → G → G^{et}` is trivial;
* `etaleQuotientHom_bijective_of_isEtale`: for étale `G`, `G → G^{et}` is an isomorphism.

**Open**: `G^{et}` is étale; `A ⊗_{A^{et}} R ≅ A⁰`, i.e. exactness of `0 → G⁰ → G → G^{et} → 0`.
-/

noncomputable section

open Coalgebra HopfAlgebra IsLocalRing TensorProduct

namespace PadicHodge

universe u

section Flat

variable {R : Type*} [CommRing R] {B A N : Type*} [AddCommGroup B] [Module R B]
  [AddCommGroup A] [Module R A] [AddCommGroup N] [Module R N]

/-- Let `ι : B → A` be injective with image the kernel of `f : A → N`, all three flat. An element
`x ∈ A ⊗ A` killed by `id ⊗ f` and by `f ⊗ id` lies in `B ⊗ B`. -/
theorem mem_range_map_of_lTensor_eq_zero_of_rTensor_eq_zero [Module.Flat R B] [Module.Flat R A]
    [Module.Flat R N] {ι : B →ₗ[R] A} {f : A →ₗ[R] N} (hex : Function.Exact ι f)
    (hι : Function.Injective ι) {x : A ⊗[R] A} (h1 : f.lTensor A x = 0)
    (h2 : f.rTensor A x = 0) : x ∈ LinearMap.range (TensorProduct.map ι ι) := by
  obtain ⟨y, rfl⟩ := (Module.Flat.rTensor_exact A hex x).mp h2
  have hy : f.lTensor B y = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := N) ι hι
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply, h1]
  obtain ⟨z, rfl⟩ := (Module.Flat.lTensor_exact B hex y).mp hy
  exact ⟨z, by rw [← LinearMap.rTensor_comp_lTensor]; rfl⟩

end Flat

namespace FFGroupScheme

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  (G : FFGroupScheme R)

/-! ### `A^{et}` as a kernel -/

/-- `f : a ↦ (id ⊗ π)(Δ a) - a ⊗ 1`, whose kernel is `A^{et}`. -/
def etaleDefect : G.A →ₗ[R] G.A ⊗[R] G.connectedComponent.A :=
  G.coactConn.toLinearMap -
    (Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] G.connectedComponent.A).toLinearMap

theorem exact_etaleDefect :
    Function.Exact G.etaleInvariants.val.toLinearMap G.etaleDefect := by
  intro a
  simp only [etaleDefect, LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.includeLeft_apply]
  constructor
  · intro h
    exact ⟨⟨a, (G.mem_etaleInvariants).mpr h⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact (G.mem_etaleInvariants).mp b.2

/-- The translation-invariance of `a ∈ A^{et}` under `G⁰`, read on `Δ a`: `(id ⊗ f)(Δ a) = 0`
(coassociativity). -/
theorem lTensor_etaleDefect_comul {a : G.A} (ha : a ∈ G.etaleInvariants) :
    G.etaleDefect.lTensor G.A (comul (R := R) a) = 0 := by
  set π : G.A →ₗ[R] G.connectedComponent.A :=
    (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A).toLinearMap
  have h1 : ∀ x : (G.A ⊗[R] G.A) ⊗[R] G.A,
      (TensorProduct.map LinearMap.id π).lTensor G.A (TensorProduct.assoc R _ _ _ x) =
      TensorProduct.assoc R _ _ _ (π.lTensor _ x) := by
    intro x
    induction x with
    | zero => simp
    | tmul x z =>
      induction x with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ x : G.A ⊗[R] G.A,
      (Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] G.connectedComponent.A
        ).toLinearMap.lTensor G.A x = TensorProduct.assoc R _ _ _ (x ⊗ₜ 1) := by
    intro x
    induction x with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  rw [mem_etaleInvariants] at ha
  simp only [etaleDefect, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero, h2]
  have hc : G.coactConn.toLinearMap = TensorProduct.map LinearMap.id π ∘ₗ comul := rfl
  have ha' : π.lTensor G.A (comul (R := R) a) = a ⊗ₜ 1 := ha
  rw [hc, LinearMap.lTensor_comp, LinearMap.comp_apply, ← coassoc_apply, h1,
    ← LinearMap.comp_apply (π.lTensor _), LinearMap.lTensor_comp_rTensor,
    ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, ha', LinearMap.rTensor_tmul]

/-- By cocommutativity also `(f ⊗ id)(Δ a) = 0`. -/
theorem rTensor_etaleDefect_comul {a : G.A} (ha : a ∈ G.etaleInvariants) :
    G.etaleDefect.rTensor G.A (comul (R := R) a) = 0 := by
  have h : ∀ x : G.A ⊗[R] G.A, G.etaleDefect.rTensor G.A (TensorProduct.comm R _ _ x) =
      TensorProduct.comm R _ _ (G.etaleDefect.lTensor G.A x) := by
    intro x
    induction x with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← comm_comul (R := R) a, h, G.lTensor_etaleDefect_comul ha, map_zero]

/-- The antipode of `A^{et}`: the restriction of `S` (`antipode_mem_etaleInvariants`). -/
def antipodeEt : G.etaleInvariants →ₗ[R] G.etaleInvariants where
  toFun b := ⟨antipode R (b : G.A), G.antipode_mem_etaleInvariants b.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] theorem coe_antipodeEt (b : G.etaleInvariants) :
    (G.antipodeEt b : G.A) = antipode R (b : G.A) := rfl

/-! ### Finiteness and freeness of `A^{et}` -/

variable [IsDomain R] [IsPrincipalIdealRing R]

instance : Module.Finite R G.etaleInvariants := by
  have : IsNoetherian R G.A := isNoetherian_of_isNoetherianRing_of_finite R G.A
  exact Module.Finite.of_injective G.etaleInvariants.val.toLinearMap Subtype.val_injective

instance : Module.Free R G.etaleInvariants := Module.free_of_finite_type_torsion_free'

/-! ### The comultiplication of `A^{et}` -/

/-- The inclusion `A^{et} ⊗ A^{et} → A ⊗ A`. -/
abbrev incl2 : G.etaleInvariants ⊗[R] G.etaleInvariants →ₐ[R] G.A ⊗[R] G.A :=
  Algebra.TensorProduct.map G.etaleInvariants.val G.etaleInvariants.val

theorem incl2_injective : Function.Injective G.incl2 :=
  TensorProduct.map_injective_of_flat_flat (R := R) G.etaleInvariants.val.toLinearMap
    G.etaleInvariants.val.toLinearMap Subtype.val_injective Subtype.val_injective

theorem comul_mem_range_incl2 {a : G.A} (ha : a ∈ G.etaleInvariants) :
    comul (R := R) a ∈ G.incl2.range := by
  obtain ⟨z, hz⟩ := mem_range_map_of_lTensor_eq_zero_of_rTensor_eq_zero G.exact_etaleDefect
    Subtype.val_injective (G.lTensor_etaleDefect_comul ha) (G.rTensor_etaleDefect_comul ha)
  exact ⟨z, hz⟩

/-- The comultiplication `A^{et} → A^{et} ⊗ A^{et}`: the restriction of `Δ`. -/
def comulEt : G.etaleInvariants →ₐ[R] G.etaleInvariants ⊗[R] G.etaleInvariants :=
  (AlgEquiv.ofInjective G.incl2 G.incl2_injective).symm.toAlgHom.comp
    (((Bialgebra.comulAlgHom R G.A).comp G.etaleInvariants.val).codRestrict G.incl2.range
      fun b => G.comul_mem_range_incl2 b.2)

theorem incl2_comulEt (b : G.etaleInvariants) :
    G.incl2 (G.comulEt b) = comul (R := R) (b : G.A) := by
  rw [← AlgEquiv.ofInjective_apply _ G.incl2_injective]
  simp [comulEt]

/-- The counit of `A^{et}`: the restriction of `ε`. -/
def counitEt : G.etaleInvariants →ₐ[R] R :=
  (Bialgebra.counitAlgHom R G.A).comp G.etaleInvariants.val

/-- The inclusion `A^{et} ⊗ (A^{et} ⊗ A^{et}) → A ⊗ (A ⊗ A)`. -/
abbrev incl3 : G.etaleInvariants ⊗[R] (G.etaleInvariants ⊗[R] G.etaleInvariants) →ₗ[R]
    G.A ⊗[R] (G.A ⊗[R] G.A) :=
  TensorProduct.map G.etaleInvariants.val.toLinearMap G.incl2.toLinearMap

theorem incl3_injective : Function.Injective G.incl3 :=
  TensorProduct.map_injective_of_flat_flat (R := R) _ _ Subtype.val_injective G.incl2_injective

theorem coassoc_et :
    (Algebra.TensorProduct.assoc R R R G.etaleInvariants G.etaleInvariants
      G.etaleInvariants).toAlgHom.comp
      ((Algebra.TensorProduct.map G.comulEt (.id R G.etaleInvariants)).comp G.comulEt) =
    (Algebra.TensorProduct.map (.id R G.etaleInvariants) G.comulEt).comp G.comulEt := by
  set ι := G.etaleInvariants.val.toLinearMap
  have L1 : ∀ y : (G.etaleInvariants ⊗[R] G.etaleInvariants) ⊗[R] G.etaleInvariants,
      G.incl3 ((Algebra.TensorProduct.assoc R R R G.etaleInvariants G.etaleInvariants
        G.etaleInvariants).toAlgHom y) =
      TensorProduct.assoc R G.A G.A G.A (TensorProduct.map G.incl2.toLinearMap ι y) := by
    intro y
    induction y with
    | zero => simp
    | tmul x z =>
      induction x with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have L2 : ∀ y : G.etaleInvariants ⊗[R] G.etaleInvariants,
      TensorProduct.map G.incl2.toLinearMap ι
        (Algebra.TensorProduct.map G.comulEt (.id R G.etaleInvariants) y) =
      (comul (R := R) (A := G.A)).rTensor G.A (G.incl2 y) := by
    intro y
    induction y with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, incl2_comulEt, LinearMap.rTensor_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have L3 : ∀ y : G.etaleInvariants ⊗[R] G.etaleInvariants,
      G.incl3 (Algebra.TensorProduct.map (.id R G.etaleInvariants) G.comulEt y) =
      (comul (R := R) (A := G.A)).lTensor G.A (G.incl2 y) := by
    intro y
    induction y with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, incl2_comulEt, LinearMap.lTensor_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine AlgHom.ext fun b => G.incl3_injective ?_
  simp only [AlgHom.comp_apply]
  rw [L1, L2, L3, incl2_comulEt, coassoc_apply]

theorem rTensor_counit_et :
    (Algebra.TensorProduct.map G.counitEt (.id R G.etaleInvariants)).comp G.comulEt =
    (Algebra.TensorProduct.lid R G.etaleInvariants).symm := by
  have L : ∀ y : G.etaleInvariants ⊗[R] G.etaleInvariants,
      (Algebra.TensorProduct.lid R G.etaleInvariants
        (Algebra.TensorProduct.map G.counitEt (.id R G.etaleInvariants) y) : G.A) =
      TensorProduct.lid R G.A ((counit (R := R) (A := G.A)).rTensor G.A (G.incl2 y)) := by
    intro y
    induction y with
    | zero => simp
    | tmul a b => simp [counitEt]
    | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  refine AlgHom.ext fun b => (Algebra.TensorProduct.lid R G.etaleInvariants).injective ?_
  refine Subtype.val_injective ?_
  simp only [AlgHom.comp_apply]
  rw [L, incl2_comulEt, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]
  exact congrArg Subtype.val (AlgEquiv.apply_symm_apply _ b).symm

theorem lTensor_counit_et :
    (Algebra.TensorProduct.map (.id R G.etaleInvariants) G.counitEt).comp G.comulEt =
    (Algebra.TensorProduct.rid R R G.etaleInvariants).symm := by
  have L : ∀ y : G.etaleInvariants ⊗[R] G.etaleInvariants,
      (Algebra.TensorProduct.rid R R G.etaleInvariants
        (Algebra.TensorProduct.map (.id R G.etaleInvariants) G.counitEt y) : G.A) =
      TensorProduct.rid R G.A ((counit (R := R) (A := G.A)).lTensor G.A (G.incl2 y)) := by
    intro y
    induction y with
    | zero => simp
    | tmul a b => simp [counitEt]
    | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  refine AlgHom.ext fun b => (Algebra.TensorProduct.rid R R G.etaleInvariants).injective ?_
  refine Subtype.val_injective ?_
  simp only [AlgHom.comp_apply]
  rw [L, incl2_comulEt, lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]
  exact congrArg Subtype.val (AlgEquiv.apply_symm_apply _ b).symm

/-! ### The Hopf algebra `A^{et}` -/

instance instBialgebraEt : Bialgebra R G.etaleInvariants :=
  Bialgebra.ofAlgHom G.comulEt G.counitEt G.coassoc_et G.rTensor_counit_et G.lTensor_counit_et

theorem comul_et (b : G.etaleInvariants) : comul (R := R) b = G.comulEt b := rfl

theorem counit_et (b : G.etaleInvariants) : counit (R := R) b = counit (R := R) (b : G.A) := rfl

instance instHopfAlgebraEt : HopfAlgebra R G.etaleInvariants where
  __ := G.instBialgebraEt
  antipode := G.antipodeEt
  mul_antipode_rTensor_comul := by
    have L : ∀ y : G.etaleInvariants ⊗[R] G.etaleInvariants,
        (LinearMap.mul' R G.etaleInvariants (G.antipodeEt.rTensor _ y) : G.A) =
        LinearMap.mul' R G.A ((antipode R (A := G.A)).rTensor G.A (G.incl2 y)) := by
      intro y
      induction y with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
    ext b
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
    erw [L, comul_et, incl2_comulEt, mul_antipode_rTensor_comul_apply]
    rfl
  mul_antipode_lTensor_comul := by
    have L : ∀ y : G.etaleInvariants ⊗[R] G.etaleInvariants,
        (LinearMap.mul' R G.etaleInvariants (G.antipodeEt.lTensor _ y) : G.A) =
        LinearMap.mul' R G.A ((antipode R (A := G.A)).lTensor G.A (G.incl2 y)) := by
      intro y
      induction y with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
    ext b
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
    erw [L, comul_et, incl2_comulEt, mul_antipode_lTensor_comul_apply]
    rfl

instance instIsCocommEt : IsCocomm R G.etaleInvariants where
  comm_comp_comul := by
    have L : ∀ y : G.etaleInvariants ⊗[R] G.etaleInvariants,
        G.incl2 (TensorProduct.comm R _ _ y) = TensorProduct.comm R _ _ (G.incl2 y) := by
      intro y
      induction y with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    ext b
    refine G.incl2_injective ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [comul_et, L, incl2_comulEt, comm_comul]

/-! ### The étale quotient -/

/-- The étale quotient `G^{et} = Spec A^{et}` of `G`. -/
def etaleQuotient : FFGroupScheme R where
  A := G.etaleInvariants

/-- The homomorphism `G → G^{et}`: the inclusion `A^{et} → A`. -/
def etaleQuotientHom : Hom G G.etaleQuotient :=
  BialgHom.ofAlgHom (A := G.etaleInvariants) G.etaleInvariants.val (AlgHom.ext fun _ => rfl)
    (AlgHom.ext fun b => G.incl2_comulEt b)

@[simp] theorem etaleQuotientHom_apply (b : G.etaleQuotient.A) :
    G.etaleQuotientHom b = Subtype.val (b : G.etaleInvariants) := rfl

theorem etaleQuotientHom_injective : Function.Injective G.etaleQuotientHom :=
  Subtype.val_injective

/-- The composite `G⁰ → G → G^{et}` is trivial: `π(b) = ε(b)` for `b ∈ A^{et}`. -/
theorem connectedComponentHom_etaleQuotientHom (b : G.etaleQuotient.A) :
    G.connectedComponentHom (G.etaleQuotientHom b) = algebraMap R _ (counit (R := R) b) :=
  G.connectedComponentHom_of_mem_etaleInvariants (b : G.etaleInvariants).2

/-- For étale `G`, `G → G^{et}` is an isomorphism. -/
theorem etaleQuotientHom_bijective_of_isEtale (hG : G.IsEtale) :
    Function.Bijective G.etaleQuotientHom := by
  refine ⟨G.etaleQuotientHom_injective, fun a => ?_⟩
  have ha : a ∈ G.etaleInvariants := by
    rw [G.etaleInvariants_eq_top_of_isEtale hG]
    exact Algebra.mem_top
  exact ⟨(⟨a, ha⟩ : G.etaleInvariants), rfl⟩

/-- For connected `G`, `G^{et}` is trivial. -/
theorem order_etaleQuotient_of_isConnected (hG : G.IsConnected) : G.etaleQuotient.order = 1 := by
  have hinj : Function.Injective (algebraMap R G.A) := fun r s h => by
    simpa using congrArg (counit (R := R) (A := G.A)) h
  rw [order]
  change Module.finrank R G.etaleInvariants = 1
  rw [G.etaleInvariants_eq_bot hG]
  exact (Algebra.botEquivOfInjective hinj).toLinearEquiv.finrank_eq.trans (Module.finrank_self R)

end FFGroupScheme

end PadicHodge
