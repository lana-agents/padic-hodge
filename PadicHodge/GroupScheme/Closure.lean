/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Quotient
import PadicHodge.GroupScheme.BaseChange
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.Bialgebra.Quotient

/-!
# Scheme-theoretic closure of a closed subgroup of the generic fibre

Let `R` be a principal ideal domain with fraction field `K`, `G = Spec A` a finite flat group
scheme over `R` and `j : H̃ → G_K` a closed immersion of finite flat group schemes over `K`
(`j : K ⊗_R A ↠ C̃` surjective). The **scheme-theoretic closure** of `H̃` in `G` is
`H = Spec (A / I)`, `I = ker (A → C̃, a ↦ j(1 ⊗ a))` ([Hong, proof of Prop. 3.5.3]):

* `I` is a Hopf ideal (`closureIdeal_isHopfIdeal`): the counit, comultiplication and antipode
  of `A/I` are read off in `C̃`, using that `A/I ⊗_R A/I → C̃ ⊗_K C̃` is injective (flatness of
  `A/I` and `C̃` over `R`, and `C̃ ⊗_R C̃ = C̃ ⊗_K C̃` for the localization `K` of `R`);
* `FFGroupScheme.closure j`: `A/I` is finite free over `R` (torsion free: it embeds into the
  `K`-vector space `C̃`), with the closed immersion `closureHom j : H → G`;
* `closureGeneric`: `K ⊗_R A/I ≅ C̃` for a closed immersion `j` (`K` is flat over `R`, and the
  image of `A` spans `C̃`), so `|H| = |H̃|` (`order_closure`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, proof of Prop. 3.5.3.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {K : Type u} [Field K]
  [Algebra R K] [IsFractionRing R K] {G : FFGroupScheme R} {H : FFGroupScheme K}

/-- The `R`-algebra structure on `O(H̃)` through `K`. -/
abbrev algebraBase (H : FFGroupScheme K) : Algebra R H.A := Algebra.compHom H.A (algebraMap R K)

attribute [local instance] algebraBase

instance (H : FFGroupScheme K) : IsScalarTower R K H.A :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

namespace Hom

variable (j : Hom H (G.baseChange K))

/-- `A → C̃`, `a ↦ j(1 ⊗ a)`. -/
def closureMap : G.A →ₐ[R] H.A :=
  ((j : (G.baseChange K).A →ₐ[K] H.A).restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : G.A →ₐ[R] K ⊗[R] G.A)

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] in
theorem closureMap_apply (a : G.A) : j.closureMap a = j (1 ⊗ₜ a) := rfl

/-- The ideal `I = ker (A → C̃)` of the closure. -/
def closureIdeal : Ideal G.A := RingHom.ker j.closureMap

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] in
theorem mem_closureIdeal {a : G.A} : a ∈ j.closureIdeal ↔ j.closureMap a = 0 := RingHom.mem_ker

/-- The embedding `A/I → C̃`. -/
def closureEmb : G.A ⧸ j.closureIdeal →ₐ[R] H.A := Ideal.kerLiftAlg j.closureMap

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] in
theorem closureEmb_injective : Function.Injective j.closureEmb :=
  Ideal.kerLiftAlg_injective _

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] in
theorem closureEmb_mk (a : G.A) : j.closureEmb (Ideal.Quotient.mk _ a) = j.closureMap a := rfl

instance : Module.Flat R H.A := by
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  exact Module.Flat.trans R K H.A

instance : Module.IsTorsionFree R H.A :=
  Module.IsTorsionFree.comap (S := K) (algebraMap R K)
    (fun r hr => by
      exact IsRegular.of_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
        hr.ne_zero))
    fun _ _ => rfl

instance : Module.IsTorsionFree R (G.A ⧸ j.closureIdeal) :=
  Function.Injective.moduleIsTorsionFree j.closureEmb j.closureEmb_injective
    fun r x => map_smul j.closureEmb r x

instance : Module.Finite R (G.A ⧸ j.closureIdeal) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ R j.closureIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

instance : Module.Free R (G.A ⧸ j.closureIdeal) := Module.free_of_finite_type_torsion_free'

/-! ### The Hopf ideal -/

/-- The embedding of the `R`-module quotient `A ⧸ I` into `C̃`. -/
def closureEmbL : (G.A ⧸ j.closureIdeal.restrictScalars R) →ₗ[R] H.A :=
  (j.closureIdeal.restrictScalars R).liftQ j.closureMap.toLinearMap fun _ hx =>
    (j.mem_closureIdeal).mp hx

omit [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] in
theorem closureEmbL_injective : Function.Injective j.closureEmbL := by
  rw [← LinearMap.ker_eq_bot, closureEmbL, Submodule.ker_liftQ_eq_bot']
  ext x
  simp [mem_closureIdeal]

instance : Module.IsTorsionFree R (G.A ⧸ j.closureIdeal.restrictScalars R) :=
  Function.Injective.moduleIsTorsionFree j.closureEmbL j.closureEmbL_injective
    fun r x => map_smul j.closureEmbL r x

instance : Module.Finite R (G.A ⧸ j.closureIdeal.restrictScalars R) :=
  Module.Finite.of_surjective (j.closureIdeal.restrictScalars R).mkQ
    (Submodule.mkQ_surjective _)

instance : Module.Free R (G.A ⧸ j.closureIdeal.restrictScalars R) :=
  Module.free_of_finite_type_torsion_free'

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem moduleTensorEquiv_comul_closureMap (x : G.A) :
    IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K H.A H.A
      (comul (R := K) (j.closureMap x)) =
      TensorProduct.map j.closureMap.toLinearMap j.closureMap.toLinearMap (comul x) := by
  have hj : comul (R := K) (j (1 ⊗ₜ x)) = TensorProduct.map (j : (G.baseChange K).A →ₗ[K] H.A)
      (j : (G.baseChange K).A →ₗ[K] H.A) (comul (R := K) ((1 : K) ⊗ₜ[R] x)) :=
    (LinearMap.congr_fun (CoalgHomClass.map_comp_comul j) _).symm
  rw [closureMap_apply, hj, TensorProduct.comul_tmul]
  have h1 : comul (R := K) (1 : K) = 1 ⊗ₜ 1 := rfl
  rw [h1]
  induction comul (R := R) x with
  | zero => simp
  | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | tmul a b =>
    simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul]
    rfl

instance closureIdeal_isHopfIdeal : Ideal.IsHopfIdeal R j.closureIdeal where
  counit_eq_zero x hx := by
    have h := congrArg (counit (R := K) (A := H.A)) ((j.mem_closureIdeal).mp hx)
    rw [closureMap_apply, CoalgHomClass.counit_comp_apply, map_zero] at h
    have : algebraMap R K (counit (R := R) x) = 0 := by simpa using h
    exact (map_eq_zero_iff _ (IsFractionRing.injective R K)).mp this
  map_mkQ_comul_eq_zero x hx := by
    have hinj : Function.Injective (TensorProduct.map j.closureEmbL j.closureEmbL) :=
      TensorProduct.map_injective_of_flat_flat (R := R) _ _ j.closureEmbL_injective
        j.closureEmbL_injective
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have : j.closureEmbL ∘ₗ (j.closureIdeal.restrictScalars R).mkQ =
        j.closureMap.toLinearMap := rfl
    rw [this, ← moduleTensorEquiv_comul_closureMap, (j.mem_closureIdeal).mp hx, map_zero,
      map_zero]
  antipode_mem x hx := by
    rw [mem_closureIdeal] at hx ⊢
    rw [closureMap_apply]
    have : (1 : K) ⊗ₜ[R] antipode R x = antipode K ((1 : K) ⊗ₜ[R] x) := by
      simp [TensorProduct.antipode_def]
    rw [this, map_antipode, ← closureMap_apply, hx, map_zero]

/-! ### The closure as a finite flat group scheme -/

instance : IsCocomm R (G.A ⧸ j.closureIdeal) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    change TensorProduct.comm R _ _ (comul (R := R) (Ideal.Quotient.mk j.closureIdeal a)) =
      comul (R := R) (Ideal.Quotient.mk j.closureIdeal a)
    rw [Bialgebra.Quotient.comul_mk]
    have : ∀ w : G.A ⊗[R] G.A, TensorProduct.comm R _ _ (TensorProduct.map
        (Ideal.Quotient.mkₐ R j.closureIdeal).toLinearMap
        (Ideal.Quotient.mkₐ R j.closureIdeal).toLinearMap w) =
        TensorProduct.map (Ideal.Quotient.mkₐ R j.closureIdeal).toLinearMap
          (Ideal.Quotient.mkₐ R j.closureIdeal).toLinearMap (TensorProduct.comm R _ _ w) := by
      intro w
      induction w with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul a b => rfl
    rw [this, comm_comul]

/-- **The scheme-theoretic closure `H = Spec (A/I)` of `H̃` in `G`.** -/
def closure : FFGroupScheme R where
  A := G.A ⧸ j.closureIdeal

/-- The closed immersion `H → G`. -/
def closureHom : Hom j.closure G := Bialgebra.Quotient.mkBialgHom j.closureIdeal

theorem closureHom_surjective : Function.Surjective j.closureHom :=
  Ideal.Quotient.mk_surjective

/-! ### The generic fibre of the closure -/

/-- `K ⊗_R (A/I) → C̃`. -/
def closureGenericMap : K ⊗[R] (G.A ⧸ j.closureIdeal) →ₐ[K] H.A :=
  Algebra.TensorProduct.lift (Algebra.ofId K H.A) j.closureEmb fun _ _ => .all _ _

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem closureGenericMap_bijective (hj : Function.Surjective j) :
    Function.Bijective j.closureGenericMap := by
  constructor
  · have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
    have h1 : Function.Injective (j.closureEmb.toLinearMap.lTensor K) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ j.closureEmb_injective
    have h2 : ⇑j.closureGenericMap = IsLocalization.moduleLid (nonZeroDivisors R) K H.A ∘
        j.closureEmb.toLinearMap.lTensor K := by
      ext z
      induction z with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz, Function.comp_apply] at *
      | tmul k q =>
        simp only [closureGenericMap, Algebra.TensorProduct.lift_tmul, Function.comp_apply,
          LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply]
        change _ = TensorProduct.lid K H.A (k ⊗ₜ[K] j.closureEmb q)
        rw [TensorProduct.lid_tmul, Algebra.smul_def]
        rfl
    rw [h2]
    exact (LinearEquiv.injective _).comp h1
  · intro c
    obtain ⟨y, rfl⟩ := hj c
    suffices j y ∈ j.closureGenericMap.range from this
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => rw [map_add]; exact add_mem hy hz
    | tmul k a =>
      refine ⟨k ⊗ₜ Ideal.Quotient.mk _ a, ?_⟩
      change algebraMap K H.A k * j.closureEmb (Ideal.Quotient.mk _ a) = j (k ⊗ₜ a)
      have hk : (k ⊗ₜ[R] a : (G.baseChange K).A) =
          algebraMap K (G.baseChange K).A k * (1 ⊗ₜ a) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one]
        rfl
      rw [closureEmb_mk, closureMap_apply, hk, map_mul, AlgHomClass.commutes]

/-- `K ⊗_R O(H) ≅ O(H̃)`: the generic fibre of the closure is `H̃`. -/
def closureGeneric (hj : Function.Surjective j) :
    K ⊗[R] (G.A ⧸ j.closureIdeal) ≃ₐ[K] H.A :=
  AlgEquiv.ofBijective j.closureGenericMap (j.closureGenericMap_bijective hj)

/-- **`|H| = |H̃|`.** -/
theorem order_closure (hj : Function.Surjective j) : j.closure.order = H.order := by
  change Module.finrank R (G.A ⧸ j.closureIdeal) = Module.finrank K H.A
  rw [← (j.closureGeneric hj).toLinearEquiv.finrank_eq, Module.finrank_baseChange]

end Hom

end FFGroupScheme

end PadicHodge
