/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TateDual
import PadicHodge.HodgeTate.Dual
import PadicHodge.HodgeTate.Tensor
import PadicHodge.HodgeTate.Character

/-!
# `V_p(G^∨) ≅ V_p(G)^* (1)` as Galois representations

* `finrank_DHT_eq_of_equiv`, `isHodgeTate_iff_of_equiv`, `htWeights_eq_of_equiv`: the
  Hodge–Tate dimensions and weights are invariant under `G_L`-equivariant isomorphisms;
* `PDivGroup.tateRepDualEquiv : ℚ_p ⊗ T_p(G^∨) ≃ Hom_{ℚ_p}(V_p G, ℚ_p) ⊗ ℚ_p(1)`: the base change
  to `ℚ_p` of the `ℤ_p`-linear isomorphism `tateDualHom : T_p(G^∨) ≃ Hom_{ℤ_p}(T_p G, ℤ_p)`
  (`TateDual.lean`), composed with `ℚ_p ⊗ Hom_{ℤ_p}(T, ℤ_p) ≃ Hom_{ℚ_p}(ℚ_p ⊗ T, ℚ_p)`
  (`IsBaseChange.toDualBaseChange`, `T` free of finite rank);
* **`tateRepDualEquiv_gal`**: it intertwines `V_p(G^∨)` with `V_p(G)^∨ ⊗ ℚ_p(1)`
  ([Hong, Prop. 3.4.6], [Stix, Cor. 85]);
* **`isHodgeTate_tateRep_dualPDiv`**: if `V_p G` is Hodge–Tate, so is `V_p(G^∨)` (duals,
  tensor products and `ℚ_p(1)` are Hodge–Tate, `HodgeTate/Dual.lean`, `HodgeTate/Tensor.lean`,
  `HodgeTate/Character.lean`).
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

section Transport

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
  {V V' : Type*} [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup V'] [Module ℚ_[p] V']
  [FiniteDimensional ℚ_[p] V] [FiniteDimensional ℚ_[p] V']
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] (PadicAlgCl p)) V}
  {ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] (PadicAlgCl p)) V'}
  (e : V ≃ₗ[ℚ_[p]] V') (he : ∀ σ, (e : V →ₗ[ℚ_[p]] V') ∘ₗ ρ σ = ρ' σ ∘ₗ e)

omit [FiniteDimensional ℚ_[p] L] [FiniteDimensional ℚ_[p] V] [FiniteDimensional ℚ_[p] V'] in
include he in
theorem equiv_symm_comm (σ : K ≃ₐ[L] K) :
    (e.symm : V' →ₗ[ℚ_[p]] V) ∘ₗ ρ' σ = ρ σ ∘ₗ e.symm := by
  ext x
  apply e.injective
  have := LinearMap.congr_fun (he σ) (e.symm x)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply] at this ⊢
  rw [this]

omit [FiniteDimensional ℚ_[p] V] [FiniteDimensional ℚ_[p] V'] in
theorem finrank_DHT_le_of_injective {f : V →ₗ[ℚ_[p]] V'} (hf : ∀ σ, f ∘ₗ ρ σ = ρ' σ ∘ₗ f)
    (hfi : Function.Injective f) [FiniteDimensional ℚ_[p] V'] (q : ℤ) :
    finrank L (DHT ρ q) ≤ finrank L (DHT ρ' q) := by
  refine LinearMap.finrank_le_finrank_of_injective (f := DHTmap f hf q) fun a b h => ?_
  have h' := congrArg Subtype.val h
  simp only [DHTmap_apply] at h'
  exact Subtype.ext (tensorMap_injective (ρ := ρ) (ρ' := ρ') hfi h')

include he in
/-- **Hodge–Tate dimensions are invariant under equivariant isomorphisms.** -/
theorem finrank_DHT_eq_of_equiv (q : ℤ) : finrank L (DHT ρ q) = finrank L (DHT ρ' q) :=
  le_antisymm (finrank_DHT_le_of_injective he e.injective q)
    (finrank_DHT_le_of_injective (equiv_symm_comm e he) e.symm.injective q)

include he in
theorem isHodgeTate_iff_of_equiv : IsHodgeTate ρ ↔ IsHodgeTate ρ' := by
  have h1 : htDim ρ = htDim ρ' := by
    unfold htDim
    congr 1
    funext q
    exact finrank_DHT_eq_of_equiv e he q
  unfold IsHodgeTate
  rw [h1, e.finrank_eq]

include he in
theorem htWeights_eq_of_equiv : htWeights ρ = htWeights ρ' := by
  ext q
  rw [count_htWeights, count_htWeights, finrank_DHT_eq_of_equiv e he]

end Transport

namespace PDivGroup

variable (G : PDivGroup ℚ_[p] p) (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- `T_p(G^∨) ≃ Hom_{ℤ_p}(T_p G, ℤ_p)` (Cartier pairing). -/
def tateDualEquiv : Additive (G.dualPDiv.TateModule K) ≃ₗ[ℤ_[p]]
    Module.Dual ℤ_[p] (Additive (G.TateModule K)) :=
  LinearEquiv.ofBijective G.tateDualHom G.tateDualHom_bijective

/-- **`V_p(G^∨) ≃ Hom_{ℚ_p}(V_p G, ℚ_p) ⊗ ℚ_p(1)`** as `ℚ_p`-vector spaces. -/
def tateRepDualEquiv : (ℚ_[p] ⊗[ℤ_[p]] Additive (G.dualPDiv.TateModule K)) ≃ₗ[ℚ_[p]]
    Module.Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (G.TateModule K)) ⊗[ℚ_[p]] ℚ_[p] :=
  (G.tateDualEquiv.baseChange ℤ_[p] ℚ_[p] _ _) ≪≫ₗ
    (TensorProduct.isBaseChange ℤ_[p] (Additive (G.TateModule K)) ℚ_[p]).toDualBaseChange ≪≫ₗ
    (TensorProduct.rid ℚ_[p] _).symm

theorem toDualBaseChange_tmul_tmul (a : ℚ_[p]) (f : Module.Dual ℤ_[p] (Additive (G.TateModule K)))
    (d : ℚ_[p]) (x : Additive (G.TateModule K)) :
    (TensorProduct.isBaseChange ℤ_[p] (Additive (G.TateModule K)) ℚ_[p]).toDualBaseChange
      (a ⊗ₜ f) (d ⊗ₜ x) = d * (a * algebraMap ℤ_[p] ℚ_[p] (f x)) := by
  have h := (TensorProduct.isBaseChange ℤ_[p] (Additive (G.TateModule K))
    ℚ_[p]).toDualBaseChange_tmul a f x
  have e : (d ⊗ₜ[ℤ_[p]] x : ℚ_[p] ⊗[ℤ_[p]] Additive (G.TateModule K)) =
      d • (TensorProduct.mk ℤ_[p] ℚ_[p] _ 1 x) := by
    rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul]
  exact congrArg (d * ·) h

theorem tateRepDualEquiv_tmul (c : ℚ_[p]) (y : Additive (G.dualPDiv.TateModule K))
    (d : ℚ_[p]) (x : Additive (G.TateModule K)) :
    TensorProduct.rid ℚ_[p] _ (G.tateRepDualEquiv (c ⊗ₜ y)) (d ⊗ₜ x) =
      d * (c * algebraMap ℤ_[p] ℚ_[p] (G.tateDualHom y x)) := by
  simp only [tateRepDualEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul]
  exact G.toDualBaseChange_tmul_tmul c _ d x

theorem chiL_one_eq (σ : K ≃ₐ[L] K) :
    chiL L 1 σ = algebraMap ℤ_[p] ℚ_[p] ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) := by
  rw [chiL, chiPow_apply, zpow_one]
  rfl

/-- **`V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` as representations of `G_L`.** -/
theorem tateRepDualEquiv_gal (σ : K ≃ₐ[L] K) :
    (G.tateRepDualEquiv : _ →ₗ[ℚ_[p]] _) ∘ₗ G.dualPDiv.tateRep L σ =
      ((G.tateRep L).dual.tprod (charRep L 1) σ) ∘ₗ G.tateRepDualEquiv := by
  set σ' := σ.restrictScalars ℚ_[p]
  apply TensorProduct.AlgebraTensorModule.ext
  intro c y
  apply (TensorProduct.rid ℚ_[p] _).injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro d x
  -- left side
  have hl : (G.dualPDiv.tateRep L σ) (c ⊗ₜ y) = c ⊗ₜ G.dualPDiv.galLin σ' y := rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hl,
    tateRepDualEquiv_tmul]
  -- right side
  set F := G.tateRepDualEquiv (c ⊗ₜ y)
  have hF : F = (TensorProduct.rid ℚ_[p] _ F) ⊗ₜ (1 : ℚ_[p]) := by
    conv_lhs => rw [← (TensorProduct.rid ℚ_[p] _).symm_apply_apply F]
    rfl
  rw [hF, Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.rid_tmul,
    charRep_apply, mul_one, LinearMap.smul_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply]
  have hr : (G.tateRep L σ⁻¹) (d ⊗ₜ x) = d ⊗ₜ G.galLin σ'⁻¹ x := rfl
  rw [hr, tateRepDualEquiv_tmul, chiL_one_eq, smul_eq_mul]
  -- the twist
  have hgal := G.tateDualHom_gal σ' y (G.galLin σ'⁻¹ x)
  have hx : G.galLin σ' (G.galLin σ'⁻¹ x) = x := by
    change Additive.ofMul (G.galTate (σ' * σ'⁻¹) (Additive.toMul x)) = x
    rw [mul_inv_cancel, galTate_one]
    rfl
  rw [hx] at hgal
  rw [hgal, map_mul]
  ring

/-- **If `V_p G` is Hodge–Tate, so is `V_p(G^∨)`.** -/
theorem isHodgeTate_tateRep_dualPDiv [FiniteDimensional ℚ_[p] L]
    (h : IsHodgeTate (G.tateRep L)) : IsHodgeTate (G.dualPDiv.tateRep L) :=
  (isHodgeTate_iff_of_equiv G.tateRepDualEquiv (G.tateRepDualEquiv_gal L)).mpr
    (isHodgeTate_tprod _ _ (isHodgeTate_dual _ h) (isHodgeTate_charRep 1))

end PDivGroup

end PadicHodge
