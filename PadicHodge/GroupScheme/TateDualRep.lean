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
* The equivariance is proved once for abstract `ℤ_p`-lattices (`baseChangeDualEquiv`,
  `baseChangeDualEquiv_gal`), which keeps elaboration cheap; it is applied to `G` over `ℚ_p`
  (`tateRepDualEquiv_gal`) and to `G` over a field `L ⊆ ℚ̄_p` (`tateRepDualEquiv_galOver`,
  `isHodgeTate_tateRepOver_dualPDiv`, `V_p G = tateRepOver` as a `G_L`-representation).
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

/-! ### Abstract form: base change of a perfect `ℤ_p`-pairing with a cyclotomic twist -/

section BaseChangeDual

variable {T T' : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Free ℤ_[p] T]
  [Module.Finite ℤ_[p] T] [AddCommGroup T'] [Module ℤ_[p] T']
  (B : T' ≃ₗ[ℤ_[p]] Module.Dual ℤ_[p] T)

/-- `ℚ_p ⊗ T' ≃ Hom_{ℚ_p}(ℚ_p ⊗ T, ℚ_p) ⊗ ℚ_p` from `B : T' ≃ Hom_{ℤ_p}(T, ℤ_p)`. -/
def baseChangeDualEquiv : (ℚ_[p] ⊗[ℤ_[p]] T') ≃ₗ[ℚ_[p]]
    Module.Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] T) ⊗[ℚ_[p]] ℚ_[p] :=
  (B.baseChange ℤ_[p] ℚ_[p] _ _) ≪≫ₗ
    (TensorProduct.isBaseChange ℤ_[p] T ℚ_[p]).toDualBaseChange ≪≫ₗ
    (TensorProduct.rid ℚ_[p] _).symm

theorem toDualBaseChange_tmul_tmul (a : ℚ_[p]) (f : Module.Dual ℤ_[p] T) (d : ℚ_[p]) (x : T) :
    (TensorProduct.isBaseChange ℤ_[p] T ℚ_[p]).toDualBaseChange (a ⊗ₜ f) (d ⊗ₜ x) =
      d * (a * algebraMap ℤ_[p] ℚ_[p] (f x)) := by
  have h := (TensorProduct.isBaseChange ℤ_[p] T ℚ_[p]).toDualBaseChange_tmul a f x
  have e : (d ⊗ₜ[ℤ_[p]] x : ℚ_[p] ⊗[ℤ_[p]] T) = d • (TensorProduct.mk ℤ_[p] ℚ_[p] _ 1 x) := by
    rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul]
  exact congrArg (d * ·) h

theorem baseChangeDualEquiv_tmul (c : ℚ_[p]) (y : T') (d : ℚ_[p]) (x : T) :
    TensorProduct.rid ℚ_[p] _ (baseChangeDualEquiv B (c ⊗ₜ y)) (d ⊗ₜ x) =
      d * (c * algebraMap ℤ_[p] ℚ_[p] (B y x)) := by
  simp only [baseChangeDualEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul]
  exact toDualBaseChange_tmul_tmul c _ d x

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- **Equivariance of `baseChangeDualEquiv`**: if `G_L` acts on `T`, `T'` through `g`, `g'`
and `B(g'_σ y)(g_σ x) = χ(σ) B(y)(x)`, then `ℚ_p ⊗ T' ≅ (ℚ_p ⊗ T)^∨ ⊗ ℚ_p(1)`
as `G_L`-representations. -/
theorem baseChangeDualEquiv_gal
    {ρ : Representation ℚ_[p] (K ≃ₐ[L] K) (ℚ_[p] ⊗[ℤ_[p]] T)}
    {ρ' : Representation ℚ_[p] (K ≃ₐ[L] K) (ℚ_[p] ⊗[ℤ_[p]] T')}
    (g : (K ≃ₐ[L] K) → T →ₗ[ℤ_[p]] T) (g' : (K ≃ₐ[L] K) → T' →ₗ[ℤ_[p]] T')
    (χ : (K ≃ₐ[L] K) → ℤ_[p])
    (hρ : ∀ σ, ρ σ = (g σ).baseChange ℚ_[p]) (hρ' : ∀ σ, ρ' σ = (g' σ).baseChange ℚ_[p])
    (hg : ∀ σ x, g σ (g σ⁻¹ x) = x) (hB : ∀ σ y x, B (g' σ y) (g σ x) = χ σ * B y x)
    (hχ : ∀ σ, chiL L 1 σ = algebraMap ℤ_[p] ℚ_[p] (χ σ)) (σ : K ≃ₐ[L] K) :
    (baseChangeDualEquiv B : _ →ₗ[ℚ_[p]] _) ∘ₗ ρ' σ =
      (ρ.dual.tprod (charRep L 1) σ) ∘ₗ baseChangeDualEquiv B := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c y
  apply (TensorProduct.rid ℚ_[p] _).injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro d x
  have hl : ρ' σ (c ⊗ₜ y) = c ⊗ₜ g' σ y := by rw [hρ']; rfl
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hl,
    baseChangeDualEquiv_tmul]
  set F := baseChangeDualEquiv B (c ⊗ₜ y)
  have hF : F = (TensorProduct.rid ℚ_[p] _ F) ⊗ₜ (1 : ℚ_[p]) := by
    conv_lhs => rw [← (TensorProduct.rid ℚ_[p] _).symm_apply_apply F]
    rfl
  rw [hF, Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.rid_tmul,
    charRep_apply, mul_one, LinearMap.smul_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply]
  have hr : ρ σ⁻¹ (d ⊗ₜ x) = d ⊗ₜ g σ⁻¹ x := by rw [hρ]; rfl
  rw [hr, baseChangeDualEquiv_tmul, hχ, smul_eq_mul]
  have hgal := hB σ y (g σ⁻¹ x)
  rw [hg] at hgal
  rw [hgal, map_mul]
  ring

end BaseChangeDual

section General

variable {F : Type} [Field F] [CharZero F] [Algebra F (PadicAlgCl p)] (G : PDivGroup F p)

/-- `T_p(G^∨) ≃ Hom_{ℤ_p}(T_p G, ℤ_p)` (Cartier pairing). -/
def tateDualEquiv : Additive (G.dualPDiv.TateModule K) ≃ₗ[ℤ_[p]]
    Module.Dual ℤ_[p] (Additive (G.TateModule K)) :=
  LinearEquiv.ofBijective G.tateDualHom G.tateDualHom_bijective

/-- **`V_p(G^∨) ≃ Hom_{ℚ_p}(V_p G, ℚ_p) ⊗ ℚ_p(1)`** as `ℚ_p`-vector spaces. -/
def tateRepDualEquiv : (ℚ_[p] ⊗[ℤ_[p]] Additive (G.dualPDiv.TateModule K)) ≃ₗ[ℚ_[p]]
    Module.Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (G.TateModule K)) ⊗[ℚ_[p]] ℚ_[p] :=
  baseChangeDualEquiv G.tateDualEquiv

theorem tateRepDualEquiv_tmul (c : ℚ_[p]) (y : Additive (G.dualPDiv.TateModule K))
    (d : ℚ_[p]) (x : Additive (G.TateModule K)) :
    TensorProduct.rid ℚ_[p] _ (G.tateRepDualEquiv (c ⊗ₜ y)) (d ⊗ₜ x) =
      d * (c * algebraMap ℤ_[p] ℚ_[p] (G.tateDualHom y x)) :=
  baseChangeDualEquiv_tmul _ c y d x

omit [CharZero F] in
theorem galLin_galLin_inv (σ : K ≃ₐ[F] K) (x : Additive (G.TateModule K)) :
    G.galLin σ (G.galLin σ⁻¹ x) = x := by
  change Additive.ofMul (G.galTate (σ * σ⁻¹) (Additive.toMul x)) = x
  rw [mul_inv_cancel, galTate_one]
  rfl

end General

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem chiL_one_eq (σ : K ≃ₐ[L] K) :
    chiL L 1 σ = algebraMap ℤ_[p] ℚ_[p] ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) := by
  rw [chiL, chiPow_apply, zpow_one]
  rfl

section Qp

variable (G : PDivGroup ℚ_[p] p)

/-- **`V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` as representations of `G_L`.** -/
theorem tateRepDualEquiv_gal (σ : K ≃ₐ[L] K) :
    (G.tateRepDualEquiv : _ →ₗ[ℚ_[p]] _) ∘ₗ G.dualPDiv.tateRep L σ =
      ((G.tateRep L).dual.tprod (charRep L 1) σ) ∘ₗ G.tateRepDualEquiv :=
  baseChangeDualEquiv_gal _ L (fun σ => G.galLin (σ.restrictScalars ℚ_[p]))
    (fun σ => G.dualPDiv.galLin (σ.restrictScalars ℚ_[p]))
    (fun σ => ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p])) (fun _ => rfl) (fun _ => rfl)
    (fun σ x => G.galLin_galLin_inv (σ.restrictScalars ℚ_[p]) x)
    (fun σ y x => G.tateDualHom_gal (σ.restrictScalars ℚ_[p]) y x) (chiL_one_eq L) σ

/-- **If `V_p G` is Hodge–Tate, so is `V_p(G^∨)`.** -/
theorem isHodgeTate_tateRep_dualPDiv [FiniteDimensional ℚ_[p] L]
    (h : IsHodgeTate (G.tateRep L)) : IsHodgeTate (G.dualPDiv.tateRep L) :=
  (isHodgeTate_iff_of_equiv G.tateRepDualEquiv (G.tateRepDualEquiv_gal L)).mpr
    (isHodgeTate_tprod _ _ (isHodgeTate_dual _ h) (isHodgeTate_charRep 1))

end Qp

section Over

variable {L} (G : PDivGroup L p)

/-- **`V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` as representations of `G_L`**, for `G` over `L` (e.g. the
generic fibre of a `p`-divisible group over `O_{K'}`, `L = K'`). -/
theorem tateRepDualEquiv_galOver (σ : K ≃ₐ[L] K) :
    (G.tateRepDualEquiv : _ →ₗ[ℚ_[p]] _) ∘ₗ G.dualPDiv.tateRepOver σ =
      (G.tateRepOver.dual.tprod (charRep L 1) σ) ∘ₗ G.tateRepDualEquiv :=
  baseChangeDualEquiv_gal _ L (fun σ => G.galLin σ) (fun σ => G.dualPDiv.galLin σ)
    (fun σ => ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p])) (fun _ => rfl) (fun _ => rfl)
    (fun σ x => G.galLin_galLin_inv σ x) (fun σ y x => G.tateDualHom_galOver σ y x)
    (chiL_one_eq L) σ

/-- **If `V_p G` is Hodge–Tate, so is `V_p(G^∨)`**, for `G` over `L`. -/
theorem isHodgeTate_tateRepOver_dualPDiv [FiniteDimensional ℚ_[p] L]
    (h : IsHodgeTate G.tateRepOver) : IsHodgeTate G.dualPDiv.tateRepOver :=
  (isHodgeTate_iff_of_equiv G.tateRepDualEquiv (G.tateRepDualEquiv_galOver)).mpr
    (isHodgeTate_tprod _ _ (isHodgeTate_dual _ h) (isHodgeTate_charRep 1))

end Over

end PDivGroup

end PadicHodge
