/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DualTateGal
import PadicHodge.FormalGroup.DAlphaInj
import PadicHodge.FormalGroup.AlphaInjK
import PadicHodge.HodgeTate.Orthogonal
import PadicHodge.GroupScheme.TateDualRep

/-!
# `dα_K : t_G(ℚ_p) ↪ Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^Γ` as Hodge–Tate invariants ([Hong, (3.9)])

Let `P` be a `p`-divisible formal group law of dimension `d` over `ℤ_p` (`ZpD p`),
`G = P.pdivGroup` and `G_{ℚ_p}` its generic fibre (`genericFibre`). In the proof of
[Hong, Thm. 3.4.10] the map `dα : t_G(ℂ_p) → W = Hom_{ℤ_p}(T_p(G^∨), ℂ_p)` of
[Hong, Prop. 3.4.9] restricts to `dα_K : t_G(ℚ_p) = ℚ_p^d → W^Γ`, which is injective, whence
`dim W^Γ ≥ d` ([Hong, (3.9)]). This file packages `dα_K` with values in the Hodge–Tate
invariants of the Tate representations of `PadicHodge.HodgeTate`:

* `W^Γ = Hom_{ℚ_p}(V_p(G^∨), ℂ_p)^{G_L} = D_0(V_p(G^∨)^∨)` (`DHT (P.tateRepDual L).dual 0`),
  where `V_p(G^∨) = tateRep` of `(G_{ℚ_p})^∨`: for `z ∈ L^d`, the functional
  `y ↦ dα(z)(y)` on `T_p(G^∨)(O_{ℂ_p})` is `ℤ_p`-linear (`dalpha_mul`, `dalpha_zpSmul`); it is
  transported along `dualTateGenLinearEquiv` to `T_p(G_{ℚ_p}^∨)(ℚ̄_p)` (`dalphaZpLin`), extended
  to `V_p(G^∨) = ℚ_p ⊗ T_p` (`dalphaQpLin`) and to `ℂ_p ⊗ V_p(G^∨)` (`dalphaCpLin`), and
  identified with an element of `ℂ_p ⊗ V_p(G^∨)^∨` (`dualEquiv`, `dalphaTensor`).
  It is `G_L`-invariant (`dalphaTensor_mem`) by the Galois equivariance of `∂U_y/∂T_j(0)`
  (`dalpha_galDualGen`, from `charSeries_gal`) and of `dualTateGenEquiv`
  (`dualTateGenEquiv_gal`). This gives the `L`-linear map
  **`dalphaK : L^d → D_0(V_p(G^∨)^∨)`**.
* **`dalphaK_injective`**: `dα_K` is injective (`dalpha_injective_K`, [Hong, Prop. 3.4.9]);
  hence **`le_finrank_DHT_tateRepDual`**: `d ≤ dim_L W^{G_L}`, which is [Hong, (3.9)].
* All of this is done over a general coefficient ring `R` (`p ∈ 𝔪_R`, coefficients fixed by
  `G_L`) with generic fibre over a field `F ⊆ ℚ̄_p`, `G_L` acting through `ι : G_L → G_F` and a
  representation `ρ` (`dalphaKGen`, `dalphaKGen_injective`); `dalphaK` is the case
  `R = ℤ_p`, `F = ℚ_p`, `ρ = tateRep L`, and the case `R = O_{K'}`, `F = K' = L` is in
  `DAlphaHTOL.lean`.
* Transport to `V_p G`: from `V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` (`tateRepDualEquiv`,
  [Hong, Prop. 3.4.6]) we get `V_p(G^∨)^∨ ≅ V_p(G)` with `σ` twisted by `χ(σ)^{-1}`
  (`tateRepDualDualEquiv`, `tateRepDualDualEquiv_gal`); twisted intertwiners shift the
  Hodge–Tate index (`DHTtwistMap`), so `D_0(V_p(G^∨)^∨) ≅ D_{-1}(V_p G)`
  (`finrank_DHT_dual_tateRep_dualPDiv`). This gives **`dalphaKTwist : L^d → D_{-1}(V_p G)`**,
  injective (`dalphaKTwist_injective`), and **`le_finrank_DHT_tateRep`**:
  `d ≤ dim_L D_{-1}(V_p G)`, the form of (3.9) used in `bijective_of_finrank_le_add_fin`.
  The dual-dual step is proved for abstract representations (`dualDualEquiv`,
  `dualDualEquiv_gal`, `finrank_DHT_dualDual`) so that it also applies over `K'`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.4.6, Prop. 3.4.9, Thm. 3.4.10 (3.9).
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

/-! ### Twisted intertwiners shift the Hodge–Tate index -/

section Twist

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  {V V' : Type*} [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup V'] [Module ℚ_[p] V']
  {ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}
  {ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V'}

/-- If `ρ'(σ) ∘ f = χ(σ)^j f ∘ ρ(σ)`, then `σ (id ⊗ f)(w) = χ(σ)^j (id ⊗ f)(σ w)`. -/
theorem tensorMap_gal_twist (j : ℤ) (f : V →ₗ[ℚ_[p]] V')
    (hf : ∀ σ x, ρ' σ (f x) = chiL L j σ • f (ρ σ x)) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (w : CpTensor ρ) :
    σ • tensorMap (ρ' := ρ') f w =
      algebraMap ℚ_[p] ℂ_[p] (chiL L j σ) • tensorMap (ρ' := ρ') f (σ • w) := by
  change TensorProduct.map (galCpLin L σ) (ρ' σ) (f.lTensor ℂ_[p] w) =
    algebraMap ℚ_[p] ℂ_[p] (chiL L j σ) •
      f.lTensor ℂ_[p] (TensorProduct.map (galCpLin L σ) (ρ σ) w)
  induction (w : ℂ_[p] ⊗[ℚ_[p]] V) using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, hf, TensorProduct.tmul_smul]
    exact (algebraMap_smul ℂ_[p] _ _).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]

variable [FiniteDimensional ℚ_[p] L]

theorem tensorMap_mem_DHT_twist (j : ℤ) (f : V →ₗ[ℚ_[p]] V')
    (hf : ∀ σ x, ρ' σ (f x) = chiL L j σ • f (ρ σ x)) {q q' : ℤ} (hq : q' = q - j)
    {w : CpTensor ρ} (hw : w ∈ DHT ρ q) : tensorMap (ρ' := ρ') f w ∈ DHT ρ' q' := by
  intro σ
  rw [tensorMap_gal_twist j f hf σ w, hw σ, psi_smul_eq, psi_smul_eq, tensorMap_smul, smul_smul,
    ← map_mul, ← chiL_add, hq, show j + -q = -(q - j) by ring]

/-- **A twisted intertwiner `V → V'` (`ρ'(σ) f = χ(σ)^j f ρ(σ)`) maps `D_q(V)` to
`D_{q-j}(V')`.** -/
def DHTtwistMap (j : ℤ) (f : V →ₗ[ℚ_[p]] V') (hf : ∀ σ x, ρ' σ (f x) = chiL L j σ • f (ρ σ x))
    {q q' : ℤ} (hq : q' = q - j) : DHT ρ q →ₗ[L] DHT ρ' q' where
  toFun w := ⟨tensorMap f w, tensorMap_mem_DHT_twist j f hf hq w.2⟩
  map_add' w w' := Subtype.ext (tensorMap_add f (w : CpTensor ρ) w')
  map_smul' a w := Subtype.ext (tensorMap_smulL f a (w : CpTensor ρ))

theorem DHTtwistMap_injective (j : ℤ) {f : V →ₗ[ℚ_[p]] V'}
    (hf : ∀ σ x, ρ' σ (f x) = chiL L j σ • f (ρ σ x)) {q q' : ℤ} (hq : q' = q - j)
    (hfi : Function.Injective f) : Function.Injective (DHTtwistMap j f hf hq) :=
  fun _ _ h => Subtype.ext (tensorMap_injective (ρ := ρ) (ρ' := ρ') hfi (congrArg Subtype.val h))

end Twist

/-! ### `V_p(G^∨)^∨ ≅ V_p(G)(-1)` -/

section DualDual

variable {p : ℕ} [hp : Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))

local notation "K" => PadicAlgCl p

theorem rid_tprod_charRep {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)
    (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (u : Dual ℚ_[p] V ⊗[ℚ_[p]] ℚ_[p]) :
    TensorProduct.rid ℚ_[p] _ ((ρ.dual.tprod (charRep L 1) τ) u) =
      chiL L 1 τ • ρ.dual τ (TensorProduct.rid ℚ_[p] _ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul ℓ a =>
    simp only [Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.rid_tmul,
      charRep_apply, map_smul, mul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-! The abstract form: an equivariant `e : V ≅ W^∨ ⊗ ℚ_p(1)` gives `V^∨ ≅ W(-1)`. Stated for
abstract representations (cheap to elaborate), then applied to `tateRepDualEquiv`. -/

section Abstract

variable {L} {V W : Type*} [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W]
  [FiniteDimensional ℚ_[p] W]
  {ρV : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V}
  {ρW : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) W}
  (e : V ≃ₗ[ℚ_[p]] Dual ℚ_[p] W ⊗[ℚ_[p]] ℚ_[p])

/-- `V^∨ ≅ W`, the dual of `e : V ≅ W^∨ ⊗ ℚ_p` composed with `W ≅ W^{∨∨}`. -/
def dualDualEquiv : Dual ℚ_[p] V ≃ₗ[ℚ_[p]] W :=
  (e ≪≫ₗ TensorProduct.rid ℚ_[p] _).symm.dualMap ≪≫ₗ (Module.evalEquiv ℚ_[p] W).symm

theorem dualDualEquiv_symm_apply (v : W) (w : V) :
    (dualDualEquiv e).symm v w = TensorProduct.rid ℚ_[p] _ (e w) v :=
  rfl

variable (he : ∀ σ, (e : V →ₗ[ℚ_[p]] _) ∘ₗ ρV σ = (ρW.dual.tprod (charRep L 1) σ) ∘ₗ e)
include he

theorem dualDualEquiv_symm_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (v : W) :
    (dualDualEquiv e).symm (ρW σ v) = chiL L 1 σ • ρV.dual σ ((dualDualEquiv e).symm v) := by
  refine LinearMap.ext fun w => ?_
  have he' : e (ρV σ⁻¹ w) = (ρW.dual.tprod (charRep L 1) σ⁻¹) (e w) :=
    LinearMap.congr_fun (he σ⁻¹) w
  rw [LinearMap.smul_apply, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, dualDualEquiv_symm_apply, dualDualEquiv_symm_apply, he',
    rid_tprod_charRep, LinearMap.smul_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ← chiL_mul, mul_inv_cancel, chiL_one, one_mul]

/-- **`V^∨ ≅ W(-1)`**: `σ (F x) = χ(σ) F(σ x)` for `F = dualDualEquiv e`. -/
theorem dualDualEquiv_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : Dual ℚ_[p] V) :
    ρW σ (dualDualEquiv e x) = chiL L 1 σ • dualDualEquiv e (ρV.dual σ x) := by
  apply (dualDualEquiv e).symm.injective
  rw [map_smul, LinearEquiv.symm_apply_apply, dualDualEquiv_symm_gal e he,
    LinearEquiv.symm_apply_apply]

theorem dualDualEquiv_symm_gal' (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (v : W) :
    ρV.dual σ ((dualDualEquiv e).symm v) =
      chiL L (-1) σ • (dualDualEquiv e).symm (ρW σ v) := by
  rw [dualDualEquiv_symm_gal e he, smul_smul, ← chiL_add, neg_add_cancel, chiL_zero, one_smul]

variable [FiniteDimensional ℚ_[p] L]

/-- `D_0(V^∨) → D_{-1}(W)`, induced by `dualDualEquiv e`. -/
def DHTdualDualMap : DHT ρV.dual 0 →ₗ[L] DHT ρW (-1) :=
  DHTtwistMap 1 (dualDualEquiv e : _ →ₗ[ℚ_[p]] _) (fun σ x => dualDualEquiv_gal e he σ x)
    (by norm_num)

theorem DHTdualDualMap_injective : Function.Injective (DHTdualDualMap e he) :=
  DHTtwistMap_injective 1 _ _ (dualDualEquiv e).injective

/-- **`dim D_0(V^∨) = dim D_{-1}(W)`.** -/
theorem finrank_DHT_dualDual [FiniteDimensional ℚ_[p] V] :
    finrank L (DHT ρV.dual 0) = finrank L (DHT ρW (-1)) :=
  le_antisymm (LinearMap.finrank_le_finrank_of_injective (DHTdualDualMap_injective e he))
    (LinearMap.finrank_le_finrank_of_injective
      (DHTtwistMap_injective (-1) (f := ((dualDualEquiv e).symm : _ →ₗ[ℚ_[p]] _))
        (fun σ v => dualDualEquiv_symm_gal' e he σ v) (q := -1) (q' := 0) (by norm_num)
        (dualDualEquiv e).symm.injective))

end Abstract

namespace PDivGroup

variable (H : PDivGroup ℚ_[p] p)

/-- **`V_p(G^∨)^∨ ≅ V_p G`** (as `ℚ_p`-vector spaces), the dual of
`tateRepDualEquiv : V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` composed with `V_p G ≅ V_p(G)^{∨∨}`. -/
def tateRepDualDualEquiv :
    Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (H.dualPDiv.TateModule (PadicAlgCl p))) ≃ₗ[ℚ_[p]]
      ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule (PadicAlgCl p)) :=
  dualDualEquiv H.tateRepDualEquiv

/-- **`V_p(G^∨)^∨ ≅ V_p(G)(-1)`**: `σ (F x) = χ(σ) F(σ x)` for `F = tateRepDualDualEquiv`. -/
theorem tateRepDualDualEquiv_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (x : Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (H.dualPDiv.TateModule K))) :
    H.tateRep L σ (H.tateRepDualDualEquiv x) =
      chiL L 1 σ • H.tateRepDualDualEquiv ((H.dualPDiv.tateRep L).dual σ x) :=
  dualDualEquiv_gal _ (H.tateRepDualEquiv_gal L) σ x

variable [FiniteDimensional ℚ_[p] L]

/-- `D_0(V_p(G^∨)^∨) → D_{-1}(V_p G)`, induced by `tateRepDualDualEquiv`. -/
def DHTdualTateEquivMap :
    DHT (H.dualPDiv.tateRep L).dual 0 →ₗ[L] DHT (H.tateRep L) (-1) :=
  DHTdualDualMap H.tateRepDualEquiv (H.tateRepDualEquiv_gal L)

theorem DHTdualTateEquivMap_injective : Function.Injective (H.DHTdualTateEquivMap L) :=
  DHTdualDualMap_injective _ _

/-- **`dim D_0(V_p(G^∨)^∨) = dim D_{-1}(V_p G)`.** -/
theorem finrank_DHT_dual_tateRep_dualPDiv :
    finrank L (DHT (H.dualPDiv.tateRep L).dual 0) = finrank L (DHT (H.tateRep L) (-1)) :=
  finrank_DHT_dualDual _ (H.tateRepDualEquiv_gal L)

end PDivGroup

end DualDual

/-! ### `dα_K` over a general coefficient ring -/

/-- `ℤ_p` acts uniformly continuously on `ℚ̄_p` (through `ℚ_p`); this makes `ℂ_p` a
`ℤ_p`-module with `IsScalarTower ℤ_p ℚ_p ℂ_p` (completion instances). -/
instance uniformContinuousConstSMul_padicInt_padicAlgCl {p : ℕ} [Fact p.Prime] :
    UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p) :=
  ⟨fun a => by
    have h : (fun x : PadicAlgCl p => a • x) = fun x => algebraMap ℤ_[p] ℚ_[p] a • x :=
      funext fun x => (algebraMap_smul ℚ_[p] a x).symm
    rw [h]
    exact uniformContinuous_const_smul _⟩

namespace PDivFGL

open PDivGroup IsLocalRing

section Gen

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R) {d : ℕ} (P : PDivFGL R d p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

omit [UniformSpace R] [DiscreteUniformity R] in
theorem dalpha_add_left (z z' : Fin d → ℂ_[p]) (y : P.pdivGroup.DualTate (OCd p)) :
    P.dalpha hpm (z + z') y = P.dalpha hpm z y + P.dalpha hpm z' y := by
  simp only [dalpha, Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [UniformSpace R] [DiscreteUniformity R] in
theorem dU_galDualGen (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hR : ∀ r : R, autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r)
    (y : P.pdivGroup.DualTate (OCd p)) (j : Fin d) :
    ((OCd.toOC (P.dU hpm (P.pdivGroup.galDualGen σ hR y) j) : OC p) : ℂ_[p]) =
      autCp σ ((OCd.toOC (P.dU hpm y j) : OC p) : ℂ_[p]) := by
  rw [← P.galDual_eq_galDualGen σ hR, dU, dU, charSeries_gal, MvPowerSeries.coeff_map]
  exact galS_apply σ hR _

omit [UniformSpace R] [DiscreteUniformity R] in
/-- **Galois equivariance of `dα`** ([Hong, Prop. 3.4.9]): for `z` fixed by `σ`,
`dα(z)(σ y) = σ(dα(z)(y))`. -/
theorem dalpha_galDualGen (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hR : ∀ r : R, autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r)
    {z : Fin d → ℂ_[p]} (hz : ∀ j, autCp σ (z j) = z j) (y : P.pdivGroup.DualTate (OCd p)) :
    P.dalpha hpm z (P.pdivGroup.galDualGen σ hR y) = autCp σ (P.dalpha hpm z y) := by
  rw [dalpha, dalpha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hz, dU_galDualGen]

variable (F : Type) [Field F] [CharZero F] [Algebra R F] [Algebra F (PadicAlgCl p)]
  [Algebra R (PadicAlgCl p)] [IsScalarTower R F (PadicAlgCl p)]
  (hRF : ∀ r : R, ((algebraMap R (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
    ((algebraMap R (OC p) r : OC p) : ℂ_[p]))

/-- `T_p((G_F)^∨)(ℚ̄_p)` for the generic fibre `G_F` of `G = F[p^∞]`, as an additive
`ℤ_p`-module. -/
abbrev TateDualF : Type :=
  Additive ((P.pdivGroup.baseChange F).dualPDiv.TateModule (PadicAlgCl p))

/-- `dα(z)` as a `ℤ_p`-linear functional on `T_p(G_F^∨)(ℚ̄_p)` (via `dualTateGenLinearEquiv`). -/
def dalphaZpLin (z : Fin d → ℂ_[p]) : P.TateDualF F →ₗ[ℤ_[p]] ℂ_[p] where
  toFun t := P.dalpha hpm z
    (Additive.toMul ((P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF).symm t))
  map_add' t t' := by simp only [map_add, toMul_add, dalpha_mul]
  map_smul' a t := by
    simp only [RingHom.id_apply]
    have h := P.dalpha_zpSmul hpm z a
      (Additive.toMul ((P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF).symm t))
    rw [ofMul_toMul] at h
    rw [map_smul, h]
    exact algebraMap_smul ℚ_[p] a _

/-- `dα(z)` as a `ℚ_p`-linear functional on `V_p(G_F^∨) = ℚ_p ⊗ T_p(G_F^∨)`. -/
def dalphaQpLin (z : Fin d → ℂ_[p]) : ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F →ₗ[ℚ_[p]] ℂ_[p] :=
  (P.dalphaZpLin hpm F hRF z).liftBaseChange ℚ_[p]

/-- `dα(z)` as a `ℂ_p`-linear functional on `ℂ_p ⊗ V_p(G_F^∨)`. -/
def dalphaCpLin (z : Fin d → ℂ_[p]) :
    Dual ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)) :=
  (P.dalphaQpLin hpm F hRF z).liftBaseChange ℂ_[p]

theorem dalphaQpLin_tmul (z : Fin d → ℂ_[p]) (a : ℚ_[p]) (t : P.TateDualF F) :
    P.dalphaQpLin hpm F hRF z (a ⊗ₜ t) = a • P.dalpha hpm z
      (Additive.toMul ((P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF).symm t)) :=
  rfl

theorem dalphaCpLin_tmul (z : Fin d → ℂ_[p]) (c : ℂ_[p])
    (v : ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F) :
    P.dalphaCpLin hpm F hRF z (c ⊗ₜ v) = c * P.dalphaQpLin hpm F hRF z v :=
  rfl

theorem dalphaCpLin_add (z z' : Fin d → ℂ_[p]) :
    P.dalphaCpLin hpm F hRF (z + z') =
      P.dalphaCpLin hpm F hRF z + P.dalphaCpLin hpm F hRF z' := by
  have hQ : P.dalphaQpLin hpm F hRF (z + z') =
      P.dalphaQpLin hpm F hRF z + P.dalphaQpLin hpm F hRF z' := by
    refine TensorProduct.AlgebraTensorModule.ext fun a t => ?_
    rw [LinearMap.add_apply, dalphaQpLin_tmul, dalphaQpLin_tmul, dalphaQpLin_tmul,
      dalpha_add_left, smul_add]
  refine TensorProduct.AlgebraTensorModule.ext fun c v => ?_
  rw [LinearMap.add_apply, dalphaCpLin_tmul, dalphaCpLin_tmul, dalphaCpLin_tmul, hQ,
    LinearMap.add_apply, mul_add]

theorem dalphaCpLin_smul (c : ℂ_[p]) (z : Fin d → ℂ_[p]) :
    P.dalphaCpLin hpm F hRF (fun j => c * z j) = c • P.dalphaCpLin hpm F hRF z := by
  have hQ : P.dalphaQpLin hpm F hRF (fun j => c * z j) = c • P.dalphaQpLin hpm F hRF z := by
    refine TensorProduct.AlgebraTensorModule.ext fun a t => ?_
    rw [LinearMap.smul_apply, dalphaQpLin_tmul, dalphaQpLin_tmul, dalpha_smul, smul_comm,
      smul_eq_mul]
  refine TensorProduct.AlgebraTensorModule.ext fun c' v => ?_
  rw [LinearMap.smul_apply, dalphaCpLin_tmul, dalphaCpLin_tmul, hQ, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, mul_left_comm]

/-! The Galois action: `G_L` acts on `V_p(G_F^∨)` through `ι : G_L → G_F` (`σ ↦ σ|_{ℚ_p}` for
`F = ℚ_p`, the identity for `F = L`) by a representation `ρ` with
`ρ(σ)(a ⊗ t) = a ⊗ (ι σ) t`. -/

variable [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)]
  (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (hRL : FGL.GalFixedOver p R L)
  (ι : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → (PadicAlgCl p ≃ₐ[F] PadicAlgCl p))
  (hι : ∀ σ x, ι σ x = σ x)
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F))
  (hρ : ∀ σ (a : ℚ_[p]) (t : P.TateDualF F),
    ρ σ (a ⊗ₜ t) = a ⊗ₜ (P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) t)

include hRL hι in
theorem dalphaZpLin_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) {z : Fin d → ℂ_[p]}
    (hz : ∀ j, galCp L σ (z j) = z j) (t : P.TateDualF F) :
    P.dalphaZpLin hpm F hRF z ((P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) t) =
      galCp L σ (P.dalphaZpLin hpm F hRF z t) := by
  set E := P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF
  set σ' := AlgEquiv.restrictScalarsHom ℚ_[p] σ
  have e : (ι σ).restrictScalars ℚ_[p] = σ' := AlgEquiv.ext (hι σ)
  have hR' : ∀ r : R, autCp ((ι σ).restrictScalars ℚ_[p])
      ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r := by
    rw [e]
    exact hRL σ
  have hE : E.symm ((P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) t) =
      Additive.ofMul (P.pdivGroup.galDualGen σ' (hRL σ) (Additive.toMul (E.symm t))) := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = Additive.ofMul (P.pdivGroup.dualTateGenEquiv (F := F) hRF
      (P.pdivGroup.galDualGen σ' (hRL σ) (Additive.toMul (E.symm t))))
    rw [← P.pdivGroup.galDualGen_congr e hR' (hRL σ), dualTateGenEquiv_gal]
    have h1 : P.pdivGroup.dualTateGenEquiv (F := F) hRF (Additive.toMul (E.symm t)) =
        Additive.toMul t :=
      (P.pdivGroup.dualTateGenLinearEquiv_apply hRF _).symm.trans
        (congrArg Additive.toMul (E.apply_symm_apply t))
    rw [h1]
    rfl
  change P.dalpha hpm z (Additive.toMul (E.symm _)) =
    galCp L σ (P.dalpha hpm z (Additive.toMul (E.symm t)))
  rw [hE]
  exact P.dalpha_galDualGen hpm σ' (hRL σ) hz _

include hRL hι hρ in
theorem dalphaQpLin_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) {z : Fin d → ℂ_[p]}
    (hz : ∀ j, galCp L σ (z j) = z j) (v : ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F) :
    P.dalphaQpLin hpm F hRF z (ρ σ v) = galCp L σ (P.dalphaQpLin hpm F hRF z v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    rw [hρ]
    change a • P.dalphaZpLin hpm F hRF z _ = galCp L σ (a • P.dalphaZpLin hpm F hRF z t)
    rw [galCp_smul, P.dalphaZpLin_gal hpm F hRF L hRL ι hι σ hz]
  | add x y hx hy => simp only [map_add, hx, hy]

include hRL hι hρ in
theorem dalphaCpLin_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) {z : Fin d → ℂ_[p]}
    (hz : ∀ j, galCp L σ (z j) = z j)
    (u : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)) :
    P.dalphaCpLin hpm F hRF z (TensorProduct.map (galCpLin L σ) (ρ σ) u) =
      galCp L σ (P.dalphaCpLin hpm F hRF z u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.map_tmul, dalphaCpLin_tmul, dalphaCpLin_tmul, galCpLin_apply,
      P.dalphaQpLin_gal hpm F hRF L hRL ι hι ρ hρ σ hz, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R]
  [Algebra R (OC p)] [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)] in
theorem galCp_algebraMap_L (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (a : L) :
    galCp L σ (algebraMap L ℂ_[p] a) = algebraMap L ℂ_[p] a := by
  rw [algebraMap_L_cp, galCp_coe]
  exact congrArg (fun x : PadicAlgCl p => (x : ℂ_[p])) (σ.commutes a)

/-- The element of `ℂ_p ⊗ V_p(G_F^∨)^∨` corresponding to `y ↦ dα(z)(y)`. -/
def dalphaTensor (z : Fin d → ℂ_[p]) : CpTensor ρ.dual :=
  (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm (P.dalphaCpLin hpm F hRF z)

variable [FiniteDimensional ℚ_[p] L]

include hRL hι hρ in
/-- **`dα(z)` is `G_L`-invariant** for `z` fixed by `G_L`: it lies in
`D_0(V_p(G_F^∨)^∨) = Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^{G_L}`. -/
theorem dalphaTensor_mem {z : Fin d → ℂ_[p]} (hz : ∀ σ j, galCp L σ (z j) = z j) :
    P.dalphaTensor hpm F hRF L ρ z ∈ DHT ρ.dual 0 := by
  intro σ
  rw [(htSetup L).ψ_zero, one_smul]
  change TensorProduct.map (galCpLin L σ) (ρ.dual σ) (P.dalphaTensor hpm F hRF L ρ z) =
    P.dalphaTensor hpm F hRF L ρ z
  apply (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).injective
  refine LinearMap.ext fun u => ?_
  have hu := tensorAct_inv_cancel ρ σ u
  rw [← hu, dualEquiv_gal, dalphaTensor, LinearEquiv.apply_symm_apply,
    P.dalphaCpLin_gal hpm F hRF L hRL ι hι ρ hρ σ (hz σ)]

/-- **`dα_K : L^d → D_0(V_p(G_F^∨)^∨) = Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^{G_L}`**,
`z ↦ (y ↦ dα(z)(y))` ([Hong, Prop. 3.4.9, Thm. 3.4.10]). -/
def dalphaKGen : (Fin d → L) →ₗ[L] DHT ρ.dual 0 where
  toFun z := ⟨P.dalphaTensor hpm F hRF L ρ (fun j => algebraMap L ℂ_[p] (z j)),
    P.dalphaTensor_mem hpm F hRF L hRL ι hι ρ hρ fun σ j => galCp_algebraMap_L L σ (z j)⟩
  map_add' z z' := Subtype.ext (by
    change (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm (P.dalphaCpLin hpm F hRF _) =
      (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm (P.dalphaCpLin hpm F hRF _) +
        (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm (P.dalphaCpLin hpm F hRF _)
    rw [← map_add, ← dalphaCpLin_add]
    congr 2
    funext j
    simp only [Pi.add_apply, map_add])
  map_smul' a z := Subtype.ext (by
    change (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm (P.dalphaCpLin hpm F hRF _) =
      algebraMap L ℂ_[p] a •
        (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm (P.dalphaCpLin hpm F hRF _)
    rw [← map_smul, ← dalphaCpLin_smul]
    congr 2
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul])

theorem dalphaKGen_apply (z : Fin d → L) :
    ((P.dalphaKGen hpm F hRF L hRL ι hι ρ hρ z : DHT ρ.dual 0) : CpTensor ρ.dual) =
      P.dalphaTensor hpm F hRF L ρ (fun j => algebraMap L ℂ_[p] (z j)) :=
  rfl

/-- **`dα_K` is injective** ([Hong, Prop. 3.4.9], `dalpha_injective_K`). -/
theorem dalphaKGen_injective
    (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) :
    Function.Injective (P.dalphaKGen hpm F hRF L hRL ι hι ρ hρ) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  have h0 : P.dalphaCpLin hpm F hRF (fun j => algebraMap L ℂ_[p] (z j)) = 0 := by
    have h := congrArg Subtype.val hz
    rw [dalphaKGen_apply] at h
    apply (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualF F)).symm.injective
    rw [map_zero]
    exact h
  refine P.dalpha_injective_K hpm hR L hRL z fun y => ?_
  have h := LinearMap.congr_fun h0
    ((1 : ℂ_[p]) ⊗ₜ ((1 : ℚ_[p]) ⊗ₜ
      P.pdivGroup.dualTateGenLinearEquiv (F := F) hRF (Additive.ofMul y)))
  rw [dalphaCpLin_tmul, dalphaQpLin_tmul, LinearEquiv.symm_apply_apply, one_smul, one_mul,
    LinearMap.zero_apply, toMul_ofMul] at h
  exact h

end Gen

/-! ### `R = ℤ_p`, `F = ℚ_p` -/

section Zp

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} (P : PDivFGL (ZpD p) d p)

/-- The generic fibre `G_{ℚ_p}` of `G = F[p^∞]`. -/
abbrev genericFibre : PDivGroup ℚ_[p] p := P.pdivGroup.baseChange ℚ_[p]

/-- `T_p(G_{ℚ_p}^∨)(ℚ̄_p)`, as an additive `ℤ_p`-module. -/
abbrev TateDualQp : Type := Additive (P.genericFibre.dualPDiv.TateModule (PadicAlgCl p))

/-- `V_p(G^∨)`: the Tate representation of `(G_{ℚ_p})^∨`, as a representation of `G_L`. -/
abbrev tateRepDual (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp) :=
  P.genericFibre.dualPDiv.tateRep L

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]

/-- **`dα_K : L^d → D_0(V_p(G^∨)^∨) = Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^{G_L}`** for `G` over `ℤ_p`
([Hong, Prop. 3.4.9, Thm. 3.4.10]). -/
def dalphaK : (Fin d → L) →ₗ[L] DHT (P.tateRepDual L).dual 0 :=
  P.dalphaKGen ZpD.p_mem ℚ_[p] ZpD.algebraMap_qbar_cp L
    (FGL.galFixedOver_of_galFixed ZpD.galFixed L)
    (fun σ => σ.restrictScalars ℚ_[p]) (fun _ _ => rfl) (P.tateRepDual L) (fun _ _ _ => rfl)

/-- **`dα_K` is injective** ([Hong, Prop. 3.4.9], `dalpha_injective_K`). -/
theorem dalphaK_injective : Function.Injective (P.dalphaK L) :=
  P.dalphaKGen_injective _ _ _ L _ _ _ _ _ ZpD.norm_lt_one

/-- **[Hong, (3.9)]**: `d ≤ dim_{ℚ_p} Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^Γ = dim D_0(V_p(G^∨)^∨)`. -/
theorem le_finrank_DHT_tateRepDual : d ≤ finrank L (DHT (P.tateRepDual L).dual 0) := by
  have h := LinearMap.finrank_le_finrank_of_injective (P.dalphaK_injective L)
  rwa [Module.finrank_fin_fun] at h

/-- **`dα_K` with values in `D_{-1}(V_p G) = (V_p G ⊗ ℂ_p(-1))^{G_L}`**, via
`V_p(G^∨)^∨ ≅ V_p(G)(-1)` ([Hong, Prop. 3.4.6]). -/
def dalphaKTwist : (Fin d → L) →ₗ[L] DHT (P.genericFibre.tateRep L) (-1) :=
  P.genericFibre.DHTdualTateEquivMap L ∘ₗ P.dalphaK L

theorem dalphaKTwist_injective : Function.Injective (P.dalphaKTwist L) :=
  (P.genericFibre.DHTdualTateEquivMap_injective L).comp (P.dalphaK_injective L)

/-- **[Hong, (3.9)] for `V_p G`**: `d ≤ dim_{ℚ_p} D_{-1}(V_p G)`. -/
theorem le_finrank_DHT_tateRep : d ≤ finrank L (DHT (P.genericFibre.tateRep L) (-1)) := by
  have h := LinearMap.finrank_le_finrank_of_injective (P.dalphaKTwist_injective L)
  rwa [Module.finrank_fin_fun] at h

end Zp

end PDivFGL

end PadicHodge
