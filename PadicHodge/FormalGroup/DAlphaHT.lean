/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DualTateGal
import PadicHodge.FormalGroup.DAlphaInj
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
  transported along `dualTateZpLinearEquiv` to `T_p(G_{ℚ_p}^∨)(ℚ̄_p)` (`dalphaZpLin`), extended
  to `V_p(G^∨) = ℚ_p ⊗ T_p` (`dalphaQpLin`) and to `ℂ_p ⊗ V_p(G^∨)` (`dalphaCpLin`), and
  identified with an element of `ℂ_p ⊗ V_p(G^∨)^∨` (`dualEquiv`, `dalphaTensor`).
  It is `G_L`-invariant (`dalphaTensor_mem`) by the Galois equivariance of `∂U_y/∂T_j(0)`
  (`dalpha_galDualZp`, from `charSeries_gal`) and of `dualTateZpEquiv` (`dualTateZpEquiv_gal`).
  This gives the `L`-linear map **`dalphaK : L^d → D_0(V_p(G^∨)^∨)`**.
* **`dalphaK_injective`**: for `L = ℚ_p` (`⊥`), `dα_K` is injective (`dalpha_injective_Qp`,
  [Hong, Prop. 3.4.9]); hence **`le_finrank_DHT_tateRepDual`**: `d ≤ dim_{ℚ_p} W^Γ`, which is
  [Hong, (3.9)].
* Transport to `V_p G`: from `V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` (`tateRepDualEquiv`,
  [Hong, Prop. 3.4.6]) we get `V_p(G^∨)^∨ ≅ V_p(G)` with `σ` twisted by `χ(σ)^{-1}`
  (`tateRepDualDualEquiv`, `tateRepDualDualEquiv_gal`); twisted intertwiners shift the
  Hodge–Tate index (`DHTtwistMap`), so `D_0(V_p(G^∨)^∨) ≅ D_{-1}(V_p G)`
  (`finrank_DHT_dual_tateRep_dualPDiv`). This gives **`dalphaKTwist : L^d → D_{-1}(V_p G)`**,
  injective for `L = ℚ_p` (`dalphaKTwist_injective`), and **`le_finrank_DHT_tateRep`**:
  `d ≤ dim_{ℚ_p} D_{-1}(V_p G)`, the form of (3.9) used in `bijective_of_finrank_le_add_fin`.

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

namespace PDivGroup

variable (H : PDivGroup ℚ_[p] p)

/-- **`V_p(G^∨)^∨ ≅ V_p G`** (as `ℚ_p`-vector spaces), the dual of
`tateRepDualEquiv : V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)` composed with `V_p G ≅ V_p(G)^{∨∨}`. -/
def tateRepDualDualEquiv :
    Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (H.dualPDiv.TateModule (PadicAlgCl p))) ≃ₗ[ℚ_[p]]
      ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule (PadicAlgCl p)) :=
  (H.tateRepDualEquiv ≪≫ₗ TensorProduct.rid ℚ_[p] _).symm.dualMap ≪≫ₗ
    (Module.evalEquiv ℚ_[p] _).symm

theorem tateRepDualDualEquiv_symm_apply (v : ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule K))
    (w : ℚ_[p] ⊗[ℤ_[p]] Additive (H.dualPDiv.TateModule K)) :
    H.tateRepDualDualEquiv.symm v w = TensorProduct.rid ℚ_[p] _ (H.tateRepDualEquiv w) v :=
  rfl

theorem tateRepDualDualEquiv_symm_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (v : ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule K)) :
    H.tateRepDualDualEquiv.symm (H.tateRep L σ v) =
      chiL L 1 σ • (H.dualPDiv.tateRep L).dual σ (H.tateRepDualDualEquiv.symm v) := by
  refine LinearMap.ext fun w => ?_
  have he : H.tateRepDualEquiv ((H.dualPDiv.tateRep L) σ⁻¹ w) =
      ((H.tateRep L).dual.tprod (charRep L 1) σ⁻¹) (H.tateRepDualEquiv w) :=
    LinearMap.congr_fun (H.tateRepDualEquiv_gal L σ⁻¹) w
  rw [LinearMap.smul_apply, Representation.dual_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, tateRepDualDualEquiv_symm_apply, tateRepDualDualEquiv_symm_apply, he,
    rid_tprod_charRep, LinearMap.smul_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, ← chiL_mul, mul_inv_cancel, chiL_one, one_mul]

/-- **`V_p(G^∨)^∨ ≅ V_p(G)(-1)`**: `σ (F x) = χ(σ) F(σ x)` for `F = tateRepDualDualEquiv`. -/
theorem tateRepDualDualEquiv_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (x : Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (H.dualPDiv.TateModule K))) :
    H.tateRep L σ (H.tateRepDualDualEquiv x) =
      chiL L 1 σ • H.tateRepDualDualEquiv ((H.dualPDiv.tateRep L).dual σ x) := by
  apply H.tateRepDualDualEquiv.symm.injective
  rw [map_smul, LinearEquiv.symm_apply_apply, tateRepDualDualEquiv_symm_gal,
    LinearEquiv.symm_apply_apply]

theorem tateRepDualDualEquiv_symm_gal' (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (v : ℚ_[p] ⊗[ℤ_[p]] Additive (H.TateModule K)) :
    (H.dualPDiv.tateRep L).dual σ (H.tateRepDualDualEquiv.symm v) =
      chiL L (-1) σ • H.tateRepDualDualEquiv.symm (H.tateRep L σ v) := by
  rw [tateRepDualDualEquiv_symm_gal, smul_smul, ← chiL_add, neg_add_cancel, chiL_zero, one_smul]

variable [FiniteDimensional ℚ_[p] L]

/-- `D_0(V_p(G^∨)^∨) → D_{-1}(V_p G)`, induced by `tateRepDualDualEquiv`. -/
def DHTdualTateEquivMap :
    DHT (H.dualPDiv.tateRep L).dual 0 →ₗ[L] DHT (H.tateRep L) (-1) :=
  DHTtwistMap 1 (H.tateRepDualDualEquiv : _ →ₗ[ℚ_[p]] _)
    (fun σ x => H.tateRepDualDualEquiv_gal L σ x) (by norm_num)

theorem DHTdualTateEquivMap_injective : Function.Injective (H.DHTdualTateEquivMap L) :=
  DHTtwistMap_injective 1 _ _ H.tateRepDualDualEquiv.injective

/-- **`dim D_0(V_p(G^∨)^∨) = dim D_{-1}(V_p G)`.** -/
theorem finrank_DHT_dual_tateRep_dualPDiv :
    finrank L (DHT (H.dualPDiv.tateRep L).dual 0) = finrank L (DHT (H.tateRep L) (-1)) :=
  le_antisymm (LinearMap.finrank_le_finrank_of_injective (H.DHTdualTateEquivMap_injective L))
    (LinearMap.finrank_le_finrank_of_injective
      (DHTtwistMap_injective (-1) (f := (H.tateRepDualDualEquiv.symm : _ →ₗ[ℚ_[p]] _))
        (fun σ v => H.tateRepDualDualEquiv_symm_gal' L σ v) (q := -1) (q' := 0) (by norm_num)
        H.tateRepDualDualEquiv.symm.injective))

end PDivGroup

end DualDual

/-! ### `dα_K` -/

namespace PDivFGL

open PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} (P : PDivFGL (ZpD p) d p)

local instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- `ℤ_p` acts uniformly continuously on `ℚ̄_p` (through `ℚ_p`); this makes `ℂ_p` a
`ℤ_p`-module with `IsScalarTower ℤ_p ℚ_p ℂ_p` (completion instances). -/
local instance : UniformContinuousConstSMul ℤ_[p] (PadicAlgCl p) :=
  ⟨fun a => by
    have h : (fun x : PadicAlgCl p => a • x) = fun x => algebraMap ℤ_[p] ℚ_[p] a • x :=
      funext fun x => (algebraMap_smul ℚ_[p] a x).symm
    rw [h]
    exact uniformContinuous_const_smul _⟩

/-- The generic fibre `G_{ℚ_p}` of `G = F[p^∞]`. -/
abbrev genericFibre : PDivGroup ℚ_[p] p := P.pdivGroup.baseChange ℚ_[p]

/-- `T_p(G_{ℚ_p}^∨)(ℚ̄_p)`, as an additive `ℤ_p`-module. -/
abbrev TateDualQp : Type := Additive (P.genericFibre.dualPDiv.TateModule (PadicAlgCl p))

/-- `V_p(G^∨)`: the Tate representation of `(G_{ℚ_p})^∨`, as a representation of `G_L`. -/
abbrev tateRepDual (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp) :=
  P.genericFibre.dualPDiv.tateRep L

theorem dalpha_add_left (z z' : Fin d → ℂ_[p]) (y : P.pdivGroup.DualTate (OCd p)) :
    P.dalpha ZpD.p_mem (z + z') y = P.dalpha ZpD.p_mem z y + P.dalpha ZpD.p_mem z' y := by
  simp only [dalpha, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dU_galDualZp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (y : P.pdivGroup.DualTate (OCd p)) (j : Fin d) :
    ((OCd.toOC (P.dU ZpD.p_mem (P.pdivGroup.galDualZp σ y) j) : OC p) : ℂ_[p]) =
      autCp σ ((OCd.toOC (P.dU ZpD.p_mem y j) : OC p) : ℂ_[p]) := by
  rw [← P.galDual_eq_galDualZp σ (ZpD.galFixed σ), dU, dU, charSeries_gal,
    MvPowerSeries.coeff_map]
  exact galS_apply σ (ZpD.galFixed σ) _

/-- **Galois equivariance of `dα`** ([Hong, Prop. 3.4.9]): for `z` fixed by `σ`,
`dα(z)(σ y) = σ(dα(z)(y))`. -/
theorem dalpha_galDualZp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {z : Fin d → ℂ_[p]}
    (hz : ∀ j, autCp σ (z j) = z j) (y : P.pdivGroup.DualTate (OCd p)) :
    P.dalpha ZpD.p_mem z (P.pdivGroup.galDualZp σ y) = autCp σ (P.dalpha ZpD.p_mem z y) := by
  rw [dalpha, dalpha, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hz, dU_galDualZp]

/-- `dα(z)` as a `ℤ_p`-linear functional on `T_p(G_{ℚ_p}^∨)(ℚ̄_p)`
(via `dualTateZpLinearEquiv`). -/
def dalphaZpLin (z : Fin d → ℂ_[p]) : P.TateDualQp →ₗ[ℤ_[p]] ℂ_[p] where
  toFun t := P.dalpha ZpD.p_mem z (Additive.toMul (P.pdivGroup.dualTateZpLinearEquiv.symm t))
  map_add' t t' := by simp only [map_add, toMul_add, dalpha_mul]
  map_smul' a t := by
    simp only [RingHom.id_apply]
    have h := P.dalpha_zpSmul z a (Additive.toMul (P.pdivGroup.dualTateZpLinearEquiv.symm t))
    rw [ofMul_toMul] at h
    rw [map_smul, h]
    exact algebraMap_smul ℚ_[p] a _

/-- `dα(z)` as a `ℚ_p`-linear functional on `V_p(G^∨) = ℚ_p ⊗ T_p(G^∨)`. -/
def dalphaQpLin (z : Fin d → ℂ_[p]) : ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp →ₗ[ℚ_[p]] ℂ_[p] :=
  (P.dalphaZpLin z).liftBaseChange ℚ_[p]

/-- `dα(z)` as a `ℂ_p`-linear functional on `ℂ_p ⊗ V_p(G^∨)`. -/
def dalphaCpLin (z : Fin d → ℂ_[p]) :
    Dual ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)) :=
  (P.dalphaQpLin z).liftBaseChange ℂ_[p]

theorem dalphaQpLin_tmul (z : Fin d → ℂ_[p]) (a : ℚ_[p]) (t : P.TateDualQp) :
    P.dalphaQpLin z (a ⊗ₜ t) =
      a • P.dalpha ZpD.p_mem z (Additive.toMul (P.pdivGroup.dualTateZpLinearEquiv.symm t)) :=
  rfl

theorem dalphaCpLin_tmul (z : Fin d → ℂ_[p]) (c : ℂ_[p])
    (v : ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp) : P.dalphaCpLin z (c ⊗ₜ v) = c * P.dalphaQpLin z v :=
  rfl

theorem dalphaCpLin_add (z z' : Fin d → ℂ_[p]) :
    P.dalphaCpLin (z + z') = P.dalphaCpLin z + P.dalphaCpLin z' := by
  have hQ : P.dalphaQpLin (z + z') = P.dalphaQpLin z + P.dalphaQpLin z' := by
    refine TensorProduct.AlgebraTensorModule.ext fun a t => ?_
    rw [LinearMap.add_apply, dalphaQpLin_tmul, dalphaQpLin_tmul, dalphaQpLin_tmul,
      dalpha_add_left, smul_add]
  refine TensorProduct.AlgebraTensorModule.ext fun c v => ?_
  rw [LinearMap.add_apply, dalphaCpLin_tmul, dalphaCpLin_tmul, dalphaCpLin_tmul, hQ,
    LinearMap.add_apply, mul_add]

theorem dalphaCpLin_smul (c : ℂ_[p]) (z : Fin d → ℂ_[p]) :
    P.dalphaCpLin (fun j => c * z j) = c • P.dalphaCpLin z := by
  have hQ : P.dalphaQpLin (fun j => c * z j) = c • P.dalphaQpLin z := by
    refine TensorProduct.AlgebraTensorModule.ext fun a t => ?_
    rw [LinearMap.smul_apply, dalphaQpLin_tmul, dalphaQpLin_tmul, dalpha_smul, smul_comm,
      smul_eq_mul]
  refine TensorProduct.AlgebraTensorModule.ext fun c' v => ?_
  rw [LinearMap.smul_apply, dalphaCpLin_tmul, dalphaCpLin_tmul, hQ, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, mul_left_comm]

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem dalphaZpLin_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) {z : Fin d → ℂ_[p]}
    (hz : ∀ j, galCp L σ (z j) = z j) (t : P.TateDualQp) :
    P.dalphaZpLin z (P.genericFibre.dualPDiv.galLin (σ.restrictScalars ℚ_[p]) t) =
      galCp L σ (P.dalphaZpLin z t) := by
  set σ' := σ.restrictScalars ℚ_[p]
  set E := P.pdivGroup.dualTateZpLinearEquiv
  have hE : E.symm (P.genericFibre.dualPDiv.galLin σ' t) =
      Additive.ofMul (P.pdivGroup.galDualZp σ' (Additive.toMul (E.symm t))) := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = Additive.ofMul (P.pdivGroup.dualTateZpEquiv
      (P.pdivGroup.galDualZp σ' (Additive.toMul (E.symm t))))
    rw [dualTateZpEquiv_gal]
    have h1 : P.pdivGroup.dualTateZpEquiv (Additive.toMul (E.symm t)) = Additive.toMul t :=
      (P.pdivGroup.dualTateZpLinearEquiv_apply _).symm.trans
        (congrArg Additive.toMul (E.apply_symm_apply t))
    rw [h1]
    rfl
  change P.dalpha ZpD.p_mem z (Additive.toMul (E.symm _)) =
    galCp L σ (P.dalpha ZpD.p_mem z (Additive.toMul (E.symm t)))
  rw [hE]
  exact P.dalpha_galDualZp σ' hz _

theorem dalphaQpLin_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) {z : Fin d → ℂ_[p]}
    (hz : ∀ j, galCp L σ (z j) = z j) (v : ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp) :
    P.dalphaQpLin z (P.tateRepDual L σ v) = galCp L σ (P.dalphaQpLin z v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    have h1 : (P.tateRepDual L σ) (a ⊗ₜ t) =
        a ⊗ₜ P.genericFibre.dualPDiv.galLin (σ.restrictScalars ℚ_[p]) t := rfl
    rw [h1]
    change a • P.dalphaZpLin z _ = galCp L σ (a • P.dalphaZpLin z t)
    rw [galCp_smul, P.dalphaZpLin_gal L σ hz]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem dalphaCpLin_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) {z : Fin d → ℂ_[p]}
    (hz : ∀ j, galCp L σ (z j) = z j) (u : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)) :
    P.dalphaCpLin z (TensorProduct.map (galCpLin L σ) (P.tateRepDual L σ) u) =
      galCp L σ (P.dalphaCpLin z u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [TensorProduct.map_tmul, dalphaCpLin_tmul, dalphaCpLin_tmul, galCpLin_apply,
      P.dalphaQpLin_gal L σ hz, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem galCp_algebraMap_L (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (a : L) :
    galCp L σ (algebraMap L ℂ_[p] a) = algebraMap L ℂ_[p] a := by
  rw [algebraMap_L_cp, galCp_coe]
  exact congrArg (fun x : PadicAlgCl p => (x : ℂ_[p])) (σ.commutes a)

/-- The element of `ℂ_p ⊗ V_p(G^∨)^∨` corresponding to `y ↦ dα(z)(y)`. -/
def dalphaTensor (z : Fin d → ℂ_[p]) : CpTensor (P.tateRepDual L).dual :=
  (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)).symm (P.dalphaCpLin z)

variable [FiniteDimensional ℚ_[p] L]

/-- **`dα(z)` is `G_L`-invariant** for `z` fixed by `G_L`: it lies in
`D_0(V_p(G^∨)^∨) = Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^{G_L}`. -/
theorem dalphaTensor_mem {z : Fin d → ℂ_[p]} (hz : ∀ σ j, galCp L σ (z j) = z j) :
    P.dalphaTensor L z ∈ DHT (P.tateRepDual L).dual 0 := by
  intro σ
  rw [(htSetup L).ψ_zero, one_smul]
  change TensorProduct.map (galCpLin L σ) ((P.tateRepDual L).dual σ) (P.dalphaTensor L z) =
    P.dalphaTensor L z
  apply (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)).injective
  refine LinearMap.ext fun u => ?_
  have hu := tensorAct_inv_cancel (P.tateRepDual L) σ u
  rw [← hu, dualEquiv_gal, dalphaTensor, LinearEquiv.apply_symm_apply,
    P.dalphaCpLin_gal L σ (hz σ)]

/-- **`dα_K : L^d → D_0(V_p(G^∨)^∨) = Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^{G_L}`**, `z ↦ (y ↦ dα(z)(y))`
([Hong, Prop. 3.4.9, Thm. 3.4.10]). -/
def dalphaK : (Fin d → L) →ₗ[L] DHT (P.tateRepDual L).dual 0 where
  toFun z := ⟨P.dalphaTensor L (fun j => algebraMap L ℂ_[p] (z j)),
    P.dalphaTensor_mem L fun σ j => galCp_algebraMap_L L σ (z j)⟩
  map_add' z z' := Subtype.ext (by
    change (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)).symm (P.dalphaCpLin _) =
      (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)).symm (P.dalphaCpLin _) +
        (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)).symm (P.dalphaCpLin _)
    rw [← map_add, ← dalphaCpLin_add]
    congr 2
    funext j
    simp only [Pi.add_apply, map_add])
  map_smul' a z := Subtype.ext (by
    change (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)).symm (P.dalphaCpLin _) =
      algebraMap L ℂ_[p] a •
        (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)).symm (P.dalphaCpLin _)
    rw [← map_smul, ← dalphaCpLin_smul]
    congr 2
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, map_mul])

theorem dalphaK_apply (z : Fin d → L) :
    ((P.dalphaK L z : DHT (P.tateRepDual L).dual 0) : CpTensor (P.tateRepDual L).dual) =
      P.dalphaTensor L (fun j => algebraMap L ℂ_[p] (z j)) :=
  rfl

/-- **`dα_K` is injective** for `L = ℚ_p` ([Hong, Prop. 3.4.9], `dalpha_injective_Qp`). -/
theorem dalphaK_injective : Function.Injective (P.dalphaK ⊥) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  have h0 : P.dalphaCpLin (fun j => algebraMap (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
      ℂ_[p] (z j)) = 0 := by
    have h := congrArg Subtype.val hz
    rw [dalphaK_apply] at h
    apply (dualEquiv (V := ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp)).symm.injective
    rw [map_zero]
    exact h
  have hq0 : ∀ j, ∃ r : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) r = (z j : PadicAlgCl p) :=
    fun j => IntermediateField.mem_bot.mp (z j).2
  choose q hq using hq0
  have hz' : ∀ j, algebraMap (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) ℂ_[p] (z j) =
      algebraMap ℚ_[p] ℂ_[p] (q j) := fun j => by
    rw [algebraMap_L_cp, ← hq j]
    change algebraMap (PadicAlgCl p) ℂ_[p] (algebraMap ℚ_[p] (PadicAlgCl p) (q j)) = _
    rw [← IsScalarTower.algebraMap_apply]
  have key := P.dalpha_injective_Qp ZpD.p_mem ZpD.norm_lt_one ZpD.galFixed q fun y => by
    have h := LinearMap.congr_fun h0
      ((1 : ℂ_[p]) ⊗ₜ ((1 : ℚ_[p]) ⊗ₜ P.pdivGroup.dualTateZpLinearEquiv (Additive.ofMul y)))
    rw [dalphaCpLin_tmul, dalphaQpLin_tmul, LinearEquiv.symm_apply_apply, one_smul, one_mul,
      LinearMap.zero_apply, toMul_ofMul] at h
    convert h using 2
    funext j
    exact (hz' j).symm
  funext j
  have h1 : ((z j : PadicAlgCl p)) = 0 := by rw [← hq j, key, Pi.zero_apply, map_zero]
  exact Subtype.ext h1

/-- **[Hong, (3.9)]**: `d ≤ dim_{ℚ_p} Hom_{ℤ_p}(T_p(G^∨), ℂ_p)^Γ = dim D_0(V_p(G^∨)^∨)`. -/
theorem le_finrank_DHT_tateRepDual :
    d ≤ finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) (DHT (P.tateRepDual ⊥).dual 0) := by
  have h := LinearMap.finrank_le_finrank_of_injective (P.dalphaK_injective)
  rwa [Module.finrank_fin_fun] at h

/-- **`dα_K` with values in `D_{-1}(V_p G) = (V_p G ⊗ ℂ_p(-1))^{G_L}`**, via
`V_p(G^∨)^∨ ≅ V_p(G)(-1)` ([Hong, Prop. 3.4.6]). -/
def dalphaKTwist : (Fin d → L) →ₗ[L] DHT (P.genericFibre.tateRep L) (-1) :=
  P.genericFibre.DHTdualTateEquivMap L ∘ₗ P.dalphaK L

theorem dalphaKTwist_injective : Function.Injective (P.dalphaKTwist ⊥) :=
  (P.genericFibre.DHTdualTateEquivMap_injective ⊥).comp P.dalphaK_injective

/-- **[Hong, (3.9)] for `V_p G`**: `d ≤ dim_{ℚ_p} D_{-1}(V_p G)`. -/
theorem le_finrank_DHT_tateRep :
    d ≤ finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
      (DHT (P.genericFibre.tateRep ⊥) (-1)) := by
  have h := LinearMap.finrank_le_finrank_of_injective (P.dalphaKTwist_injective)
  rwa [Module.finrank_fin_fun] at h

end PDivFGL

end PadicHodge
