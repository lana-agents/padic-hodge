/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.Basic
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Duals of Hodge–Tate representations

`isHodgeTate_dual`: if `V` is Hodge–Tate then so is `V^∨` ([BC, §2.4], "if `W` is Hodge–Tate
then so is `W^∨`, with negated Hodge–Tate weights"). Proof: the base-change isomorphism
`Φ : ℂ_p ⊗ V^∨ ≃ Hom_{ℂ_p}(ℂ_p ⊗ V, ℂ_p)` (`IsBaseChange.toDualBaseChange`) satisfies
`Φ(σ x)(σ w) = σ(Φ x w)`, so it carries the dual basis of an eigenbasis of `ℂ_p ⊗ V` (weights
`q_i`) to an eigenbasis of `ℂ_p ⊗ V^∨` (weights `-q_i`).
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)

variable [FiniteDimensional ℚ_[p] V]

/-- The base-change isomorphism `ℂ_p ⊗ V^∨ ≃ Hom_{ℂ_p}(ℂ_p ⊗ V, ℂ_p)`. -/
def dualEquiv : (ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] V) ≃ₗ[ℂ_[p]] Dual ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) :=
  (TensorProduct.isBaseChange ℚ_[p] V ℂ_[p]).toDualBaseChange

theorem dualEquiv_tmul_tmul (a : ℂ_[p]) (f : Dual ℚ_[p] V) (d : ℂ_[p]) (v : V) :
    dualEquiv (V := V) (a ⊗ₜ f) (d ⊗ₜ v) = d * (a * algebraMap ℚ_[p] ℂ_[p] (f v)) := by
  have h := (TensorProduct.isBaseChange ℚ_[p] V ℂ_[p]).toDualBaseChange_tmul a f v
  have e : (d ⊗ₜ[ℚ_[p]] v : ℂ_[p] ⊗[ℚ_[p]] V) = d • (TensorProduct.mk ℚ_[p] ℂ_[p] V 1 v) := by
    rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul]
  exact congrArg (d * ·) h

theorem galCp_algebraMap_Qp (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (t : ℚ_[p]) :
    galCp L σ (algebraMap ℚ_[p] ℂ_[p] t) = algebraMap ℚ_[p] ℂ_[p] t :=
  galCp_algebraMap σ t

/-- Equivariance of `dualEquiv`: `Φ(σ x)(σ w) = σ(Φ x w)`. -/
theorem dualEquiv_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] V)
    (w : ℂ_[p] ⊗[ℚ_[p]] V) :
    dualEquiv (V := V) (TensorProduct.map (galCpLin L σ) (ρ.dual σ) x)
      (TensorProduct.map (galCpLin L σ) (ρ σ) w) = galCp L σ (dualEquiv (V := V) x w) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hy, ← map_add, ← LinearMap.add_apply,
      ← map_add]
  | tmul a f =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => rw [map_add, map_add, hw, hw', ← map_add, ← map_add]
    | tmul d v =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, dualEquiv_tmul_tmul,
        dualEquiv_tmul_tmul, galCpLin_apply, galCpLin_apply, Representation.dual_apply,
        Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply, map_mul, map_mul,
        galCp_algebraMap_Qp]

section HT

variable [FiniteDimensional ℚ_[p] L]

theorem psi_smul_eq {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    {π : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) W} (q : ℤ)
    (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : CpTensor π) :
    (htSetup L).ψ q σ • x = (algebraMap ℚ_[p] ℂ_[p] (chiL L (-q) σ)) • x := by
  change algebraMap L ℂ_[p] (algebraMap ℚ_[p] L (chiL L (-q) σ)) • x = _
  rw [algebraMap_L_cp_algebraMap]

omit [FiniteDimensional ℚ_[p] L] in
theorem chiL_inv (j : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    chiL L (-j) σ⁻¹ = chiL L j σ := by
  have e : σ⁻¹.restrictScalars ℚ_[p] = (σ.restrictScalars ℚ_[p])⁻¹ := rfl
  rw [chiL, chiL, e, chiPow_neg, map_inv, inv_inv]

omit [FiniteDimensional ℚ_[p] V] [FiniteDimensional ℚ_[p] L] in
theorem tensorAct_inv_cancel (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (w : ℂ_[p] ⊗[ℚ_[p]] V) :
    TensorProduct.map (galCpLin L σ) (ρ σ) (TensorProduct.map (galCpLin L σ⁻¹) (ρ σ⁻¹) w) = w := by
  change (tensorAct ρ σ * tensorAct ρ σ⁻¹) w = w
  rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- **The dual of a Hodge–Tate representation is Hodge–Tate.** -/
theorem isHodgeTate_dual (h : IsHodgeTate ρ) : IsHodgeTate ρ.dual := by
  classical
  obtain ⟨ι, hι, b, q, hb⟩ := (isHodgeTate_iff_exists_basis ρ).mp h
  let b' : Basis ι ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) := b
  let bd := b'.dualBasis
  let bdual : Basis ι ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] V) := bd.map (dualEquiv (V := V)).symm
  refine (isHodgeTate_iff_exists_basis ρ.dual).mpr ⟨ι, hι, bdual, fun i => -q i, fun i σ => ?_⟩
  rw [psi_smul_eq, neg_neg]
  apply (dualEquiv (V := V)).injective
  refine b'.ext fun l => ?_
  have hbl : b' l = TensorProduct.map (galCpLin L σ) (ρ σ)
      (TensorProduct.map (galCpLin L σ⁻¹) (ρ σ⁻¹) (b' l)) := (tensorAct_inv_cancel ρ σ _).symm
  change dualEquiv (TensorProduct.map (galCpLin L σ) (ρ.dual σ) (bdual i)) (b' l) =
    dualEquiv ((algebraMap ℚ_[p] ℂ_[p] (chiL L (q i) σ)) • bdual i) (b' l)
  have hinv : TensorProduct.map (galCpLin L σ⁻¹) (ρ σ⁻¹) (b' l) =
      (algebraMap ℚ_[p] ℂ_[p] (chiL L (-q l) σ⁻¹)) • b' l := by
    have := hb l σ⁻¹
    rw [psi_smul_eq] at this
    exact this
  conv_lhs => rw [hbl]
  rw [dualEquiv_gal, hinv, map_smul, LinearEquiv.map_smul, LinearMap.smul_apply]
  simp only [bdual, Basis.map_apply, LinearEquiv.apply_symm_apply, bd,
    Basis.dualBasis_apply_self, smul_eq_mul, chiL_inv]
  split_ifs with hli
  · rw [mul_one, mul_one, galCp_algebraMap_Qp, hli]
  · rw [mul_zero, mul_zero, map_zero]

end HT

end PadicHodge
