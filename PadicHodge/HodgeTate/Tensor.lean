/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.HodgeTate.Dual
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products of Hodge–Tate representations

`isHodgeTate_tprod`: if `V` and `V'` are Hodge–Tate then so is `V ⊗ V'` ([BC, §2.4]). Proof: the
base-change isomorphism `ℂ_p ⊗ (V ⊗ V') ≃ (ℂ_p ⊗ V) ⊗_{ℂ_p} (ℂ_p ⊗ V')`
(`AlgebraTensorModule.distribBaseChange`) is compatible with the semilinear `G_L`-actions, so
the tensor products of eigenbases (weights `q_i + q'_k`) give an eigenbasis.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  {V V' : Type*} [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup V'] [Module ℚ_[p] V']
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V)
  (ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V')

/-- `ℂ_p ⊗ (V ⊗ V') ≃ (ℂ_p ⊗ V) ⊗_{ℂ_p} (ℂ_p ⊗ V')`. -/
abbrev tensorEquiv : ℂ_[p] ⊗[ℚ_[p]] (V ⊗[ℚ_[p]] V') ≃ₗ[ℂ_[p]]
    (ℂ_[p] ⊗[ℚ_[p]] V) ⊗[ℂ_[p]] (ℂ_[p] ⊗[ℚ_[p]] V') :=
  AlgebraTensorModule.distribBaseChange ℚ_[p] ℂ_[p] V V'

theorem tensorEquiv_symm_gal (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : ℂ_[p] ⊗[ℚ_[p]] V)
    (y : ℂ_[p] ⊗[ℚ_[p]] V') :
    TensorProduct.map (galCpLin L σ) ((ρ.tprod ρ') σ) ((tensorEquiv (V := V) (V' := V')).symm
      (x ⊗ₜ y)) = (tensorEquiv (V := V) (V' := V')).symm
        (TensorProduct.map (galCpLin L σ) (ρ σ) x ⊗ₜ
          TensorProduct.map (galCpLin L σ) (ρ' σ) y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [TensorProduct.add_tmul, map_add, map_add, hx, hx', map_add,
      TensorProduct.add_tmul, map_add]
  | tmul c v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy', map_add,
        TensorProduct.tmul_add, map_add]
    | tmul d w =>
      rw [AlgebraTensorModule.distribBaseChange_symm_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.map_tmul,
        AlgebraTensorModule.distribBaseChange_symm_tmul,
        Representation.tprod_apply, TensorProduct.map_tmul, galCpLin_apply, galCpLin_apply,
        galCpLin_apply, map_mul]

variable [FiniteDimensional ℚ_[p] L] [FiniteDimensional ℚ_[p] V] [FiniteDimensional ℚ_[p] V']

/-- **The tensor product of Hodge–Tate representations is Hodge–Tate.** -/
theorem isHodgeTate_tprod (h : IsHodgeTate ρ) (h' : IsHodgeTate ρ') :
    IsHodgeTate (ρ.tprod ρ') := by
  classical
  obtain ⟨ι, hι, b, q, hb⟩ := (isHodgeTate_iff_exists_basis ρ).mp h
  obtain ⟨κ, hκ, b', q', hb'⟩ := (isHodgeTate_iff_exists_basis ρ').mp h'
  let c : Basis ι ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V) := b
  let c' : Basis κ ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] V') := b'
  let B : Basis (ι × κ) ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] (V ⊗[ℚ_[p]] V')) :=
    (c.tensorProduct c').map (tensorEquiv (V := V) (V' := V')).symm
  refine (isHodgeTate_iff_exists_basis (ρ.tprod ρ')).mpr
    ⟨ι × κ, inferInstance, B, fun x => q x.1 + q' x.2, fun x σ => ?_⟩
  rw [psi_smul_eq]
  have h1 : TensorProduct.map (galCpLin L σ) (ρ σ) (c x.1) =
      (algebraMap ℚ_[p] ℂ_[p] (chiL L (-q x.1) σ)) • c x.1 := by
    have := hb x.1 σ; rw [psi_smul_eq] at this; exact this
  have h2 : TensorProduct.map (galCpLin L σ) (ρ' σ) (c' x.2) =
      (algebraMap ℚ_[p] ℂ_[p] (chiL L (-q' x.2) σ)) • c' x.2 := by
    have := hb' x.2 σ; rw [psi_smul_eq] at this; exact this
  change TensorProduct.map (galCpLin L σ) ((ρ.tprod ρ') σ) (B x) = _ • B x
  simp only [B, Basis.map_apply, Basis.tensorProduct_apply']
  rw [tensorEquiv_symm_gal, h1, h2, TensorProduct.smul_tmul_smul, map_smul, ← map_mul,
    ← chiL_add, neg_add]
  rfl

end PadicHodge
