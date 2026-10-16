/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.NumberTheory.Padics.Complex

/-!
# Galois groups of `ℚ̄_p` and their action on `ℂ_[p]`

We use Mathlib's fixed algebraic closure `PadicAlgCl p` of `ℚ_[p]` and its completion
`ℂ_[p] = PadicComplex p`. For an intermediate field `L` of `PadicAlgCl p / ℚ_[p]` we write
`G_L = PadicAlgCl p ≃ₐ[L] PadicAlgCl p`.

## Main results

* `PadicHodge.norm_gal_apply`: elements of `G_L` are isometries of `PadicAlgCl p`.
* `PadicHodge.galCp`: the action of `G_L` on `ℂ_[p]`, the unique continuous extension.
* `PadicHodge.norm_galCp_apply`: this action is isometric.
-/

noncomputable section

open UniformSpace

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- Automorphisms of `PadicAlgCl p` over an intermediate field are isometries. -/
theorem norm_gal_apply {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  exact (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm

/-- Automorphisms of `PadicAlgCl p` over `ℚ_[p]` are isometries. -/
theorem norm_aut_apply (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    ‖σ x‖ = ‖x‖ := by
  have := spectralNorm_eq_of_equiv σ x
  simpa only [PadicAlgCl.spectralNorm_eq] using this.symm

theorem isometry_aut (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ (norm_aut_apply σ)

/-- The ring endomorphism of `ℂ_[p]` induced by an automorphism of `PadicAlgCl p`. -/
def autCpHom (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℂ_[p] →+* ℂ_[p] :=
  Completion.mapRingHom (σ : PadicAlgCl p →+* PadicAlgCl p) (isometry_aut σ).continuous

theorem autCpHom_coe (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    autCpHom σ (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  Completion.map_coe (isometry_aut σ).uniformContinuous x

theorem continuous_autCpHom (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Continuous (autCpHom σ) :=
  Completion.continuous_map

theorem norm_autCpHom (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) :
    ‖autCpHom σ x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_autCpHom σ).norm) continuous_norm
  | ih a =>
    rw [autCpHom_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_aut_apply]

theorem autCpHom_one (x : ℂ_[p]) : autCpHom 1 x = x := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_autCpHom (1 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
      continuous_id
  | ih a => rw [autCpHom_coe]; rfl

theorem autCpHom_mul (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) :
    autCpHom (σ * τ) x = autCpHom σ (autCpHom τ x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_autCpHom (σ * τ))
      ((continuous_autCpHom σ).comp (continuous_autCpHom τ))
  | ih a => rw [autCpHom_coe, autCpHom_coe, autCpHom_coe]; rfl

/-- The action of `Aut(ℚ̄_p/ℚ_p)` on `ℂ_[p]` by continuous ring automorphisms. -/
def autCp : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* (ℂ_[p] ≃+* ℂ_[p]) where
  toFun σ :=
    { autCpHom σ with
      invFun := autCpHom σ⁻¹
      left_inv := fun x => by
        change autCpHom σ⁻¹ (autCpHom σ x) = x
        rw [← autCpHom_mul, inv_mul_cancel, autCpHom_one]
      right_inv := fun x => by
        change autCpHom σ (autCpHom σ⁻¹ x) = x
        rw [← autCpHom_mul, mul_inv_cancel, autCpHom_one] }
  map_one' := by ext x; exact autCpHom_one x
  map_mul' σ τ := by ext x; exact autCpHom_mul σ τ x

@[simp] theorem autCp_apply (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) :
    autCp σ x = autCpHom σ x := rfl

theorem autCp_coe (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    autCp σ (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  autCpHom_coe σ x

theorem norm_autCp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : ℂ_[p]) :
    ‖autCp σ x‖ = ‖x‖ :=
  norm_autCpHom σ x

theorem continuous_autCp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Continuous (autCp σ) :=
  continuous_autCpHom σ

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The action of `G_L = Gal(ℚ̄_p/L)` on `ℂ_[p]`. -/
def galCp : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) →* (ℂ_[p] ≃+* ℂ_[p]) :=
  autCp.comp (AlgEquiv.restrictScalarsHom ℚ_[p])

variable {L}

theorem galCp_coe (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : PadicAlgCl p) :
    galCp L σ (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  autCp_coe _ x

theorem norm_galCp (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : ℂ_[p]) :
    ‖galCp L σ x‖ = ‖x‖ :=
  norm_autCp _ x

theorem continuous_galCp (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    Continuous (galCp L σ) :=
  continuous_autCp _

end PadicHodge
