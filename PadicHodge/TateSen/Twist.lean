/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.TateSen.Invariants

/-!
# Tate twists `ℂ_p(j)` and `H⁰(G_L, ℂ_p(j))`

`cpTwistRep L j` is `ℂ_p(j)`: the `ℚ_p`-linear continuous representation of `G_L` on `ℂ_[p]`
given by `σ · c = χ(σ)^j σ(c)` ([BC, §2], convention for `M(r)`). We prove ([BC, Thm. 2.2.7], first
half; [LocAn, Lemma 2.2], "`Hⁿ(Γ_K, R̂_K(j)) = 0` (`j ≠ 0`; `n = 0`)" for `R = O_K`):

* `cpTwistRep_invariants_eq_bot`: `ℂ_p(j)^{G_L} = 0` for `j ≠ 0`, `L / ℚ_p` finite;
* `H0CpTwistIso`: `H⁰_cont(G_L, ℂ_p(j)) ≅ 0` for `j ≠ 0`;
* `cpTwistRep_zero_invariants`: `ℂ_p(0)^{G_L} = L`.
-/

noncomputable section

open CategoryTheory

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The twisting scalar `χ(σ)^j ∈ ℚ_p` of `σ ∈ G_L`. -/
def chiL (j : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : ℚ_[p] :=
  ((chiPow j (σ.restrictScalars ℚ_[p]) : ℚ_[p]ˣ) : ℚ_[p])

theorem chiL_mul (j : ℤ) (σ τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    chiL L j (σ * τ) = chiL L j σ * chiL L j τ := by
  have e : (σ * τ).restrictScalars ℚ_[p] = σ.restrictScalars ℚ_[p] * τ.restrictScalars ℚ_[p] :=
    rfl
  rw [chiL, chiL, chiL, e, map_mul, Units.val_mul]

theorem chiL_one (j : ℤ) : chiL L j 1 = 1 := by
  have e : (1 : PadicAlgCl p ≃ₐ[L] PadicAlgCl p).restrictScalars ℚ_[p] = 1 := rfl
  rw [chiL, e, map_one, Units.val_one]

/-- `ℂ_p(j)` as a continuous `ℚ_p`-linear representation of `G_L`:
`σ · c = χ(σ)^j σ(c)`. -/
def cpTwistRep (j : ℤ) : ContRepresentation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) ℂ_[p] where
  toMonoidHom :=
    { toFun := fun σ =>
        { toFun := fun x => chiL L j σ • galCp L σ x
          map_add' := fun x y => by rw [map_add, smul_add]
          map_smul' := fun c x => by
            rw [galCp_smul, smul_comm]; rfl
          cont := (continuous_const_smul (chiL L j σ)).comp (continuous_galCp σ) }
      map_one' := by
        ext x
        simp [chiL_one]
      map_mul' := fun σ τ => by
        ext x
        change chiL L j (σ * τ) • galCp L (σ * τ) x =
          chiL L j σ • galCp L σ (chiL L j τ • galCp L τ x)
        rw [map_mul, chiL_mul, galCp_smul, smul_smul, mul_comm (chiL L j σ)]
        rfl }

variable {L}

theorem cpTwistRep_apply (j : ℤ) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : ℂ_[p]) :
    cpTwistRep L j σ x = chiL L j σ • galCp L σ x := rfl

/-- **Tate**: `ℂ_p(j)^{G_L} = 0` for `j ≠ 0` and `L / ℚ_p` finite. -/
theorem cpTwistRep_invariants_eq_bot [FiniteDimensional ℚ_[p] L] {j : ℤ} (hj : j ≠ 0) :
    (cpTwistRep L j).invariants = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [ContRepresentation.mem_invariants] at hx
  rw [Submodule.mem_bot]
  refine eq_zero_of_galCp_eq_chi_smul (L := L) (j := -j) (neg_ne_zero.mpr hj) fun σ => ?_
  have h := hx σ
  rw [cpTwistRep_apply] at h
  conv_rhs => rw [← h]
  rw [smul_smul, chiPow_neg, chiL, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem cpTwistRep_zero_invariants [FiniteDimensional ℚ_[p] L] :
    (cpTwistRep L 0).invariants = cpSubmodule L := by
  ext x
  rw [ContRepresentation.mem_invariants, ← galCp_eq_self_iff_mem]
  have h : ∀ σ, chiL L 0 σ = 1 := fun σ => by
    rw [chiL, chiPow]; simp
  simp only [cpTwistRep_apply, h, one_smul]

variable (L) in
/-- **`H⁰(G_L, ℂ_p(j)) = 0`** for `j ≠ 0` and `L / ℚ_p` finite. -/
def H0CpTwistIso [FiniteDimensional ℚ_[p] L] {j : ℤ} (hj : j ≠ 0) :
    continuousCohomology 0 (TopRep.of (cpTwistRep L j)) ≅
      TopModuleCat.of ℚ_[p] (⊥ : Submodule ℚ_[p] ℂ_[p]) :=
  ContinuousCohomology.zeroIso (TopRep.of (cpTwistRep L j)) ≪≫
    TopModuleCat.ofIso (ContinuousLinearEquiv.ofEq _ _ (cpTwistRep_invariants_eq_bot hj))

end PadicHodge
