/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.TateSen.H1Gamma

/-!
# `H¹(Γ, \hat{ℚ_p(μ_{p^∞})}(j)) = 0` for `j ≠ 0`: the main argument

See `PadicHodge/TateSen/H1Gamma.lean` for the overview.
-/

noncomputable section

open IntermediateField Topology

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- A continuous function on `G` vanishing on `H` is small on `Gal(ℚ̄_p/ℚ_p(μ_{p^N}))` for `N`
large (compactness of `G`). -/
theorem exists_small_on_fixingSubgroup {F : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p]}
    (hc : Continuous F) (hH : ∀ h ∈ (cycFieldInf p).fixingSubgroup, F h = 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ N, ∀ τ ∈ (cycField p N).fixingSubgroup, ‖F τ‖ < ε := by
  by_contra hne
  push Not at hne
  set t : ℕ → Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :=
    fun N => ((cycField p N).fixingSubgroup : Set _) ∩ {τ | ε ≤ ‖F τ‖} with ht
  have hanti : ∀ {a b : ℕ}, a ≤ b → t b ⊆ t a := by
    intro a b hab τ hτ
    exact ⟨fixingSubgroup_antitone (cycField_mono hab) hτ.1, hτ.2⟩
  have hdir : Directed (· ⊇ ·) t := fun a b =>
    ⟨max a b, hanti (le_max_left _ _), hanti (le_max_right _ _)⟩
  have hne' : ∀ N, (t N).Nonempty := fun N => by
    obtain ⟨τ, hτ, hτε⟩ := hne N
    exact ⟨τ, hτ, hτε⟩
  have hcl : ∀ N, IsClosed (t N) := fun N => by
    haveI := finiteDimensional_cycField (p := p) N
    exact (IntermediateField.fixingSubgroup_isClosed _).inter
      (isClosed_le continuous_const hc.norm)
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne'
    (fun N => (hcl N).isCompact) hcl
  rw [Set.mem_iInter] at hτ
  have hτH : τ ∈ (cycFieldInf p).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨k, hk⟩ := mem_cycFieldInf.mp hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (hτ k).1 x hk
  have := (hτ 0).2
  simp only [Set.mem_setOf_eq, hH τ hτH, norm_zero] at this
  linarith

theorem chiPow_props {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {u : ℤ_[p]} (hu : IsUnit u)
    (hγ : ((chi γ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ 5 * u) {j : ℤ} (hj : j ≠ 0) :
    ((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) ≠ 1 ∧
      (p : ℝ) ^ 4 * ‖((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ < 1 := by
  constructor
  · intro h
    apply zpow_ne_one (by norm_num : 2 ≤ 5) hu hγ hj
    rw [chiPow_apply] at h
    exact Subtype.ext (h.trans PadicInt.coe_one.symm)
  · have h1 : ‖((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ ≤ ‖((chi γ : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ := by
      rw [chiPow_apply]
      have := norm_zpow_sub_one_le (chi γ) j
      rw [← PadicInt.padic_norm_e_of_padicInt] at this
      push_cast at this
      exact this
    rw [hγ, add_sub_cancel_left, norm_mul, norm_pow, PadicInt.norm_p,
      PadicInt.isUnit_iff.mp hu, mul_one] at h1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    calc (p : ℝ) ^ 4 * ‖((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ 4 * ((p : ℝ)⁻¹ ^ 5) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (p : ℝ)⁻¹ := by field_simp
      _ < 1 := inv_lt_one_of_one_lt₀ hp1

theorem fixingSubgroup_cycField_finiteIndex (N : ℕ) :
    (cycField p N).fixingSubgroup.FiniteIndex := by
  haveI := finiteDimensional_cycField (p := p) N
  exact ⟨by rw [← finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'⟩

/-- **`H¹(Γ, \hat{ℚ_p(μ_{p^∞})}(j)) = 0` for `j ≠ 0`**, where `Γ = Gal(ℚ_p(μ_{p^∞})/ℚ_p)`
and the coefficients are `(ℂ_p(j))^H`, `H = Gal(ℚ̄_p/ℚ_p(μ_{p^∞}))`. -/
theorem subsingleton_H1_quotient_twist {j : ℤ} (hj : j ≠ 0) :
    Subsingleton (ContH1.H1 ((cpTwistRepQ (p := p) j).quotientToInvariants
      (cycFieldInf p).fixingSubgroup)) := by
  set ρ := cpTwistRepQ (p := p) j with hρ
  set H := (cycFieldInf p).fixingSubgroup with hHdef
  suffices hz : ∀ x : ContH1.H1 (ρ.quotientToInvariants H), x = 0 from
    ⟨fun x y => by rw [hz x, hz y]⟩
  intro x
  apply ContH1.inf_injective ρ H
  rw [map_zero]
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change ContH1.inf ρ H (ContH1.mk (ρ.quotientToInvariants H) f) = 0
  rw [ContH1.inf_mk]
  set F := ContH1.infCocycles ρ H f with hFdef
  have hFapp : ∀ g, (F : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p]) g =
      (((f : Gal(PadicAlgCl p/ℚ_[p]) ⧸ H → Representation.invariants (ρ.comp H.subtype))
        (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ H)) : ℂ_[p]) :=
    fun g => rfl
  -- `F` vanishes on `H` and takes values in the closure of `ℚ_p(μ_{p^∞})`
  have hFH : ∀ h ∈ H, (F : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p]) h = 0 := by
    intro h hh
    rw [hFapp, (QuotientGroup.eq_one_iff h).mpr hh, ContH1.cocycle_one _ f.2]
    rfl
  have hFval : ∀ g, (F : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p]) g ∈
      closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]) := by
    intro g
    refine mem_closure_of_H_fixed fun h hh => ?_
    have := ((f : Gal(PadicAlgCl p/ℚ_[p]) ⧸ H → Representation.invariants (ρ.comp H.subtype))
      (g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ H)).2 ⟨h, hh⟩
    rw [hFapp, ← cpTwistRepQ_of_mem_H j hh]
    exact this
  -- a Tate generator and the solution `m`
  obtain ⟨γ, u, hu, hγ⟩ := exists_chi_eq (p := p) 5 (by norm_num)
  have hT := isTateGen_of_chi (by norm_num) hu hγ
  obtain ⟨hlam1, hlam⟩ := chiPow_props hu hγ hj
  obtain ⟨m, hm, hmeq⟩ := exists_twist_eq hT (by norm_num) hlam1 hlam (hFval γ)
  -- the modified cocycle
  set F' : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p] :=
    fun g => (F : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p]) g - (ρ g m - m) with hF'
  have hF'c : F' ∈ ContH1.cocycles ρ := by
    refine ⟨F.2.1.sub ((continuous_cpTwistRepQ_apply j m).sub continuous_const), fun g h => ?_⟩
    simp only [hF', F.2.2 g h, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hF'γ : F' γ = 0 := by
    simp only [hF']
    rw [cpTwistRepQ_apply, hmeq, sub_self]
  have hF'H : ∀ h ∈ H, F' h = 0 := by
    intro h hh
    simp only [hF']
    rw [hFH h hh, cpTwistRepQ_of_mem_H j hh, autCp_eq_self_of_mem_closure hm hh]
    simp
  have hpow : ∀ k : ℕ, F' (γ ^ k) = 0 := by
    intro k
    induction k with
    | zero => exact ContH1.cocycle_one ρ hF'c
    | succ k ih => rw [pow_succ, hF'c.2, ih, hF'γ, map_zero, add_zero]
  -- `F'` vanishes on `Gal(ℚ̄_p/ℚ_p(μ_{p^5}))`
  have hG5 : ∀ σ ∈ (cycField p 5).fixingSubgroup, F' σ = 0 := by
    intro σ hσ
    by_contra hne
    have hε : 0 < ‖F' σ‖ := norm_pos_iff.mpr hne
    obtain ⟨N0, hN0⟩ := exists_small_on_fixingSubgroup hF'c.1 hF'H hε
    set N := max N0 5 with hN
    obtain ⟨k, hk⟩ := exists_pow_dvd_sub (by norm_num : 2 ≤ 5) hu (dvd_chi_sub_one_of_mem hσ)
      (le_max_right N0 5)
    rw [← hγ] at hk
    set τ := (γ ^ k)⁻¹ * σ with hτ
    have hτN : τ ∈ (cycField p N).fixingSubgroup := by
      refine mem_of_dvd_chi_sub_one (by omega) ?_
      have e : ((chi τ : ℤ_[p]ˣ) : ℤ_[p]) - 1 =
          (((chi γ ^ k)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
            (((chi σ : ℤ_[p]ˣ) : ℤ_[p]) - ((chi γ ^ k : ℤ_[p]ˣ) : ℤ_[p])) := by
        rw [hτ, map_mul, map_inv, map_pow, mul_sub, ← Units.val_mul, ← Units.val_mul,
          inv_mul_cancel, Units.val_one]
      rw [e, Units.val_pow_eq_pow_val]
      exact Dvd.dvd.mul_left hk _
    have hστ : σ = γ ^ k * τ := by rw [hτ, mul_inv_cancel_left]
    have h1 : F' σ = ρ (γ ^ k) (F' τ) := by
      rw [hστ, hF'c.2, hpow, zero_add]
    have h2 : ‖F' τ‖ < ‖F' σ‖ := hN0 τ (fixingSubgroup_antitone
      (cycField_mono (le_max_left N0 5)) hτN)
    rw [h1, norm_cpTwistRepQ] at h2
    exact lt_irrefl _ h2
  haveI := fixingSubgroup_cycField_finiteIndex (p := p) 5
  have hidx : ((cycField p 5).fixingSubgroup.index : ℚ_[p]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Subgroup.FiniteIndex.index_ne_zero)
  have h0 := ContH1.mk_eq_zero_of_vanish ρ _ hidx ⟨F', hF'c⟩ hG5
  rw [← h0]
  refine (Submodule.Quotient.eq _).mpr ⟨m, fun g => ?_⟩
  change (F : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p]) g - F' g = ρ g m - m
  simp only [hF']
  abel

end PadicHodge
