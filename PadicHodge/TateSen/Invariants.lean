/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Character
import Mathlib.FieldTheory.KrullTopology

/-!
# Tate's theorem: `ℂ_p(j)^{G_K} = 0` for `j ≠ 0`

([BC, Thm. 2.2.7], first half; [Tate, §3.3], as quoted in [LocAn, Lemma 2.2].)

* `eq_zero_of_autCp_eq_chi_smul`: over `ℚ_p`: if `σ x = χ(σ)^j x` for all `σ ∈ Gal(ℚ̄_p/ℚ_p)` and
  `j ≠ 0`, then `x = 0`. Proof: `x` is fixed by `Gal(ℚ̄_p/ℚ_p(μ_{p^∞}))`, hence (Ax–Sen–Tate) a
  limit of elements of `ℚ_p(μ_{p^∞})`; it is an eigenvector of a Tate generator `γ` at level `5`
  with eigenvalue `χ(γ)^j ≠ 1` close to `1`; conclude with `eq_zero_of_autCp_eq_smul`.
* `eq_zero_of_galCp_eq_chi_smul`: for `L / ℚ_p` finite, by the norm trick: the product of the
  normalised conjugates `χ(g)^{-j} g(x)` over `g ∈ G_{ℚ_p}/G_L` is a `χ^{j[L:ℚ_p]}`-eigenvector.
-/

noncomputable section

open IntermediateField

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- `σ ↦ χ(σ)^j ∈ ℚ_p^×`. -/
def chiPow (j : ℤ) : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* ℚ_[p]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom).comp ((zpowGroupHom j).comp chi)

theorem chiPow_apply (j : ℤ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ((chiPow j σ : ℚ_[p]ˣ) : ℚ_[p]) = (((chi σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := rfl

theorem chiPow_mul_right (j k : ℤ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    chiPow (j * k) σ = chiPow j σ ^ k := by
  simp only [chiPow, MonoidHom.comp_apply, zpowGroupHom_apply, zpow_mul, map_zpow]

theorem chiPow_neg (j : ℤ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    chiPow (-j) σ = (chiPow j σ)⁻¹ := by
  simp only [chiPow, MonoidHom.comp_apply, zpowGroupHom_apply, zpow_neg, map_inv]

theorem autCp_algebraMap (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (q : ℚ_[p]) :
    autCp σ (algebraMap ℚ_[p] ℂ_[p] q) = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    autCp_coe, σ.commutes]

theorem autCp_smul (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (q : ℚ_[p]) (x : ℂ_[p]) :
    autCp σ (q • x) = q • autCp σ x := by
  rw [Algebra.smul_def, map_mul, autCp_algebraMap, ← Algebra.smul_def]

/-- **Tate** (over `ℚ_p`): `ℂ_p(j)^{G_{ℚ_p}} = 0` for `j ≠ 0`. -/
theorem eq_zero_of_autCp_eq_chi_smul {j : ℤ} (hj : j ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ, autCp σ x = ((chiPow j σ : ℚ_[p]ˣ) : ℚ_[p]) • x) : x = 0 := by
  obtain ⟨γ, u, hu, hγ⟩ := exists_chi_eq (p := p) 5 (by norm_num)
  have hT := isTateGen_of_chi (by norm_num) hu hγ
  set lam := ((chiPow j γ : ℚ_[p]ˣ) : ℚ_[p]) with hlamdef
  have hlam1 : lam ≠ 1 := by
    intro h
    apply zpow_ne_one (by norm_num : 2 ≤ 5) hu hγ hj
    rw [hlamdef, chiPow_apply] at h
    exact Subtype.ext (h.trans PadicInt.coe_one.symm)
  have hlam : (p : ℝ) ^ 4 * ‖lam - 1‖ < 1 := by
    have h1 : ‖lam - 1‖ ≤ ‖((chi γ : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ := by
      rw [hlamdef, chiPow_apply]
      have := norm_zpow_sub_one_le (chi γ) j
      rw [← PadicInt.padic_norm_e_of_padicInt] at this
      push_cast at this
      exact this
    rw [hγ, add_sub_cancel_left, norm_mul, norm_pow, PadicInt.norm_p,
      PadicInt.isUnit_iff.mp hu, mul_one] at h1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    calc (p : ℝ) ^ 4 * ‖lam - 1‖ ≤ (p : ℝ) ^ 4 * ((p : ℝ)⁻¹ ^ 5) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (p : ℝ)⁻¹ := by field_simp
      _ < 1 := inv_lt_one_of_one_lt₀ hp1
  -- `x` is fixed by `Gal(ℚ̄_p/ℚ_p(μ_{p^∞}))`
  have hfix : ∀ σ : PadicAlgCl p ≃ₐ[cycFieldInf p] PadicAlgCl p,
      galCp (cycFieldInf p) σ x = x := by
    intro σ
    have h1 : chi (σ.restrictScalars ℚ_[p]) = 1 := by
      refine chi_eq_one_of_fix fun k t ht => ?_
      have htL : t ∈ cycFieldInf p := mem_cycFieldInf.mpr ⟨k, pow_mem_cycField ht⟩
      exact σ.commutes ⟨t, htL⟩
    change autCp (σ.restrictScalars ℚ_[p]) x = x
    rw [hx, chiPow_apply, h1, one_zpow, Units.val_one, PadicInt.coe_one, one_smul]
  have hcl := (galCp_eq_self_iff_mem_closure x).mp hfix
  have happrox : ∀ ε > 0, ∃ M, ∃ y ∈ cycField p M, ‖x - (y : ℂ_[p])‖ ≤ ε := by
    intro ε hε
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
    obtain ⟨a, ha, rfl⟩ := mem_cpSubmodule.mp hb
    obtain ⟨M, hM⟩ := mem_cycFieldInf.mp ha
    exact ⟨M, a, hM, by rw [← dist_eq_norm]; exact hdist.le⟩
  exact eq_zero_of_autCp_eq_smul hT (by norm_num) hlam1 hlam happrox (hx γ)

section Finite

instance isGalois_padicAlgCl : IsGalois ℚ_[p] (PadicAlgCl p) := IsGalois.mk

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]

theorem fixingSubgroup_finiteIndex : L.fixingSubgroup.FiniteIndex :=
  ⟨by rw [← finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'⟩

omit [FiniteDimensional ℚ_[p] L] in
theorem galCp_eq_autCp (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (x : ℂ_[p]) :
    galCp L σ x = autCp (σ.restrictScalars ℚ_[p]) x := rfl

variable {L}

/-- **Tate**: `ℂ_p(j)^{G_L} = 0` for `j ≠ 0` and `L / ℚ_p` finite ([BC, Thm. 2.2.7]). -/
theorem eq_zero_of_galCp_eq_chi_smul {j : ℤ} (hj : j ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galCp L σ x = ((chiPow j (σ.restrictScalars ℚ_[p]) : ℚ_[p]ˣ) : ℚ_[p]) • x) : x = 0 := by
  classical
  haveI := fixingSubgroup_finiteIndex L
  letI : Fintype ((PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ L.fixingSubgroup) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  -- the eigen relation on the fixing subgroup
  have hxH : ∀ h ∈ L.fixingSubgroup, autCp h x = ((chiPow j h : ℚ_[p]ˣ) : ℚ_[p]) • x := by
    intro h hh
    have e : (fixingSubgroupEquiv L ⟨h, hh⟩).restrictScalars ℚ_[p] = h := by ext; rfl
    have := hx (fixingSubgroupEquiv L ⟨h, hh⟩)
    rwa [galCp_eq_autCp, e] at this
  -- normalised conjugates
  set f : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p] :=
    fun g => (((chiPow j g)⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) • autCp g x with hfdef
  have hf : ∀ g h, h ∈ L.fixingSubgroup → f (g * h) = f g := by
    intro g h hh
    simp only [hfdef, map_mul, autCp_apply]
    rw [autCpHom_mul, ← autCp_apply h, hxH h hh, ← autCp_apply g, autCp_smul, smul_smul,
      mul_inv, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mul_one]
    rfl
  have hrel : ∀ a b : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      (QuotientGroup.leftRel L.fixingSubgroup) a b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have := hf a (a⁻¹ * b) hab
    rw [mul_inv_cancel_left] at this
    exact this.symm
  set f' : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ L.fixingSubgroup → ℂ_[p] :=
    Quotient.lift f hrel with hf'def
  have hf'σ : ∀ σ c, autCp σ (f' c) = ((chiPow j σ : ℚ_[p]ˣ) : ℚ_[p]) • f' (σ • c) := by
    intro σ c
    induction c using QuotientGroup.induction_on with
    | H g =>
      change autCp σ (f g) = _ • f (σ * g)
      simp only [hfdef, map_mul, autCp_apply]
      rw [autCpHom_mul, smul_smul, ← Units.val_mul, mul_inv, ← mul_assoc, mul_inv_cancel,
        one_mul]
      exact autCp_smul σ _ _
  set d := Fintype.card ((PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ⧸ L.fixingSubgroup) with hd
  set N := ∏ c, f' c with hNdef
  have hN : ∀ σ, autCp σ N = ((chiPow (j * d) σ : ℚ_[p]ˣ) : ℚ_[p]) • N := by
    intro σ
    rw [hNdef, map_prod]
    simp_rw [hf'σ σ, Algebra.smul_def]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hd,
      chiPow_mul_right, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    congr 1
    exact Fintype.prod_equiv (MulAction.toPerm σ) _ _ (fun c => rfl)
  have hd0 : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN0 := eq_zero_of_autCp_eq_chi_smul (mul_ne_zero hj hd0) hN
  rw [hNdef, Finset.prod_eq_zero_iff] at hN0
  obtain ⟨c, -, hc⟩ := hN0
  induction c using QuotientGroup.induction_on with
  | H g =>
    change f g = 0 at hc
    rw [hfdef, smul_eq_zero] at hc
    rcases hc with hc | hc
    · exact absurd hc (Units.ne_zero _)
    · exact (map_eq_zero_iff (autCp g) (autCp g).injective).mp hc

end Finite

end PadicHodge
