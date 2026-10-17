/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AlmostEtale.H1
import PadicHodge.TateSen.H1KZero

/-!
# Tate's theorem: `H¹(G_K, ℂ_p(j))`

For a finite extension `K / ℚ_p` ([BC, Thm. 2.2.7], second half; [BC, §14]):

* `subsingleton_H1_twist`: `H¹_cont(G_K, ℂ_p(j)) = 0` for `j ≠ 0`;
* `H1ZeroEquiv : K ≃ₗ[ℚ_p] H¹_cont(G_K, ℂ_p)`, `s ↦ [s log χ]`; in particular
  `H¹(G_K, ℂ_p)` is free of rank one over `K`, spanned by `log χ` (`finrank_H1_zero`:
  `dim_{ℚ_p} = [K : ℚ_p]`).

Proof: by inflation–restriction (`Cohomology/ContH1.lean`) along `H_K = Gal(ℚ̄_p/K_∞) ⊆ G_K`:
restriction to `H_K` vanishes because `χ` is trivial on `H_K` and `H¹(H_K, ℂ_p) = 0`
(`exists_coboundary`, from Tate's almost-étaleness via Faltings' method), so every class is
inflated from `H¹(Γ_K, \hat K_∞(j))`, which is `0` for `j ≠ 0` (`subsingleton_H1_quotient_twist_K`)
and `≅ K` for `j = 0` (`H1QuotientZeroEquivK`).
-/

noncomputable section

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]

/-- Restriction to `H_K` kills `H¹(G_K, ℂ_p(j))`. -/
theorem res_HK_eq_zero (j : ℤ) (x : ContH1.H1 (rhoK K j)) :
    ContH1.res (rhoK K j) (HK K) x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change ContH1.res (rhoK K j) (HK K) (ContH1.mk (rhoK K j) f) = 0
  rw [ContH1.res_mk, ContH1.mk_eq_zero_iff]
  have hact : ∀ (g : HK K) (m : ℂ_[p]), (rhoK K j) (g : K.fixingSubgroup) m = actH K g m :=
    fun g m => cpTwistRepQ_of_mem_HK j (hk_mem g) m
  obtain ⟨B, hB⟩ := exists_coboundary (K := K) (fun g => (f : K.fixingSubgroup → ℂ_[p]) g)
    (f.2.1.comp continuous_subtype_val) (fun g h => by
      change (f : K.fixingSubgroup → ℂ_[p]) ((g : K.fixingSubgroup) * h) = _
      rw [f.2.2, hact])
  refine ⟨B, fun g => ?_⟩
  change (f : K.fixingSubgroup → ℂ_[p]) g = (rhoK K j) (g : K.fixingSubgroup) B - B
  rw [hact]
  exact hB g

omit [FiniteDimensional ℚ_[p] K] in
theorem continuous_rhoK_apply (j : ℤ) (m : ℂ_[p]) :
    Continuous fun g : K.fixingSubgroup => rhoK K j g m :=
  (continuous_cpTwistRepQ_apply j m).comp continuous_subtype_val

/-- Every class in `H¹(G_K, ℂ_p(j))` is inflated from `Γ_K = G_K / H_K`. -/
theorem inf_surjective (j : ℤ) : Function.Surjective (ContH1.inf (rhoK K j) (HK K)) :=
  fun x => ContH1.exists_inf_of_res_eq_zero _ _ (continuous_rhoK_apply j) x (res_HK_eq_zero j x)

/-- **Tate**: `H¹_cont(G_K, ℂ_p(j)) = 0` for `j ≠ 0`. -/
theorem subsingleton_H1_twist {j : ℤ} (hj : j ≠ 0) : Subsingleton (ContH1.H1 (rhoK K j)) := by
  haveI := subsingleton_H1_quotient_twist_K (K := K) hj
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', rfl⟩ := inf_surjective j x
  obtain ⟨y', rfl⟩ := inf_surjective j y
  rw [Subsingleton.elim x' y']

variable (K) in
/-- **Tate**: `H¹_cont(G_K, ℂ_p) ≅ K`, `s ↦ [s log χ]`. -/
def H1ZeroEquiv : K ≃ₗ[ℚ_[p]] ContH1.H1 (rhoK K 0) :=
  (H1QuotientZeroEquivK (K := K)).trans (LinearEquiv.ofBijective (ContH1.inf (rhoK K 0) (HK K))
    ⟨ContH1.inf_injective _ _, inf_surjective 0⟩)

theorem finrank_H1_zero : Module.finrank ℚ_[p] (ContH1.H1 (rhoK K 0)) = Module.finrank ℚ_[p] K :=
  (H1ZeroEquiv K).finrank_eq.symm

end PadicHodge
