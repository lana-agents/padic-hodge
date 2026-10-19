/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.OmegaLimit
import PadicHodge.Cyclotomic.Norms

/-!
# The different of `ℚ_p(ζ_{p^r})/ℚ_p` and `Ann(dζ)` ([Fo, §2.7])

Let `ζ` be a primitive `p^{m+1}`-th root of unity in `ℚ̄_p`, `E = ℚ_p(ζ)`, and let `OL ⊥ = ℤ_p`
(the ring of integers of the bottom intermediate field).

* `norm_coeff_le_of_pi`, `norm_coeff_le_one_of_pi`: for `π ∈ ℚ̄_p` with `|π|^D = p^{-1}`, the
  expansion `∑_{j<D} a_j π^j` (`a_j ∈ ℚ_p`) is orthogonal, so `|∑ a_j π^j| ≤ 1` forces `|a_j| ≤ 1`;
* **`OL.adjoin_zetaO_eq_top`**: `O_E = ℤ_p[ζ]` (with `π = ζ - 1`, `D = [E:ℚ_p] = φ(p^{m+1})`);
* `OL.minpoly_zetaO_map`: the minimal polynomial of `ζ` over `ℤ_p` is `Φ_{p^{m+1}}`;
* **`OL.dnorm_bot_cyc`**: `‖𝔇_{E/ℚ_p}‖ · |ζ^{p^m} - 1| = |p|^{m+1}`, i.e.
  `v(𝔇_{E/ℚ_p}) = (m+1) - 1/(p-1)` (`|ζ_p - 1|^{p-1} = p^{-1}`);
* **`OL.smul_D_zeta_eq_zero_iff_bot`** ([Fo, Lemme 7] for `Ĝ_m` over `K = K₀ = ℚ_p`):
  `y · dζ = 0` in `Ω_{O_K̄/ℤ_p}` iff `|y| ≤ ‖𝔇_{E/ℚ_p}‖`.

## References

* [Fo] J.-M. Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur
  les corps locaux*, Invent. Math. 65 (1982), §2.7.
-/

noncomputable section

open IsLocalRing Polynomial Module KaehlerDifferential IntermediateField

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Orthogonality of `π`-adic expansions with `|π|^D = p^{-1}` -/

section Ortho

variable {π : PadicAlgCl p} {D : ℕ} (hπ : ‖π‖ ^ D = (p : ℝ)⁻¹)
include hπ

theorem pow_finrank_eq_zpow (v : ℤ) (i : ℕ) :
    ((p : ℝ) ^ (-v) * ‖π‖ ^ i) ^ D = (p : ℝ) ^ (-(v * D) - i) := by
  rw [mul_pow, ← pow_mul, mul_comm i D, pow_mul, hπ, ← zpow_natCast, ← zpow_mul, inv_pow,
    ← zpow_natCast (p : ℝ) i, ← zpow_neg, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]
  congr 1
  ring

theorem norm_qp_mul_pow_ne {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0) {i j : ℕ} (hij : i < j)
    (hjD : j < D) :
    ‖algebraMap ℚ_[p] (PadicAlgCl p) a * π ^ i‖ ≠ ‖algebraMap ℚ_[p] (PadicAlgCl p) b * π ^ j‖ := by
  intro h
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_algebraMap', norm_algebraMap',
    Padic.norm_eq_zpow_neg_valuation ha, Padic.norm_eq_zpow_neg_valuation hb] at h
  have h2 := congrArg (fun t : ℝ => t ^ D) h
  rw [pow_finrank_eq_zpow hπ, pow_finrank_eq_zpow hπ] at h2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have h3 := zpow_right_injective₀ (by positivity : (0 : ℝ) < p) hp1.ne' h2
  have h4 : (D : ℤ) ∣ (j : ℤ) - i := ⟨a.valuation - b.valuation, by linarith⟩
  have h5 : (D : ℤ) ≤ (j : ℤ) - i := Int.le_of_dvd (by omega) h4
  omega

/-- **Orthogonality** of `∑_{j<D} a_j π^j`, `a_j ∈ ℚ_p`. -/
theorem norm_coeff_le_of_pi (a : ℕ → ℚ_[p]) {i : ℕ} (hi : i < D) :
    ‖a i‖ * ‖π‖ ^ i ≤
      ‖∑ l ∈ Finset.range D, algebraMap ℚ_[p] (PadicAlgCl p) (a l) * π ^ l‖ := by
  classical
  by_cases hai : a i = 0
  · rw [hai, norm_zero, zero_mul]; exact norm_nonneg _
  set s := (Finset.range D).filter (fun l => a l ≠ 0) with hs
  have hsum : ∑ l ∈ Finset.range D, algebraMap ℚ_[p] (PadicAlgCl p) (a l) * π ^ l =
      ∑ l ∈ s, algebraMap ℚ_[p] (PadicAlgCl p) (a l) * π ^ l := by
    rw [hs, Finset.sum_filter_of_ne]
    intro l _ h h0
    exact h (by rw [h0, map_zero, zero_mul])
  have his : i ∈ s := by simp [hs, hi, hai]
  rw [hsum, IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne ⟨i, his⟩]
  · have := Finset.le_sup' (fun l => ‖algebraMap ℚ_[p] (PadicAlgCl p) (a l) * π ^ l‖) his
    rwa [norm_mul, norm_pow, norm_algebraMap'] at this
  · intro k hk l hl hkl
    simp only [hs, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk hl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact norm_qp_mul_pow_ne hπ hk.2 hl.2 h hl.1
    · exact (norm_qp_mul_pow_ne hπ hl.2 hk.2 h hk.1).symm

/-- If `|∑_{j<D} a_j π^j| ≤ 1` then all `|a_j| ≤ 1`. -/
theorem norm_coeff_le_one_of_pi (a : ℕ → ℚ_[p])
    (h : ‖∑ l ∈ Finset.range D, algebraMap ℚ_[p] (PadicAlgCl p) (a l) * π ^ l‖ ≤ 1) {i : ℕ}
    (hi : i < D) : ‖a i‖ ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have hai : a i ≠ 0 := by rintro h0; rw [h0, norm_zero] at hgt; linarith
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  -- `|a_i| ≥ p`
  have hge : (p : ℝ) ≤ ‖a i‖ := by
    rw [Padic.norm_eq_zpow_neg_valuation hai] at hgt ⊢
    have : (0 : ℤ) < -(a i).valuation := by
      by_contra h0
      push Not at h0
      exact absurd hgt (not_lt.mpr (zpow_le_one_of_nonpos₀ hp1.le h0))
    calc (p : ℝ) = (p : ℝ) ^ (1 : ℤ) := (zpow_one _).symm
      _ ≤ _ := zpow_le_zpow_right₀ hp1.le this
  -- `|π|^i > p^{-1}`
  have hD : 0 < D := by omega
  have hπ0 : 0 < ‖π‖ := by
    rcases (norm_nonneg π).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, zero_pow hD.ne'] at hπ
      exact absurd hπ.symm (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))
  have hπ1 : ‖π‖ < 1 := by
    by_contra h1
    push Not at h1
    have := one_le_pow₀ (n := D) h1
    rw [hπ] at this
    exact absurd this (not_le.mpr (inv_lt_one_of_one_lt₀ hp1))
  have hpow : (p : ℝ)⁻¹ < ‖π‖ ^ i := by
    rw [← hπ]
    exact pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 hi
  have := (norm_coeff_le_of_pi hπ a hi).trans h
  have h2 : 1 < ‖a i‖ * ‖π‖ ^ i := by
    calc (1 : ℝ) = p * (p : ℝ)⁻¹ := (mul_inv_cancel₀ (by positivity)).symm
      _ < ‖a i‖ * ‖π‖ ^ i := mul_lt_mul' hge hpow (by positivity) (by positivity)
  linarith

end Ortho

namespace OL

variable {L E : IntermediateField ℚ_[p] (PadicAlgCl p)}

instance [hLE : Fact (L ≤ E)] : IsScalarTower (OL L) (OL E) (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun x => (algebraMap_qbar_ofLE hLE.out x).symm

instance instFactBotLE : Fact ((⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) ≤ E) := ⟨bot_le⟩

theorem algebraMap_qbar_injective : Function.Injective (algebraMap (OL E) (PadicAlgCl p)) :=
  fun _ _ h => toL_injective (Subtype.val_injective h)

/-- Elements of `O_⊥ = ℤ_p` are (images of) `p`-adic integers. -/
theorem exists_algebraMap_bot_eq {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    ∃ c' : OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)),
      algebraMap _ (PadicAlgCl p) c' = algebraMap ℚ_[p] (PadicAlgCl p) c :=
  ⟨ofL ⟨algebraMap ℚ_[p] (PadicAlgCl p) c, IntermediateField.algebraMap_mem _ c⟩
    (by rw [norm_algebraMap']; exact hc), algebraMap_ofL _ _⟩

theorem exists_qp_eq (c : OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))) :
    ∃ c₀ : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) c₀ = algebraMap _ (PadicAlgCl p) c := by
  have h := (toL c).2
  rw [IntermediateField.mem_bot] at h
  exact h

instance : FiniteDimensional ℚ_[p] (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) :=
  inferInstance

/-! ### `O_{ℚ_p(ζ)} = ℤ_p[ζ]` -/

variable {ζ : PadicAlgCl p} {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1)))

instance (ζ : PadicAlgCl p) : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ⟯ :=
  adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)

include hζ in
theorem norm_zeta : ‖ζ‖ = 1 :=
  norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp.out.ne_zero) hζ.pow_eq_one

/-- `ζ ∈ O_{ℚ_p(ζ)}`. -/
def zetaO : OL ℚ_[p]⟮ζ⟯ := ofL ⟨ζ, mem_adjoin_simple_self _ _⟩ (norm_zeta hζ).le

theorem algebraMap_zetaO : algebraMap (OL ℚ_[p]⟮ζ⟯) (PadicAlgCl p) (zetaO hζ) = ζ :=
  algebraMap_ofL _ _

include hζ in
/-- **`O_{ℚ_p(ζ)} = ℤ_p[ζ]`** (`ζ - 1` is a uniformiser of the totally ramified extension). -/
theorem adjoin_zetaO_eq_top :
    Algebra.adjoin (OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))) {zetaO hζ} = ⊤ := by
  classical
  set π := ζ - 1 with hπdef
  have hint : IsIntegral ℚ_[p] ζ := Algebra.IsIntegral.isIntegral ζ
  set D := (minpoly ℚ_[p] ζ).natDegree with hD
  have hDφ : D = (p ^ (m + 1)).totient := by
    rw [hD, ← adjoin.finrank hint, finrank_adjoin_primitiveRoot hζ]
  have hπ : ‖π‖ ^ D = (p : ℝ)⁻¹ := by rw [hDφ]; exact norm_sub_one_pow_totient hζ
  rw [eq_top_iff]
  intro z _
  -- `z = f(ζ)` with `deg f < D`
  obtain ⟨f, hfdeg, hf⟩ := (adjoin.powerBasis hint).exists_eq_aeval (toL z)
  have hz : algebraMap (OL ℚ_[p]⟮ζ⟯) (PadicAlgCl p) z = aeval ζ f := by
    rw [algebraMap_qbar_eq, IntermediateField.algebraMap_apply, hf, adjoin.powerBasis_gen,
      AdjoinSimple.coe_aeval_gen_apply]
  -- `z = r(π)`, `r = f(X + 1)`
  set r := f.comp (X + 1) with hr
  have hrdeg : r.natDegree < D := by
    rw [hr, natDegree_comp, show (X + 1 : ℚ_[p][X]).natDegree = 1 by
      simpa using natDegree_X_add_C (1 : ℚ_[p]), mul_one]
    exact hfdeg
  have hzr : algebraMap (OL ℚ_[p]⟮ζ⟯) (PadicAlgCl p) z =
      ∑ l ∈ Finset.range D, algebraMap ℚ_[p] (PadicAlgCl p) (r.coeff l) * π ^ l := by
    rw [hz, show aeval ζ f = aeval π r by
      rw [hr, aeval_comp, map_add, aeval_X, map_one, hπdef, sub_add_cancel],
      aeval_eq_sum_range' hrdeg]
    simp only [Algebra.smul_def]
  have hcoeff : ∀ l, ‖r.coeff l‖ ≤ 1 := by
    intro l
    by_cases hl : l < D
    · refine norm_coeff_le_one_of_pi hπ (fun l => r.coeff l) ?_ hl
      rw [← hzr, ← nrm_eq_norm]; exact nrm_le_one z
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]; exact zero_le_one
  -- lift `r` to `ℤ_p[X]`
  have hl : r.map (algebraMap ℚ_[p] (PadicAlgCl p)) ∈
      lifts (algebraMap (OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))) (PadicAlgCl p)) := by
    rw [lifts_iff_coeff_lifts]
    intro l
    obtain ⟨c', hc'⟩ := exists_algebraMap_bot_eq (hcoeff l)
    exact ⟨c', by rw [coeff_map, hc']⟩
  obtain ⟨r', hr'⟩ := hl
  change r'.map _ = _ at hr'
  have hz' : z = aeval (zetaO hζ - 1) r' := by
    apply algebraMap_qbar_injective
    rw [hzr, ← aeval_algebraMap_apply, map_sub, map_one, algebraMap_zetaO, ← hπdef, aeval_def,
      ← eval_map, hr', eval_map, ← aeval_def, aeval_eq_sum_range' hrdeg]
    simp only [Algebra.smul_def]
  rw [hz']
  have h1 : zetaO hζ - 1 ∈
      Algebra.adjoin (OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))) {zetaO hζ} :=
    sub_mem (Algebra.subset_adjoin (Set.mem_singleton _)) (one_mem _)
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr h1) (aeval_mem_adjoin_singleton _ _)

/-! ### The minimal polynomial and the different -/

theorem aeval_cyclotomic_zetaO :
    aeval (zetaO hζ)
      (cyclotomic (p ^ (m + 1)) (OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)))) = 0 := by
  apply algebraMap_qbar_injective
  rw [← aeval_algebraMap_apply, algebraMap_zetaO, map_zero, aeval_def, eval₂_eq_eval_map,
    map_cyclotomic]
  exact (isRoot_cyclotomic_iff.mpr hζ)

include hζ in
/-- The minimal polynomial of `ζ` over `ℤ_p` is `Φ_{p^{m+1}}`. -/
theorem minpoly_zetaO :
    minpoly (OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))) (zetaO hζ) =
      cyclotomic (p ^ (m + 1)) (OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))) := by
  classical
  set A := OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
  have hint : IsIntegral A (zetaO hζ) := Algebra.IsIntegral.isIntegral _
  have hdvd := minpoly.isIntegrallyClosed_dvd hint (aeval_cyclotomic_zetaO hζ)
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _)
    hdvd ?_).symm
  -- `φ(p^{m+1}) = [ℚ_p(ζ):ℚ_p] ≤ deg`
  set g := (minpoly A (zetaO hζ)).map (algebraMap A (PadicAlgCl p))
  have hgmon : g.Monic := (minpoly.monic hint).map _
  have hl : g ∈ lifts (algebraMap ℚ_[p] (PadicAlgCl p)) := by
    rw [lifts_iff_coeff_lifts]
    intro l
    obtain ⟨c₀, hc₀⟩ := exists_qp_eq ((minpoly A (zetaO hζ)).coeff l)
    exact ⟨c₀, by rw [coeff_map, hc₀]⟩
  obtain ⟨g₀, hg₀, hdeg, hmon⟩ := lifts_and_natDegree_eq_and_monic hl hgmon
  have h0 := congrArg (algebraMap (OL ℚ_[p]⟮ζ⟯) (PadicAlgCl p)) (minpoly.aeval A (zetaO hζ))
  rw [← aeval_algebraMap_apply, algebraMap_zetaO, map_zero] at h0
  have hroot : aeval ζ g₀ = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hg₀, eval_map, ← aeval_def]; exact h0
  have h1 := natDegree_le_of_dvd (minpoly.dvd ℚ_[p] ζ hroot) hmon.ne_zero
  rw [← adjoin.finrank (Algebra.IsIntegral.isIntegral ζ), finrank_adjoin_primitiveRoot hζ, hdeg,
    (minpoly.monic hint).natDegree_map] at h1
  rw [natDegree_cyclotomic]
  exact h1

include hζ in
/-- `Φ_{p^{m+1}}'(ζ) · (ζ^{p^m} - 1) = p^{m+1} ζ^{p^{m+1} - 1}`. -/
theorem eval_derivative_cyclotomic_mul :
    eval ζ (derivative (cyclotomic (p ^ (m + 1)) (PadicAlgCl p))) * (ζ ^ p ^ m - 1) =
      (p : PadicAlgCl p) ^ (m + 1) * ζ ^ (p ^ (m + 1) - 1) := by
  have h := congrArg (fun q => eval ζ (derivative q))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (PadicAlgCl p) p m)
  have hΦ : eval ζ (cyclotomic (p ^ (m + 1)) (PadicAlgCl p)) = 0 := isRoot_cyclotomic_iff.mpr hζ
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, eval_add,
    eval_mul, eval_sub, eval_pow, eval_X, eval_one, eval_C, hΦ, zero_mul, add_zero, sub_zero] at h
  rw [h]
  push_cast
  ring

include hζ in
/-- **The different of `ℚ_p(ζ_{p^{m+1}})/ℚ_p`**: `‖𝔇‖ · |ζ^{p^m} - 1| = |p|^{m+1}`, i.e.
`v(𝔇) = m + 1 - 1/(p-1)` ([Fo, §2.7]). -/
theorem dnorm_bot_cyc :
    dnorm (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) ℚ_[p]⟮ζ⟯ * ‖ζ ^ p ^ m - 1‖ =
      ‖(p : PadicAlgCl p)‖ ^ (m + 1) := by
  set A := OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
  have hb := adjoin_zetaO_eq_top hζ
  have h := differentIdeal_eq_span hb
  rw [← span_dgen, Ideal.span_singleton_eq_span_singleton] at h
  rw [dnorm, nrm_eq_of_associated h, nrm_eq_norm, ← aeval_algebraMap_apply, algebraMap_zetaO,
    minpoly_zetaO hζ, aeval_def, eval₂_eq_eval_map, ← derivative_map, map_cyclotomic, ← norm_mul,
    eval_derivative_cyclotomic_mul hζ, norm_mul, norm_pow, norm_pow, norm_zeta hζ, one_pow,
    mul_one]

/-- `ζ ∈ O_{K̄}`. -/
def zetaK : OKbar p := ⟨ζ, (norm_zeta hζ).le⟩

theorem algebraMap_zetaO_OKbar : algebraMap (OL ℚ_[p]⟮ζ⟯) (OKbar p) (zetaO hζ) = zetaK hζ :=
  Subtype.ext (algebraMap_zetaO hζ)

/-- **[Fo, Lemme 7] for `Ĝ_m` over `ℚ_p`**: `y · dζ = 0` in `Ω_{O_K̄/ℤ_p}` iff
`|y| ≤ ‖𝔇_{ℚ_p(ζ)/ℚ_p}‖`. -/
theorem smul_D_zeta_eq_zero_iff_bot (y : OKbar p) :
    y • D (OL (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))) (OKbar p) (zetaK hζ) = 0 ↔
      ‖(y : PadicAlgCl p)‖ ≤ dnorm (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) ℚ_[p]⟮ζ⟯ := by
  have h := smul_mapOK_smul_D_eq_zero_iff (adjoin_zetaO_eq_top hζ) 1 y
  rwa [one_smul, map_D, algebraMap_zetaO_OKbar, nrm_one, mul_one] at h

end OL

end PadicHodge
