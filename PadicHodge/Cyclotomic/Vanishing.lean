/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Core
import PadicHodge.AxSenTate.Basic

/-!
# No eigenvectors with eigenvalue `≠ 1` near `1` in `\hat{ℚ_p(μ_{p^∞})}`

`eq_zero_of_autCp_eq_smul`: if `γ` is a Tate generator at level `n ≥ 1`, `x ∈ ℂ_[p]` is a limit
of elements of `ℚ_p(μ_{p^∞})` and `γ x = λ x` with `λ ∈ ℚ_p`, `λ ≠ 1` and `p^4 ‖λ - 1‖ < 1`, then
`x = 0`. (Tate's argument with normalised traces, [BC, §14].)
-/

noncomputable section

open IntermediateField

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

theorem coe_smul_cp (c : ℚ_[p]) (y : PadicAlgCl p) :
    ((c • y : PadicAlgCl p) : ℂ_[p]) = c • (y : ℂ_[p]) := by
  rw [PadicComplex.coe_eq, PadicComplex.coe_eq, Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply]

theorem eq_zero_of_autCp_eq_smul {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {n : ℕ}
    (hγ : IsTateGen γ n) (hn : 1 ≤ n) {lam : ℚ_[p]} (hlam1 : lam ≠ 1)
    (hlam : (p : ℝ) ^ 4 * ‖lam - 1‖ < 1) {x : ℂ_[p]}
    (happrox : ∀ ε > 0, ∃ M, ∃ y ∈ cycField p M, ‖x - (y : ℂ_[p])‖ ≤ ε)
    (hx : autCp γ x = lam • x) : x = 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hl0 : 0 < ‖1 - lam‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hlam1))
  have hp4 : (1 : ℝ) ≤ (p : ℝ) ^ 4 := one_le_pow₀ hp1
  have hlamle : ‖lam - 1‖ < 1 :=
    lt_of_le_of_lt (le_mul_of_one_le_left (norm_nonneg _) hp4) hlam
  have hlam_norm : ‖lam‖ ≤ 1 := by
    have e : lam = (lam - 1) + 1 := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hlamle.le ?_)
    rw [norm_one]
  set C : ℝ := max ((p : ℝ) ^ 4) (p / ‖1 - lam‖) with hC
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have key : ∀ ε > 0, ‖x‖ ≤ max ((p : ℝ) ^ 4 * ‖lam - 1‖ * ‖x‖) (C * ε) := by
    intro ε hε
    obtain ⟨M0, y, hyM0, hxy⟩ := happrox ε hε
    set M := max M0 n with hM
    have hy : y ∈ cycField p M := cycField_mono (le_max_left _ _) hyM0
    set t := M - n with htdef
    have ht : n + t ≤ M := by omega
    have hMt : M - t = n := by omega
    set A := acomp γ n M t y with hAdef
    have hA : A ∈ cycField p n := by
      have := acomp_mem hγ hn ht hy; rwa [hMt] at this
    have hγA : γ A = A := gal_fix_cycField hγ hn hA
    have hyx : ‖(y : ℂ_[p]) - x‖ ≤ ε := by rw [norm_sub_rev]; exact hxy
    -- (a) `‖γ y - λ y‖ ≤ ε`
    have ha : ‖γ y - lam • y‖ ≤ ε := by
      have e : ((γ y - lam • y : PadicAlgCl p) : ℂ_[p]) =
          autCp γ ((y : ℂ_[p]) - x) + lam • (x - (y : ℂ_[p])) := by
        rw [map_sub, hx, autCp_coe, coe_sub_cp, coe_smul_cp, smul_sub]; ring
      rw [← PadicComplex.norm_extends, e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_autCp]; exact hyx
      · rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) hlam_norm).trans hxy
    -- (b) `‖1 - λ‖ ‖A‖ ≤ p ε`
    have hb : ‖1 - lam‖ * ‖A‖ ≤ p * ε := by
      have e : acomp γ n M t (γ y - lam • y) = (1 - lam) • A := by
        rw [acomp_sub, acomp_comm, acomp_smul, ← hAdef, hγA, sub_smul, one_smul]
      have hmem : γ y - lam • y ∈ cycField p M :=
        sub_mem (gal_mem_cycField γ hy) (IntermediateField.smul_mem _ hy)
      have h := norm_acomp_le hγ hn ht hmem
      rw [e, norm_smul] at h
      exact h.trans (mul_le_mul_of_nonneg_left ha hp0.le)
    -- (c) `‖y - A‖ ≤ p^4 max ε (‖λ - 1‖ ‖x‖)`
    have hc : ‖γ y - y‖ ≤ max ε (‖lam - 1‖ * ‖x‖) := by
      have e : ((γ y - y : PadicAlgCl p) : ℂ_[p]) =
          autCp γ ((y : ℂ_[p]) - x) + ((lam - 1) • x + (x - (y : ℂ_[p]))) := by
        rw [map_sub, hx, autCp_coe, coe_sub_cp, sub_smul, one_smul]; ring
      rw [← PadicComplex.norm_extends, e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_autCp]; exact hyx.trans (le_max_left _ _)
      · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · rw [norm_smul]; exact le_max_right _ _
        · exact hxy.trans (le_max_left _ _)
    have hd := norm_sub_acomp_le hγ hn ht hy
    -- (d) combine
    have e : x = (x - (y : ℂ_[p])) + (((y - A : PadicAlgCl p) : ℂ_[p]) + (A : ℂ_[p])) := by
      rw [coe_sub_cp]; ring
    conv_lhs => rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine hxy.trans (le_max_of_le_right ?_)
      exact le_mul_of_one_le_left hε.le (hp4.trans (le_max_left _ _))
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [PadicComplex.norm_extends]
      refine hd.trans ?_
      rcases le_total ε (‖lam - 1‖ * ‖x‖) with h | h
      · rw [max_eq_right h] at hc
        exact le_max_of_le_left (by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hc (by positivity))
      · rw [max_eq_left h] at hc
        exact le_max_of_le_right
          ((mul_le_mul_of_nonneg_left hc (by positivity)).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le))
    · rw [PadicComplex.norm_extends]
      refine le_max_of_le_right ?_
      have : ‖A‖ ≤ p / ‖1 - lam‖ * ε := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hl0, mul_comm]; exact hb
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε.le)
  by_contra hx0
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set ε := ‖x‖ / (2 * C) with hε
  have hεpos : 0 < ε := by positivity
  have h := key ε hεpos
  have h1 : (p : ℝ) ^ 4 * ‖lam - 1‖ * ‖x‖ < ‖x‖ := by
    calc (p : ℝ) ^ 4 * ‖lam - 1‖ * ‖x‖ < 1 * ‖x‖ := mul_lt_mul_of_pos_right hlam hxpos
      _ = ‖x‖ := one_mul _
  have h2 : C * ε < ‖x‖ := by
    have : C * ε = ‖x‖ / 2 := by rw [hε]; field_simp
    rw [this]; linarith
  exact absurd h (not_le.mpr (max_lt h1 h2))

end PadicHodge
