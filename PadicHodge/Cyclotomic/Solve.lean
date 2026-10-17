/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Vanishing

/-!
# Solving `λ γ m - m = z` on the completion of `ℚ_p(μ_{p^∞})`

Let `γ` be a Tate generator at level `n ≥ 1` and `λ ∈ ℚ_p` with `λ ≠ 1`, `p^4 ‖λ - 1‖ < 1`.

* `norm_le_of_twist`: on `ℚ_p(μ_{p^M})` (any `M`), `‖y‖ ≤ C ‖λ γ y - y‖` with
  `C = max (p / ‖λ - 1‖) p^5` independent of `M` (Tate's normalised traces).
* `exists_twist_eq_of_mem`: `y ↦ λ γ y - y` is bijective on each `ℚ_p(μ_{p^M})`.
* `exists_twist_eq`: for every `z` in the closure of `ℚ_p(μ_{p^∞})` in `ℂ_p` there is `m` in that
  closure with `λ γ m - m = z`.

This is the analytic input for `H¹(Γ, \hat{ℚ_p(μ_{p^∞})}(j)) = 0`, `j ≠ 0` ([BC, §14.3]).
-/

noncomputable section

open IntermediateField

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

section

variable {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {n : ℕ} (hγ : IsTateGen γ n) (hn : 1 ≤ n)
include hγ hn

theorem acomp_of_mem_low {M t : ℕ} (ht : n + t ≤ M) {y : PadicAlgCl p} (hy : y ∈ cycField p n) :
    acomp γ n M t y = y := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [acomp]
    rw [ih (by omega)]
    exact tr_of_mem hγ hn (by omega) (cycField_mono (by omega) hy)

/-- **Uniform estimate**: `‖y‖ ≤ max (p/‖λ-1‖) p^5 · ‖λ γ y - y‖` on `ℚ_p(μ_{p^M})`. -/
theorem norm_le_of_twist {lam : ℚ_[p]} (hlam1 : lam ≠ 1) (hlam : (p : ℝ) ^ 4 * ‖lam - 1‖ < 1)
    {M : ℕ} (hM : n ≤ M) {y : PadicAlgCl p} (hy : y ∈ cycField p M) :
    ‖y‖ ≤ max ((p : ℝ) / ‖lam - 1‖) ((p : ℝ) ^ 5) * ‖lam • γ y - y‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hl0 : 0 < ‖lam - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hlam1)
  set t := M - n with htdef
  have ht : n + t ≤ M := by omega
  set A := acomp γ n M t with hA
  set u := lam • γ y - y with hu
  have hAy : A y ∈ cycField p n := by
    have := acomp_mem hγ hn ht hy; rwa [show M - t = n by omega] at this
  have hγAy : γ (A y) = A y := gal_fix_cycField hγ hn hAy
  have hγy : γ y ∈ cycField p M := gal_mem_cycField γ hy
  have humem : u ∈ cycField p M := sub_mem (IntermediateField.smul_mem _ hγy) hy
  -- `A u = (λ - 1) A y`
  have hAu : A u = (lam - 1) • A y := by
    rw [hu, hA, acomp_sub, acomp_smul, acomp_comm, ← hA, hγAy, sub_smul, one_smul]
  have h1 : ‖lam - 1‖ * ‖A y‖ ≤ p * ‖u‖ := by
    have := norm_acomp_le hγ hn ht humem
    rw [← hA, hAu, norm_smul] at this
    exact this
  have hAy_le : ‖A y‖ ≤ p / ‖lam - 1‖ * ‖u‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl0, mul_comm]; exact h1
  -- the complement `w = y - A y`
  set w := y - A y with hw
  have hwmem : w ∈ cycField p M := sub_mem hy (cycField_mono hM hAy)
  have hw1 : ‖w‖ ≤ (p : ℝ) ^ 4 * ‖γ w - w‖ := by
    have hAw : acomp γ n M t w = 0 := by
      rw [hw, acomp_sub, ← hA,
        show A (A y) = A y from acomp_of_mem_low hγ hn ht hAy, sub_self]
    have := norm_sub_acomp_le hγ hn ht hwmem
    rwa [hAw, sub_zero] at this
  have hrel : lam • γ w - w = u - (lam - 1) • A y := by
    rw [hw, map_sub, hγAy, hu, smul_sub, sub_smul, one_smul]; abel
  have hw2 : ‖lam • γ w - w‖ ≤ p * ‖u‖ := by
    rw [hrel]
    refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · exact le_mul_of_one_le_left (norm_nonneg _) (by exact_mod_cast hp.out.one_lt.le)
    · rw [norm_smul]; exact h1
  have hw3 : ‖w‖ ≤ (p : ℝ) ^ 4 * ‖lam • γ w - w‖ := by
    have e : γ w - w = (lam • γ w - w) - (lam - 1) • γ w := by
      rw [sub_smul, one_smul]; abel
    have hle : ‖γ w - w‖ ≤ max ‖lam • γ w - w‖ (‖lam - 1‖ * ‖w‖) := by
      rw [e]
      refine (norm_sub_le_max' _ _).trans (max_le_max le_rfl ?_)
      rw [norm_smul, norm_aut_apply]
    rcases le_total ‖lam • γ w - w‖ (‖lam - 1‖ * ‖w‖) with h | h
    · rw [max_eq_right h] at hle
      have : ‖w‖ ≤ (p : ℝ) ^ 4 * ‖lam - 1‖ * ‖w‖ := by
        rw [mul_assoc]; exact hw1.trans (mul_le_mul_of_nonneg_left hle (by positivity))
      have hw0 : ‖w‖ = 0 := by
        by_contra hne
        have hpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
        have := lt_of_le_of_lt this (mul_lt_of_lt_one_left hpos hlam)
        exact lt_irrefl _ this
      rw [hw0]; positivity
    · rw [max_eq_left h] at hle
      exact hw1.trans (mul_le_mul_of_nonneg_left hle (by positivity))
  have hw4 : ‖w‖ ≤ (p : ℝ) ^ 5 * ‖u‖ := by
    calc ‖w‖ ≤ (p : ℝ) ^ 4 * ‖lam • γ w - w‖ := hw3
      _ ≤ (p : ℝ) ^ 4 * (p * ‖u‖) := mul_le_mul_of_nonneg_left hw2 (by positivity)
      _ = (p : ℝ) ^ 5 * ‖u‖ := by ring
  calc ‖y‖ = ‖A y + w‖ := by rw [hw, add_sub_cancel]
    _ ≤ max ‖A y‖ ‖w‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le
      (hAy_le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
      (hw4.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))

end

theorem norm_sub_le_max_ultra {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem finiteDimensional_cycField (M : ℕ) : FiniteDimensional ℚ_[p] (cycField p M) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) M
  rw [cycField_eq hζ]
  exact adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)

section

variable {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {n : ℕ} (hγ : IsTateGen γ n) (hn : 1 ≤ n)
  {lam : ℚ_[p]} (hlam1 : lam ≠ 1) (hlam : (p : ℝ) ^ 4 * ‖lam - 1‖ < 1)
include hγ hn hlam1 hlam

/-- `y ↦ λ γ y - y` is surjective on `ℚ_p(μ_{p^M})` (it is injective by `norm_le_of_twist`). -/
theorem exists_twist_eq_of_mem {M : ℕ} (hM : n ≤ M) {z : PadicAlgCl p}
    (hz : z ∈ cycField p M) : ∃ m ∈ cycField p M, lam • γ m - m = z := by
  haveI := finiteDimensional_cycField (p := p) M
  let T : cycField p M →ₗ[ℚ_[p]] cycField p M :=
    { toFun := fun y => ⟨lam • γ y - y,
        sub_mem (IntermediateField.smul_mem _ (gal_mem_cycField γ y.2)) y.2⟩
      map_add' := fun y y' => Subtype.ext (by
        simp only [IntermediateField.coe_add, map_add, smul_add]; abel)
      map_smul' := fun c y => Subtype.ext (by
        simp only [IntermediateField.coe_smul, RingHom.id_apply]
        have h : γ (c • (y : PadicAlgCl p)) = c • γ y := by
          rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]
        rw [h, smul_sub, smul_comm]) }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have h0 : lam • γ (y : PadicAlgCl p) - y = 0 := congrArg Subtype.val hy
    have := norm_le_of_twist hγ hn hlam1 hlam hM y.2
    rw [h0, norm_zero, mul_zero] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext (norm_le_zero_iff.mp this)
  obtain ⟨m, hm⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨z, hz⟩
  exact ⟨m, m.2, congrArg Subtype.val hm⟩

/-- `λ γ - 1` is surjective on the closure of `ℚ_p(μ_{p^∞})` in `ℂ_p`. -/
theorem exists_twist_eq {z : ℂ_[p]}
    (hz : z ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p])) :
    ∃ m ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]), lam • autCp γ m - m = z := by
  set C := max ((p : ℝ) / ‖lam - 1‖) ((p : ℝ) ^ 5) with hC
  have hC0 : 0 ≤ C := le_trans (by positivity) (le_max_right _ _)
  -- approximations of `z` and exact solutions at finite level
  have happrox : ∀ k : ℕ, ∃ M, n ≤ M ∧ ∃ y ∈ cycField p M, dist z (y : ℂ_[p]) < 1 / (k + 1) := by
    intro k
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hz (1 / (k + 1)) (by positivity)
    obtain ⟨a, ha, rfl⟩ := mem_cpSubmodule.mp hb
    obtain ⟨M, hM⟩ := mem_cycFieldInf.mp ha
    exact ⟨max M n, le_max_right _ _, a, cycField_mono (le_max_left _ _) hM, hd⟩
  choose M hM y hy hyd using happrox
  have hsol : ∀ k, ∃ m ∈ cycField p (M k), lam • γ m - m = y k := fun k =>
    exists_twist_eq_of_mem hγ hn hlam1 hlam (hM k) (hy k)
  choose m hm hmeq using hsol
  -- the solutions form a Cauchy sequence
  have hdist : ∀ k l N, N ≤ k → N ≤ l →
      dist ((m k : PadicAlgCl p) : ℂ_[p]) (m l) ≤ C * (1 / (N + 1)) := by
    intro k l N hk hl
    rw [dist_eq_norm, ← coe_sub_cp, PadicComplex.norm_extends]
    have hmem : m k - m l ∈ cycField p (max (M k) (M l)) :=
      sub_mem (cycField_mono (le_max_left _ _) (hm k)) (cycField_mono (le_max_right _ _) (hm l))
    have h1 := norm_le_of_twist hγ hn hlam1 hlam (le_trans (hM k) (le_max_left _ _)) hmem
    have h2 : lam • γ (m k - m l) - (m k - m l) = y k - y l := by
      rw [map_sub, smul_sub, ← hmeq k, ← hmeq l]; abel
    rw [h2] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    rw [← PadicComplex.norm_extends, coe_sub_cp,
      show ((y k : PadicAlgCl p) : ℂ_[p]) - y l = (z - y l) - (z - y k) by ring]
    have hNk : (N : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hNl : (N : ℝ) + 1 ≤ (l : ℝ) + 1 := by
      have : (N : ℝ) ≤ l := by exact_mod_cast hl
      linarith
    have hk' : dist z (y k : ℂ_[p]) ≤ 1 / (N + 1) :=
      (hyd k).le.trans (one_div_le_one_div_of_le (by positivity) hNk)
    have hl' : dist z (y l : ℂ_[p]) ≤ 1 / (N + 1) :=
      (hyd l).le.trans (one_div_le_one_div_of_le (by positivity) hNl)
    rw [dist_eq_norm] at hk' hl'
    exact (norm_sub_le_max_ultra _ _).trans (max_le hl' hk')
  have hcauchy : CauchySeq fun k => ((m k : PadicAlgCl p) : ℂ_[p]) := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => C * (1 / ((N : ℝ) + 1))) hdist ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
  obtain ⟨mlim, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨mlim, mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
    coe_mem_cpSubmodule (mem_cycFieldInf.mpr ⟨M k, hm k⟩)), ?_⟩
  have hcont : Continuous fun x : ℂ_[p] => lam • autCp γ x - x :=
    ((continuous_autCp γ).const_smul lam).sub continuous_id
  have h1 : Filter.Tendsto (fun k => lam • autCp γ ((m k : PadicAlgCl p) : ℂ_[p]) -
      ((m k : PadicAlgCl p) : ℂ_[p])) Filter.atTop (nhds (lam • autCp γ mlim - mlim)) :=
    (hcont.tendsto mlim).comp hlim
  have h2 : Filter.Tendsto (fun k => ((y k : PadicAlgCl p) : ℂ_[p])) Filter.atTop (nhds z) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]; exact (hyd k).le
  have e : ∀ k, lam • autCp γ ((m k : PadicAlgCl p) : ℂ_[p]) - ((m k : PadicAlgCl p) : ℂ_[p]) =
      ((y k : PadicAlgCl p) : ℂ_[p]) := fun k => by
    rw [autCp_coe, ← coe_smul_cp, ← coe_sub_cp, hmeq k]
  simp only [e] at h1
  exact tendsto_nhds_unique h1 h2

end


end PadicHodge
