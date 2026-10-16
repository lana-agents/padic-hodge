/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AxSenTate.AxLemma
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ax's lemma

**Theorem** (`PadicHodge.ax`). Let `L` be an intermediate field of `ℚ̄_p / ℚ_p` and `α ∈ ℚ̄_p`
with `‖σ α - α‖ ≤ c` for all `σ ∈ G_L`. Then there is `a ∈ L` with
`‖α - a‖ ≤ p ^ (p / (p - 1)²) * c`.

This is [Ax, Prop. 1] as quoted in [BC, proof of Prop. 2.1.2] (the paper [Ax] itself is not
available locally). The proof is by strong induction on the degree `n` of `α` over `L`, using the
step `exists_root_hasseDeriv` with `d = p^v` if `n = p^v m` with `p ∤ m`, `m > 1`
(then `binom(n, d) ≡ m (mod p)` by Lucas), and `d = p^k` if `n = p^{k+1}` (then
`v_p(binom(n, d)) = 1`). The loss in the second case is `p^{1/(p^k (p-1))}`; the total exponent
is `axExp p n = Σ_{k < log_p n} 1/(p^k (p-1)) ≤ p/(p-1)²`.
-/

noncomputable section

open Polynomial

namespace PadicHodge

/-! ### Binomial coefficients -/

theorem choose_pow_mul_modEq (p : ℕ) [Fact p.Prime] (v m : ℕ) :
    (p ^ v * m).choose (p ^ v) ≡ m [MOD p] := by
  induction v with
  | zero => simp [Nat.ModEq]
  | succ v ih =>
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    refine (Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p)).trans ?_
    have h1 : p ^ (v + 1) * m % p = 0 := by
      rw [pow_succ, mul_assoc, mul_comm p, ← mul_assoc]; exact Nat.mul_mod_left _ _
    have h2 : p ^ (v + 1) % p = 0 := by rw [pow_succ]; exact Nat.mul_mod_left _ _
    have h3 : p ^ (v + 1) * m / p = p ^ v * m := by
      rw [pow_succ, mul_assoc, mul_comm p, ← mul_assoc, Nat.mul_div_cancel _ hp0]
    have h4 : p ^ (v + 1) / p = p ^ v := by rw [pow_succ, Nat.mul_div_cancel _ hp0]
    rw [h1, h2, h3, h4, Nat.choose_zero_right, one_mul]
    exact ih

theorem not_dvd_choose_pow_mul (p : ℕ) [Fact p.Prime] (v m : ℕ) (hm : ¬ p ∣ m) :
    ¬ p ∣ (p ^ v * m).choose (p ^ v) := by
  intro h
  apply hm
  have := choose_pow_mul_modEq p v m
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  rw [← this, h]

theorem choose_prime_pow_succ_eq (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    ∃ u, ¬ p ∣ u ∧ (p ^ (k + 1)).choose (p ^ k) = p * u := by
  have hpp : p.Prime := hp.out
  have h := hpp.emultiplicity_choose_prime_pow (n := k + 1) (k := p ^ k)
    (Nat.pow_le_pow_right hpp.pos (Nat.le_succ k)) (pow_ne_zero _ hpp.ne_zero)
  rw [multiplicity_pow_self_of_prime hpp.prime, Nat.add_sub_cancel_left] at h
  have h' := (emultiplicity_eq_coe (n := 1)).mp (by exact_mod_cast h)
  obtain ⟨⟨u, hu⟩, hn⟩ := h'
  refine ⟨u, fun hpu => hn ?_, by simpa using hu⟩
  obtain ⟨w, rfl⟩ := hpu
  exact ⟨w, by rw [hu]; ring⟩

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_natCast_padicAlgCl (N : ℕ) : ‖(N : PadicAlgCl p)‖ = ‖(N : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) N]
  exact PadicAlgCl.norm_extends p _

theorem norm_choose_pow_mul (v m : ℕ) (hm : ¬ p ∣ m) :
    ‖(((p ^ v * m).choose (p ^ v) : ℕ) : PadicAlgCl p)‖ = 1 := by
  rw [norm_natCast_padicAlgCl, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr (not_dvd_choose_pow_mul p v m hm)

theorem norm_choose_prime_pow_succ (k : ℕ) :
    ‖(((p ^ (k + 1)).choose (p ^ k) : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  obtain ⟨u, hu, he⟩ := choose_prime_pow_succ_eq p k
  rw [he, norm_natCast_padicAlgCl, Nat.cast_mul, norm_mul, Padic.norm_p,
    (Padic.norm_natCast_eq_one_iff).mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hu), mul_one]

/-! ### The exponent -/

variable (p) in
/-- The exponent in Ax's lemma for elements of degree `n`:
`Σ_{k < log_p n} 1 / (p^k (p - 1))`. -/
def axExp (n : ℕ) : ℝ := ∑ k ∈ Finset.range (Nat.log p n), 1 / ((p : ℝ) ^ k * ((p : ℝ) - 1))

theorem one_lt_p_real : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

theorem axExp_term_pos (k : ℕ) : 0 < 1 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
  have := one_lt_p_real (p := p)
  positivity

theorem axExp_nonneg (n : ℕ) : 0 ≤ axExp p n :=
  Finset.sum_nonneg fun k _ => (axExp_term_pos k).le

theorem axExp_mono_log {m n : ℕ} (h : Nat.log p m ≤ Nat.log p n) : axExp p m ≤ axExp p n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    fun k _ _ => (axExp_term_pos k).le

theorem axExp_mono {m n : ℕ} (h : m ≤ n) : axExp p m ≤ axExp p n :=
  axExp_mono_log (Nat.log_mono_right h)

theorem axExp_le (n : ℕ) : axExp p n ≤ p / ((p : ℝ) - 1) ^ 2 := by
  have h1 := one_lt_p_real (p := p)
  have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  unfold axExp
  have : ∀ k ∈ Finset.range (Nat.log p n), 1 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) =
      ((p : ℝ) - 1)⁻¹ * (p : ℝ)⁻¹ ^ k := by
    intro k _
    rw [one_div, mul_inv, inv_pow, mul_comm]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, geom_sum_eq hr1.ne]
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpow : 0 ≤ (p : ℝ)⁻¹ ^ Nat.log p n := pow_nonneg hr0 _
  rw [div_eq_mul_inv, show ((p : ℝ) - 1) ^ 2 = ((p : ℝ) - 1) * ((p : ℝ) - 1) by ring]
  have hden : (p : ℝ)⁻¹ - 1 = -(((p : ℝ) - 1) / p) := by field_simp; ring
  rw [hden]
  have hp0 : (0 : ℝ) < p := by linarith
  have key : ((p : ℝ)⁻¹ ^ Nat.log p n - 1) * (-(((p : ℝ) - 1) / p))⁻¹ =
      (1 - (p : ℝ)⁻¹ ^ Nat.log p n) * (p / ((p : ℝ) - 1)) := by
    field_simp
    ring
  rw [key]
  have : (1 - (p : ℝ)⁻¹ ^ Nat.log p n) * (p / ((p : ℝ) - 1)) ≤ p / ((p : ℝ) - 1) := by
    have : 0 ≤ p / ((p : ℝ) - 1) := by positivity
    nlinarith
  calc ((p : ℝ) - 1)⁻¹ * ((1 - (p : ℝ)⁻¹ ^ Nat.log p n) * (p / ((p : ℝ) - 1)))
      ≤ ((p : ℝ) - 1)⁻¹ * (p / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = p * (((p : ℝ) - 1) * ((p : ℝ) - 1))⁻¹ := by field_simp

/-! ### The induction -/

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem norm_gal_sub_le_of_close {α β : PadicAlgCl p} {c : ℝ}
    (hα : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ‖σ α - α‖ ≤ c)
    (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : ‖σ β - β‖ ≤ max c ‖α - β‖ := by
  have e : σ β - β = σ (β - α) + ((σ α - α) + (α - β)) := by rw [map_sub]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_gal_apply, norm_sub_rev]; exact le_max_right _ _
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hα σ) le_rfl)

theorem rpow_axExp_ge_one (n : ℕ) : 1 ≤ (p : ℝ) ^ axExp p n :=
  Real.one_le_rpow one_lt_p_real.le (axExp_nonneg n)

/-- Ax's lemma with the degree-dependent constant `p ^ axExp p n`. -/
theorem ax_of_natDegree (n : ℕ) :
    ∀ α : PadicAlgCl p, (minpoly L α).natDegree = n → ∀ c : ℝ, 0 ≤ c →
      (∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ‖σ α - α‖ ≤ c) →
      ∃ a ∈ L, ‖α - (a : PadicAlgCl p)‖ ≤ (p : ℝ) ^ axExp p n * c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α hn c hc hα
  have hpos : 0 < n := hn ▸ minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral α)
  have hp1 := one_lt_p_real (p := p)
  -- the common final step
  have finish : ∀ β : PadicAlgCl p, ∀ t : ℝ, c ≤ t → ‖α - β‖ ≤ t →
      (minpoly L β).natDegree < n → (p : ℝ) ^ axExp p (minpoly L β).natDegree * t ≤
        (p : ℝ) ^ axExp p n * c →
      ∃ a ∈ L, ‖α - (a : PadicAlgCl p)‖ ≤ (p : ℝ) ^ axExp p n * c := by
    intro β t hct hαβ hdeg hbound
    obtain ⟨a, haL, ha⟩ := ih _ hdeg β rfl t (hc.trans hct) fun σ =>
      (norm_gal_sub_le_of_close hα σ).trans (max_le hct hαβ)
    refine ⟨a, haL, ?_⟩
    have e : α - a = (α - β) + (β - a) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (ha.trans hbound))
    refine le_trans ?_ hbound
    exact hαβ.trans (le_mul_of_one_le_left (hc.trans hct) (rpow_axExp_ge_one _))
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · -- degree one: `α ∈ L`
    have h1 : (minpoly L α).natDegree = 1 := by omega
    obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.mp h1
    refine ⟨a, a.2, ?_⟩
    rw [← ha]
    change ‖(a : PadicAlgCl p) - a‖ ≤ _
    rw [sub_self, norm_zero]
    exact mul_nonneg (by positivity) hc
  obtain ⟨v, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hp.out.ne_one
  by_cases hm1 : m = 1
  · -- `n = p^(k+1)`, take `d = p^k`
    subst hm1
    rw [mul_one] at hnm
    obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := by
      rcases v with _ | k
      · rw [pow_zero] at hnm; omega
      · exact ⟨k, rfl⟩
    have hd : p ^ k < (minpoly L α).natDegree := by
      rw [hn, hnm]; exact Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self k)
    obtain ⟨β, hβdeg, hβ⟩ := exists_root_hasseDeriv hc hα hd
    rw [hn, hnm, norm_choose_prime_pow_succ] at hβ
    set N := p ^ (k + 1) - p ^ k with hN
    have hNval : (N : ℝ) = (p : ℝ) ^ k * ((p : ℝ) - 1) := by
      rw [hN, pow_succ, Nat.cast_sub (Nat.le_mul_of_pos_right _ hp.out.pos)]
      push_cast; ring
    have hN0 : N ≠ 0 := by
      intro h; rw [h, Nat.cast_zero] at hNval
      have : (0 : ℝ) < (p : ℝ) ^ k * ((p : ℝ) - 1) := by
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
      linarith
    set t := (p : ℝ) ^ ((N : ℝ)⁻¹) * c with ht
    have hp0 : (0 : ℝ) ≤ p := by linarith
    have hct : c ≤ t := le_mul_of_one_le_left hc
      (Real.one_le_rpow hp1.le (inv_nonneg.mpr (Nat.cast_nonneg _)))
    have hαβ : ‖α - β‖ ≤ t := by
      have h' : ‖α - β‖ ^ N ≤ t ^ N := by
        rw [ht, mul_pow, Real.rpow_inv_natCast_pow hp0 hN0]
        have := hβ
        rw [inv_mul_le_iff₀ (by linarith)] at this
        exact this
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hc.trans hct) hN0).mp h'
    have hlt : (minpoly L β).natDegree < p ^ (k + 1) := by
      refine lt_of_le_of_lt (hβdeg.trans_eq (by rw [hn, hnm])) ?_
      have := Nat.pow_pos (n := k) hp.out.pos
      omega
    refine finish β t hct hαβ (by rw [hnm]; exact hlt) ?_
    -- exponent bookkeeping
    have hlog : Nat.log p (minpoly L β).natDegree ≤ k := by
      have := Nat.log_lt_of_lt_pow' (b := p) (Nat.succ_ne_zero k) hlt
      omega
    have hexp : axExp p (minpoly L β).natDegree + (N : ℝ)⁻¹ ≤ axExp p n := by
      have hlogn : Nat.log p n = k + 1 := by rw [hnm]; exact Nat.log_pow hp.out.one_lt _
      have : axExp p n = (∑ j ∈ Finset.range k, 1 / ((p : ℝ) ^ j * ((p : ℝ) - 1))) +
          1 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
        rw [axExp, hlogn, Finset.sum_range_succ]
      rw [this, hNval, one_div]
      gcongr
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hlog)
        fun j _ _ => (axExp_term_pos j).le
    rw [ht, ← mul_assoc, ← Real.rpow_add (by linarith)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hp1.le hexp) hc
  · -- `n = p^v m` with `p ∤ m`, `m > 1`: take `d = p^v`
    have hm0 : m ≠ 0 := by rintro rfl; simp at hpm
    have hd : p ^ v < (minpoly L α).natDegree := by
      rw [hn, hnm]
      exact lt_mul_of_one_lt_right (Nat.pow_pos (n := v) hp.out.pos) (by omega)
    obtain ⟨β, hβdeg, hβ⟩ := exists_root_hasseDeriv hc hα hd
    rw [hn, hnm, norm_choose_pow_mul v m hpm, one_mul] at hβ
    have hN0 : p ^ v * m - p ^ v ≠ 0 := by
      have := Nat.pow_pos (n := v) hp.out.pos
      have : p ^ v < p ^ v * m := lt_mul_of_one_lt_right this (by omega)
      omega
    have hαβ : ‖α - β‖ ≤ c := (pow_le_pow_iff_left₀ (norm_nonneg _) hc hN0).mp hβ
    have hlt : (minpoly L β).natDegree < n := by
      have := Nat.pow_pos (n := v) hp.out.pos
      rw [hn] at hd
      omega
    refine finish β c le_rfl hαβ hlt ?_
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hp1.le (axExp_mono hlt.le)) hc

/-- **Ax's lemma** ([Ax, Prop. 1], as quoted in [BC, proof of Prop. 2.1.2]). If all
`G_L`-conjugates of `α ∈ ℚ̄_p` lie within `c` of `α`, then `α` lies within `p^{p/(p-1)²} c` of
an element of `L`. -/
theorem ax (α : PadicAlgCl p) {c : ℝ} (hc : 0 ≤ c)
    (hα : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ‖σ α - α‖ ≤ c) :
    ∃ a ∈ L, ‖α - (a : PadicAlgCl p)‖ ≤ (p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2) * c := by
  obtain ⟨a, haL, ha⟩ := ax_of_natDegree (minpoly L α).natDegree α rfl c hc hα
  refine ⟨a, haL, ha.trans (mul_le_mul_of_nonneg_right ?_ hc)⟩
  exact Real.rpow_le_rpow_of_exponent_le one_lt_p_real.le (axExp_le _)

end PadicHodge
