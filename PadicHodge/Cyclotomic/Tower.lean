/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Norms
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# One step of the cyclotomic tower

Let `ζ` be a primitive `p^{m+2}`-th root of unity in `ℚ̄_p`, `E = ℚ_p(ζ^p)` and `π = ζ - 1`.
Every element of `ℚ_p(ζ)` is `∑_{i<p} a_i ζ^i` with `a_i ∈ E` (`exists_repr`), and the
`π`-adic expansion is orthogonal: `‖b_i‖ ‖π‖^i ≤ ‖∑ b_l π^l‖` for `b_l ∈ E` (`norm_le_of_pi`),
because the norms `‖b_l π^l‖` lie in distinct cosets of the value group `p^{ℤ/φ(p^{m+1})}` of `E`.
Consequently `‖a_i‖ ‖π‖^{p-1} ≤ ‖∑ a_l ζ^l‖` (`norm_le_of_zeta`).
-/

noncomputable section

open Polynomial Module IntermediateField Finset

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_sub_le_max' (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

section Step

variable {ζ : PadicAlgCl p} {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 2)))
include hζ

theorem isPrimitiveRoot_pow_p : IsPrimitiveRoot (ζ ^ p) (p ^ (m + 1)) :=
  hζ.pow (pow_pos hp.out.pos _) (by ring)

theorem finrank_adjoin_pow_p :
    finrank ℚ_[p] ℚ_[p]⟮ζ ^ p⟯ = (p ^ (m + 1)).totient :=
  finrank_adjoin_primitiveRoot (isPrimitiveRoot_pow_p hζ)

omit hζ in
theorem totient_succ_eq : (p ^ (m + 2)).totient = p * (p ^ (m + 1)).totient := by
  rw [Nat.totient_prime_pow_succ hp.out, Nat.totient_prime_pow_succ hp.out]; ring

theorem norm_pi_pow : ‖ζ - 1‖ ^ (p * (p ^ (m + 1)).totient) = (p : ℝ)⁻¹ := by
  rw [← totient_succ_eq (p := p) (m := m)]; exact norm_sub_one_pow_totient hζ

theorem norm_pi_pos : 0 < ‖ζ - 1‖ := by
  rcases (norm_nonneg (ζ - 1)).lt_or_eq with h | h
  · exact h
  · have := norm_pi_pow hζ
    rw [← h, zero_pow (Nat.mul_ne_zero hp.out.ne_zero
      (Nat.totient_pos.mpr (pow_pos hp.out.pos _)).ne')] at this
    exact absurd this.symm (inv_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero))

theorem norm_pi_le_one : ‖ζ - 1‖ ≤ 1 := by
  have h1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp.out.ne_zero) hζ.pow_eq_one
  refine (norm_sub_le_max' ζ 1).trans ?_
  rw [h1, norm_one, max_self]

/-- Norms of nonzero elements of `E` raised to `D = [E : ℚ_p]` are integral powers of `p`. -/
theorem norm_pow_eq_zpow_of_mem {a : PadicAlgCl p} (ha : a ∈ ℚ_[p]⟮ζ ^ p⟯) (ha0 : a ≠ 0) :
    ∃ v : ℤ, ‖a‖ ^ (p ^ (m + 1)).totient = (p : ℝ) ^ v := by
  have : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ ^ p⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  obtain ⟨v, hv⟩ := norm_pow_finrank_eq_zpow ℚ_[p]⟮ζ ^ p⟯ ⟨a, ha⟩
    (fun h => ha0 (congrArg Subtype.val h))
  exact ⟨v, by rw [← finrank_adjoin_pow_p hζ]; exact hv⟩

/-- The norms `‖b_i π^i‖`, `i < p`, `b_i ∈ E ∖ {0}`, are pairwise distinct. -/
theorem norm_mul_pi_pow_ne {a b : PadicAlgCl p} (ha : a ∈ ℚ_[p]⟮ζ ^ p⟯)
    (hb : b ∈ ℚ_[p]⟮ζ ^ p⟯) (ha0 : a ≠ 0) (hb0 : b ≠ 0) {i j : ℕ} (hij : i < j) (hjp : j < p) :
    ‖a * (ζ - 1) ^ i‖ ≠ ‖b * (ζ - 1) ^ j‖ := by
  intro h
  set D := (p ^ (m + 1)).totient
  obtain ⟨u, hu⟩ := norm_pow_eq_zpow_of_mem hζ ha ha0
  obtain ⟨v, hv⟩ := norm_pow_eq_zpow_of_mem hζ hb hb0
  have h2 := congrArg (fun t : ℝ => t ^ (p * D)) h
  simp only [norm_mul, norm_pow, mul_pow] at h2
  have hpi := norm_pi_pow hζ
  have e1 : ‖a‖ ^ (p * D) = (p : ℝ) ^ (p * u) := by
    rw [mul_comm p D, pow_mul, hu, ← zpow_natCast, ← zpow_mul, mul_comm]
  have e2 : ‖b‖ ^ (p * D) = (p : ℝ) ^ (p * v) := by
    rw [mul_comm p D, pow_mul, hv, ← zpow_natCast, ← zpow_mul, mul_comm]
  have e3 : ∀ k : ℕ, (‖ζ - 1‖ ^ k) ^ (p * D) = (p : ℝ) ^ (-(k : ℤ)) := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, hpi, inv_pow, ← zpow_natCast, zpow_neg]
  rw [e1, e2, e3, e3, ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero),
    ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)] at h2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have h3 := zpow_right_injective₀ (by positivity : (0 : ℝ) < p) hp1.ne' h2
  have h4 : (p : ℤ) ∣ (j : ℤ) - i := ⟨v - u, by linarith⟩
  have h5 : (p : ℤ) ≤ (j : ℤ) - i := Int.le_of_dvd (by omega) h4
  omega

/-- **Orthogonality of the `π`-adic expansion** over `E = ℚ_p(ζ^p)`. -/
theorem norm_le_of_pi (b : ℕ → PadicAlgCl p) (hb : ∀ l, b l ∈ ℚ_[p]⟮ζ ^ p⟯) {i : ℕ}
    (hi : i < p) : ‖b i‖ * ‖ζ - 1‖ ^ i ≤ ‖∑ l ∈ range p, b l * (ζ - 1) ^ l‖ := by
  classical
  by_cases hbi : b i = 0
  · rw [hbi, norm_zero, zero_mul]; exact norm_nonneg _
  set s := (range p).filter (fun l => b l ≠ 0) with hs
  have hsum : ∑ l ∈ range p, b l * (ζ - 1) ^ l = ∑ l ∈ s, b l * (ζ - 1) ^ l := by
    rw [hs, Finset.sum_filter_of_ne]
    intro l _ h
    exact left_ne_zero_of_mul h
  have his : i ∈ s := by simp [hs, hi, hbi]
  have hne : s.Nonempty := ⟨i, his⟩
  rw [hsum, IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne hne]
  · rw [← norm_pow, ← norm_mul]
    exact Finset.le_sup' (fun l => ‖b l * (ζ - 1) ^ l‖) his
  · intro k hk l hl hkl
    simp only [hs, coe_filter, mem_range, Set.mem_setOf_eq] at hk hl
    rcases lt_or_gt_of_ne hkl with h | h
    · exact norm_mul_pi_pow_ne hζ (hb k) (hb l) hk.2 hl.2 h hl.1
    · exact (norm_mul_pi_pow_ne hζ (hb l) (hb k) hl.2 hk.2 h hk.1).symm

omit hζ in
/-- Change of basis `ζ^i = ∑_l binom(i,l) π^l`. -/
theorem sum_zeta_eq_sum_pi (a : ℕ → PadicAlgCl p) :
    ∑ i ∈ range p, a i * ζ ^ i =
      ∑ l ∈ range p, (∑ i ∈ range p, (i.choose l : PadicAlgCl p) * a i) * (ζ - 1) ^ l := by
  have h : ∀ i ∈ range p, a i * ζ ^ i =
      ∑ l ∈ range p, (i.choose l : PadicAlgCl p) * a i * (ζ - 1) ^ l := by
    intro i hi
    have e : ζ = (ζ - 1) + 1 := by ring
    conv_lhs => rw [e, add_pow]
    rw [Finset.mul_sum]
    have hsub : range (i + 1) ⊆ range p := range_subset_range.mpr (mem_range.mp hi)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun l _ => ?_
      rw [one_pow, mul_one]; ring
    · intro l _ hl
      rw [mem_range, not_lt] at hl
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]

omit hζ in
theorem norm_natCast_le_one' (n : ℕ) : ‖(n : PadicAlgCl p)‖ ≤ 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) n]
  rw [show ‖algebraMap ℚ_[p] (PadicAlgCl p) n‖ = ‖(n : ℚ_[p])‖ from PadicAlgCl.norm_extends p _]
  exact_mod_cast Padic.norm_int_le_one (p := p) n

/-- Coefficients in the basis `1, ζ, …, ζ^{p-1}` are bounded by the norm:
`‖a_i‖ ‖π‖^{p-1} ≤ ‖∑ a_l ζ^l‖`. -/
theorem norm_le_of_zeta (a : ℕ → PadicAlgCl p) (ha : ∀ l, a l ∈ ℚ_[p]⟮ζ ^ p⟯) {i : ℕ}
    (hi : i < p) : ‖a i‖ * ‖ζ - 1‖ ^ (p - 1) ≤ ‖∑ l ∈ range p, a l * ζ ^ l‖ := by
  set y := ∑ l ∈ range p, a l * ζ ^ l
  set b : ℕ → PadicAlgCl p := fun l => ∑ i ∈ range p, (i.choose l : PadicAlgCl p) * a i with hbdef
  have hbE : ∀ l, b l ∈ ℚ_[p]⟮ζ ^ p⟯ := fun l =>
    sum_mem fun i _ => mul_mem (IntermediateField.natCast_mem _ _) (ha i)
  have hy : y = ∑ l ∈ range p, b l * (ζ - 1) ^ l := sum_zeta_eq_sum_pi a
  have hπ0 := norm_pi_pos hζ
  have hπ1 := norm_pi_le_one hζ
  set K := ‖y‖ / ‖ζ - 1‖ ^ (p - 1) with hK
  have hpos : 0 < ‖ζ - 1‖ ^ (p - 1) := pow_pos hπ0 _
  have hK0 : 0 ≤ K := div_nonneg (norm_nonneg _) hpos.le
  -- all `‖b_l‖ ≤ K`
  have hb : ∀ l < p, ‖b l‖ ≤ K := by
    intro l hl
    rw [hK, le_div_iff₀ hpos]
    have h1 := norm_le_of_pi hζ b hbE hl
    rw [← hy] at h1
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hπ0.le hπ1 (by omega)) (norm_nonneg _)
  -- downward induction: all `‖a_i‖ ≤ K`
  have ha' : ∀ t, ∀ i, p ≤ i + t + 1 → i < p → ‖a i‖ ≤ K := by
    intro t
    induction t with
    | zero =>
      intro i h1 h2
      have hi : i = p - 1 := by omega
      have : b i = a i := by
        rw [hbdef]
        simp only
        rw [Finset.sum_eq_single i]
        · rw [Nat.choose_self, Nat.cast_one, one_mul]
        · intro k hk hki
          rw [mem_range] at hk
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
        · intro h; exact absurd (mem_range.mpr h2) h
      rw [← this]; exact hb i h2
    | succ t ih =>
      intro i h1 h2
      by_cases hit : p ≤ i + t + 1
      · exact ih i hit h2
      have hsplit : b i = a i + ∑ k ∈ (range p).filter (fun k => i < k),
          (k.choose i : PadicAlgCl p) * a k := by
        rw [hbdef]; dsimp only
        rw [← Finset.sum_filter_add_sum_filter_not (range p) (fun k => i < k), add_comm]
        congr 1
        rw [Finset.sum_eq_single_of_mem i (by simp [h2])]
        · rw [Nat.choose_self, Nat.cast_one, one_mul]
        · intro k hk hki
          simp only [mem_filter, mem_range, not_lt] at hk
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
      have e : a i = b i - ∑ k ∈ (range p).filter (fun k => i < k),
          (k.choose i : PadicAlgCl p) * a k := by
        rw [hsplit]; ring
      rw [e]
      refine (norm_sub_le_max' _ _).trans (max_le (hb i h2) ?_)
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hK0 fun k hk => ?_
      rw [mem_filter, mem_range] at hk
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_natCast_le_one' _)).trans
        (ih k (by omega) hk.1)
  have := ha' p i (by omega) hi
  rwa [hK, le_div_iff₀ hpos] at this

omit hζ in
/-- Every element of `ℚ_p(ζ)` is `∑_{i<p} a_i ζ^i` with `a_i ∈ ℚ_p(ζ^p)`. -/
theorem exists_repr {y : PadicAlgCl p} (hy : y ∈ ℚ_[p]⟮ζ⟯) :
    ∃ a : ℕ → PadicAlgCl p, (∀ i, a i ∈ ℚ_[p]⟮ζ ^ p⟯) ∧ y = ∑ i ∈ range p, a i * ζ ^ i := by
  classical
  have hint : IsIntegral ℚ_[p] ζ := Algebra.IsIntegral.isIntegral ζ
  rw [← mem_toSubalgebra, adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨f, rfl⟩ := hy
  refine ⟨fun i => ∑ n ∈ f.support.filter (fun n => n % p = i),
    algebraMap ℚ_[p] (PadicAlgCl p) (f.coeff n) * (ζ ^ p) ^ (n / p), ?_, ?_⟩
  · intro i
    exact sum_mem fun n _ => mul_mem (IntermediateField.algebraMap_mem _ _)
      (pow_mem (mem_adjoin_simple_self _ _) _)
  · change aeval ζ f = _
    simp only [Finset.sum_mul]
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % p) (t := range p)
      (fun n _ => mem_range.mpr (Nat.mod_lt _ hp.out.pos))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun n hn => ?_
    rw [mem_filter] at hn
    rw [mul_assoc, ← pow_mul, ← hn.2, ← pow_add, Nat.div_add_mod]

end Step

end PadicHodge
