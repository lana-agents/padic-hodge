/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Tower

/-!
# Tate's normalised trace for one step of the cyclotomic tower

Let `ζ` be a primitive `p^{m+2}`-th root of unity, `E = ℚ_p(ζ^p)`, and `δ ∈ Gal(ℚ̄_p/ℚ_p)` with
`δ ζ = ζ ω` for a primitive `p`-th root of unity `ω`. The averaging operator
`T y = p⁻¹ ∑_{s<p} δ^s y` is the normalised trace `ℚ_p(ζ) → E`:
`T (∑ a_i ζ^i) = a_0` (`avg_repr`). We prove ([BC, §14.1], following Tate):

* `avg_mem`: `T` maps `ℚ_p(ζ)` to `E`; `avg_of_mem`: `T` is the identity on `E`;
* `norm_avg_le`: `‖T y‖ * ‖π‖^{p-1} ≤ ‖y‖`;
* `norm_le_of_avg_eq_zero`: if `T y = 0` then `‖y‖ * (‖ω - 1‖ * ‖π‖^{p-1}) ≤ ‖δ y - y‖`.
-/

noncomputable section

open Polynomial Module IntermediateField Finset

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- The averaging operator `y ↦ p⁻¹ ∑_{s<p} δ^s y`. -/
def avg (δ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : PadicAlgCl p) : PadicAlgCl p :=
  (p : PadicAlgCl p)⁻¹ * ∑ s ∈ range p, (δ ^ s) y

theorem avg_add (δ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y z : PadicAlgCl p) :
    avg δ (y + z) = avg δ y + avg δ z := by
  simp only [avg, map_add, Finset.sum_add_distrib, mul_add]

theorem avg_sub (δ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y z : PadicAlgCl p) :
    avg δ (y - z) = avg δ y - avg δ z := by
  simp only [avg, map_sub, Finset.sum_sub_distrib, mul_sub]

theorem gal_natCast_inv (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    σ (p : PadicAlgCl p)⁻¹ = (p : PadicAlgCl p)⁻¹ := by
  rw [map_inv₀, map_natCast]

/-- `avg δ` commutes with every automorphism commuting with `δ`. -/
theorem avg_comm {δ γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (h : δ * γ = γ * δ)
    (y : PadicAlgCl p) : avg δ (γ y) = γ (avg δ y) := by
  simp only [avg, map_mul, map_sum, gal_natCast_inv]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, (Commute.pow_left h s).eq]

theorem norm_avg_le_of_le {δ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {y : PadicAlgCl p} :
    ‖avg δ y‖ ≤ p * ‖y‖ := by
  rw [avg, norm_mul, norm_inv]
  have hp0 : (0 : ℝ) < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.mpr (by exact_mod_cast hp.out.ne_zero)
  have hpn : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
    exact (PadicAlgCl.norm_extends p _).trans Padic.norm_p
  rw [hpn, inv_inv]
  gcongr
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun s _ => ?_
  rw [norm_aut_apply]

section Step

variable {ζ ω : PadicAlgCl p} {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 2)))
  (hω : IsPrimitiveRoot ω p) {δ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hδ : δ ζ = ζ * ω)
include hζ hω hδ

omit hδ in
theorem omega_mem : ω ∈ ℚ_[p]⟮ζ ^ p⟯ := by
  have h1 : IsPrimitiveRoot ((ζ ^ p) ^ p ^ m) p :=
    (isPrimitiveRoot_pow_p hζ).pow (pow_pos hp.out.pos _) (by ring)
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hω.pow_eq_one
  rw [← hi]
  exact pow_mem (pow_mem (mem_adjoin_simple_self _ _) _) _

omit hζ in
theorem delta_pow_p : δ (ζ ^ p) = ζ ^ p := by
  rw [map_pow, hδ, mul_pow, hω.pow_eq_one, mul_one]

omit hζ in
theorem delta_fix {a : PadicAlgCl p} (ha : a ∈ ℚ_[p]⟮ζ ^ p⟯) : δ a = a := by
  have hint : IsIntegral ℚ_[p] (ζ ^ p) := Algebra.IsIntegral.isIntegral _
  rw [← mem_toSubalgebra, adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  change δ (aeval (ζ ^ p) f) = aeval (ζ ^ p) f
  rw [← Polynomial.aeval_algHom_apply, delta_pow_p hω hδ]

omit hζ in
theorem delta_pow_fix (s : ℕ) {a : PadicAlgCl p} (ha : a ∈ ℚ_[p]⟮ζ ^ p⟯) : (δ ^ s) a = a := by
  induction s with
  | zero => rfl
  | succ s ih => rw [pow_succ', AlgEquiv.mul_apply, ih, delta_fix hω hδ ha]

theorem delta_pow_zeta (s : ℕ) : (δ ^ s) ζ = ζ * ω ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, hδ, map_pow,
      delta_fix hω hδ (omega_mem hζ hω), pow_succ]
    ring

theorem delta_pow_repr (s : ℕ) (a : ℕ → PadicAlgCl p) (ha : ∀ i, a i ∈ ℚ_[p]⟮ζ ^ p⟯) :
    (δ ^ s) (∑ i ∈ range p, a i * ζ ^ i) = ∑ i ∈ range p, (a i * (ω ^ i) ^ s) * ζ ^ i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, delta_pow_fix hω hδ s (ha i), delta_pow_zeta hζ hω hδ]
  ring

omit hζ hδ in
theorem sum_omega_pow (i : ℕ) (hi : i < p) :
    ∑ s ∈ range p, (ω ^ i) ^ s = if i = 0 then (p : PadicAlgCl p) else 0 := by
  split_ifs with h
  · subst h; simp
  · have : IsPrimitiveRoot (ω ^ i) p :=
      hω.pow_of_coprime i ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
        (fun hd => h (Nat.eq_zero_of_dvd_of_lt hd hi)))))
    exact this.geom_sum_eq_zero hp.out.one_lt

/-- `T (∑ a_i ζ^i) = a_0`. -/
theorem avg_repr (a : ℕ → PadicAlgCl p) (ha : ∀ i, a i ∈ ℚ_[p]⟮ζ ^ p⟯) :
    avg δ (∑ i ∈ range p, a i * ζ ^ i) = a 0 := by
  rw [avg]
  simp_rw [delta_pow_repr hζ hω hδ _ a ha]
  rw [Finset.sum_comm]
  have : ∀ i ∈ range p, ∑ s ∈ range p, a i * (ω ^ i) ^ s * ζ ^ i =
      a i * ζ ^ i * (if i = 0 then (p : PadicAlgCl p) else 0) := by
    intro i hi
    rw [← sum_omega_pow hω i (mem_range.mp hi), Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [Finset.sum_congr rfl this]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', mem_range, hp.out.pos, if_true, pow_zero,
    mul_one]
  rw [← mul_assoc, mul_comm _ (a 0), mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hp.out.ne_zero),
    mul_one]

theorem delta_sub_repr (a : ℕ → PadicAlgCl p) (ha : ∀ i, a i ∈ ℚ_[p]⟮ζ ^ p⟯) :
    δ (∑ i ∈ range p, a i * ζ ^ i) - ∑ i ∈ range p, a i * ζ ^ i =
      ∑ i ∈ range p, (a i * (ω ^ i - 1)) * ζ ^ i := by
  have h := delta_pow_repr hζ hω hδ 1 a ha
  rw [pow_one] at h
  rw [h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem avg_mem {y : PadicAlgCl p} (hy : y ∈ ℚ_[p]⟮ζ⟯) : avg δ y ∈ ℚ_[p]⟮ζ ^ p⟯ := by
  obtain ⟨a, ha, rfl⟩ := exists_repr hy
  rw [avg_repr hζ hω hδ a ha]
  exact ha 0

omit hζ in
theorem avg_of_mem {a : PadicAlgCl p} (ha : a ∈ ℚ_[p]⟮ζ ^ p⟯) : avg δ a = a := by
  rw [avg, Finset.sum_congr rfl fun s _ => delta_pow_fix hω hδ s ha, Finset.sum_const,
    card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hp.out.ne_zero),
    one_mul]

theorem norm_avg_le {y : PadicAlgCl p} (hy : y ∈ ℚ_[p]⟮ζ⟯) :
    ‖avg δ y‖ * ‖ζ - 1‖ ^ (p - 1) ≤ ‖y‖ := by
  obtain ⟨a, ha, rfl⟩ := exists_repr hy
  rw [avg_repr hζ hω hδ a ha]
  exact norm_le_of_zeta hζ a ha hp.out.pos

theorem norm_le_of_avg_eq_zero {y : PadicAlgCl p} (hy : y ∈ ℚ_[p]⟮ζ⟯) (h0 : avg δ y = 0) :
    ‖y‖ * (‖ω - 1‖ * ‖ζ - 1‖ ^ (p - 1)) ≤ ‖δ y - y‖ := by
  obtain ⟨a, ha, rfl⟩ := exists_repr hy
  rw [avg_repr hζ hω hδ a ha] at h0
  rw [delta_sub_repr hζ hω hδ a ha]
  set z := ∑ i ∈ range p, (a i * (ω ^ i - 1)) * ζ ^ i
  have hc : ∀ i, a i * (ω ^ i - 1) ∈ ℚ_[p]⟮ζ ^ p⟯ := fun i =>
    mul_mem (ha i) (sub_mem (pow_mem (omega_mem hζ hω) _) (one_mem _))
  have hω1 : 0 < ‖ω - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]; exact hω.ne_one hp.out.one_lt
  have hπ := pow_pos (norm_pi_pos hζ) (p - 1)
  have hpos : 0 < ‖ω - 1‖ * ‖ζ - 1‖ ^ (p - 1) := mul_pos hω1 hπ
  have hζ1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp.out.ne_zero) hζ.pow_eq_one
  rw [← le_div_iff₀ hpos]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (div_nonneg (norm_nonneg _) hpos.le) fun i hi => ?_
  rw [norm_mul, norm_pow, hζ1, one_pow, mul_one, le_div_iff₀ hpos]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [h0, norm_zero, zero_mul]; exact norm_nonneg _
  · have h1 := norm_le_of_zeta hζ _ hc (mem_range.mp hi)
    have hωi : ‖ω ^ i - 1‖ = ‖ω - 1‖ := by
      have : IsPrimitiveRoot (ω ^ i) p :=
        hω.pow_of_coprime i ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
          (fun hd => (Nat.lt_irrefl _ (lt_of_lt_of_le (mem_range.mp hi)
            (Nat.le_of_dvd hi0 hd)))))))
      exact norm_sub_one_eq_of_isPrimitiveRoot hp.out.ne_zero hω this
    rw [norm_mul, hωi] at h1
    calc ‖a i‖ * (‖ω - 1‖ * ‖ζ - 1‖ ^ (p - 1)) = ‖a i‖ * ‖ω - 1‖ * ‖ζ - 1‖ ^ (p - 1) := by ring
      _ ≤ _ := h1

end Step

end PadicHodge
