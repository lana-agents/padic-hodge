/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Galois.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Norms of roots of unity in `ℚ̄_p` and the degree of `ℚ_p(ζ_{p^m})`

* `norm_eq_one_of_pow_eq_one`: roots of unity have norm `1`.
* `norm_sub_one_pow_totient`: for a primitive `p^{m+1}`-th root of unity `ζ`,
  `‖ζ - 1‖ ^ φ(p^{m+1}) = p⁻¹` (from `Φ_{p^{m+1}}(1) = p`).
* `norm_pow_finrank_eq_zpow`: for `a` in a finite extension `F/ℚ_p` of degree `D` inside `ℚ̄_p`,
  `‖a‖ ^ D ∈ p ^ ℤ`.
* `finrank_adjoin_primitiveRoot`: `[ℚ_p(ζ) : ℚ_p] = φ(p^{m+1})` (hence `Φ_{p^{m+1}}` is
  irreducible over `ℚ_p`); this follows from the two previous facts.
-/

noncomputable section

open Polynomial Module IntermediateField

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_eq_one_of_pow_eq_one {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (h : ζ ^ N = 1) :
    ‖ζ‖ = 1 := by
  have : ‖ζ‖ ^ N = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).mp this

theorem norm_geom_sum_le {ζ : PadicAlgCl p} (hζ : ‖ζ‖ = 1) (a : ℕ) :
    ‖∑ i ∈ Finset.range a, ζ ^ i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
    rw [norm_pow, hζ, one_pow]

theorem norm_pow_sub_one_le {ζ : PadicAlgCl p} (hζ : ‖ζ‖ = 1) (a : ℕ) :
    ‖ζ ^ a - 1‖ ≤ ‖ζ - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_geom_sum_le hζ a)

theorem norm_sub_one_eq_of_isPrimitiveRoot {ζ μ : PadicAlgCl p} {n : ℕ} (hn : n ≠ 0)
    (hζ : IsPrimitiveRoot ζ n) (hμ : IsPrimitiveRoot μ n) : ‖μ - 1‖ = ‖ζ - 1‖ := by
  haveI : NeZero n := ⟨hn⟩
  have hζ1 := norm_eq_one_of_pow_eq_one hn hζ.pow_eq_one
  have hμ1 := norm_eq_one_of_pow_eq_one hn hμ.pow_eq_one
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
  obtain ⟨b, -, hb⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine le_antisymm ?_ ?_
  · rw [← ha]; exact norm_pow_sub_one_le hζ1 a
  · rw [← hb]; exact norm_pow_sub_one_le hμ1 b

theorem norm_sub_one_pow_totient {ζ : PadicAlgCl p} {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) :
    ‖ζ - 1‖ ^ (p ^ (m + 1)).totient = (p : ℝ)⁻¹ := by
  have hn : p ^ (m + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have h1 := eval_one_cyclotomic_prime_pow (R := PadicAlgCl p) (p := p) m
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod] at h1
  have h2 := congrArg norm h1
  rw [norm_prod] at h2
  simp only [eval_sub, eval_X, eval_C] at h2
  have h3 : ∀ μ ∈ primitiveRoots (p ^ (m + 1)) (PadicAlgCl p), ‖1 - μ‖ = ‖ζ - 1‖ := by
    intro μ hμ
    rw [norm_sub_rev]
    exact norm_sub_one_eq_of_isPrimitiveRoot hn hζ
      ((mem_primitiveRoots (Nat.pos_of_ne_zero hn)).mp hμ)
  rw [Finset.prod_congr rfl h3, Finset.prod_const, hζ.card_primitiveRoots] at h2
  rw [h2, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends p _).trans Padic.norm_p

/-- In a finite extension of degree `D` of `ℚ_p` inside `ℚ̄_p`, `‖a‖ ^ D` is an integral power
of `p` for `a ≠ 0`. -/
theorem norm_pow_finrank_eq_zpow (F : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] F] (a : F) (ha : a ≠ 0) :
    ∃ v : ℤ, ‖(a : PadicAlgCl p)‖ ^ finrank ℚ_[p] F = (p : ℝ) ^ v := by
  have hint : IsIntegral ℚ_[p] a := Algebra.IsIntegral.isIntegral a
  obtain ⟨e, he⟩ := minpoly.degree_dvd hint
  set d := (minpoly ℚ_[p] a).natDegree with hd
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hc : (minpoly ℚ_[p] a).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint ha
  have hnorm : ‖(a : PadicAlgCl p)‖ = ‖(minpoly ℚ_[p] a).coeff 0‖ ^ (1 / d : ℝ) := by
    rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
      ← IntermediateField.minpoly_eq]
  refine ⟨-((minpoly ℚ_[p] a).coeff 0).valuation * e, ?_⟩
  rw [hnorm, he, Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_natCast,
    ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  field_simp

/-- `ℚ_p(ζ_{p^{m+1}})` has degree `φ(p^{m+1})` over `ℚ_p`. -/
theorem finrank_adjoin_primitiveRoot {ζ : PadicAlgCl p} {m : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (m + 1))) :
    finrank ℚ_[p] ℚ_[p]⟮ζ⟯ = (p ^ (m + 1)).totient := by
  have hn : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hint : IsIntegral ℚ_[p] ζ := Algebra.IsIntegral.isIntegral ζ
  have : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint
  set D := finrank ℚ_[p] ℚ_[p]⟮ζ⟯ with hD
  set φ := (p ^ (m + 1)).totient with hφ
  have hφ0 : 0 < φ := Nat.totient_pos.mpr hn
  -- `D ≤ φ`: `ζ` is a root of `Φ_{p^{m+1}}`
  have hle : D ≤ φ := by
    rw [hD, IntermediateField.adjoin.finrank hint, hφ, ← natDegree_cyclotomic (p ^ (m + 1)) ℚ_[p]]
    refine natDegree_le_of_dvd (minpoly.dvd _ _ ?_) (cyclotomic_ne_zero _ _)
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (isRoot_cyclotomic_iff.mpr hζ)
  -- `φ ∣ D`: `‖ζ - 1‖ = p^{-1/φ}` lies in the value group `p^{ℤ/D}`
  have hz : (⟨ζ - 1, sub_mem (IntermediateField.mem_adjoin_simple_self _ _) (one_mem _)⟩ :
      ℚ_[p]⟮ζ⟯) ≠ 0 := by
    intro h
    have : ζ - 1 = 0 := congrArg Subtype.val h
    have h1 := norm_sub_one_pow_totient hζ
    rw [this, norm_zero, zero_pow hφ0.ne'] at h1
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero)) h1.symm
  obtain ⟨v, hv⟩ := norm_pow_finrank_eq_zpow ℚ_[p]⟮ζ⟯ _ hz
  have hv' : ‖ζ - 1‖ ^ D = (p : ℝ) ^ v := hv
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have key : ((p : ℝ) ^ v) ^ φ = ((p : ℝ)⁻¹) ^ D := by
    rw [← hv', ← pow_mul, mul_comm, pow_mul, norm_sub_one_pow_totient hζ]
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, inv_zpow'] at key
  have key' := zpow_right_injective₀ (by positivity : (0 : ℝ) < p) hp1.ne' key
  have hdvd : (φ : ℤ) ∣ D := ⟨-v, by linarith⟩
  have hD0 : 0 < D := Module.finrank_pos
  have := Nat.le_of_dvd hD0 (Int.natCast_dvd_natCast.mp hdvd)
  omega

end PadicHodge
