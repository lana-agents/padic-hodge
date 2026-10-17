/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AlmostEtale.Step

/-!
# The cyclotomic input to Faltings' step

Let `ζ` be a primitive `p^{m+2}`-th root of unity, `F = ℚ_p(ζ^p)`, `F' = ℚ_p(ζ) = F(ζ)`.

* `mem_adj_of_mem_cyc`: `O_{F'} = O_F[ζ]` (from the orthogonality of the `π`-adic expansion,
  `Cyclotomic/Tower.lean`, and the value group of `F`);
* `mp_zeta`: the minimal polynomial of `ζ` over `F` is `X^p − ζ^p`, so its derivative at `ζ` is
  `p ζ^{p−1}`: the different of `O_{F'}/O_F` is `(p)` ([BC, Ex. 13.7.4 (3)]:
  `Ω_{A_n/A_{n−1}} ≅ A_n/p`);
* `cyc_transitivity`: if `ℚ_p(z) ⊇ F'` and `‖z‖ ≤ 1`, then `‖G'(z)‖ ≤ ‖p‖ ‖g'(z)‖` for the minimal
  polynomials `G`, `g` of `z` over `F`, `F'` (transitivity of the different, proved with traces:
  `Tr_{F(z)/F} = Tr_{F'/F} ∘ Tr_{F'(z)/F'}` and Euler's lemma for `ζ` and for `z`).
-/

noncomputable section

open Polynomial IntermediateField Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K̄" => PadicAlgCl p

/-- Tower law `[ℚ_p(z) : ℚ_p] = [F : ℚ_p] [F(z) : F]` for `F ⊆ ℚ_p(z)`. -/
theorem finrank_adjoin_eq_mul {F : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] F] {z : PadicAlgCl p} (hF : F ≤ ℚ_[p]⟮z⟯) :
    finrank ℚ_[p] ℚ_[p]⟮z⟯ = finrank ℚ_[p] F * dg F z := by
  have h1 := Module.finrank_mul_finrank ℚ_[p] F F⟮z⟯
  rw [finrank_adjoin_eq_dg] at h1
  rw [h1]
  have h2 : (F⟮z⟯).restrictScalars ℚ_[p] = ℚ_[p]⟮z⟯ := by
    rw [restrictScalars_adjoin]
    refine le_antisymm (adjoin_le_iff.mpr (Set.union_subset (fun x hx => hF hx) ?_))
      (adjoin.mono _ _ _ Set.subset_union_right)
    exact Set.singleton_subset_iff.mpr (mem_adjoin_simple_self _ _)
  rw [← h2]
  rfl

section Zeta

variable {ζ : PadicAlgCl p} {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 2)))
include hζ

/-- `O_{ℚ_p(ζ)} = O_{ℚ_p(ζ^p)}[ζ]`. -/
theorem mem_adj_of_mem_cyc {t : PadicAlgCl p} (ht : t ∈ ℚ_[p]⟮ζ⟯) (ht1 : ‖t‖ ≤ 1) :
    t ∈ adj (OK ℚ_[p]⟮ζ ^ p⟯) ζ := by
  obtain ⟨a, haF, rfl⟩ := exists_repr (p := p) ht
  have hpi0 := norm_pi_pos hζ
  have hpi := norm_pi_pow hζ
  set φ := (p ^ (m + 1)).totient with hφ
  have hφ0 : 0 < φ := Nat.totient_pos.mpr (pow_pos hp.out.pos _)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have ha1 : ∀ i < p, ‖a i‖ ≤ 1 := by
    intro i hi
    by_cases ha0 : a i = 0
    · rw [ha0, norm_zero]; exact zero_le_one
    obtain ⟨v, hv⟩ := norm_pow_eq_zpow_of_mem hζ (haF i) ha0
    have hle := (norm_le_of_zeta hζ a haF hi).trans ht1
    -- raise to the power `p φ`
    have h2 : (‖a i‖ * ‖ζ - 1‖ ^ (p - 1)) ^ (p * φ) ≤ 1 :=
      pow_le_one₀ (by positivity) hle
    rw [← hφ] at hv
    have e : (‖a i‖ * ‖ζ - 1‖ ^ (p - 1)) ^ (p * φ) =
        (‖a i‖ ^ φ) ^ p * (‖ζ - 1‖ ^ (p * φ)) ^ (p - 1) := by ring
    rw [e, hpi, hv] at h2
    -- `p^{v p} p^{-(p-1)} ≤ 1` forces `v ≤ 0`
    have hv0 : v ≤ 0 := by
      by_contra hv0
      push Not at hv0
      have e1 : ((p : ℝ) ^ v) ^ p ≥ (p : ℝ) ^ p := by
        apply pow_le_pow_left₀ (by positivity)
        calc (p : ℝ) = (p : ℝ) ^ (1 : ℤ) := by simp
          _ ≤ (p : ℝ) ^ v := zpow_le_zpow_right₀ hp1.le (by omega)
      have e2 : ((p : ℝ)⁻¹) ^ (p - 1) * (p : ℝ) ^ p = p := by
        rw [inv_pow, ← Nat.sub_add_cancel hp.out.one_le, pow_succ]
        simp only [Nat.add_sub_cancel]
        field_simp
      have : (p : ℝ) ≤ 1 := by
        calc (p : ℝ) = ((p : ℝ)⁻¹) ^ (p - 1) * (p : ℝ) ^ p := e2.symm
          _ ≤ ((p : ℝ)⁻¹) ^ (p - 1) * ((p : ℝ) ^ v) ^ p :=
            mul_le_mul_of_nonneg_left e1 (by positivity)
          _ = ((p : ℝ) ^ v) ^ p * ((p : ℝ)⁻¹) ^ (p - 1) := by ring
          _ ≤ 1 := h2
      linarith
    have : ‖a i‖ ^ φ ≤ 1 := by
      rw [hv]; exact zpow_le_one_of_nonpos₀ hp1.le hv0
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hφ0.ne').mp this
  refine mem_adj.mpr ⟨∑ i ∈ Finset.range p, C (a i) * X ^ i, ?_, ?_⟩
  · refine sum_mem fun i hi => mul_mem (C_mem_polyOver ⟨haF i, ha1 i (Finset.mem_range.mp hi)⟩)
      (pow_mem (X_mem_polyOver _) _)
  · simp [eval_finsetSum]

theorem norm_zeta : ‖ζ‖ = 1 :=
  norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp.out.ne_zero) hζ.pow_eq_one

/-- The minimal polynomial of `ζ` over `ℚ_p(ζ^p)` is `X^p − ζ^p`. -/
theorem mp_zeta : mp ℚ_[p]⟮ζ ^ p⟯ ζ = X ^ p - C (ζ ^ p) := by
  have hFd : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ ^ p⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  have hle : ℚ_[p]⟮ζ ^ p⟯ ≤ ℚ_[p]⟮ζ⟯ :=
    adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self _ _) _)
  have hdeg : dg ℚ_[p]⟮ζ ^ p⟯ ζ = p := by
    have h1 := finrank_adjoin_eq_mul hle
    rw [finrank_adjoin_primitiveRoot hζ, finrank_adjoin_pow_p hζ, totient_succ_eq] at h1
    have hφ0 : 0 < (p ^ (m + 1)).totient := Nat.totient_pos.mpr (pow_pos hp.out.pos _)
    rw [mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_left hφ0 h1).symm
  have hQ : (X ^ p - C (ζ ^ p) : (PadicAlgCl p)[X]).Monic :=
    monic_X_pow_sub_C _ hp.out.ne_zero
  have hζp : ζ ^ p ∈ OK ℚ_[p]⟮ζ ^ p⟯ :=
    ⟨mem_adjoin_simple_self _ _, by
      change ‖ζ ^ p‖ ≤ 1
      rw [norm_pow, norm_zeta hζ, one_pow]⟩
  have hQO : (X ^ p - C (ζ ^ p) : (PadicAlgCl p)[X]) ∈ polyOver (OK ℚ_[p]⟮ζ ^ p⟯) :=
    sub_mem (pow_mem (X_mem_polyOver _) _) (C_mem_polyOver hζp)
  have hQz : (X ^ p - C (ζ ^ p) : (PadicAlgCl p)[X]).eval ζ = 0 := by
    rw [eval_sub, eval_pow, eval_X, eval_C, sub_self]
  obtain ⟨k, -, hk⟩ := exists_eq_mp_mul _ (norm_zeta hζ).le hQO hQz
  refine (eq_of_monic_of_dvd_of_natDegree_le (mp_monic _ ζ) hQ ⟨k, hk⟩ ?_).symm
  rw [natDegree_X_pow_sub_C, natDegree_mp]
  exact hdeg.ge

theorem derivative_mp_zeta :
    (derivative (mp ℚ_[p]⟮ζ ^ p⟯ ζ)).eval ζ = (p : PadicAlgCl p) * ζ ^ (p - 1) := by
  rw [mp_zeta hζ, derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
    eval_pow, eval_X]

theorem dg_zeta : dg ℚ_[p]⟮ζ ^ p⟯ ζ = p := by
  rw [dg, ← natDegree_mp, mp_zeta hζ, natDegree_X_pow_sub_C]

end Zeta

theorem eval_mem_of_coeff_mem (E : IntermediateField ℚ_[p] (PadicAlgCl p)) {q : (PadicAlgCl p)[X]}
    (hq : ∀ n, q.coeff n ∈ E) {z : PadicAlgCl p} (hz : z ∈ E) : q.eval z ∈ E := by
  rw [eval_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hq i) (pow_mem hz _)

/-- **Transitivity of the different**, abstract form: for `F ⊆ F' = F(ζ)` with
`O_{F'} = O_F[ζ]`, `[F' : F] = p`, `g_ζ'(ζ) = p ζ^{p-1}`, and `z` with `F' ⊆ F(z)`,
`[F(z) : F] = p [F'(z) : F']`: `‖G'(z)‖ ≤ ‖p‖ ‖g'(z)‖`. -/
theorem transitivity_of_data {F F' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hFF' : F ≤ F')
    {ζ : PadicAlgCl p} (hζ1 : ‖ζ‖ = 1) (hadj : ∀ t ∈ F', ‖t‖ ≤ 1 → t ∈ adj (OK F) ζ)
    (hdζ : dg F ζ = p) (hcζ : (derivative (mp F ζ)).eval ζ = (p : PadicAlgCl p) * ζ ^ (p - 1))
    {z : PadicAlgCl p} (hz : ‖z‖ ≤ 1) (hF'z : F' ≤ (F⟮z⟯).restrictScalars ℚ_[p])
    (hN : dg F z = p * dg F' z) :
    ‖(derivative (mp F z)).eval z‖ ≤
      ‖(p : PadicAlgCl p)‖ * ‖(derivative (mp F' z)).eval z‖ := by
  have hp0 : (p : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  set E := (F⟮z⟯).restrictScalars ℚ_[p] with hE
  set b := (derivative (mp F' z)).eval z with hb
  have hb0 : b ≠ 0 := derivative_mp_ne_zero F' z
  set n' := dg F' z
  have hn'0 : (n' : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.mpr (dg_pos F' z).ne'
  have hbE : b ∈ E := by
    refine eval_mem_of_coeff_mem E (fun n => ?_) (mem_restrictScalars_adjoin F z)
    rw [coeff_derivative]
    exact mul_mem (hF'z (coeff_mp_mem F' z _)) (by exact_mod_cast IntermediateField.natCast_mem E _)
  set y := ((p : PadicAlgCl p) * b)⁻¹ with hy
  have hyE : y ∈ E := inv_mem (mul_mem (IntermediateField.natCast_mem E p) hbE)
  have hyF : y ∈ F⟮z⟯ := hyE
  have htr : ∀ j < dg F z, (dg F z : PadicAlgCl p) * nt F (y * z ^ j) ∈ OK F := by
    intro j _
    set t := (n' : PadicAlgCl p) * nt F' (z ^ j / b) with ht
    have htO : t ∈ OK F' := trace_div_derivative_mem F' hz (pow_mem (self_mem_adj _ _) _)
    have htadj : t ∈ adj (OK F) ζ := hadj t htO.1 htO.2
    have h1 : nt F' (y * z ^ j) = ((p : PadicAlgCl p) * n')⁻¹ * t := by
      rw [show y * z ^ j = (p : PadicAlgCl p)⁻¹ * (z ^ j / b) by rw [hy]; field_simp,
        nt_mul_left F' (inv_mem (IntermediateField.natCast_mem _ _)), ht]
      field_simp
    have hpinvF : ((p : PadicAlgCl p) * n')⁻¹ ∈ F :=
      inv_mem (mul_mem (IntermediateField.natCast_mem _ _) (IntermediateField.natCast_mem _ _))
    rw [← nt_nt hFF', h1, nt_mul_left F hpinvF, ← mul_assoc, hN]
    push_cast
    rw [mul_inv_cancel₀ (mul_ne_zero hp0 hn'0), one_mul]
    have hmem := trace_div_derivative_mem F hζ1.le
      (mul_mem htadj (pow_mem (self_mem_adj _ _) (p - 1)))
    rw [hdζ, hcζ] at hmem
    have : t * ζ ^ (p - 1) / ((p : PadicAlgCl p) * ζ ^ (p - 1)) = (p : PadicAlgCl p)⁻¹ * t := by
      field_simp
    rw [this, nt_mul_left F (inv_mem (IntermediateField.natCast_mem _ _)), ← mul_assoc,
      mul_inv_cancel₀ hp0, one_mul] at hmem
    exact hmem
  have hmem := mul_derivative_mem_adj F hz hyF htr
  have h1 : ‖y * (derivative (mp F z)).eval z‖ ≤ 1 := norm_le_one_of_mem_adj hz hmem
  rw [hy, norm_mul, norm_inv, norm_mul] at h1
  have hpb : 0 < ‖(p : PadicAlgCl p)‖ * ‖b‖ :=
    mul_pos (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hb0)
  rwa [inv_mul_le_iff₀ hpb, mul_one] at h1

section Zeta'

variable {ζ : PadicAlgCl p} {m : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (m + 2)))
include hζ

/-- **Transitivity of the different in the cyclotomic step**: for `F = ℚ_p(ζ^p) ⊆ F' = ℚ_p(ζ)`
and `‖z‖ ≤ 1` with `F' ⊆ ℚ_p(z)`: `‖G'(z)‖ ≤ ‖p‖ ‖g'(z)‖` (`G`, `g` the minimal polynomials of `z`
over `F`, `F'`). -/
theorem cyc_transitivity {z : PadicAlgCl p} (hz : ‖z‖ ≤ 1) (hFz : ℚ_[p]⟮ζ⟯ ≤ ℚ_[p]⟮z⟯) :
    ‖(derivative (mp ℚ_[p]⟮ζ ^ p⟯ z)).eval z‖ ≤
      ‖(p : PadicAlgCl p)‖ * ‖(derivative (mp ℚ_[p]⟮ζ⟯ z)).eval z‖ := by
  haveI : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ ^ p⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  haveI : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  have hFF' : ℚ_[p]⟮ζ ^ p⟯ ≤ ℚ_[p]⟮ζ⟯ :=
    adjoin_simple_le_iff.mpr (pow_mem (mem_adjoin_simple_self _ _) _)
  have hN : dg ℚ_[p]⟮ζ ^ p⟯ z = p * dg ℚ_[p]⟮ζ⟯ z := by
    have h1 := finrank_adjoin_eq_mul (hFF'.trans hFz)
    have h2 := finrank_adjoin_eq_mul hFz
    rw [finrank_adjoin_primitiveRoot hζ, totient_succ_eq] at h2
    rw [finrank_adjoin_pow_p hζ] at h1
    have hφ0 : 0 < (p ^ (m + 1)).totient := Nat.totient_pos.mpr (pow_pos hp.out.pos _)
    have : (p ^ (m + 1)).totient * dg ℚ_[p]⟮ζ ^ p⟯ z =
        (p ^ (m + 1)).totient * (p * dg ℚ_[p]⟮ζ⟯ z) := by
      rw [← h1, h2]; ring
    exact Nat.eq_of_mul_eq_mul_left hφ0 this
  have hF'z : ℚ_[p]⟮ζ⟯ ≤ (ℚ_[p]⟮ζ ^ p⟯⟮z⟯).restrictScalars ℚ_[p] :=
    hFz.trans (adjoin_simple_le_iff.mpr (mem_restrictScalars_adjoin _ z))
  exact transitivity_of_data hFF' (norm_zeta hζ) (fun t ht ht1 => mem_adj_of_mem_cyc hζ ht ht1)
    (dg_zeta hζ) (derivative_mp_zeta hζ) hz hF'z hN

end Zeta'

end PadicHodge
