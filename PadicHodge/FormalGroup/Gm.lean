/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Torsion

/-!
# Divisible formal groups and `Ĝ_m(m_{ℂ_p}) = 1 + m_{ℂ_p}`

* `logF_surjective_of_divisible`: if `F(m_{ℂ_p})` is `p`-divisible, then `log_F` is surjective
  onto `ℂ_p^d`; with `logF_eq_zero_iff_mem_torsionBy` this is the exact sequence
  `0 → F(m_{ℂ_p})[p^∞] → F(m_{ℂ_p}) → ℂ_p^d → 0` ([Hong, Prop. 3.4.7] for formal groups;
  [Hong, Prop. 3.2.7] gives the `p`-divisibility for `p`-divisible formal group laws).
* For the multiplicative formal group law ([Hong, Ex. 2.2.4, 3.3.5, 3.4.8]): `n · x = (1 + x)^n − 1`
  (`gm_nsmul_val`), `Ĝ_m(m_{ℂ_p})` is `p`-divisible (`gm_exists_p_nsmul_eq`: `p`-th roots of
  principal units are principal units, `ℂ_p` being algebraically closed), its `p^v`-torsion is
  `{x | (1 + x)^{p^v} = 1}` (`gm_mem_torsionBy_iff`), and **the exact sequence
  `0 → μ_{p^∞} → 1 + m_{ℂ_p} → ℂ_p → 0`** of [Hong, Ex. 3.4.8] (`gm_logF_surjective`,
  `gm_logF_eq_zero_iff`).
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)]

theorem exists_pow_nsmul_eq {d : ℕ} {F : FGL R d} (h : ∀ x : F.Pt p, ∃ y, p • y = x)
    (n : ℕ) (x : F.Pt p) : ∃ y, (p ^ n) • y = x := by
  induction n generalizing x with
  | zero => exact ⟨x, by rw [pow_zero, one_nsmul]⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨z, hz⟩ := h y
    exact ⟨z, by rw [pow_succ', mul_nsmul, hz, hy]⟩

/-- **A `p`-divisible formal group has surjective logarithm.** -/
theorem logF_surjective_of_divisible {d : ℕ} (F : FGL R d)
    (h : ∀ x : F.Pt p, ∃ y, p • y = x) (τ : Fin d → ℂ_[p]) :
    ∃ x : F.Pt p, ∀ i, F.logF x i = τ i := by
  obtain ⟨x, n, hx⟩ := F.exists_logF_eq_pow_mul τ
  obtain ⟨y, rfl⟩ := exists_pow_nsmul_eq h n x
  refine ⟨y, fun i => ?_⟩
  have e := hx i
  rw [logF_nsmul, Nat.cast_pow] at e
  exact mul_left_cancel₀ (pow_ne_zero _ p_ne_zero') e

/-- **`n · x = (1 + x)^n − 1` in `Ĝ_m`.** -/
theorem gm_nsmul_val (n : ℕ) (x : (multiplicative R).Pt p) :
    (((n • x).1 0 : OC p) : ℂ_[p]) = (1 + ((x.1 0 : OC p) : ℂ_[p])) ^ n - 1 := by
  induction n with
  | zero => rw [zero_nsmul, zero_val, pow_zero, sub_self]; rfl
  | succ n ih =>
    rw [succ_nsmul, multiplicative_add_val, Subring.coe_add, Subring.coe_add, Subring.coe_mul,
      ih]
    ring

/-- `p`-th roots of principal units of `ℂ_p` are principal units. -/
theorem norm_sub_one_lt_of_pow {z : ℂ_[p]} (hz : ‖z ^ p - 1‖ < 1) : ‖z - 1‖ < 1 := by
  have hp := (Fact.out : p.Prime)
  set w := z - 1 with hw
  have hz1 : ‖z ^ p‖ = 1 := by
    have e : z ^ p = (z ^ p - 1) + 1 := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hz.ne)]
    rw [norm_one]; exact max_eq_right hz.le
  have hzn : ‖z‖ = 1 := by
    rw [norm_pow] at hz1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).mp hz1
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw]
    refine (norm_sub_le_max_Cp _ _).trans (max_le hzn.le (by rw [norm_one]))
  -- `(W + 1)^p = W^p + 1 + p S` in `O_{ℂ_p}`
  set W : OC p := ⟨w, hw1⟩
  obtain ⟨S, hS⟩ : ∃ S : OC p, (W + 1) ^ p = W ^ p + 1 ^ p + p * S :=
    ⟨_, add_pow_prime_eq' hp W 1⟩
  have hS' : z ^ p = w ^ p + 1 + p * ((S : OC p) : ℂ_[p]) := by
    have := congrArg (fun a : OC p => (a : ℂ_[p])) hS
    simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast,
      OneMemClass.coe_one, one_pow, W] at this
    rw [← this, hw]
    ring
  have hwp : ‖w ^ p‖ < 1 := by
    have e : w ^ p = (z ^ p - 1) - p * ((S : OC p) : ℂ_[p]) := by rw [hS']; ring
    rw [e]
    refine (norm_sub_le_max_Cp _ _).trans_lt (max_lt hz ?_)
    rw [norm_mul]
    calc np p * ‖((S : OC p) : ℂ_[p])‖ ≤ np p * 1 :=
          mul_le_mul_of_nonneg_left (norm_OC_le S) np_pos.le
      _ < 1 := by rw [mul_one]; exact np_lt_one
  rw [norm_pow] at hwp
  by_contra hcon
  push Not at hcon
  have : 1 ≤ ‖w‖ ^ p := one_le_pow₀ hcon
  linarith

/-- **`Ĝ_m(m_{ℂ_p})` is `p`-divisible.** -/
theorem gm_exists_p_nsmul_eq (x : (multiplicative R).Pt p) :
    ∃ y : (multiplicative R).Pt p, p • y = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (1 + ((x.1 0 : OC p) : ℂ_[p]))
    (Fact.out : p.Prime).pos
  have hz1 : ‖z - 1‖ < 1 := norm_sub_one_lt_of_pow (by rw [hz, add_sub_cancel_left]; exact x.2 0)
  set y : (multiplicative R).Pt p := (multiplicative R).ofVec (fun _ => z - 1) fun _ => hz1
  refine ⟨y, (multiplicative R).pt_ext fun j => Subtype.ext ?_⟩
  rw [Subsingleton.elim j 0, gm_nsmul_val]
  simp only [y, ofVec_val, add_sub_cancel, hz, add_sub_cancel_left]

/-- **The logarithm of `Ĝ_m` is surjective** ([Hong, Ex. 3.4.8]). -/
theorem gm_logF_surjective (τ : ℂ_[p]) :
    ∃ x : (multiplicative R).Pt p, (multiplicative R).logF x 0 = τ := by
  obtain ⟨x, hx⟩ := logF_surjective_of_divisible (multiplicative R) gm_exists_p_nsmul_eq
    fun _ => τ
  exact ⟨x, hx 0⟩

/-- `Ĝ_m(m_{ℂ_p})[p^v] = μ_{p^v} − 1`. -/
theorem gm_mem_torsionBy_iff {v : ℕ} {x : (multiplicative R).Pt p} :
    x ∈ (multiplicative R).torsionBy v ↔ (1 + ((x.1 0 : OC p) : ℂ_[p])) ^ (p ^ v) = 1 := by
  rw [mem_torsionBy]
  constructor
  · intro h
    have e := gm_nsmul_val (p ^ v) x
    rw [h, zero_val, ZeroMemClass.coe_zero] at e
    exact (sub_eq_zero.mp e.symm)
  · intro h
    refine (multiplicative R).pt_ext fun j => Subtype.ext ?_
    rw [Subsingleton.elim j 0, gm_nsmul_val, h, sub_self, zero_val, ZeroMemClass.coe_zero]

/-- **`ker log_{Ĝ_m} = μ_{p^∞} − 1`** ([Hong, Ex. 3.4.8]). -/
theorem gm_logF_eq_zero_iff (x : (multiplicative R).Pt p) :
    (multiplicative R).logF x 0 = 0 ↔
      ∃ v, (1 + ((x.1 0 : OC p) : ℂ_[p])) ^ (p ^ v) = 1 := by
  have h := (multiplicative R).logF_eq_zero_iff_mem_torsionBy x
  simp only [gm_mem_torsionBy_iff] at h
  rw [← h]
  constructor
  · intro h0 i; rw [Subsingleton.elim i 0]; exact h0
  · intro h0; exact h0 0

end FGL

end PadicHodge
