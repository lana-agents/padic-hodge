/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Fields
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Tate's normalised traces on `ℚ_p(μ_{p^∞})` and the vanishing of twisted invariants

Let `γ ∈ Gal(ℚ̄_p/ℚ_p)` be a "Tate generator at level `n`" (`IsTateGen γ n`): for every `k ≥ n`,
`γ^{p^{k-n}}` multiplies each primitive `p^{k+1}`-th root of unity by a primitive `p`-th root of
unity (i.e. `γ^{p^{k-n}}` generates `Gal(ℚ_p(μ_{p^{k+1}})/ℚ_p(μ_{p^k}))`). The normalised traces
`T_k = p⁻¹ ∑_{s<p} γ^{s p^{k-n}}` and their composites `A = T_n ∘ ⋯ ∘ T_{M-1}` satisfy, on
`ℚ_p(μ_{p^M})` and uniformly in `M` ([BC, §14.1], after Tate):

* `acomp_mem`: `A y ∈ ℚ_p(μ_{p^n})`;
* `norm_acomp_le`: `‖A y‖ ≤ p ‖y‖`;
* `norm_sub_acomp_le`: `‖y - A y‖ ≤ p^4 ‖γ y - y‖`.

**Main result** (`eq_zero_of_autCp_eq_smul`): if `x ∈ ℂ_[p]` is a limit of elements of
`ℚ_p(μ_{p^∞})` and `γ x = λ x` with `λ ∈ ℚ_p`, `λ ≠ 1`, `p^4 ‖λ - 1‖ < 1`, then `x = 0`.
This is the analytic core of Tate's theorem `ℂ_p(j)^{G_K} = 0` for `j ≠ 0`.
-/

noncomputable section

open IntermediateField Finset

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- `γ` is a *Tate generator at level `n`*: for `k ≥ n`, `γ^{p^{k-n}}` acts on every primitive
`p^{k+1}`-th root of unity `ζ` by `ζ ↦ ζ ω` with `ω` a primitive `p`-th root of unity. -/
def IsTateGen (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n : ℕ) : Prop :=
  ∀ k, n ≤ k → ∀ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ (k + 1)) →
    ∃ ω, IsPrimitiveRoot ω p ∧ (γ ^ (p ^ (k - n))) ζ = ζ * ω

/-- The normalised trace from level `k + 1` to level `k`. -/
def tr (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n k : ℕ) : PadicAlgCl p → PadicAlgCl p :=
  avg (γ ^ (p ^ (k - n)))

theorem norm_le_one_sub_one {ζ : PadicAlgCl p} {N : ℕ} (hN : N ≠ 0) (h : ζ ^ N = 1) :
    ‖ζ - 1‖ ≤ 1 := by
  refine (norm_sub_le_max' ζ 1).trans ?_
  rw [norm_eq_one_of_pow_eq_one hN h, norm_one, max_self]

omit hp in
theorem inv_p_le_of_pow {x : ℝ} {N : ℕ} (hN : N ≠ 0) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (h : x ^ N = (p : ℝ)⁻¹) : (p : ℝ)⁻¹ ≤ x := by
  rw [← h]; exact pow_le_of_le_one hx0 hx1 hN

theorem norm_omega_sub_one_ge {ω : PadicAlgCl p} (hω : IsPrimitiveRoot ω p) :
    (p : ℝ)⁻¹ ≤ ‖ω - 1‖ := by
  have hω' : IsPrimitiveRoot ω (p ^ (0 + 1)) := by rwa [zero_add, pow_one]
  have h := norm_sub_one_pow_totient hω'
  rw [zero_add, pow_one, Nat.totient_prime hp.out] at h
  exact inv_p_le_of_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt) (norm_nonneg _)
    (norm_le_one_sub_one hp.out.ne_zero hω.pow_eq_one) h

/-- `‖ζ - 1‖^{p-1} = p^{-1/p^k}` for `ζ` a primitive `p^{k+1}`-th root of unity. -/
theorem norm_pi_pow_eq_rpow {ζ : PadicAlgCl p} {k : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    ‖ζ - 1‖ ^ (p - 1) = (p : ℝ) ^ (-((p : ℝ) ^ k)⁻¹) := by
  have h := norm_sub_one_pow_totient hζ
  rw [Nat.totient_prime_pow_succ hp.out, mul_comm, pow_mul] at h
  have hθ : 0 ≤ ‖ζ - 1‖ ^ (p - 1) := pow_nonneg (norm_nonneg _) _
  have hk : p ^ k ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  rw [← Real.pow_rpow_inv_natCast hθ hk, h, Real.rpow_neg (by positivity), Nat.cast_pow,
    Real.inv_rpow (by positivity)]

section Level

variable {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {n : ℕ} (hγ : IsTateGen γ n) (hn : 1 ≤ n)
include hγ hn

/-- The data of one level `k ≥ n`. -/
theorem level_data {k : ℕ} (hk : n ≤ k) :
    ∃ ζ ω : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ ((k - 1) + 2)) ∧ IsPrimitiveRoot ω p ∧
      (γ ^ (p ^ (k - n))) ζ = ζ * ω ∧ cycField p (k + 1) = ℚ_[p]⟮ζ⟯ ∧
      cycField p k = ℚ_[p]⟮ζ ^ p⟯ ∧ ‖ζ - 1‖ ^ (p - 1) = (p : ℝ) ^ (-((p : ℝ) ^ k)⁻¹) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (k + 1)
  obtain ⟨ω, hω, hδ⟩ := hγ k hk ζ hζ
  have hk1 : k - 1 + 2 = k + 1 := by omega
  have hζ' : IsPrimitiveRoot ζ (p ^ ((k - 1) + 2)) := by rwa [hk1]
  have hζp : IsPrimitiveRoot (ζ ^ p) (p ^ k) := by
    have := isPrimitiveRoot_pow_p hζ'
    rwa [show k - 1 + 1 = k by omega] at this
  exact ⟨ζ, ω, hζ', hω, hδ, cycField_eq hζ, cycField_eq hζp, norm_pi_pow_eq_rpow hζ⟩

theorem tr_mem {k : ℕ} (hk : n ≤ k) {y : PadicAlgCl p} (hy : y ∈ cycField p (k + 1)) :
    tr γ n k y ∈ cycField p k := by
  obtain ⟨ζ, ω, hζ, hω, hδ, h1, h2, -⟩ := level_data hγ hn hk
  rw [h1] at hy; rw [h2]
  exact avg_mem hζ hω hδ hy

theorem tr_of_mem {k : ℕ} (hk : n ≤ k) {y : PadicAlgCl p} (hy : y ∈ cycField p k) :
    tr γ n k y = y := by
  obtain ⟨ζ, ω, hζ, hω, hδ, -, h2, -⟩ := level_data hγ hn hk
  rw [h2] at hy
  exact avg_of_mem hω hδ hy

theorem norm_tr_le {k : ℕ} (hk : n ≤ k) {y : PadicAlgCl p} (hy : y ∈ cycField p (k + 1)) :
    ‖tr γ n k y‖ ≤ (p : ℝ) ^ ((p : ℝ) ^ k)⁻¹ * ‖y‖ := by
  obtain ⟨ζ, ω, hζ, hω, hδ, h1, -, hθ⟩ := level_data hγ hn hk
  rw [h1] at hy
  have h := norm_avg_le hζ hω hδ hy
  rw [hθ] at h
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-((p : ℝ) ^ k)⁻¹) := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  rw [← le_div_iff₀ hpos] at h
  refine h.trans_eq ?_
  rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity), neg_neg, mul_comm]

theorem norm_tr_le_p {k : ℕ} (hk : n ≤ k) {y : PadicAlgCl p} (hy : y ∈ cycField p (k + 1)) :
    ‖tr γ n k y‖ ≤ p * ‖y‖ := by
  refine (norm_tr_le hγ hn hk hy).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  conv_rhs => rw [← Real.rpow_one (p : ℝ)]
  refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hp1)

theorem norm_le_of_tr_eq_zero {k : ℕ} (hk : n ≤ k) {y : PadicAlgCl p}
    (hy : y ∈ cycField p (k + 1)) (h0 : tr γ n k y = 0) :
    ‖y‖ ≤ (p : ℝ) ^ 2 * ‖(γ ^ (p ^ (k - n))) y - y‖ := by
  obtain ⟨ζ, ω, hζ, hω, hδ, h1, -, hθ⟩ := level_data hγ hn hk
  rw [h1] at hy
  have h := norm_le_of_avg_eq_zero hζ hω hδ hy h0
  have hω1 := norm_omega_sub_one_ge hω
  have hθ1 : (p : ℝ)⁻¹ ≤ ‖ζ - 1‖ ^ (p - 1) := by
    rw [hθ]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
    rw [← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg ?_)
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hp1)
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have h2 : ‖y‖ * ((p : ℝ)⁻¹ * (p : ℝ)⁻¹) ≤ ‖(γ ^ (p ^ (k - n))) y - y‖ :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul hω1 hθ1 hp0.le (norm_nonneg _))
      (norm_nonneg _)) h
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    positivity
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  calc ‖y‖ = (p : ℝ) ^ 2 * (‖y‖ * ((p : ℝ)⁻¹ * (p : ℝ)⁻¹)) := by
        rw [show (p : ℝ) ^ 2 * (‖y‖ * ((p : ℝ)⁻¹ * (p : ℝ)⁻¹)) =
          ‖y‖ * ((p : ℝ) * (p : ℝ)⁻¹) * ((p : ℝ) * (p : ℝ)⁻¹) by ring,
          mul_inv_cancel₀ hpne, mul_one, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hp2.le

/-- `γ` fixes `ℚ_p(μ_{p^n})`. -/
theorem gal_fix_cycField {y : PadicAlgCl p} (hy : y ∈ cycField p n) : γ y = y := by
  obtain ⟨ζ, ω, hζ, hω, hδ, -, h2, -⟩ := level_data hγ hn le_rfl
  rw [Nat.sub_self, pow_zero, pow_one] at hδ
  rw [h2] at hy
  exact delta_fix hω hδ hy

end Level

theorem norm_pow_apply_sub_le (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (N : ℕ)
    (w : PadicAlgCl p) : ‖(σ ^ N) w - w‖ ≤ ‖σ w - w‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (σ ^ (N + 1)) w - w = σ ((σ ^ N) w - w) + (σ w - w) := by
      rw [pow_succ', AlgEquiv.mul_apply, map_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_aut_apply]; exact ih

theorem tr_comm (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n k : ℕ) (y : PadicAlgCl p) :
    tr γ n k (γ y) = γ (tr γ n k y) :=
  avg_comm (Commute.pow_left (Commute.refl γ) _).eq y

theorem tr_sub (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n k : ℕ) (y z : PadicAlgCl p) :
    tr γ n k (y - z) = tr γ n k y - tr γ n k z :=
  avg_sub _ y z

theorem tr_smul (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n k : ℕ) (c : ℚ_[p])
    (y : PadicAlgCl p) : tr γ n k (c • y) = c • tr γ n k y := by
  have h : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ (c • y) = c • σ y := fun σ => by
    rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]
  unfold tr avg
  rw [Finset.sum_congr rfl fun s _ => h _, ← Finset.smul_sum, mul_smul_comm]

/-- The composite of the normalised traces from level `M` down to level `M - t`. -/
def acomp (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M : ℕ) :
    ℕ → PadicAlgCl p → PadicAlgCl p
  | 0 => id
  | t + 1 => fun y => tr γ n (M - (t + 1)) (acomp γ n M t y)

theorem acomp_comm (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M t : ℕ) (y : PadicAlgCl p) :
    acomp γ n M t (γ y) = γ (acomp γ n M t y) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [acomp, ih, tr_comm]

theorem acomp_sub (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M t : ℕ) (y z : PadicAlgCl p) :
    acomp γ n M t (y - z) = acomp γ n M t y - acomp γ n M t z := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [acomp, ih, tr_sub]

theorem acomp_smul (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M t : ℕ) (c : ℚ_[p])
    (y : PadicAlgCl p) : acomp γ n M t (c • y) = c • acomp γ n M t y := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [acomp, ih, tr_smul]

section Composite

variable {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {n : ℕ} (hγ : IsTateGen γ n) (hn : 1 ≤ n)
include hγ hn

theorem acomp_mem {M t : ℕ} (ht : n + t ≤ M) {y : PadicAlgCl p} (hy : y ∈ cycField p M) :
    acomp γ n M t y ∈ cycField p (M - t) := by
  induction t with
  | zero => simpa [acomp] using hy
  | succ t ih =>
    have h := ih (by omega)
    rw [show M - t = (M - (t + 1)) + 1 by omega] at h
    exact tr_mem hγ hn (by omega) h

/-- The exponent `∑_{l ∈ [k, M)} p^{-l}`. -/
def trExp (p M k : ℕ) : ℝ := ∑ l ∈ Ico k M, ((p : ℝ) ^ l)⁻¹

theorem norm_acomp_le_rpow {M t : ℕ} (ht : n + t ≤ M) {y : PadicAlgCl p}
    (hy : y ∈ cycField p M) :
    ‖acomp γ n M t y‖ ≤ (p : ℝ) ^ trExp p M (M - t) * ‖y‖ := by
  induction t with
  | zero => simp [acomp, trExp]
  | succ t ih =>
    have h := acomp_mem hγ hn (t := t) (by omega) hy
    rw [show M - t = (M - (t + 1)) + 1 by omega] at h
    have h1 := norm_tr_le hγ hn (k := M - (t + 1)) (by omega) h
    have h2 := ih (by omega)
    simp only [acomp]
    refine h1.trans ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    calc (p : ℝ) ^ ((p : ℝ) ^ (M - (t + 1)))⁻¹ * ‖acomp γ n M t y‖
        ≤ (p : ℝ) ^ ((p : ℝ) ^ (M - (t + 1)))⁻¹ * ((p : ℝ) ^ trExp p M (M - t) * ‖y‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (p : ℝ) ^ trExp p M (M - (t + 1)) * ‖y‖ := by
          have hlt : M - (t + 1) < M := by omega
          have hsplit : trExp p M (M - (t + 1)) =
              ((p : ℝ) ^ (M - (t + 1)))⁻¹ + trExp p M (M - t) := by
            rw [trExp, trExp, Finset.sum_eq_sum_Ico_succ_bot hlt,
              show M - (t + 1) + 1 = M - t by omega]
          rw [← mul_assoc, ← Real.rpow_add hp0, hsplit]

omit hγ hn in
theorem trExp_le_one {M k : ℕ} (hk : 1 ≤ k) : trExp p M k ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hx0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have e : trExp p M k = ∑ l ∈ Ico k M, ((p : ℝ)⁻¹) ^ l := by
    simp only [trExp, inv_pow]
  rw [e]
  refine (geom_sum_Ico_le_of_lt_one hx0 hx1).trans ?_
  rw [div_le_one (by linarith)]
  calc ((p : ℝ)⁻¹) ^ k ≤ (p : ℝ)⁻¹ := pow_le_of_le_one hx0 hx1.le (by omega)
    _ ≤ 1 - (p : ℝ)⁻¹ := by
        rw [le_sub_iff_add_le, ← two_mul, ← div_eq_mul_inv, div_le_one (by linarith)]
        exact hp2

theorem norm_acomp_le {M t : ℕ} (ht : n + t ≤ M) {y : PadicAlgCl p} (hy : y ∈ cycField p M) :
    ‖acomp γ n M t y‖ ≤ p * ‖y‖ := by
  refine (norm_acomp_le_rpow hγ hn ht hy).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  conv_rhs => rw [← Real.rpow_one (p : ℝ)]
  exact Real.rpow_le_rpow_of_exponent_le hp1 (trExp_le_one (by omega))

/-- **Tate's estimate**: `‖y - A y‖ ≤ p^4 ‖γ y - y‖` on `ℚ_p(μ_{p^M})`, uniformly in `M`. -/
theorem norm_sub_acomp_le {M t : ℕ} (ht : n + t ≤ M) {y : PadicAlgCl p}
    (hy : y ∈ cycField p M) :
    ‖y - acomp γ n M t y‖ ≤ (p : ℝ) ^ 4 * ‖γ y - y‖ := by
  have hp0 : (0 : ℝ) ≤ p := by exact_mod_cast hp.out.pos.le
  induction t with
  | zero => simp only [acomp, id, sub_self, norm_zero]; positivity
  | succ t ih =>
    set k := M - (t + 1) with hkdef
    have hkn : n ≤ k := by omega
    have hk1 : M - t = k + 1 := by omega
    set v := acomp γ n M t y with hv
    have hvmem : v ∈ cycField p (k + 1) := by
      rw [← hk1]; exact acomp_mem hγ hn (by omega) hy
    set w := v - tr γ n k v with hw
    have hwmem : w ∈ cycField p (k + 1) :=
      sub_mem hvmem (cycField_mono (Nat.le_succ k) (tr_mem hγ hn hkn hvmem))
    have htw : tr γ n k w = 0 := by
      rw [hw, tr_sub, tr_of_mem hγ hn hkn (tr_mem hγ hn hkn hvmem), sub_self]
    -- `γ w - w = (1 - T_k) A_t (γ y - y)`
    set u := acomp γ n M t (γ y - y) with hu
    have hgu : γ v - v = u := by rw [hu, acomp_sub, acomp_comm]
    have humem : u ∈ cycField p (k + 1) := by
      rw [← hk1]
      exact acomp_mem hγ hn (by omega) (sub_mem (gal_mem_cycField γ hy) hy)
    have hgw : γ w - w = u - tr γ n k u := by
      rw [hw, map_sub, ← tr_comm, ← hgu, tr_sub]; ring
    have hnu : ‖u‖ ≤ p * ‖γ y - y‖ :=
      norm_acomp_le hγ hn (by omega) (sub_mem (gal_mem_cycField γ hy) hy)
    have hgw' : ‖γ w - w‖ ≤ (p : ℝ) ^ 2 * ‖γ y - y‖ := by
      rw [hgw]
      refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
      · refine hnu.trans ?_
        have : (p : ℝ) ≤ (p : ℝ) ^ 2 := by
          rw [sq]; exact le_mul_of_one_le_left hp0 (by exact_mod_cast hp.out.one_lt.le)
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      · refine (norm_tr_le_p hγ hn hkn humem).trans ?_
        rw [sq, mul_assoc]
        exact mul_le_mul_of_nonneg_left hnu hp0
    have hnw : ‖w‖ ≤ (p : ℝ) ^ 4 * ‖γ y - y‖ := by
      refine (norm_le_of_tr_eq_zero hγ hn hkn hwmem htw).trans ?_
      calc (p : ℝ) ^ 2 * ‖(γ ^ (p ^ (k - n))) w - w‖ ≤ (p : ℝ) ^ 2 * ‖γ w - w‖ :=
            mul_le_mul_of_nonneg_left (norm_pow_apply_sub_le γ _ w) (by positivity)
        _ ≤ (p : ℝ) ^ 2 * ((p : ℝ) ^ 2 * ‖γ y - y‖) :=
            mul_le_mul_of_nonneg_left hgw' (by positivity)
        _ = (p : ℝ) ^ 4 * ‖γ y - y‖ := by ring
    have e : y - acomp γ n M (t + 1) y = (y - v) + w := by
      simp only [acomp, hw, hv]; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ih (by omega)) hnw)

end Composite

end PadicHodge
