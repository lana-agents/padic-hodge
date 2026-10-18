/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Partial derivatives of multivariate power series

For `f : MvPowerSeries σ R` and `i : σ`, the partial derivative `∂f/∂X_i` has coefficients
`coeff n (∂_i f) = coeff (n + e_i) f * (n i + 1)` (as `MvPolynomial.coeff_pderiv`). It is an
`R`-derivation (`MvPowerSeries.pderiv`), compatible with `MvPolynomial.pderiv` (`pderiv_coe`).
The Leibniz rule is reduced to the polynomial case by truncation (`trunc'`), as for
`PowerSeries.derivative` in Mathlib.

Not in Mathlib (pin `v4.32.0`), which has `MvPolynomial.pderiv` and the one-variable
`PowerSeries.derivative`. Needed for invariant differentials / invariant derivations of formal
group laws ([Hong, Prop. 1.5.10, proof]; [Tate, §(2.2), p. 165]).
-/

noncomputable section

open Finsupp

namespace MvPowerSeries

variable {σ R : Type*} [CommSemiring R]

/-- The partial derivative `∂f/∂X_i` of a multivariate power series, as a function. -/
def pderivFun (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun n => coeff (n + single i 1) f * (n i + 1)

theorem coeff_pderivFun (i : σ) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (pderivFun i f) = coeff (n + single i 1) f * (n i + 1) := rfl

/-- Coefficients of a product up to `n` only depend on coefficients of the factors up to `n`. -/
theorem coeff_mul_congr {f f' g g' : MvPowerSeries σ R} {n : σ →₀ ℕ}
    (hf : ∀ m ≤ n, coeff m f = coeff m f') (hg : ∀ m ≤ n, coeff m g = coeff m g') :
    coeff n (f * g) = coeff n (f' * g') := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [hf x.1 (hx ▸ le_self_add), hg x.2 (hx ▸ le_add_self)]

/-- On polynomials, `pderivFun` is `MvPolynomial.pderiv`. -/
theorem pderivFun_coe (i : σ) (p : MvPolynomial σ R) :
    pderivFun i (p : MvPowerSeries σ R) = (MvPolynomial.pderiv i p : MvPowerSeries σ R) := by
  ext n
  rw [coeff_pderivFun, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_pderiv]

/-- The coefficients of `∂_i f` up to `n` only depend on the truncation of `f` at `n + e_i`. -/
theorem coeff_pderivFun_trunc' [DecidableEq σ] (i : σ) (f : MvPowerSeries σ R) {n m : σ →₀ ℕ}
    (h : m ≤ n) :
    coeff m (pderivFun i ((trunc' R (n + single i 1) f : MvPolynomial σ R) :
      MvPowerSeries σ R)) = coeff m (pderivFun i f) := by
  rw [coeff_pderivFun, coeff_pderivFun, MvPolynomial.coeff_coe, coeff_trunc',
    if_pos (add_le_add h le_rfl)]

theorem pderivFun_add (i : σ) (f g : MvPowerSeries σ R) :
    pderivFun i (f + g) = pderivFun i f + pderivFun i g := by
  ext n
  simp only [coeff_pderivFun, map_add, add_mul]

theorem pderivFun_C (i : σ) (r : R) : pderivFun i (C r : MvPowerSeries σ R) = 0 := by
  classical
  ext n
  rw [coeff_pderivFun, coeff_C, if_neg, zero_mul, map_zero]
  intro h
  have := congrArg (fun m : σ →₀ ℕ => m i) h
  simp at this

theorem pderivFun_one (i : σ) : pderivFun i (1 : MvPowerSeries σ R) = 0 := by
  rw [← map_one (C (σ := σ) (R := R)), pderivFun_C]

/-- **Leibniz rule** for `pderivFun`. -/
theorem pderivFun_mul (i : σ) (f g : MvPowerSeries σ R) :
    pderivFun i (f * g) = f * pderivFun i g + g * pderivFun i f := by
  classical
  ext n
  set N := n + single i 1
  set tf : MvPolynomial σ R := trunc' R N f
  set tg : MvPolynomial σ R := trunc' R N g
  have h1 : coeff n (pderivFun i (f * g)) = coeff n (pderivFun i ((tf * tg : MvPolynomial σ R) :
      MvPowerSeries σ R)) := by
    rw [coeff_pderivFun, coeff_pderivFun, MvPolynomial.coeff_coe,
      coeff_trunc'_mul_trunc'_eq_coeff_mul N f g le_rfl]
  have hf : ∀ m ≤ n, coeff m (tf : MvPowerSeries σ R) = coeff m f := fun m hm => by
    rw [MvPolynomial.coeff_coe, coeff_trunc', if_pos (hm.trans le_self_add)]
  have hg : ∀ m ≤ n, coeff m (tg : MvPowerSeries σ R) = coeff m g := fun m hm => by
    rw [MvPolynomial.coeff_coe, coeff_trunc', if_pos (hm.trans le_self_add)]
  rw [h1, pderivFun_coe, Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [MvPolynomial.coe_add,
    MvPolynomial.coe_mul, MvPolynomial.coe_mul, map_add, map_add, ← pderivFun_coe,
    ← pderivFun_coe]
  congr 1
  · exact coeff_mul_congr hf fun m hm => coeff_pderivFun_trunc' i g hm
  · exact coeff_mul_congr hg fun m hm => coeff_pderivFun_trunc' i f hm

theorem pderivFun_smul (i : σ) (r : R) (f : MvPowerSeries σ R) :
    pderivFun i (r • f) = r • pderivFun i f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, pderivFun_mul, pderivFun_C, mul_zero, add_zero]

variable (R) in
/-- **The partial derivative `∂/∂X_i`** on `R⟦X_σ⟧`, an `R`-derivation. -/
def pderiv (i : σ) : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := pderivFun i
  map_add' := pderivFun_add i
  map_smul' := pderivFun_smul i
  map_one_eq_zero' := pderivFun_one i
  leibniz' f g := by
    change pderivFun i (f * g) = f * pderivFun i g + g * pderivFun i f
    exact pderivFun_mul i f g

theorem coeff_pderiv (i : σ) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1) := rfl

@[simp] theorem pderiv_C (i : σ) (r : R) : pderiv R i (C r : MvPowerSeries σ R) = 0 :=
  pderivFun_C i r

theorem pderiv_coe (i : σ) (p : MvPolynomial σ R) :
    pderiv R i (p : MvPowerSeries σ R) = (MvPolynomial.pderiv i p : MvPowerSeries σ R) :=
  pderivFun_coe i p

@[simp] theorem pderiv_X_self (i : σ) : pderiv R i (X i : MvPowerSeries σ R) = 1 := by
  rw [← MvPolynomial.coe_X, pderiv_coe, MvPolynomial.pderiv_X_self, MvPolynomial.coe_one]

theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv R i (X j : MvPowerSeries σ R) = 0 := by
  rw [← MvPolynomial.coe_X, pderiv_coe, MvPolynomial.pderiv_X_of_ne h, MvPolynomial.coe_zero]

theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv R i (X j : MvPowerSeries σ R) = Pi.single (M := fun _ => MvPowerSeries σ R) i 1 j := by
  by_cases h : j = i
  · subst h; rw [pderiv_X_self, Pi.single_eq_same]
  · rw [pderiv_X_of_ne h, Pi.single_eq_of_ne h]

/-- The constant coefficient of `∂_i f` is the coefficient of `X_i` in `f`. -/
theorem constantCoeff_pderiv (i : σ) (f : MvPowerSeries σ R) :
    constantCoeff (pderiv R i f) = coeff (single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, Finsupp.coe_zero,
    Pi.zero_apply, Nat.cast_zero, zero_add, mul_one]

end MvPowerSeries

/-! ### The chain rule -/

namespace MvPolynomial

variable {σ R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [Fintype σ]

/-- **Chain rule for polynomials**: `D(p(x)) = ∑_i (∂p/∂X_i)(x) • D(x_i)` for any derivation
`D`. -/
theorem derivation_aeval (D : Derivation R A M) (x : σ → A) (p : MvPolynomial σ R) :
    D (aeval x p) = ∑ i, aeval x (pderiv i p) • D (x i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have e : ∀ i, aeval x (pderiv i (p * X k)) =
        aeval x p * aeval x (pderiv i (X k : MvPolynomial σ R)) + x k * aeval x (pderiv i p) := by
      intro i
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, aeval_X]
    simp only [e, add_smul, Finset.sum_add_distrib]
    rw [map_mul, aeval_X, Derivation.leibniz]
    congr 1
    · rw [Finset.sum_eq_single k (fun i _ hik => by
        rw [pderiv_X_of_ne (Ne.symm hik), map_zero, mul_zero, zero_smul])
        (fun h => absurd (Finset.mem_univ k) h), pderiv_X_self, map_one, mul_one]
    · rw [hp, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm

end MvPolynomial

namespace MvPowerSeries

variable {σ τ R : Type*} [CommRing R]

/-- If `degree e < degree d` and the `a_s` have no constant term, then `X^d(a)` has no `e`-th
coefficient. -/
theorem coeff_prod_pow_eq_zero {a : σ → MvPowerSeries τ R} (ha : ∀ s, constantCoeff (a s) = 0)
    {d : σ →₀ ℕ} {e : τ →₀ ℕ} (h : e.degree < d.degree) :
    coeff e (d.prod fun s n => a s ^ n) = 0 := by
  apply coeff_of_lt_order
  have h1 : ((d.degree : ℕ) : ℕ∞) ≤ (d.prod fun s n => a s ^ n).order := by
    rw [Finsupp.prod]
    refine le_trans ?_ (le_order_prod _ _)
    change ((∑ i ∈ d.support, d i : ℕ) : ℕ∞) ≤ _
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (ha s)
  exact lt_of_lt_of_le (by exact_mod_cast h) h1

/-- Substitution of power series without constant terms preserves the constant coefficient. -/
theorem constantCoeff_subst_of_constantCoeff_zero [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  rw [constantCoeff_subst (hasSubst_of_constantCoeff_zero ha), finsum_eq_single _ 0]
  · simp
  · intro e he
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_prod_pow_eq_zero ha, smul_zero]
    rw [map_zero]
    exact Nat.pos_of_ne_zero fun h => he ((Finsupp.degree_eq_zero_iff e).mp h)

/-- Substituting `0` gives the constant coefficient. -/
theorem subst_zero_eq_C (f : MvPowerSeries σ R) :
    subst (0 : σ → MvPowerSeries τ R) f = C (constantCoeff f) := by
  classical
  have hs : HasSubst (0 : σ → MvPowerSeries τ R) := HasSubst.zero
  ext e
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp only [Finsupp.prod_zero_index, smul_eq_mul, coeff_C, coeff_one,
      coeff_zero_eq_constantCoeff_apply]
    split_ifs <;> simp
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
    rw [Finsupp.prod, Finset.prod_eq_zero hs (by
      rw [Pi.zero_apply, zero_pow (Finsupp.mem_support_iff.mp hs)]), map_zero, smul_zero]

/-- Coefficients of `f(a)` up to total degree `k` only depend on the coefficients of `f` up to
total degree `k`, if the `a_s` have no constant term. -/
theorem coeff_subst_congr [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0)
    {f f' : MvPowerSeries σ R} {k : ℕ} (hf : ∀ d : σ →₀ ℕ, d.degree ≤ k → coeff d f = coeff d f')
    {e : τ →₀ ℕ} (he : e.degree ≤ k) :
    coeff e (subst a f) = coeff e (subst a f') := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hs, coeff_subst hs]
  refine finsum_congr fun d => ?_
  by_cases hd : d.degree ≤ k
  · rw [hf d hd]
  · rw [coeff_prod_pow_eq_zero ha (by omega), smul_zero, smul_zero]

/-- **Chain rule**: `∂_i (f(a)) = ∑_j (∂_j f)(a) · ∂_i a_j`, for `a_j` without constant term. -/
theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ R} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ R) (i : τ) :
    pderiv R i (subst a f) = ∑ j, subst a (pderiv R j f) * pderiv R i (a j) := by
  have hs := hasSubst_of_constantCoeff_zero ha
  ext e
  set k := e.degree + 2
  set t : MvPolynomial σ R := truncTotal k f
  have ht : ∀ d : σ →₀ ℕ, d.degree < k → coeff d (t : MvPowerSeries σ R) = coeff d f :=
    fun d hd => by rw [MvPolynomial.coeff_coe, coeff_truncTotal _ hd]
  have h1 : coeff e (pderiv R i (subst a f)) =
      coeff e (pderiv R i (subst a (t : MvPowerSeries σ R))) := by
    rw [coeff_pderiv, coeff_pderiv, coeff_subst_congr ha (k := e.degree + 1)
      (fun d hd => (ht d (by omega)).symm)]
    simp [map_add, Finsupp.degree_single]
  rw [h1, subst_coe, MvPolynomial.derivation_aeval, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul]
  refine coeff_mul_congr (fun m hm => ?_) fun _ _ => rfl
  rw [← subst_coe, ← pderiv_coe]
  have hmdeg : m.degree ≤ e.degree := Finsupp.degree_mono hm
  refine coeff_subst_congr ha (k := e.degree) (fun d hd => ?_) hmdeg
  rw [coeff_pderiv, coeff_pderiv, ht _ (by simp [map_add, Finsupp.degree_single]; omega)]

end MvPowerSeries
