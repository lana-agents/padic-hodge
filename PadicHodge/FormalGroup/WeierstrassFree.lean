/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.LayerFree
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# `A[[X]]` is free over itself via substitution of a Weierstrass divisor

Let `A` be a complete local ring and `g ∈ A[[X]]` a power series without constant term whose
reduction modulo the maximal ideal has order `n` (finite). Then `A[[X]]` is free of rank `n`
over itself via `ψ : f ↦ f(g)`, with basis `1, X, …, X^{n−1}` (`freeVia_substAlgHom`):

* existence: iterate Weierstrass division `f = g q + r` (Mathlib,
  `PowerSeries.eq_mul_weierstrassDiv_add_weierstrassMod`), `f = ∑_k g^k r_k`; the error after
  `N` steps is divisible by `g^N`, hence by `X^N`;
* uniqueness: from `PowerSeries.IsWeierstrassDivision.eq_zero` (`0 = g q + r` forces
  `q = r = 0`), coefficient by coefficient.

This is the input for "`Ĝ_m` is `p`-divisible of height `1`" (`FormalGroup/GmHeight.lean`).
-/

noncomputable section

open PowerSeries

namespace PadicHodge

namespace WeierstrassFree

variable {A : Type*} [CommRing A] {g : A⟦X⟧} (hg0 : constantCoeff g = 0)

include hg0 in
theorem hasSubst : HasSubst g := HasSubst.of_constantCoeff_zero' hg0

/-- `ψ : f ↦ f(g)`. -/
abbrev psi : A⟦X⟧ →ₐ[A] A⟦X⟧ := substAlgHom (hasSubst hg0)

theorem psi_C_add_X_mul (a : A) (c : A⟦X⟧) :
    psi hg0 (C a + X * c) = C a + g * psi hg0 c := by
  rw [map_add, map_mul, coe_substAlgHom, subst_X (hasSubst hg0), subst_C]
  rfl

/-- The comparison map `(c_i)_{i < n} ↦ ∑ ψ(c_i) X^i`. -/
def comb (n : ℕ) (c : Fin n → A⟦X⟧) : A⟦X⟧ := ∑ i, psi hg0 (c i) * X ^ (i : ℕ)

theorem coe_sum_C_mul_X_pow (n : ℕ) (a : Fin n → A) :
    ((∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial A) : A⟦X⟧) =
      ∑ i : Fin n, C (a i) * X ^ (i : ℕ) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp only [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X]

theorem comb_split (n : ℕ) (c : Fin n → A⟦X⟧) :
    comb hg0 n c =
      ((∑ i : Fin n, Polynomial.C (constantCoeff (c i)) * Polynomial.X ^ (i : ℕ) :
          Polynomial A) : A⟦X⟧) +
        g * comb hg0 n (fun i => mk fun k => coeff (k + 1) (c i)) := by
  rw [coe_sum_C_mul_X_pow, comb, comb, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := eq_X_mul_shift_add_const (c i)
  conv_lhs => rw [e, add_comm, psi_C_add_X_mul]
  ring

variable [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (hg : g.map (IsLocalRing.residue A) ≠ 0) (n : ℕ) {hg0}

include hg in
/-- Uniqueness: `∑ ψ(c_i) X^i = 0` forces all coefficients of all `c_i` to vanish. -/
theorem coeff_eq_zero_of_comb_eq_zero
    (hn : n = (g.map (IsLocalRing.residue A)).order.toNat) (k : ℕ) :
    ∀ c : Fin n → A⟦X⟧, comb hg0 n c = 0 → ∀ i, coeff k (c i) = 0 := by
  induction k with
  | zero =>
    intro c hc i
    rw [comb_split, add_comm] at hc
    have H : IsWeierstrassDivision 0 g
        (-comb hg0 n (fun i => mk fun k => coeff (k + 1) (c i)))
        (-(∑ i : Fin n, Polynomial.C (constantCoeff (c i)) * Polynomial.X ^ (i : ℕ))) := by
      refine ⟨?_, ?_⟩
      · rw [Polynomial.degree_neg]
        refine lt_of_lt_of_eq (Polynomial.degree_sum_fin_lt (fun i => constantCoeff (c i))) ?_
        rw [hn]
        rfl
      · rw [Polynomial.coe_neg, mul_neg, ← neg_add, hc, neg_zero]
    have h2 := congrArg (fun r => Polynomial.coeff r i) (H.eq_zero hg).2
    simp only [Polynomial.coeff_neg, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero, neg_eq_zero] at h2
    simpa only [Fin.val_inj, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      coeff_zero_eq_constantCoeff_apply] using h2
  | succ k ih =>
    intro c hc i
    rw [comb_split, add_comm] at hc
    have H : IsWeierstrassDivision 0 g
        (-comb hg0 n (fun i => mk fun k => coeff (k + 1) (c i)))
        (-(∑ i : Fin n, Polynomial.C (constantCoeff (c i)) * Polynomial.X ^ (i : ℕ))) := by
      refine ⟨?_, ?_⟩
      · rw [Polynomial.degree_neg]
        refine lt_of_lt_of_eq (Polynomial.degree_sum_fin_lt (fun i => constantCoeff (c i))) ?_
        rw [hn]
        rfl
      · rw [Polynomial.coe_neg, mul_neg, ← neg_add, hc, neg_zero]
    have h1 := neg_eq_zero.mp (H.eq_zero hg).1
    have := ih _ h1 i
    rwa [coeff_mk] at this

/-! ### Existence -/

section Exist

variable (g) in
/-- The iterated Weierstrass quotients `f, f /ʷ g, (f /ʷ g) /ʷ g, …`. -/
def seqQ (f : A⟦X⟧) (k : ℕ) : A⟦X⟧ := (fun f => f /ʷ g)^[k] f

variable (g) in
/-- The coefficients `c_i = ∑_k (r_k)_i X^k`, `r_k = seqQ f k %ʷ g`. -/
def coeffs (f : A⟦X⟧) : Fin n → A⟦X⟧ :=
  fun i => mk fun k => Polynomial.coeff (seqQ g f k %ʷ g) i

theorem seqQ_succ (f : A⟦X⟧) (k : ℕ) : seqQ g f (k + 1) = seqQ g (f /ʷ g) k :=
  Function.iterate_succ_apply _ _ _

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
theorem sum_coeff_eq (hn : n = (g.map (IsLocalRing.residue A)).order.toNat) (r : Polynomial A)
    (hr : r.degree < (g.map (IsLocalRing.residue A)).order.toNat) :
    (∑ i : Fin n, Polynomial.C (r.coeff i) * Polynomial.X ^ (i : ℕ)) = r := by
  subst hn
  rw [Polynomial.sum_fin (fun i a => Polynomial.C a * Polynomial.X ^ i) (by simp) hr,
    Polynomial.sum_C_mul_X_pow_eq]

include hg in
theorem comb_coeffs_sub (hn : n = (g.map (IsLocalRing.residue A)).order.toNat) (f : A⟦X⟧) :
    comb hg0 n (coeffs g n f) - f = g * (comb hg0 n (coeffs g n (f /ʷ g)) - f /ʷ g) := by
  rw [comb_split]
  have e1 : ∀ i, constantCoeff (coeffs g n f i) = (f %ʷ g).coeff (i : ℕ) := by
    intro i
    rw [coeffs, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    rfl
  have e2 : (fun i => mk fun k => coeff (k + 1) (coeffs g n f i)) = coeffs g n (f /ʷ g) := by
    funext i
    ext k
    rw [coeff_mk, coeffs, coeff_mk, coeffs, coeff_mk, seqQ_succ]
  simp only [e1]
  rw [e2, sum_coeff_eq n hn _ (degree_weierstrassMod_lt f g)]
  have hf := eq_mul_weierstrassDiv_add_weierstrassMod f hg
  linear_combination (-1 : A⟦X⟧) * hf

include hg in
theorem comb_coeffs_sub_pow (hn : n = (g.map (IsLocalRing.residue A)).order.toNat) (N : ℕ) :
    ∀ f : A⟦X⟧, comb hg0 n (coeffs g n f) - f =
      g ^ N * (comb hg0 n (coeffs g n (seqQ g f N)) - seqQ g f N) := by
  induction N with
  | zero => intro f; simp [seqQ]
  | succ N ih =>
    intro f
    rw [comb_coeffs_sub hg n hn f, ih (f /ʷ g), seqQ_succ, pow_succ]
    ring

include hg in
theorem comb_coeffs (hn : n = (g.map (IsLocalRing.residue A)).order.toNat) (f : A⟦X⟧) :
    comb hg0 n (coeffs g n f) = f := by
  rw [← sub_eq_zero]
  ext m
  rw [comb_coeffs_sub_pow hg n hn (m + 1) f, map_zero]
  generalize comb hg0 n _ - _ = E
  obtain ⟨u, hu⟩ := X_dvd_iff.mpr hg0
  rw [hu, mul_pow, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

end Exist

include hg in
/-- **`A[[X]]` is free of rank `n` over itself via `f ↦ f(g)`**, basis `1, X, …, X^{n−1}`,
for `g` without constant term whose reduction has order `n`. -/
theorem freeVia_psi (hn : n = (g.map (IsLocalRing.residue A)).order.toNat) :
    FGL.FreeVia (psi hg0).toRingHom n := by
  refine ⟨fun i => X ^ (i : ℕ), ?_, fun f => ⟨coeffs g n f, comb_coeffs hg n hn f⟩⟩
  intro c c' h
  have h0 : comb hg0 n (c - c') = 0 := by
    have : comb hg0 n (c - c') = comb hg0 n c - comb hg0 n c' := by
      simp only [comb, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [this]
    exact sub_eq_zero.mpr h
  funext i
  ext k
  have := coeff_eq_zero_of_comb_eq_zero hg n hn k _ h0 i
  rwa [Pi.sub_apply, map_sub, sub_eq_zero] at this

end WeierstrassFree

end PadicHodge
