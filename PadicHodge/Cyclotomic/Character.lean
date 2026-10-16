/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Vanishing
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.Data.Nat.Choose.Dvd

/-!
# The cyclotomic character of `Gal(ℚ̄_p/ℚ_p)` and Tate generators

`chi σ ∈ ℤ_[p]ˣ` is Mathlib's `cyclotomicCharacter` of `σ`. We show:

* `chi_eq_one_of_fix`: `chi σ = 1` if `σ` fixes all `p`-power roots of unity;
* `exists_chi_eq`: for `n ≥ 1` there is `γ` with `chi γ = 1 + p^n u`, `u ∈ ℤ_p^×`
  (from `[ℚ_p(ζ_{p^{n+1}}) : ℚ_p] = φ(p^{n+1})`);
* `isTateGen_of_chi`: such a `γ` is a Tate generator at level `n` (for `n ≥ 2`);
* `chi_zpow_ne_one`, `norm_chi_zpow_sub_one_le`: `chi(γ)^j ≠ 1` for `j ≠ 0` and
  `‖chi(γ)^j - 1‖ ≤ p^{-n}`.
-/

noncomputable section

open IntermediateField Polynomial

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-- The `p`-adic cyclotomic character of `Gal(ℚ̄_p/ℚ_p)`. -/
def chi : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (PadicAlgCl p))

theorem chi_spec (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {t : PadicAlgCl p} {k : ℕ}
    (ht : t ^ (p ^ k) = 1) : σ t = t ^ (((chi σ : ℤ_[p]ˣ) : ℤ_[p]).toZModPow k).val :=
  cyclotomicCharacter.spec p
    (MulSemiringAction.toRingAut (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (PadicAlgCl p) σ) t ht

theorem pow_eq_pow_iff_of_prim {ζ : PadicAlgCl p} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N)
    {a b : ℕ} : ζ ^ a = ζ ^ b ↔ a ≡ b [MOD N] := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf]

theorem toZModPow_chi_of_apply {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {ζ : PadicAlgCl p}
    {k : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ k)) {a : ℕ} (h : σ ζ = ζ ^ a) :
    ((chi σ : ℤ_[p]ˣ) : ℤ_[p]).toZModPow k = (a : ZMod (p ^ k)) := by
  have h1 := chi_spec σ hζ.pow_eq_one
  rw [h] at h1
  have h2 := (pow_eq_pow_iff_of_prim hζ (pow_pos hp.out.pos _)).mp h1
  rw [← ZMod.natCast_eq_natCast_iff] at h2
  rw [h2, ZMod.natCast_val, ZMod.cast_id]

theorem chi_eq_one_of_fix {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (h : ∀ k : ℕ, ∀ t : PadicAlgCl p, t ^ (p ^ k) = 1 → σ t = t) : chi σ = 1 := by
  ext1
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) k
  have := toZModPow_chi_of_apply hζ (a := 1) (by rw [pow_one]; exact h k ζ hζ.pow_eq_one)
  rw [this, Units.val_one, map_one, Nat.cast_one]

/-- The minimal polynomial of a primitive `p^{n+1}`-th root of unity over `ℚ_p` is cyclotomic. -/
theorem minpoly_primitiveRoot {ζ : PadicAlgCl p} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    minpoly ℚ_[p] ζ = cyclotomic (p ^ (n + 1)) ℚ_[p] := by
  have hint : IsIntegral ℚ_[p] ζ := Algebra.IsIntegral.isIntegral ζ
  have hroot : aeval ζ (cyclotomic (p ^ (n + 1)) ℚ_[p]) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact isRoot_cyclotomic_iff.mpr hζ
  have hdvd := minpoly.dvd ℚ_[p] ζ hroot
  have hdeg : (minpoly ℚ_[p] ζ).natDegree = (cyclotomic (p ^ (n + 1)) ℚ_[p]).natDegree := by
    rw [natDegree_cyclotomic, ← adjoin.finrank hint, finrank_adjoin_primitiveRoot hζ]
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
    (cyclotomic.monic _ _) hdvd hdeg.ge).symm

/-- For `n ≥ 1` there is `γ` acting on `μ_{p^{n+1}}` by `ζ ↦ ζ^{1+p^n}`. -/
theorem exists_gal_pow (n : ℕ) {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    (hn : 1 ≤ n) : ∃ γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, γ ζ = ζ ^ (1 + p ^ n) := by
  have hcop : (1 + p ^ n).Coprime (p ^ (n + 1)) := by
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hd
    have : p ∣ p ^ n := dvd_pow_self p (by omega)
    have h1 : p ∣ 1 := (Nat.dvd_add_right this).mp (by rwa [add_comm] at hd)
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h1)
  have hμ : IsPrimitiveRoot (ζ ^ (1 + p ^ n)) (p ^ (n + 1)) := hζ.pow_of_coprime _ hcop
  have h : minpoly ℚ_[p] (ζ ^ (1 + p ^ n)) = minpoly ℚ_[p] ζ := by
    rw [minpoly_primitiveRoot hμ, minpoly_primitiveRoot hζ]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[p]) (E := PadicAlgCl p)).mp h
  exact ⟨σ, hσ⟩

omit hp in
theorem natCast_one_add_pow (n : ℕ) :
    (((1 + p ^ n : ℕ)) : ZMod (p ^ (n + 1))) = 1 + (p : ZMod (p ^ (n + 1))) ^ n := by
  push_cast; ring

theorem isUnit_add_of_norm_lt {u x : ℤ_[p]} (hu : IsUnit u) (hx : ‖x‖ < 1) :
    IsUnit (u + x) := by
  rw [PadicInt.isUnit_iff] at hu ⊢
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hu]; exact hx.ne'), hu,
    max_eq_left hx.le]

theorem norm_p_mul_lt_one (w : ℤ_[p]) : ‖(p : ℤ_[p]) * w‖ < 1 := by
  rw [norm_mul, PadicInt.norm_p]
  have : ‖w‖ ≤ 1 := PadicInt.norm_le_one w
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  calc (p : ℝ)⁻¹ * ‖w‖ ≤ (p : ℝ)⁻¹ * 1 := by gcongr
    _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hp1

/-- For `n ≥ 1` there is `γ` with `chi γ = 1 + p^n u`, `u` a unit. -/
theorem exists_chi_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∃ u : ℤ_[p], IsUnit u ∧
      ((chi γ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ n * u := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (n + 1)
  obtain ⟨γ, hγ⟩ := exists_gal_pow n hζ hn
  have h := toZModPow_chi_of_apply hζ hγ
  set c := ((chi γ : ℤ_[p]ˣ) : ℤ_[p])
  have hker : c - (1 + (p : ℤ_[p]) ^ n) ∈ RingHom.ker (PadicInt.toZModPow (p := p) (n + 1)) := by
    rw [RingHom.mem_ker, map_sub, h, map_add, map_one, map_pow, map_natCast,
      natCast_one_add_pow, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨w, hw⟩ := hker
  refine ⟨γ, 1 + p * w, isUnit_add_of_norm_lt isUnit_one (norm_p_mul_lt_one w), ?_⟩
  rw [sub_eq_iff_eq_add] at hw
  change c = _
  rw [hw]; ring

/-- A weak form of the lifting-the-exponent lemma: `(1 + p^k u)^p = 1 + p^{k+1} u'` with `u'` a
unit, for `k ≥ 2` and `u` a unit. -/
theorem one_add_pow_p {k : ℕ} (hk : 2 ≤ k) {u : ℤ_[p]} (hu : IsUnit u) :
    ∃ u' : ℤ_[p], IsUnit u' ∧ (1 + (p : ℤ_[p]) ^ k * u) ^ p = 1 + (p : ℤ_[p]) ^ (k + 1) * u' := by
  set x := (p : ℤ_[p]) ^ k * u with hx
  have hp2 : 2 ≤ p := hp.out.two_le
  -- the terms of index `≥ 2` of the binomial expansion are divisible by `p^{k+2}`
  have hdiv : ∀ l ∈ Finset.range (p - 1),
      (p : ℤ_[p]) ^ (k + 2) ∣ x ^ (l + 2) * ((p.choose (l + 2) : ℕ) : ℤ_[p]) := by
    intro l hl
    rw [Finset.mem_range] at hl
    rw [hx, mul_pow, ← pow_mul]
    rcases Nat.lt_or_ge (l + 2) p with hlt | hge
    · obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (by omega) hlt
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show k + 2 ≤ k * (l + 2) + 1 by nlinarith)
      refine ⟨(p : ℤ_[p]) ^ d * u ^ (l + 2) * c, ?_⟩
      rw [hc, Nat.cast_mul]
      calc (p : ℤ_[p]) ^ (k * (l + 2)) * u ^ (l + 2) * ((p : ℤ_[p]) * (c : ℤ_[p]))
          = (p : ℤ_[p]) ^ (k * (l + 2) + 1) * (u ^ (l + 2) * c) := by ring
        _ = _ := by rw [hd, pow_add]; ring
    · have hl2 : l + 2 = p := by omega
      rw [hl2, Nat.choose_self, Nat.cast_one, mul_one]
      refine Dvd.dvd.mul_right (pow_dvd_pow _ ?_) _
      nlinarith
  obtain ⟨w, hw⟩ := Finset.dvd_sum hdiv
  refine ⟨u + p * w, isUnit_add_of_norm_lt hu (norm_p_mul_lt_one w), ?_⟩
  have hexp : (1 + x) ^ p = 1 + p * x +
      ∑ l ∈ Finset.range (p - 1), x ^ (l + 2) * ((p.choose (l + 2) : ℕ) : ℤ_[p]) := by
    rw [add_comm 1 x, add_pow]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      show q + 2 - 1 = q + 1 by omega]
    rw [Nat.choose_one_right]
    push_cast; ring
  rw [hexp, hw, hx]; ring

theorem one_add_pow_p_pow {n : ℕ} (hn : 2 ≤ n) {u : ℤ_[p]} (hu : IsUnit u) (e : ℕ) :
    ∃ u' : ℤ_[p], IsUnit u' ∧
      (1 + (p : ℤ_[p]) ^ n * u) ^ (p ^ e) = 1 + (p : ℤ_[p]) ^ (n + e) * u' := by
  induction e with
  | zero => exact ⟨u, hu, by simp⟩
  | succ e ih =>
    obtain ⟨u1, hu1, h1⟩ := ih
    obtain ⟨u2, hu2, h2⟩ := one_add_pow_p (k := n + e) (by omega) hu1
    exact ⟨u2, hu2, by rw [pow_succ, pow_mul, h1, h2, add_assoc]⟩

/-- A `γ` with `chi γ = 1 + p^n u` (`n ≥ 2`, `u` a unit) is a Tate generator at level `n`. -/
theorem isTateGen_of_chi {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {n : ℕ} (hn : 2 ≤ n)
    {u : ℤ_[p]} (hu : IsUnit u) (hγ : ((chi γ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ n * u) :
    IsTateGen γ n := by
  intro k hk ζ hζ
  obtain ⟨ue, hue, he⟩ := one_add_pow_p_pow hn hu (k - n)
  rw [show n + (k - n) = k by omega] at he
  set σ := γ ^ (p ^ (k - n))
  have hσ : ((chi σ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ k * ue := by
    rw [map_pow, Units.val_pow_eq_pow_val, hγ, he]
  set v := (PadicInt.toZModPow (k + 1) ue).val with hv
  have hζk : IsPrimitiveRoot (ζ ^ (p ^ k)) p :=
    hζ.pow (pow_pos hp.out.pos _) (by ring)
  refine ⟨(ζ ^ (p ^ k)) ^ v, ?_, ?_⟩
  · refine hζk.pow_of_coprime v ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hpv
    have h1 : PadicInt.toZModPow 1 ue = 0 := by
      rw [← PadicInt.zmod_cast_comp_toZModPow 1 (k + 1) (by omega), RingHom.comp_apply,
        ← ZMod.natCast_zmod_val (PadicInt.toZModPow (k + 1) ue), ← hv, map_natCast, pow_one,
        ZMod.natCast_eq_zero_iff]
      exact hpv
    have h2 : ue ∈ RingHom.ker (PadicInt.toZModPow (p := p) 1) := h1
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one,
      ← PadicInt.norm_lt_one_iff_dvd] at h2
    rw [PadicInt.isUnit_iff] at hue
    exact h2.ne hue
  · have hspec := chi_spec σ hζ.pow_eq_one
    rw [hspec, ← pow_mul, ← pow_succ']
    refine (pow_eq_pow_iff_of_prim hζ (pow_pos hp.out.pos _)).mpr ?_
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.cast_id', id, hσ, map_add, map_one,
      map_mul, map_pow, map_natCast, ← ZMod.natCast_zmod_val (PadicInt.toZModPow (k + 1) ue),
      ← hv]
    push_cast; ring

theorem norm_zpow_sub_one_le (c : ℤ_[p]ˣ) (j : ℤ) :
    ‖((c ^ j : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ ‖(c : ℤ_[p]) - 1‖ := by
  have hdvd : ∀ m : ℕ, ((c : ℤ_[p]) - 1) ∣ ((c ^ m : ℤ_[p]ˣ) : ℤ_[p]) - 1 := by
    intro m
    rw [Units.val_pow_eq_pow_val]
    simpa using sub_dvd_pow_sub_pow (c : ℤ_[p]) 1 m
  have key : ((c : ℤ_[p]) - 1) ∣ ((c ^ j : ℤ_[p]ˣ) : ℤ_[p]) - 1 := by
    rcases Int.eq_nat_or_neg j with ⟨m, rfl | rfl⟩
    · simpa using hdvd m
    · have e : ((c ^ (-(m : ℤ)) : ℤ_[p]ˣ) : ℤ_[p]) - 1 =
          -(((c ^ (-(m : ℤ)) : ℤ_[p]ˣ) : ℤ_[p]) * (((c ^ m : ℤ_[p]ˣ) : ℤ_[p]) - 1)) := by
        rw [mul_sub, ← Units.val_mul, ← zpow_natCast, ← zpow_add, neg_add_cancel, zpow_zero,
          Units.val_one]; ring
      rw [e]
      exact (Dvd.dvd.mul_left (hdvd m) _).neg_right
  obtain ⟨d, hd⟩ := key
  rw [hd, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one d)

/-- `1 + p^n u` (`n ≥ 2`, `u` a unit) is not a root of unity. -/
theorem zpow_ne_one {c : ℤ_[p]ˣ} {n : ℕ} (hn : 2 ≤ n) {u : ℤ_[p]} (hu : IsUnit u)
    (hc : (c : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ n * u) {j : ℤ} (hj : j ≠ 0) :
    ((c ^ j : ℤ_[p]ˣ) : ℤ_[p]) ≠ 1 := by
  -- reduce to a positive exponent
  suffices H : ∀ m : ℕ, m ≠ 0 → (c : ℤ_[p]) ^ m ≠ 1 by
    intro h
    rcases Int.eq_nat_or_neg j with ⟨m, rfl | rfl⟩
    · have hm : m ≠ 0 := by rintro rfl; exact hj rfl
      exact H m hm (by rw [← Units.val_pow_eq_pow_val, ← h, zpow_natCast])
    · have hm : m ≠ 0 := by rintro rfl; exact hj (by simp)
      apply H m hm
      have h' : c ^ (-(m : ℤ)) = 1 := Units.val_eq_one.mp h
      rw [zpow_neg, inv_eq_one, zpow_natCast] at h'
      rw [← Units.val_pow_eq_pow_val, h', Units.val_one]
  intro m hm h
  obtain ⟨e, m', hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.ne_one
  obtain ⟨ue, hue, he⟩ := one_add_pow_p_pow hn hu e
  set w := (c : ℤ_[p]) ^ (p ^ e) with hw
  have hw' : w = 1 + (p : ℤ_[p]) ^ (n + e) * ue := by rw [hw, hc, he]
  have hwm : w ^ m' = 1 := by rw [hw, ← pow_mul, h]
  have hw1 : w - 1 ≠ 0 := by
    rw [hw', add_sub_cancel_left]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)) hue.ne_zero
  have hgeom : (∑ i ∈ Finset.range m', w ^ i) * (w - 1) = 0 := by
    rw [geom_sum_mul, hwm, sub_self]
  have hsum0 : ∑ i ∈ Finset.range m', w ^ i = 0 :=
    (mul_eq_zero.mp hgeom).resolve_right hw1
  -- but `∑ w^i ≡ m' (mod p)`
  have hpw : (p : ℤ_[p]) ∣ w - 1 :=
    ⟨(p : ℤ_[p]) ^ (n + e - 1) * ue, by
      rw [hw', add_sub_cancel_left, ← mul_assoc, ← pow_succ', show n + e - 1 + 1 = n + e by omega]⟩
  have hdvd : ∀ i, (p : ℤ_[p]) ∣ w ^ i - 1 := fun i =>
    hpw.trans (by simpa using sub_dvd_pow_sub_pow w 1 i)
  have hsum : (p : ℤ_[p]) ∣ ∑ i ∈ Finset.range m', w ^ i - m' := by
    have : ∑ i ∈ Finset.range m', w ^ i - m' = ∑ i ∈ Finset.range m', (w ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]; exact Finset.dvd_sum fun i _ => hdvd i
  rw [hsum0, zero_sub, dvd_neg] at hsum
  have h1 : ‖(m' : ℤ_[p])‖ = 1 := by
    rw [← PadicInt.isUnit_iff]
    have : ‖((m' : ℤ_[p]) : ℚ_[p])‖ = 1 := by
      push_cast
      exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm)
    rw [PadicInt.isUnit_iff]; exact this
  have h2 := (PadicInt.norm_lt_one_iff_dvd _).mpr hsum
  rw [h1] at h2
  exact lt_irrefl _ h2

end PadicHodge
