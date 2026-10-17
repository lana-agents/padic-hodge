/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Character
import PadicLogVolume.PadicLog

/-!
# The logarithm of the cyclotomic character

We reuse the `p`-adic logarithm `PadicLogVolume.padicLog` of `lana-agents/padic-log-volume`,
which is defined for complete `ℤᵐ⁰`-valued fields. Mathlib's model of such a field isomorphic to
`ℚ_p` is the completion `QpV p` of `ℚ` at the `p`-adic valuation (`Padic.withValRingEquiv`,
a homeomorphism); we transport the logarithm along it:

* `logQp x = e (log (e⁻¹ x))` with `e : QpV p ≃+* ℚ_p`, a homomorphism on `1 + pℤ_p`
  (`logQp_mul`), continuous at `1`, and `logQp (1 + p^2 c) ≠ 0` for `c ≠ 0` (`logQp_ne_zero`);
* `logChi σ = log (χ(σ)^{p-1})`: a continuous homomorphism
  `Gal(ℚ̄_p/ℚ_p) → ℚ_p` (`logChi_mul`, `continuous_logChi`), trivial where `χ` is trivial,
  and `logChi γ ≠ 0` if `χ(γ) = 1 + p^n u` with `n ≥ 2`, `u` a unit (`logChi_ne_zero`).
-/

noncomputable section

open scoped Valued
open Topology Filter

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

variable (p) in
/-- `ℚ_p` as the completion of `ℚ` at the `p`-adic valuation, a `ℤᵐ⁰`-valued field. (A `def`,
so that its norm is the one of `Valued.toNormedField`.) -/
def QpV : Type := (Rat.padicValuation p).Completion

instance : Field (QpV p) := inferInstanceAs (Field (Rat.padicValuation p).Completion)

instance : Valued (QpV p) (WithZero (Multiplicative ℤ)) :=
  inferInstanceAs (Valued (Rat.padicValuation p).Completion (WithZero (Multiplicative ℤ)))

instance : CompleteSpace (QpV p) :=
  inferInstanceAs (CompleteSpace (Rat.padicValuation p).Completion)

/-- The isomorphism `QpV p ≃+* ℚ_p`. -/
def eQ : QpV p ≃+* ℚ_[p] := Padic.withValRingEquiv

instance : CharZero (QpV p) := (eQ (p := p)).toRingHom.charZero

theorem continuous_eQ : Continuous (eQ (p := p)) :=
  (Padic.withValUniformEquiv (p := p)).continuous

theorem continuous_eQ_symm : Continuous (eQ (p := p)).symm :=
  (Padic.withValUniformEquiv (p := p)).symm.continuous

theorem v_le_one_iff (x : QpV p) : Valued.v x ≤ 1 ↔ ‖eQ x‖ ≤ 1 :=
  (Padic.withValUniformEquiv_norm_le_one_iff (p := p) x).symm

theorem v_p_ne_one : Valued.v ((p : ℕ) : QpV p) ≠ 1 := by
  intro h
  have h1 : Valued.v (((p : ℕ) : QpV p)⁻¹) ≤ 1 := by rw [map_inv₀, h, inv_one]
  rw [v_le_one_iff, map_inv₀, map_natCast, norm_inv, Padic.norm_p, inv_inv] at h1
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  linarith

theorem v_p_ne_zero : Valued.v ((p : ℕ) : QpV p) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)

instance : Nontrivial (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass (Valued.v : Valuation (QpV p) (WithZero (Multiplicative ℤ))))) :=
  ⟨⟨⟨Units.mk0 _ v_p_ne_zero, MonoidWithZeroHom.mem_valueGroup _ ⟨_, rfl⟩⟩, 1,
    fun h => v_p_ne_one (p := p) (by
    have := congrArg (fun u : MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass
      (Valued.v : Valuation (QpV p) (WithZero (Multiplicative ℤ)))) =>
        ((u : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))) h
    simpa using this)⟩⟩

instance rankOneQpV :
    (Valued.v : Valuation (QpV p) (WithZero (Multiplicative ℤ))).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (e := (p : NNReal)) (by exact_mod_cast hp.out.one_lt)

theorem normV_le_one_iff (x : QpV p) : ‖x‖ ≤ 1 ↔ ‖eQ x‖ ≤ 1 := by
  rw [← v_le_one_iff, ← norm_one (α := QpV p), Valued.toNormedField.norm_le_iff, map_one]

theorem normV_p_lt_one : ‖((p : ℕ) : QpV p)‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have h1 : ¬ ‖((p : ℕ) : QpV p)⁻¹‖ ≤ 1 := by
    rw [normV_le_one_iff, map_inv₀, map_natCast, norm_inv, Padic.norm_p, inv_inv]
    exact not_le.mpr hp1
  have h0 : ((p : ℕ) : QpV p) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [norm_inv] at h1
  push Not at h1
  have hpos : 0 < ‖((p : ℕ) : QpV p)‖ := norm_pos_iff.mpr h0
  exact (one_lt_inv₀ hpos).mp h1

theorem normV_symm_le (k : ℕ) (c : ℤ_[p]) :
    ‖(eQ (p := p)).symm (((p : ℚ_[p]) ^ k) * (c : ℚ_[p]))‖ ≤ ‖((p : ℕ) : QpV p)‖ ^ k := by
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [normV_le_one_iff, RingEquiv.apply_symm_apply]
  exact PadicInt.norm_le_one c

/-- The `p`-adic logarithm on `ℚ_p`, transported from `QpV p`. -/
def logQp (x : ℚ_[p]) : ℚ_[p] := eQ (PadicLogVolume.padicLog ((eQ (p := p)).symm x))

theorem logQp_one : logQp (p := p) 1 = 0 := by
  rw [logQp, map_one, PadicLogVolume.padicLog_one, map_zero]

theorem normV_symm_sub_one_lt (c : ℤ_[p]) :
    ‖(eQ (p := p)).symm (1 + (p : ℚ_[p]) * (c : ℚ_[p])) - 1‖ < 1 := by
  rw [map_add, map_one, add_sub_cancel_left]
  have := normV_symm_le (p := p) 1 c
  rw [pow_one, pow_one] at this
  exact this.trans_lt normV_p_lt_one

theorem logQp_mul (c d : ℤ_[p]) :
    logQp ((1 + (p : ℚ_[p]) * (c : ℚ_[p])) * (1 + (p : ℚ_[p]) * (d : ℚ_[p]))) =
      logQp (1 + (p : ℚ_[p]) * (c : ℚ_[p])) + logQp (1 + (p : ℚ_[p]) * (d : ℚ_[p])) := by
  unfold logQp
  rw [map_mul, PadicLogVolume.padicLog_mul hp.out normV_p_lt_one (normV_symm_sub_one_lt c)
    (normV_symm_sub_one_lt d), map_add]

theorem normV_p_le_two_mul : ‖((p : ℕ) : QpV p)‖ ^ 2 ≤ ‖2 * ((p : ℕ) : QpV p)‖ := by
  rw [norm_mul, sq]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases hp.out.eq_two_or_odd' with h2 | hodd
  · subst h2
    norm_num
  · rw [PadicLogVolume.norm_two_eq_one hp.out normV_p_lt_one hodd]
    exact normV_p_lt_one.le

/-- `log (1 + b) ≠ 0` for `b ≠ 0` small. -/
theorem logQp_ne_zero {c : ℤ_[p]} (hc : c ≠ 0) :
    logQp (1 + (p : ℚ_[p]) ^ 2 * (c : ℚ_[p])) ≠ 0 := by
  unfold logQp
  rw [map_add, map_one, map_ne_zero_iff _ (eQ (p := p)).injective]
  set b := (eQ (p := p)).symm ((p : ℚ_[p]) ^ 2 * (c : ℚ_[p])) with hb
  have hb0 : b ≠ 0 := by
    rw [hb, map_ne_zero_iff _ (eQ (p := p)).symm.injective]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero))
      (PadicInt.coe_ne_zero.mpr hc)
  have hbs : ‖b‖ ≤ ‖2 * ((p : ℕ) : QpV p)‖ := (normV_symm_le 2 c).trans normV_p_le_two_mul
  have hb1 : ‖b‖ < 1 :=
    hbs.trans_lt (PadicLogVolume.norm_two_mul_lt_one normV_p_lt_one)
  rw [PadicLogVolume.padicLog_one_add hp.out normV_p_lt_one hb1]
  intro h
  have hrem := PadicLogVolume.norm_logRem_le hp.out normV_p_lt_one hbs
  rw [eq_neg_of_add_eq_zero_right h, norm_neg] at hrem
  have hpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have := normV_p_lt_one (p := p)
  nlinarith

/-- `‖log (1 + b)‖ ≤ ‖b‖` for `‖b‖ ≤ ‖2p‖` (in `QpV p`). -/
theorem normV_padicLog_one_add_le {b : QpV p} (hb : ‖b‖ ≤ ‖2 * ((p : ℕ) : QpV p)‖) :
    ‖PadicLogVolume.padicLog (1 + b)‖ ≤ ‖b‖ := by
  have hb1 : ‖b‖ < 1 := hb.trans_lt (PadicLogVolume.norm_two_mul_lt_one normV_p_lt_one)
  rw [PadicLogVolume.padicLog_one_add hp.out normV_p_lt_one hb1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
  refine (PadicLogVolume.norm_logRem_le hp.out normV_p_lt_one hb).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) normV_p_lt_one.le

theorem continuousAt_padicLog_one :
    ContinuousAt (PadicLogVolume.padicLog : QpV p → QpV p) 1 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have h2p : 0 < ‖2 * ((p : ℕ) : QpV p)‖ := norm_pos_iff.mpr
    (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero))
  refine ⟨min ε ‖2 * ((p : ℕ) : QpV p)‖, lt_min hε h2p, fun {x} hx => ?_⟩
  rw [dist_eq_norm] at hx ⊢
  rw [PadicLogVolume.padicLog_one, sub_zero]
  have hx' := lt_min_iff.mp hx
  have e : x = 1 + (x - 1) := by ring
  rw [e]
  exact (normV_padicLog_one_add_le hx'.2.le).trans_lt hx'.1

theorem continuousAt_logQp_one : ContinuousAt (logQp (p := p)) 1 := by
  have h1 : ContinuousAt (fun x : ℚ_[p] => (eQ (p := p)).symm x) 1 :=
    continuous_eQ_symm.continuousAt
  have h2 : ContinuousAt (PadicLogVolume.padicLog : QpV p → QpV p) ((eQ (p := p)).symm 1) := by
    rw [map_one]; exact continuousAt_padicLog_one
  exact continuous_eQ.continuousAt.comp (h2.comp h1)

/-! ### `log χ` -/

/-- Fermat: `u^{p-1} ≡ 1 (mod p)` for `u ∈ ℤ_p^×`. -/
theorem exists_pow_sub_one_eq (u : ℤ_[p]ˣ) :
    ∃ c : ℤ_[p], ((u ^ (p - 1) : ℤ_[p]ˣ) : ℤ_[p]) = 1 + p * c := by
  have hu : PadicInt.toZMod (u : ℤ_[p]) ≠ 0 := fun h0 =>
    not_isUnit_zero (h0 ▸ (Units.isUnit u).map PadicInt.toZMod)
  have h : ((u ^ (p - 1) : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, Units.val_pow_eq_pow_val, map_pow, map_one,
      ZMod.pow_card_sub_one_eq_one hu, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [← hc]; ring⟩

/-- `log χ(σ) := log (χ(σ)^{p-1})` (the factor `p - 1` makes `χ^{p-1}` a principal unit). -/
def logChiHom : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Multiplicative ℚ_[p] where
  toFun σ := Multiplicative.ofAdd (logQp ((((chi σ ^ (p - 1) : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])))
  map_one' := by simp [logQp_one]
  map_mul' σ τ := by
    obtain ⟨c, hc⟩ := exists_pow_sub_one_eq (chi σ)
    obtain ⟨d, hd⟩ := exists_pow_sub_one_eq (chi τ)
    rw [← ofAdd_add, map_mul, mul_pow, Units.val_mul, PadicInt.coe_mul, hc, hd]
    push_cast
    rw [logQp_mul]

/-- `log χ : Gal(ℚ̄_p/ℚ_p) → ℚ_p`. -/
def logChi (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℚ_[p] := (logChiHom σ).toAdd

theorem ofAdd_logChi (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Multiplicative.ofAdd (logChi σ) = logChiHom σ := rfl

theorem logChi_mul (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    logChi (σ * τ) = logChi σ + logChi τ := by
  rw [logChi, map_mul, toAdd_mul]; rfl

theorem logChi_eq_zero_of_chi_eq_one {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (h : chi σ = 1) : logChi σ = 0 := by
  change logQp _ = 0
  rw [h, one_pow, Units.val_one, PadicInt.coe_one, logQp_one]

theorem logChi_ne_zero {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {n : ℕ} (hn : 2 ≤ n)
    {u : ℤ_[p]} (hu : IsUnit u) (hγ : ((chi γ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ n * u) :
    logChi γ ≠ 0 := by
  -- `χ(γ)^{p-1} = 1 + p^2 c` with `c ≠ 0`
  have hne : ((chi γ ^ ((p - 1 : ℕ) : ℤ) : ℤ_[p]ˣ) : ℤ_[p]) ≠ 1 :=
    zpow_ne_one hn hu hγ (by have := hp.out.two_le; omega)
  rw [zpow_natCast] at hne
  have hdvd : (p : ℤ_[p]) ^ 2 ∣ ((chi γ ^ (p - 1) : ℤ_[p]ˣ) : ℤ_[p]) - 1 := by
    have h1 : ((chi γ : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∣ ((chi γ ^ (p - 1) : ℤ_[p]ˣ) : ℤ_[p]) - 1 := by
      rw [Units.val_pow_eq_pow_val]
      simpa using sub_dvd_pow_sub_pow ((chi γ : ℤ_[p]ˣ) : ℤ_[p]) 1 (p - 1)
    refine dvd_trans ?_ h1
    rw [hγ, add_sub_cancel_left]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ hn) _
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero, sub_eq_zero] at hc
    exact hne hc
  change logQp _ ≠ 0
  rw [show ((((chi γ ^ (p - 1) : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) = 1 + (p : ℚ_[p]) ^ 2 * c by
    rw [eq_add_of_sub_eq' hc]; push_cast; ring]
  exact logQp_ne_zero hc0

theorem continuous_logChi : Continuous (logChi (p := p)) := by
  -- continuity at `1`
  have hw : Continuous fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p =>
      ((((chi σ ^ (p - 1) : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) := by
    have h := cyclotomicCharacter.continuous p ℚ_[p] (PadicAlgCl p)
    have hc : Continuous (fun z : ℤ_[p] => (z : ℚ_[p])) :=
      Metric.continuous_iff.mpr fun b ε hε => ⟨ε, hε, fun a h => h⟩
    exact hc.comp (Units.continuous_val.comp ((continuous_pow (p - 1)).comp h))
  have h1 : ContinuousAt (logChi (p := p)) 1 := by
    have : ContinuousAt (fun σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p =>
        logQp ((((chi σ ^ (p - 1) : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))) 1 := by
      refine ContinuousAt.comp (g := logQp) ?_ hw.continuousAt
      simp only [map_one, one_pow, Units.val_one, PadicInt.coe_one]
      exact continuousAt_logQp_one
    exact this
  rw [continuous_iff_continuousAt]
  intro τ
  have ht : Tendsto (fun σ => logChi (τ⁻¹ * σ)) (𝓝 τ) (𝓝 (logChi (p := p) 1)) := by
    refine h1.tendsto.comp ?_
    have := (continuous_const_mul τ⁻¹).tendsto τ
    rwa [inv_mul_cancel] at this
  have e : ∀ σ, logChi σ = logChi τ + logChi (τ⁻¹ * σ) := fun σ => by
    rw [← logChi_mul, mul_inv_cancel_left]
  have h0 : logChi (p := p) 1 = 0 := logChi_eq_zero_of_chi_eq_one (map_one _)
  rw [h0] at ht
  have := (tendsto_const_nhds (x := logChi τ)).add ht
  rw [add_zero] at this
  exact this.congr fun σ => (e σ).symm

end PadicHodge
