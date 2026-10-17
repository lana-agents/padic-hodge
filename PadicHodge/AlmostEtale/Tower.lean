/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AlmostEtale.Cyclo
import PadicHodge.AlmostEtale.Mono
import PadicHodge.Cyclotomic.Fields

/-!
# The differents along the cyclotomic tower tend to `1`

Let `F_m = ℚ_p(μ_{p^{m+1}})` and `L_m ⊇ F_m` finite extensions of `ℚ_p` with
`L_{m+1} = L_m F_{m+1}`. Choose generators `O_{L_m} = ℤ_p[z_m]` (`exists_monogenic`) and let
`a_m = ‖g_m'(z_m)‖` for the minimal polynomial `g_m` of `z_m` over `F_m` (so `a_m = p^{-δ_m}` with
`δ_m = v(𝔇_{L_m/F_m})`). Faltings' step (`faltings_step`, with the cyclotomic input
`cyc_transitivity`) gives `a_m² ≤ a_{m+1}² max(a_m, ‖p‖)`, hence `a_m → 1` (`tendsto_one_of_step`),
i.e. `δ_m → 0` ([BC, Exercise 13.7.4 (6)]).

Consequently (`exists_trace_large`) for every `ρ < 1` and all large `m` there is `u ∈ O_{L_m}`
with `‖Tr_{L_m/F_m}(u)‖ ≥ ρ`: the trace of `O_{L_m}` is almost all of `O_{F_m}`.
-/

noncomputable section

open Polynomial IntermediateField Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K̄" => PadicAlgCl p

/-! ### A real-analysis lemma -/

theorem tendsto_one_of_step {a : ℕ → ℝ} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (ha0 : ∀ m, 0 < a m) (ha1 : ∀ m, a m ≤ 1)
    (h : ∀ m, a m ^ 2 ≤ a (m + 1) ^ 2 * max (a m) c) {ρ : ℝ} (hρ : ρ < 1) :
    ∃ M, ∀ m ≥ M, ρ ≤ a m := by
  set b : ℕ → ℝ := fun m => -Real.log (a m) with hbdef
  set Lc := -Real.log c with hLc
  have hL0 : 0 < Lc := by rw [hLc]; exact neg_pos.mpr (Real.log_neg hc0 hc1)
  have hb0 : ∀ m, 0 ≤ b m := fun m => neg_nonneg.mpr (Real.log_nonpos (ha0 m).le (ha1 m))
  -- one step
  have hstep : ∀ m, b (m + 1) ≤ b m - min (b m) Lc / 2 := by
    intro m
    have h1 := h m
    have hpos : 0 < a m ^ 2 := by have := ha0 m; positivity
    have hlog := Real.log_le_log hpos h1
    rw [Real.log_mul (by have := ha0 (m + 1); positivity)
      (by have := ha0 m; positivity : max (a m) c ≠ 0), Real.log_pow, Real.log_pow] at hlog
    simp only [hbdef]
    rcases le_total c (a m) with hca | hca
    · rw [max_eq_left hca] at hlog
      have : -Real.log (a m) ≤ Lc := by
        rw [hLc]; exact neg_le_neg (Real.log_le_log hc0 hca)
      rw [min_eq_left this]
      push_cast at hlog
      linarith
    · rw [max_eq_right hca] at hlog
      have : Lc ≤ -Real.log (a m) := by
        rw [hLc]; exact neg_le_neg (Real.log_le_log (ha0 m) hca)
      rw [min_eq_right this]
      push_cast at hlog
      linarith
  have hmono : ∀ m, b (m + 1) ≤ b m := fun m => by
    have := hstep m
    have : 0 ≤ min (b m) Lc := le_min (hb0 m) hL0.le
    linarith
  have hB : ∀ m, b m ≤ b 0 := by
    intro m
    induction m with
    | zero => exact le_rfl
    | succ m ih => exact (hmono m).trans ih
  set B' := max (b 0) Lc with hB'
  have hB'0 : 0 < B' := lt_of_lt_of_le hL0 (le_max_right _ _)
  set θ := 1 - Lc / (2 * B') with hθ
  have hθ0 : 0 ≤ θ := by
    rw [hθ, sub_nonneg, div_le_one (by positivity)]
    linarith [le_max_right (b 0) Lc]
  have hθ1 : θ < 1 := by rw [hθ]; have : 0 < Lc / (2 * B') := by positivity
                         linarith
  have hcontr : ∀ m, b (m + 1) ≤ θ * b m := by
    intro m
    have hs := hstep m
    rcases le_total (b m) Lc with hbl | hbl
    · rw [min_eq_left hbl] at hs
      have : (1 : ℝ) / 2 ≤ θ := by
        rw [hθ]
        have : Lc / (2 * B') ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith [le_max_right (b 0) Lc]
        linarith
      nlinarith [hb0 m]
    · rw [min_eq_right hbl] at hs
      have hbm : 0 < b m := lt_of_lt_of_le hL0 hbl
      have : b m * (Lc / (2 * B')) ≤ Lc / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        have : b m ≤ B' := (hB m).trans (le_max_left _ _)
        nlinarith
      rw [hθ]; nlinarith
  have hgeo : ∀ m, b m ≤ θ ^ m * b 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc b (m + 1) ≤ θ * b m := hcontr m
        _ ≤ θ * (θ ^ m * b 0) := mul_le_mul_of_nonneg_left ih hθ0
        _ = θ ^ (m + 1) * b 0 := by ring
  by_cases hρ0 : ρ ≤ 0
  · exact ⟨0, fun m _ => hρ0.trans (ha0 m).le⟩
  push Not at hρ0
  have hε : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ0 hρ)
  obtain ⟨M, hM⟩ : ∃ M, θ ^ M * b 0 < -Real.log ρ := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
    have := (ht.mul_const (b 0)).eventually
      (gt_mem_nhds (show 0 * b 0 < -Real.log ρ by rw [zero_mul]; exact hε))
    exact this.exists
  refine ⟨M, fun m hm => ?_⟩
  have h1 : b m < -Real.log ρ :=
    lt_of_le_of_lt ((hgeo m).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hθ0 hθ1.le hm) (hb0 0))) hM
  simp only [hbdef, neg_lt_neg_iff] at h1
  exact ((Real.log_lt_log_iff hρ0 (ha0 m)).mp h1).le

/-! ### Monogenic generators generate -/

theorem le_restrictScalars_of_mono {L : IntermediateField ℚ_[p] (PadicAlgCl p)} {z : PadicAlgCl p}
    (hmono : ∀ y ∈ L, ‖y‖ ≤ 1 → y ∈ adj (OK (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))) z)
    (F : IntermediateField ℚ_[p] (PadicAlgCl p)) : L ≤ (F⟮z⟯).restrictScalars ℚ_[p] := by
  intro y hy
  by_cases hy0 : y = 0
  · rw [hy0]; exact zero_mem _
  have hp1 : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr (norm_pos_iff.mpr hy0)) hp1
  have hp0 : ((p : PadicAlgCl p) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have h1 : (p : PadicAlgCl p) ^ k * y ∈ adj (OK F) z := by
    refine adj_mono (OK_mono bot_le) z
      (hmono _ (mul_mem (pow_mem (IntermediateField.natCast_mem _ _) _) hy) ?_)
    rw [norm_mul, norm_pow]
    have := mul_lt_mul_of_pos_right hk (norm_pos_iff.mpr hy0)
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)] at this
    exact this.le
  have h2 := mem_adjoin_of_mem_adj F h1
  have : y = ((p : PadicAlgCl p) ^ k)⁻¹ * ((p : PadicAlgCl p) ^ k * y) := by field_simp
  rw [this]
  exact mul_mem (inv_mem (pow_mem (by exact_mod_cast (F⟮z⟯).natCast_mem p) _)) h2

/-! ### The tower -/

theorem norm_p_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)


section Tower

variable (L : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) [∀ m, FiniteDimensional ℚ_[p] (L m)]
  (hFL : ∀ m, cycField p (m + 1) ≤ L m) (hL : ∀ m, L (m + 1) = L m ⊔ cycField p (m + 2))
include hFL hL

/-- **Almost étaleness along the cyclotomic tower**: the traces `Tr_{L_m/F_m}(O_{L_m})` contain
elements of norm `≥ ρ` for every `ρ < 1` and all large `m`. -/
theorem exists_trace_large {ρ : ℝ} (hρ : ρ < 1) : ∃ M, ∀ m ≥ M, ∃ u ∈ L m, ‖u‖ ≤ 1 ∧
    ρ ≤ ‖(rdeg (cycField p (m + 1)) (L m) : PadicAlgCl p) * nt (cycField p (m + 1)) u‖ := by
  classical
  choose z hzL hz1 hzmono using fun m => exists_monogenic (L m)
  set F : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p) := fun m => cycField p (m + 1) with hF
  haveI : ∀ m, FiniteDimensional ℚ_[p] (F m) := fun m => finiteDimensional_of_le' (hFL m)
  have hLz : ∀ m (E : IntermediateField ℚ_[p] (PadicAlgCl p)),
      L m ≤ (E⟮z m⟯).restrictScalars ℚ_[p] := fun m E => le_restrictScalars_of_mono (hzmono m) E
  have hLeq : ∀ m, ((F m)⟮z m⟯).restrictScalars ℚ_[p] = L m := fun m =>
    le_antisymm (restrictScalars_adjoin_le _ (hFL m) (hzL m)) (hLz m _)
  have hLQ : ∀ m, L m ≤ ℚ_[p]⟮z m⟯ := fun m =>
    (hLz m ⊥).trans (restrictScalars_adjoin_le _ bot_le (mem_adjoin_simple_self _ _))
  have hLmono : ∀ m, L m ≤ L (m + 1) := fun m => by rw [hL m]; exact le_sup_left
  set a : ℕ → ℝ := fun m => ‖(derivative (mp (F m) (z m))).eval (z m)‖ with ha
  have ha0 : ∀ m, 0 < a m := fun m => norm_pos_iff.mpr (derivative_mp_ne_zero _ _)
  have ha1 : ∀ m, a m ≤ 1 := fun m =>
    norm_eval_le_one (OK_le_ballK _) (derivative_mem_polyOver (mp_mem_polyOver _ (hz1 m))) (hz1 m)
  have hstep : ∀ m, a m ^ 2 ≤ a (m + 1) ^ 2 * max (a m) ‖(p : PadicAlgCl p)‖ := by
    intro m
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (m + 2)
    have e1 : F m = ℚ_[p]⟮ζ ^ p⟯ := cycField_eq (isPrimitiveRoot_pow_p hζ)
    have e2 : F (m + 1) = ℚ_[p]⟮ζ⟯ := cycField_eq hζ
    have hFF' : F m ≤ F (m + 1) := cycField_mono (by omega)
    have hxz : z m ∈ adj (OK (F m)) (z (m + 1)) :=
      adj_mono (OK_mono bot_le) _ (hzmono (m + 1) _ (hLmono m (hzL m)) (hz1 m))
    have hzx : z (m + 1) ∈ (F (m + 1))⟮z m⟯ := by
      have : L (m + 1) ≤ ((F (m + 1))⟮z m⟯).restrictScalars ℚ_[p] := by
        rw [hL m]
        exact sup_le (hLz m _) (le_restrictScalars_adjoin _ _)
      exact this (hzL (m + 1))
    have hT := cyc_transitivity hζ (hz1 (m + 1))
      (e2 ▸ (hFL (m + 1)).trans (hLQ (m + 1)))
    rw [← e1, ← e2] at hT
    exact faltings_step hFF' (hz1 m) (hz1 (m + 1)) hxz hzx hT
  -- `a_m → 1`
  set s := Real.sqrt ρ with hs
  by_cases hρ0 : ρ ≤ 0
  · refine ⟨0, fun m _ => ⟨0, zero_mem _, by simp, ?_⟩⟩
    rw [show nt (cycField p (m + 1)) 0 = 0 by simp [nt], mul_zero, norm_zero]
    exact hρ0
  push Not at hρ0
  have hs0 : 0 < s := Real.sqrt_pos.mpr hρ0
  have hs1 : s < 1 := by rw [hs, Real.sqrt_lt' one_pos]; simpa using hρ
  have hp0' : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  obtain ⟨M₁, hM₁⟩ := tendsto_one_of_step hp0' norm_p_lt_one ha0 ha1 hstep hs1
  obtain ⟨M₂, hM₂⟩ := exists_pow_lt_of_lt_one hp0' hs1
  refine ⟨max M₁ M₂, fun m hm => ?_⟩
  -- the uniformizer `π = ζ_{p^{m+1}} - 1` of `F_m` has `‖π‖ ≥ s`
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p := p) (m + 1)
  set π := ζ - 1 with hπ
  have hπF : π ∈ F m := sub_mem (pow_mem_cycField hζ.pow_eq_one) (one_mem _)
  have hπφ := norm_sub_one_pow_totient hζ
  have hπ0 : 0 < ‖π‖ := by
    rcases (norm_nonneg π).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_pow (Nat.totient_pos.mpr (pow_pos hp.out.pos _)).ne'] at hπφ
      exact absurd hπφ.symm (inv_ne_zero (Nat.cast_ne_zero.mpr hp.out.ne_zero))
  have hpn : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hπs : s ≤ ‖π‖ := by
    by_contra hlt
    push Not at hlt
    have hφ : M₂ ≤ (p ^ (m + 1)).totient := by
      have h1 : m + 1 < p ^ (m + 1) := Nat.lt_pow_self hp.out.one_lt
      rw [Nat.totient_prime_pow_succ hp.out]
      have : p ^ m * 1 ≤ p ^ m * (p - 1) := Nat.mul_le_mul_left _ (by have := hp.out.two_le; omega)
      have h2 : m + 1 ≤ p ^ m := by
        have := Nat.lt_pow_self (n := m) hp.out.one_lt
        omega
      have := le_max_right M₁ M₂
      omega
    have : (p : ℝ)⁻¹ < (p : ℝ)⁻¹ := by
      calc (p : ℝ)⁻¹ = ‖π‖ ^ (p ^ (m + 1)).totient := hπφ.symm
        _ ≤ s ^ (p ^ (m + 1)).totient := pow_le_pow_left₀ (norm_nonneg _) hlt.le _
        _ ≤ s ^ M₂ := pow_le_pow_of_le_one hs0.le hs1.le hφ
        _ < ‖(p : PadicAlgCl p)‖ := hM₂
        _ = (p : ℝ)⁻¹ := hpn
    exact lt_irrefl _ this
  -- the element `u = π^k z^{d-1} / g'(z)`
  set b := (derivative (mp (F m) (z m))).eval (z m) with hb
  have hb0 : b ≠ 0 := derivative_mp_ne_zero _ _
  have hab : s ≤ ‖b‖ := hM₁ m (le_of_max_le_left hm)
  have hζ1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one (pow_ne_zero _ hp.out.ne_zero) hζ.pow_eq_one
  have hπ1 : ‖π‖ < 1 := lt_of_le_of_ne ((norm_sub_le_max' ζ 1).trans (by rw [hζ1, norm_one,
    max_self])) (by
      intro h; rw [h, one_pow] at hπφ
      exact absurd hπφ (by
        have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
        exact ne_of_gt (inv_lt_one_of_one_lt₀ this)))
  have hex : ∃ k : ℕ, ‖π‖ ^ k ≤ ‖b‖ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hb0) hπ1
    exact ⟨k, hk.le⟩
  set k := Nat.find hex
  have hk : ‖π‖ ^ k ≤ ‖b‖ := Nat.find_spec hex
  have hk' : ‖b‖ * ‖π‖ ≤ ‖π‖ ^ k := by
    by_cases hk0 : k = 0
    · rw [hk0, pow_zero]
      exact mul_le_one₀ (ha1 m) hπ0.le hπ1.le
    · have := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)
      push Not at this
      calc ‖b‖ * ‖π‖ ≤ ‖π‖ ^ (k - 1) * ‖π‖ :=
            mul_le_mul_of_nonneg_right this.le hπ0.le
        _ = ‖π‖ ^ k := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
  set d := dg (F m) (z m)
  have hd0 := dg_pos (F m) (z m)
  refine ⟨π ^ k * (z m ^ (d - 1) / b), ?_, ?_, ?_⟩
  · refine mul_mem (pow_mem ((hFL m) hπF) _) (div_mem (pow_mem (hzL m) _) ?_)
    rw [← hLeq m, hb]
    exact eval_mem_adjoin _ (fun n => by
      rw [coeff_derivative]
      exact mul_mem (coeff_mp_mem _ _ _) (by exact_mod_cast IntermediateField.natCast_mem _ _)) _
  · rw [norm_mul, norm_div, norm_pow, norm_pow]
    calc ‖π‖ ^ k * (‖z m‖ ^ (d - 1) / ‖b‖) ≤ ‖b‖ * (1 / ‖b‖) :=
          mul_le_mul hk (div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (hz1 m))
            (norm_nonneg _)) (by positivity) (norm_nonneg _)
      _ = 1 := by field_simp
  · rw [rdeg_adjoin (hLeq m), nt_mul_left _ (pow_mem hπF _), mul_left_comm,
      trace_pow_div_derivative _ _ (by omega), if_pos rfl, mul_one, norm_pow]
    calc ρ = s * s := by rw [hs, Real.mul_self_sqrt hρ0.le]
      _ ≤ ‖b‖ * ‖π‖ := mul_le_mul hab hπs hs0.le (norm_nonneg _)
      _ ≤ ‖π‖ ^ k := hk'

end Tower

end PadicHodge
