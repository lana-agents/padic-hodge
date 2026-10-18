/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Log
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# `O_{ℂ_p}` is `p`-adically complete

`x ∈ p^n O_{ℂ_p}` iff `|x| ≤ |p|^n` (`mem_span_p_pow_iff`), so the `p`-adic topology of
`O_{ℂ_p}` is its metric topology on the closed unit ball, and metric completeness gives
**`IsAdicComplete (p) O_{ℂ_p}`** (`OC.isAdicComplete_span_p`). This is the hypothesis of
`FormalGroup/LayerLimitBase.lean` for `S = O_{ℂ_p}` (over `ℤ_p`, `𝔪 O_{ℂ_p} = (p)`), used to
turn points of `T_p(G^∨)` into formal homomorphisms `F_{O_{ℂ_p}} → Ĝ_m`
([Hong, Prop. 3.4.9, proof, (3.7)]).
-/

noncomputable section

open Topology Filter

namespace PadicHodge

namespace OC

variable {p : ℕ} [hp : Fact p.Prime]

theorem coe_p : ((p : OC p) : ℂ_[p]) = (p : ℂ_[p]) := by simp

theorem norm_p_pos : 0 < ‖((p : OC p) : ℂ_[p])‖ := by
  rw [coe_p]; exact FGL.np_pos

theorem norm_p_lt_one : ‖((p : OC p) : ℂ_[p])‖ < 1 := by
  rw [coe_p]; exact FGL.np_lt_one

/-- **`x ∈ p^n O_{ℂ_p}` iff `|x| ≤ |p|^n`.** -/
theorem mem_span_p_pow_iff (n : ℕ) (x : OC p) :
    x ∈ Ideal.span {(p : OC p)} ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖((p : OC p) : ℂ_[p])‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subring.coe_mul, norm_mul, Subring.coe_pow, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (norm_OC_le c)
  · intro hx
    have hp0 : ((p : OC p) : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp norm_p_pos)
    refine ⟨⟨(x : ℂ_[p]) / ((p : OC p) : ℂ_[p]) ^ n, ?_⟩, ?_⟩
    · rw [mem_OC, norm_div, norm_pow]
      exact div_le_one_of_le₀ hx (pow_nonneg (norm_nonneg _) _)
    · apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_pow]
      change (x : ℂ_[p]) = ((p : OC p) : ℂ_[p]) ^ n * ((x : ℂ_[p]) / ((p : OC p) : ℂ_[p]) ^ n)
      rw [mul_div_cancel₀ _ hp0]

theorem tendsto_norm_p_pow : Tendsto (fun n : ℕ => ‖((p : OC p) : ℂ_[p])‖ ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_p_lt_one

/-- **`O_{ℂ_p}` is `p`-adically complete.** -/
theorem isAdicComplete_span_p : IsAdicComplete (Ideal.span {(p : OC p)}) (OC p) where
  haus' x hx := by
    have h : ∀ n, ‖(x : ℂ_[p])‖ ≤ ‖((p : OC p) : ℂ_[p])‖ ^ n := fun n => by
      have := hx n
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
      exact (mem_span_p_pow_iff n x).mp this
    have h0 : ‖(x : ℂ_[p])‖ ≤ 0 :=
      ge_of_tendsto tendsto_norm_p_pow (Eventually.of_forall h)
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact norm_le_zero_iff.mp h0
  prec' f hf := by
    have hd : ∀ {m n}, m ≤ n → ‖((f n : OC p) : ℂ_[p]) - (f m : ℂ_[p])‖ ≤
        ‖((p : OC p) : ℂ_[p])‖ ^ m := by
      intro m n hmn
      have := hf hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
      have h2 := (mem_span_p_pow_iff m _).mp this
      rwa [AddSubgroupClass.coe_sub, norm_sub_rev] at h2
    have hc : CauchySeq f := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ :=
        ((tendsto_norm_p_pow (p := p)).eventually (gt_mem_nhds hε)).exists_forall_of_atTop
      refine ⟨N, fun n hn => ?_⟩
      rw [Subtype.dist_eq, dist_eq_norm]
      exact (hd hn).trans_lt (hN N le_rfl)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_p_pow_iff]
    have hlim : Tendsto (fun k => ‖((f n : OC p) : ℂ_[p]) - (f k : ℂ_[p])‖) atTop
        (𝓝 ‖((f n : OC p) : ℂ_[p]) - (L : ℂ_[p])‖) :=
      ((continuous_subtype_val.tendsto L).comp hL |>.const_sub _).norm
    rw [AddSubgroupClass.coe_sub]
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop n] with k hk
    rw [norm_sub_rev]
    exact hd hk

/-- `O_{ℂ_p}` is complete for `𝔪 O_{ℂ_p}` whenever `𝔪 O_{ℂ_p} = (p)` (e.g. `R = ℤ_p`). -/
theorem isAdicComplete_of_map_eq {R : Type*} [CommRing R] [Algebra R (OC p)] {𝔪 : Ideal R}
    (h : 𝔪.map (algebraMap R (OC p)) = Ideal.span {(p : OC p)}) :
    IsAdicComplete (𝔪.map (algebraMap R (OC p))) (OC p) := by
  rw [h]; exact isAdicComplete_span_p

/-- For any `ℤ_p`-algebra structure on `O_{ℂ_p}`: `𝔪_{ℤ_p} O_{ℂ_p} = (p)`. -/
theorem map_maximalIdeal_padicInt [Algebra ℤ_[p] (OC p)] :
    (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (OC p)) =
      Ideal.span {(p : OC p)} := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]

/-- **`O_{ℂ_p}` is `𝔪_{ℤ_p}`-adically complete** (the hypothesis of
`PDivFGL.exists_evB_eq` for `S = O_{ℂ_p}`, `R = ℤ_p`). -/
theorem isAdicComplete_padicInt [Algebra ℤ_[p] (OC p)] :
    IsAdicComplete ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] (OC p))) (OC p) :=
  isAdicComplete_of_map_eq map_maximalIdeal_padicInt

end OC

end PadicHodge
