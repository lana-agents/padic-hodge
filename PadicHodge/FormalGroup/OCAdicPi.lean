/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.OCAdic

/-!
# `O_{ℂ_p}` is `π`-adically complete for every `0 < |π| < 1`

Generalisation of `OCAdic.lean` (`π = p`) needed for coefficient rings `O_{K'}` with
`K'/ℚ_p` ramified, where `𝔪_{K'} O_{ℂ_p} = (π)` for a uniformiser `π`:

* `OC.mem_span_pow_iff`: `x ∈ π^n O_{ℂ_p}` iff `|x| ≤ |π|^n`;
* **`OC.isAdicComplete_span`**: `O_{ℂ_p}` is `(π)`-adically complete;
* `OC.isAdicComplete_of_map_eq_span`: hence complete for `𝔪 O_{ℂ_p}` whenever `𝔪 O_{ℂ_p} = (π)`.
-/

noncomputable section

open Topology Filter

namespace PadicHodge

namespace OC

variable {p : ℕ} [hp : Fact p.Prime] {π : OC p}

/-- **`x ∈ π^n O_{ℂ_p}` iff `|x| ≤ |π|^n`** (for `π ≠ 0`). -/
theorem mem_span_pow_iff (hπ : 0 < ‖(π : ℂ_[p])‖) (n : ℕ) (x : OC p) :
    x ∈ Ideal.span {π} ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖(π : ℂ_[p])‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subring.coe_mul, norm_mul, Subring.coe_pow, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (norm_OC_le c)
  · intro hx
    have hπ0 : (π : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp hπ)
    refine ⟨⟨(x : ℂ_[p]) / (π : ℂ_[p]) ^ n, ?_⟩, ?_⟩
    · rw [mem_OC, norm_div, norm_pow]
      exact div_le_one_of_le₀ hx (pow_nonneg (norm_nonneg _) _)
    · apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_pow]
      change (x : ℂ_[p]) = (π : ℂ_[p]) ^ n * ((x : ℂ_[p]) / (π : ℂ_[p]) ^ n)
      rw [mul_div_cancel₀ _ hπ0]

/-- **`O_{ℂ_p}` is `π`-adically complete** for `0 < |π| < 1`. -/
theorem isAdicComplete_span (hπ : 0 < ‖(π : ℂ_[p])‖) (hπ1 : ‖(π : ℂ_[p])‖ < 1) :
    IsAdicComplete (Ideal.span {π}) (OC p) where
  haus' x hx := by
    have h : ∀ n, ‖(x : ℂ_[p])‖ ≤ ‖(π : ℂ_[p])‖ ^ n := fun n => by
      have := hx n
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at this
      exact (mem_span_pow_iff hπ n x).mp this
    have h0 : ‖(x : ℂ_[p])‖ ≤ 0 :=
      ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ1)
        (Eventually.of_forall h)
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact norm_le_zero_iff.mp h0
  prec' f hf := by
    have ht : Tendsto (fun n : ℕ => ‖(π : ℂ_[p])‖ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ1
    have hd : ∀ {m n}, m ≤ n → ‖((f n : OC p) : ℂ_[p]) - (f m : ℂ_[p])‖ ≤
        ‖(π : ℂ_[p])‖ ^ m := by
      intro m n hmn
      have := hf hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
      have h2 := (mem_span_pow_iff hπ m _).mp this
      rwa [AddSubgroupClass.coe_sub, norm_sub_rev] at h2
    have hc : CauchySeq f := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
      refine ⟨N, fun n hn => ?_⟩
      rw [Subtype.dist_eq, dist_eq_norm]
      exact (hd hn).trans_lt (hN N le_rfl)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow_iff hπ]
    have hlim : Tendsto (fun k => ‖((f n : OC p) : ℂ_[p]) - (f k : ℂ_[p])‖) atTop
        (𝓝 ‖((f n : OC p) : ℂ_[p]) - (L : ℂ_[p])‖) :=
      ((continuous_subtype_val.tendsto L).comp hL |>.const_sub _).norm
    rw [AddSubgroupClass.coe_sub]
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop n] with k hk
    rw [norm_sub_rev]
    exact hd hk

/-- `O_{ℂ_p}` is complete for `𝔪 O_{ℂ_p}` whenever `𝔪 O_{ℂ_p} = (π)` with `0 < |π| < 1`
(e.g. `R = O_{K'}` with uniformiser `π`). -/
theorem isAdicComplete_of_map_eq_span {R : Type*} [CommRing R] [Algebra R (OC p)]
    {𝔪 : Ideal R} (hπ : 0 < ‖(π : ℂ_[p])‖) (hπ1 : ‖(π : ℂ_[p])‖ < 1)
    (h : 𝔪.map (algebraMap R (OC p)) = Ideal.span {π}) :
    IsAdicComplete (𝔪.map (algebraMap R (OC p))) (OC p) := by
  rw [h]; exact isAdicComplete_span hπ hπ1

end OC

end PadicHodge
