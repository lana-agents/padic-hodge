/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AlmostEtale.Euler

/-!
# Faltings' inductive step

This is the heart of Faltings' commutative-algebra proof of Tate's almost-étaleness theorem
([BC, Exercise 13.7.4 (4)–(6)], case `d = 0`), written with explicit generators instead of
Kähler differentials.

Setting: `F ⊆ F'` intermediate fields of `ℚ̄_p`, `x, z` integral, `x ∈ O_F[z]` (so
`O_{F'}[x] ⊆ O_{F'}[z]`) and `F'(x) = F'(z)`. Write
`a = f'(x)` (`f` the minimal polynomial of `x` over `F`; for `O_L = O_F[x]` this generates the
different `𝔇_{L/F}`), `b = g'(z)` (`g` the minimal polynomial of `z` over `F'`) and
`c = G'(z)` (`G` the minimal polynomial of `z` over `F`). Assume `‖c‖ ≤ ‖p‖ ‖b‖`
(in the cyclotomic tower this is the transitivity of the different together with
`𝔇_{F'/F} = (p)`, see `AlmostEtale/Cyclo.lean`). Then (`faltings_step`)

  `‖a‖² ≤ ‖b‖² · max(‖a‖, ‖p‖)`,

i.e. with `δ = v(a)`, `δ' = v(b)` (`v(p) = 1`): `2(δ − δ') ≥ min(δ, 1)` — [BC, Ex. 13.7.4 (6)]
`δ_n − δ_{n+1} ≥ β_n − (d+1)(δ_n − δ_{n+1})` with `d = 0`.

Proof. With `x = h(z)`, `h ∈ O_F[X]`, and `s = h'(z)` (the image of `dx` in `Ω_{O_F[z]/O_{F'}}`):

* (kernel estimate, [BC, Ex. 13.7.4 (4)]) `f(h(X))` vanishes at `z`, so `G ∣ f ∘ h` in
  `O_F[X]`; differentiating, `a s = c k(z)`, so `‖a‖ ‖s‖ ≤ ‖c‖ ≤ ‖p‖ ‖b‖`;
* (cokernel estimate, [BC, Ex. 13.7.4 (5)]) by Euler's lemma (`AlmostEtale/Euler.lean`) applied
  to `z` and to `x` over `F'`, `e = a / b` satisfies `e, e z ∈ O_{F'}[x]`; writing
  `e = q₂(x)`, `e z = q₁(x)` and differentiating `q₁(h(X)) − X q₂(h(X))` (which vanishes at `z`,
  hence is divisible by `g`) gives `e ∈ s O + b O`, so `‖a‖ / ‖b‖ ≤ max(‖s‖, ‖b‖)`.
-/

noncomputable section

open Polynomial IntermediateField Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K̄" => PadicAlgCl p

theorem eval_mem_adjoin (F : IntermediateField ℚ_[p] (PadicAlgCl p)) {q : (PadicAlgCl p)[X]}
    (hq : ∀ n, q.coeff n ∈ F) (z : PadicAlgCl p) : q.eval z ∈ F⟮z⟯ := by
  rw [eval_eq_sum_range]
  refine sum_mem fun i _ => mul_mem ?_ (pow_mem (mem_adjoin_simple_self _ _) _)
  exact (F⟮z⟯).algebraMap_mem ⟨q.coeff i, hq i⟩

theorem mem_adjoin_of_mem_adj (F : IntermediateField ℚ_[p] (PadicAlgCl p)) {z u : PadicAlgCl p}
    (hu : u ∈ adj (OK F) z) : u ∈ F⟮z⟯ := by
  obtain ⟨q, hq, rfl⟩ := mem_adj.mp hu
  exact eval_mem_adjoin F (fun n => (mem_polyOver.mp hq n).1) z

theorem norm_eval_le_one {S : Subring (PadicAlgCl p)} (hS : S ≤ ballK p) {q : (PadicAlgCl p)[X]}
    (hq : q ∈ polyOver S) {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) : ‖q.eval x‖ ≤ 1 :=
  eval_mem (polyOver_mono hS hq) hx

/-- **Faltings' inductive step** ([BC, Exercise 13.7.4 (4)–(6)], `d = 0`). -/
theorem faltings_step {F F' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hFF' : F ≤ F')
    {x z : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hxz : x ∈ adj (OK F) z)
    (hzx : z ∈ F'⟮x⟯)
    (hT : ‖(derivative (mp F z)).eval z‖ ≤ ‖(p : PadicAlgCl p)‖ *
      ‖(derivative (mp F' z)).eval z‖) :
    ‖(derivative (mp F x)).eval x‖ ^ 2 ≤
      ‖(derivative (mp F' z)).eval z‖ ^ 2 *
        max ‖(derivative (mp F x)).eval x‖ ‖(p : PadicAlgCl p)‖ := by
  set a := (derivative (mp F x)).eval x with ha
  set b := (derivative (mp F' z)).eval z with hb
  set c := (derivative (mp F z)).eval z with hc
  have ha0 : a ≠ 0 := derivative_mp_ne_zero F x
  have hb0 : b ≠ 0 := derivative_mp_ne_zero F' z
  have hOK : OK F ≤ OK F' := OK_mono hFF'
  obtain ⟨h, hh, hhz⟩ := mem_adj.mp hxz
  have hh' : h ∈ polyOver (OK F') := polyOver_mono hOK hh
  set s := (derivative h).eval z with hs
  -- the fields `F'(x) = F'(z)` and their degrees
  have hxz' : x ∈ F'⟮z⟯ := mem_adjoin_of_mem_adj F' (adj_mono hOK z hxz)
  have hadj : F'⟮x⟯ = F'⟮z⟯ :=
    le_antisymm (adjoin_simple_le_iff.mpr hxz') (adjoin_simple_le_iff.mpr hzx)
  have hdg : dg F' x = dg F' z := by
    rw [← finrank_adjoin_eq_dg, ← finrank_adjoin_eq_dg, hadj]
  -- (1) kernel estimate: `‖a‖ ‖s‖ ≤ ‖c‖`
  have hker : ‖a‖ * ‖s‖ ≤ ‖c‖ := by
    have hP : (mp F x).comp h ∈ polyOver (OK F) := comp_mem_polyOver (mp_mem_polyOver F hx) hh
    have hPz : ((mp F x).comp h).eval z = 0 := by rw [eval_comp, hhz, eval_mp]
    obtain ⟨k, hk, hkeq⟩ := exists_eq_mp_mul F hz hP hPz
    have := congrArg (fun q => (derivative q).eval z) hkeq
    simp only [derivative_comp, derivative_mul, eval_mul, eval_add, eval_comp, hhz, eval_mp,
      zero_mul, add_zero] at this
    -- `s * a = c * k(z)`
    have hk1 : ‖k.eval z‖ ≤ 1 := norm_eval_le_one (OK_le_ballK F) hk hz
    have this' : a * s = c * k.eval z := by rw [ha, hs, hc, mul_comm]; exact this
    calc ‖a‖ * ‖s‖ = ‖c * k.eval z‖ := by rw [← norm_mul, this']
      _ ≤ ‖c‖ := by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hk1
  -- (2) `e z^k ∈ O_{F'}[x]` for `e = a / b`, `k = 0, 1`
  have hb_mem : b ∈ F'⟮x⟯ := by
    rw [hadj, hb]
    refine eval_mem_adjoin F' (fun n => ?_) z
    rw [coeff_derivative]
    exact mul_mem (coeff_mp_mem F' z _) (by exact_mod_cast IntermediateField.natCast_mem _ _)
  obtain ⟨f₂, hf₂, hf⟩ := exists_eq_mp_mul F' hx
    (polyOver_mono hOK (mp_mem_polyOver F hx)) (eval_mp F x)
  have ha_eq : a = (derivative (mp F' x)).eval x * f₂.eval x := by
    rw [ha, hf, derivative_mul, eval_add, eval_mul, eval_mul, eval_mp, zero_mul, add_zero]
  have hez : ∀ k : ℕ, k ≤ 1 → a / b * z ^ k ∈ adj (OK F') x := by
    intro k _
    set y := z ^ k / b with hy
    have hyF : y ∈ F'⟮x⟯ := div_mem (pow_mem hzx _) hb_mem
    have hy1 : y * (derivative (mp F' x)).eval x ∈ adj (OK F') x := by
      refine mul_derivative_mem_adj F' hx hyF fun i _ => ?_
      rw [hdg, show y * x ^ i = z ^ k * x ^ i / b by rw [hy]; ring]
      exact trace_div_derivative_mem F' hz
        (mul_mem (pow_mem (self_mem_adj _ _) _) (pow_mem (adj_mono hOK z hxz) _))
    have : a / b * z ^ k = y * (derivative (mp F' x)).eval x * f₂.eval x := by
      rw [hy, ha_eq]; field_simp
    rw [this]
    exact mul_mem hy1 (eval_mem_adj hf₂ x)
  -- (3) cokernel estimate: `‖a / b‖ ≤ max ‖s‖ ‖b‖`
  have hcok : ‖a / b‖ ≤ max ‖s‖ ‖b‖ := by
    obtain ⟨q₂, hq₂, hq₂x⟩ := mem_adj.mp (by simpa using hez 0 (by norm_num))
    obtain ⟨q₁, hq₁, hq₁x⟩ := mem_adj.mp (by simpa using hez 1 le_rfl)
    set r := q₁.comp h - X * q₂.comp h with hr
    have hrO : r ∈ polyOver (OK F') :=
      sub_mem (comp_mem_polyOver hq₁ hh') (mul_mem (X_mem_polyOver _) (comp_mem_polyOver hq₂ hh'))
    have hrz : r.eval z = 0 := by
      rw [hr, eval_sub, eval_mul, eval_X, eval_comp, eval_comp, hhz, hq₁x, hq₂x]; ring
    obtain ⟨k, hk, hkeq⟩ := exists_eq_mp_mul F' hz hrO hrz
    have hd := congrArg (fun q => (derivative q).eval z) hkeq
    simp only [hr, derivative_sub, derivative_mul, derivative_X, derivative_comp, eval_sub,
      eval_add, eval_mul, eval_X, eval_comp, hhz, hq₂x, eval_mp, zero_mul,
      add_zero, one_mul] at hd
    -- `e = s (q₁'(x) - z q₂'(x)) - b k(z)`
    have he : a / b = s * ((derivative q₁).eval x - z * (derivative q₂).eval x) -
        b * k.eval z := by
      rw [← hs, ← hb] at hd; linear_combination -hd
    have h1 : ‖(derivative q₁).eval x - z * (derivative q₂).eval x‖ ≤ 1 :=
      (norm_sub_le_max' _ _).trans (max_le
        (norm_eval_le_one (OK_le_ballK F') (derivative_mem_polyOver hq₁) hx)
        (by rw [norm_mul]; exact mul_le_one₀ hz (norm_nonneg _)
              (norm_eval_le_one (OK_le_ballK F') (derivative_mem_polyOver hq₂) hx)))
    have h2 : ‖k.eval z‖ ≤ 1 := norm_eval_le_one (OK_le_ballK F') hk hz
    rw [he]
    refine (norm_sub_le_max' _ _).trans (max_le_max ?_ ?_) <;>
      rw [norm_mul] <;> exact mul_le_of_le_one_right (norm_nonneg _) (by assumption)
  -- (4) combine
  have hA : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hB : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hS : 0 ≤ ‖s‖ := norm_nonneg _
  have hP : 0 ≤ ‖(p : PadicAlgCl p)‖ := norm_nonneg _
  rw [norm_div, div_le_iff₀ hB] at hcok
  have hker' : ‖a‖ * ‖s‖ ≤ ‖(p : PadicAlgCl p)‖ * ‖b‖ := hker.trans hT
  rcases le_total ‖b‖ ‖s‖ with hbs | hbs
  · rw [max_eq_left hbs] at hcok
    calc ‖a‖ ^ 2 ≤ ‖a‖ * (‖s‖ * ‖b‖) := by nlinarith
      _ = ‖b‖ * (‖a‖ * ‖s‖) := by ring
      _ ≤ ‖b‖ * (‖(p : PadicAlgCl p)‖ * ‖b‖) := mul_le_mul_of_nonneg_left hker' hB.le
      _ = ‖b‖ ^ 2 * ‖(p : PadicAlgCl p)‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  · rw [max_eq_right hbs] at hcok
    calc ‖a‖ ^ 2 ≤ ‖a‖ * (‖b‖ * ‖b‖) := by nlinarith
      _ = ‖b‖ ^ 2 * ‖a‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

end PadicHodge
