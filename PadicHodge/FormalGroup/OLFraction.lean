/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DAlphaHTOL
import PadicHodge.FormalGroup.OLCompact

/-!
# `L` is the fraction field of `O_L`

For a finite extension `L/ℚ_p` inside `ℚ̄_p`, `O_L → L` (`OL.toL`) is injective and every
`z ∈ L` is `x / p^n` with `x ∈ O_L` (`|p^n z| ≤ 1` for large `n`): `IsFractionRing (OL L) L`.
This lets the generic-fibre constructions over a fraction field (`GroupScheme/Closure.lean`)
be used over `O_{K'}`.
-/

noncomputable section

namespace PadicHodge

namespace OL

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem toL_injective : Function.Injective (toL : OL L →+* L) := fun x y h =>
  toOC_injective (Subtype.ext ((coeL_toLFun x).symm.trans
    ((congrArg coeL h).trans (coeL_toLFun y))))

theorem exists_mul_pow_mem (z : L) :
    ∃ (n : ℕ) (x : OL L), z * toL ((p : OL L) ^ n) = toL x := by
  set c : ℂ_[p] := coeL z with hc
  obtain ⟨n, hn⟩ : ∃ n : ℕ, FGL.np p ^ n * ‖c‖ ≤ 1 := by
    by_cases hc1 : ‖c‖ ≤ 1
    · exact ⟨0, by simpa using hc1⟩
    push Not at hc1
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (inv_pos.mpr (one_pos.trans hc1)) (FGL.np_lt_one (p := p))
    refine ⟨n, ?_⟩
    have := mul_lt_mul_of_pos_right hn (one_pos.trans hc1)
    rw [inv_mul_cancel₀ (one_pos.trans hc1).ne'] at this
    exact this.le
  have hw1 : ‖(p : ℂ_[p]) ^ n * c‖ ≤ 1 := by rw [norm_mul, norm_pow]; exact hn
  have hwL : (p : ℂ_[p]) ^ n * c ∈ cpSubmodule L := by
    refine mem_cpSubmodule.mpr ⟨(((p : L) ^ n * z : L) : PadicAlgCl p),
      ((p : L) ^ n * z).2, ?_⟩
    rw [hc]
    change algebraMap (PadicAlgCl p) ℂ_[p] (((p : L) ^ n * z : L) : PadicAlgCl p) = _
    simp [coeL]
  refine ⟨n, mk ⟨_, hw1⟩ hwL, coeL_injective ?_⟩
  rw [map_mul, map_pow, map_natCast, map_pow, map_natCast, mul_comm]
  change _ = coeL (toLFun (mk ⟨_, hw1⟩ hwL))
  rw [coeL_toLFun, toOC_mk]

instance : IsFractionRing (OL L) L where
  map_units y := by
    have hy : (y : OL L) ≠ 0 := nonZeroDivisors.ne_zero y.2
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ toL_injective).mpr hy)
  surj z := by
    obtain ⟨n, x, hx⟩ := exists_mul_pow_mem z
    refine ⟨⟨x, ⟨(p : OL L) ^ n, ?_⟩⟩, hx⟩
    refine mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ fun h => ?_)
    have := congrArg toL h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at this
    exact hp.out.ne_zero this
  exists_of_eq {x y} h := ⟨1, by rw [toL_injective h]⟩

end OL

end PadicHodge
