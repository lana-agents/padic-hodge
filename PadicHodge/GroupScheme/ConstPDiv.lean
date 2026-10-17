/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.ConstPDivMap
import PadicHodge.GroupScheme.Mu
import PadicHodge.GroupScheme.PDivisible

/-!
# The constant `p`-divisible group `ℚ_p/ℤ_p`

The constant `p`-divisible group `(ℚ_p/ℤ_p)_R` (a `p`-divisible group of height `1` in the
sense of [BC, Def. 7.2.1]; over a field, [BC, §7.2] identifies such groups with the Galois modules
`M_n`, here `ℤ/p^n` with trivial action) has layers `G_v = (ℤ/p^v)_R` (constant group schemes,
`CycP p v = Multiplicative (ZMod (p^v))`) and transition maps induced by the injection
`ℤ/p^v → ℤ/p^{v+1}`, `x ↦ p x` (`mulP`), whose image is the `p^v`-torsion (`mem_range_mulP_iff`).

* `constPDiv R p : PDivGroup R p`, of height `1`;
* the kernel condition `range_eq` holds for all `R`-algebras `S` (not only domains), via the
  description of points of constant groups by orthogonal idempotents
  (`GroupScheme/ConstPDivMap.lean`).
-/

noncomputable section

namespace PadicHodge

universe u

open FFGroupScheme

section Mul

variable (p : ℕ) [hp : Fact p.Prime]

/-- Multiplication by `p`, `ℤ/p^v → ℤ/p^{v+1}`. -/
def mulP (v : ℕ) : ZMod (p ^ v) →+ ZMod (p ^ (v + 1)) :=
  ZMod.lift (p ^ v) ⟨(AddMonoidHom.mulLeft (p : ZMod (p ^ (v + 1)))).comp
      (Int.castAddHom (ZMod (p ^ (v + 1)))), by
    change (p : ZMod (p ^ (v + 1))) * (((p ^ v : ℕ) : ℤ) : ZMod (p ^ (v + 1))) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, ← pow_succ', ZMod.natCast_self]⟩

variable {p}

theorem mulP_apply {v : ℕ} (x : ZMod (p ^ v)) :
    mulP p v x = ((p * x.val : ℕ) : ZMod (p ^ (v + 1))) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Int.cast_natCast]
  rw [mulP, ZMod.lift_coe]
  simp

theorem mulP_injective (v : ℕ) : Function.Injective (mulP p v) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [mulP_apply, ZMod.natCast_eq_zero_iff, pow_succ'] at hx
  have h := Nat.dvd_of_mul_dvd_mul_left hp.out.pos hx
  rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]
  exact h

/-- The image of `x ↦ p x` is the `p^v`-torsion of `ℤ/p^{v+1}`. -/
theorem mem_range_mulP_iff {v : ℕ} (y : ZMod (p ^ (v + 1))) :
    y ∈ Set.range (mulP p v) ↔ ((p ^ v : ℕ) : ZMod (p ^ (v + 1))) * y = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [mulP_apply, ← Nat.cast_mul, ← mul_assoc, ← pow_succ, ZMod.natCast_eq_zero_iff]
    exact Dvd.intro _ rfl
  · intro hy
    rw [← ZMod.natCast_zmod_val y, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hy
    have hy' : p ^ v * p ∣ p ^ v * y.val := by rw [← pow_succ]; exact hy
    obtain ⟨q, hq⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos v) hy'
    refine ⟨(q : ZMod (p ^ v)), ?_⟩
    rw [mulP_apply, ← ZMod.natCast_zmod_val y, hq, ZMod.val_natCast,
      ZMod.natCast_eq_natCast_iff', pow_succ', Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
      Nat.mod_mod]

/-- The transition map `ℤ/p^v → ℤ/p^{v+1}`, written multiplicatively. -/
def incP (v : ℕ) : CycP p v →* CycP p (v + 1) := AddMonoidHom.toMultiplicative (mulP p v)

theorem incP_injective (v : ℕ) : Function.Injective (incP (p := p) v) :=
  mulP_injective v

theorem mem_range_incP_iff {v : ℕ} (y : CycP p (v + 1)) :
    y ∈ Set.range (incP (p := p) v) ↔ y ^ (p ^ v) = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    have := (mem_range_mulP_iff (mulP p v (Multiplicative.toAdd x))).mp ⟨_, rfl⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
    exact this
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul] at h'
    obtain ⟨x, hx⟩ := (mem_range_mulP_iff (Multiplicative.toAdd y)).mpr h'
    exact ⟨Multiplicative.ofAdd x, Multiplicative.toAdd.injective hx⟩

end Mul

/-- **The constant `p`-divisible group `ℚ_p/ℤ_p`** over `R`: layers `(ℤ/p^v)_R`, height `1`. -/
def constPDiv (R : Type u) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime] :
    PDivGroup R p where
  height := 1
  G v := const R (CycP p v)
  order_eq v := by
    rw [order_const, one_mul]
    exact ZMod.card _
  incl v := constMap R (incP v)
  incl_surjective v := constMap_surjective (incP_injective v)
  range_eq v S _ _ y := by
    rw [exists_mapPoints_eq_iff (incP_injective v), FFGroupScheme.pow_eq_one_iff]
    refine forall_congr' fun m => ?_
    rw [mem_range_incP_iff]

end PadicHodge
