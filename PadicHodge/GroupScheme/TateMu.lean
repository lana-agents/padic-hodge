/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Mu
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The Tate module of `μ_{p^∞}`

* `muPointsEquiv`: `μ_{p^v}(S) ≃* μ_{p^v}(S)ᵘ = rootsOfUnity (p^v) S` (a character of `ℤ/p^v` is
  determined by its value at `1`);
* `tateMuEquiv`: `T_p μ_{p^∞}(S) ≃* RootSys p S`, the group of compatible systems `(ζ_v)` of
  `p^v`-th roots of unity in `S` with `ζ_{v+1}^p = ζ_v`.

The identification `RootSys p L ≃ ℤ_p(1)` for a field `L` with all `p`-power roots of unity is in
`GroupScheme/TateMuZp.lean`.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv

namespace PadicHodge

universe u

open FFGroupScheme

variable (p : ℕ) [hp : Fact p.Prime]

/-- The generator `1` of `ℤ/p^v`. -/
abbrev genP (v : ℕ) : CycP p v := Multiplicative.ofAdd 1

theorem eq_genP_pow {v : ℕ} (a : CycP p v) : a = genP p v ^ (Multiplicative.toAdd a).val := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

omit hp in
theorem genP_pow_card (v : ℕ) : genP p v ^ (p ^ v) = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, ZMod.natCast_self]; rfl

omit hp in
theorem redP_genP (v : ℕ) : redP p v (genP p (v + 1)) = genP p v := by
  apply Multiplicative.toAdd.injective
  change (ZMod.cast (1 : ZMod (p ^ (v + 1))) : ZMod (p ^ v)) = 1
  rw [ZMod.cast_one (pow_dvd_pow p (Nat.le_succ v))]

theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hx : x ^ n = 1) (k : ℕ) :
    x ^ (k % n) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, hx, one_pow, mul_one]

variable (S : Type u) [CommRing S]

/-- Characters of `ℤ/p^v` with values in `S` are `p^v`-th roots of unity. -/
def charEquivRoots (v : ℕ) : (CycP p v →* S) ≃* rootsOfUnity (p ^ v) S where
  toFun ψ := ⟨Units.ofPowEqOne (ψ (genP p v)) (p ^ v)
      (by rw [← map_pow, genP_pow_card, map_one]) (NeZero.ne _), by
    rw [mem_rootsOfUnity]; ext; simp⟩
  invFun ζ :=
    { toFun := fun a => ((ζ : Sˣ) : S) ^ (Multiplicative.toAdd a).val
      map_one' := by simp
      map_mul' := fun a b => by
        have hζ : ((ζ : Sˣ) : S) ^ (p ^ v) = 1 := by
          rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ζ.2, Units.val_one]
        rw [toAdd_mul, ZMod.val_add, pow_mod_of_pow_eq_one hζ, pow_add] }
  left_inv ψ := by
    refine MonoidHom.ext fun a => ?_
    change ψ (genP p v) ^ (Multiplicative.toAdd a).val = ψ a
    conv_rhs => rw [eq_genP_pow p a]
    rw [map_pow]
  right_inv ζ := by
    apply Subtype.ext; apply Units.ext
    change ((ζ : Sˣ) : S) ^ (Multiplicative.toAdd (genP p v)).val = ((ζ : Sˣ) : S)
    have hζ : ((ζ : Sˣ) : S) ^ (p ^ v) = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp ζ.2, Units.val_one]
    rw [toAdd_ofAdd, ZMod.val_one_eq_one_mod, pow_mod_of_pow_eq_one hζ, pow_one]
  map_mul' ψ φ := by
    apply Subtype.ext; apply Units.ext
    rfl

theorem charEquivRoots_apply (v : ℕ) (ψ : CycP p v →* S) :
    (((charEquivRoots p S v ψ : rootsOfUnity (p ^ v) S) : Sˣ) : S) = ψ (genP p v) := rfl

variable (R : Type u) [CommRing R] [Algebra R S]

/-- `μ_{p^v}(S) ≃* rootsOfUnity (p^v) S`. -/
def muPointsEquiv (v : ℕ) : (muP R p v).points S ≃* rootsOfUnity (p ^ v) S :=
  (diagPointsEquiv (R := R) (CycP p v) S).trans (charEquivRoots p S v)

theorem muPointsEquiv_muIncl (v : ℕ) (x : (muP R p v).points S) :
    muPointsEquiv p S R (v + 1) ((muIncl R p v).mapPoints S x) =
      ⟨(muPointsEquiv p S R v x : Sˣ), by
        rw [mem_rootsOfUnity, pow_succ, pow_mul, (mem_rootsOfUnity _ _).mp
          (muPointsEquiv p S R v x).2, one_pow]⟩ := by
  apply Subtype.ext; apply Units.ext
  change (diagPointsEquiv (CycP p (v + 1)) S ((muIncl R p v).mapPoints S x)) (genP p (v + 1)) =
    (diagPointsEquiv (CycP p v) S x) (genP p v)
  rw [diagPointsEquiv_muIncl, MonoidHom.comp_apply, redP_genP]

/-- Compatible systems `(ζ_v)` of `p^v`-th roots of unity with `ζ_{v+1}^p = ζ_v`. -/
def RootSys : Subgroup ((v : ℕ) → rootsOfUnity (p ^ v) S) where
  carrier := {ζ | ∀ v, ((ζ v : rootsOfUnity (p ^ v) S) : Sˣ) = ((ζ (v + 1) : Sˣ)) ^ p}
  mul_mem' := fun {x y} hx hy v => by
    simp only [Pi.mul_apply, Subgroup.coe_mul, hx v, hy v, mul_pow]
  one_mem' := fun v => by simp
  inv_mem' := fun {x} hx v => by
    simp only [Pi.inv_apply, Subgroup.coe_inv, hx v, inv_pow]

variable [Nontrivial R]

theorem mem_tateModule_iff (x : (v : ℕ) → (muP R p v).points S) :
    x ∈ (muPDiv R p).TateModule S ↔
      (fun v => muPointsEquiv p S R v (x v)) ∈ RootSys p S := by
  change (∀ v, (muIncl R p v).mapPoints S (x v) = (x (v + 1)) ^ p) ↔
    ∀ v, ((muPointsEquiv p S R v (x v) : rootsOfUnity (p ^ v) S) : Sˣ) =
      ((muPointsEquiv p S R (v + 1) (x (v + 1)) : Sˣ)) ^ p
  refine forall_congr' fun v => ?_
  rw [← (muPointsEquiv p S R (v + 1)).injective.eq_iff, muPointsEquiv_muIncl, map_pow]
  constructor
  · intro h
    have := congrArg (fun ζ : rootsOfUnity (p ^ (v + 1)) S => (ζ : Sˣ)) h
    simpa using this
  · intro h
    apply Subtype.ext
    simpa using h

/-- **`T_p μ_{p^∞}(S)` is the group of compatible systems of `p`-power roots of unity.** -/
def tateMuEquiv : (muPDiv R p).TateModule S ≃* RootSys p S where
  toFun x := ⟨fun v => muPointsEquiv p S R v (x.1 v),
    (mem_tateModule_iff p S R _).mp x.2⟩
  invFun ζ := ⟨fun v => (muPointsEquiv p S R v).symm ((ζ : (v : ℕ) → rootsOfUnity (p ^ v) S) v),
    (mem_tateModule_iff p S R _).mpr (by simp [ζ.2])⟩
  left_inv x := by ext1; funext v; simp
  right_inv ζ := by ext1; funext v; simp
  map_mul' x y := by
    ext1; funext v
    exact map_mul (muPointsEquiv p S R v) (x.1 v) (y.1 v)

theorem tateMuEquiv_apply (x : (muPDiv R p).TateModule S) (v : ℕ) :
    ((tateMuEquiv p S R x : (v : ℕ) → rootsOfUnity (p ^ v) S) v) =
      muPointsEquiv p S R v (x.1 v) := rfl

end PadicHodge
