/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cohomology.Kummer
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The `ℤ_p`-module structure on `T_p M`

For an abelian group `M` and a prime `p`, `T_p M = lim M[p^n]` is a `ℤ_p`-module:
`c · (x_n) = (c mod p^n · x_n)` (`Kummer.Tp.instModule`), the scalar action is continuous in the
second variable (`ContinuousConstSMul`), and the Galois action `tpRep` is `ℤ_p`-linear
(`Kummer.tpRepZp`). Hence `H¹_cont(Γ, T_p M)` is a `ℤ_p`-module
(`ContH1.H1 (Kummer.tpRepZp p ρ)`), and the `ℤ`-linear Kummer map lands in it
(`Kummer.toH1Zp`: the identity on cocycles).
-/

noncomputable section

namespace PadicHodge

namespace Kummer

variable {M : Type*} [AddCommGroup M] {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem pow_smul_val (x : Tp M p) (n : ℕ) : p ^ n • val M p x n = 0 := by
  induction n with
  | zero => rw [pow_zero, one_smul, val_zero]
  | succ n ih => rw [pow_succ, mul_smul, val_succ, ih]

omit hp in
/-- `a · y = b · y` for `a ≡ b mod p^n` when `p^n y = 0`. -/
theorem nsmul_eq_of_cast_eq {y : M} {n a b : ℕ} (hy : p ^ n • y = 0)
    (h : (a : ZMod (p ^ n)) = b) : a • y = b • y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.div_add_mod a (p ^ n), ← Nat.div_add_mod b (p ^ n), add_smul, add_smul, mul_comm,
    mul_smul, hy, smul_zero, mul_comm, mul_smul, hy, smul_zero, h]

/-- `c mod p^n` as a natural number. -/
abbrev cmod (c : ℤ_[p]) (n : ℕ) : ℕ := (PadicInt.toZModPow n c).val

theorem cast_cmod (c : ℤ_[p]) (n : ℕ) :
    ((cmod c n : ℕ) : ZMod (p ^ n)) = PadicInt.toZModPow n c := ZMod.natCast_zmod_val _

theorem cast_cmod_succ (c : ℤ_[p]) (n : ℕ) :
    ((cmod c (n + 1) : ℕ) : ZMod (p ^ n)) = PadicInt.toZModPow n c := by
  rw [cmod, ZMod.natCast_val, ← PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ]
  rfl

theorem cmod_smul_val (c : ℤ_[p]) {x : Tp M p} {n a : ℕ}
    (h : (a : ZMod (p ^ n)) = PadicInt.toZModPow n c) :
    a • val M p x n = cmod c n • val M p x n :=
  nsmul_eq_of_cast_eq (pow_smul_val x n) (by rw [h, cast_cmod])

/-- The scalar action of `ℤ_p` on `T_p M`. -/
def zpSmul (c : ℤ_[p]) (x : Tp M p) : Tp M p :=
  mk (fun n => cmod c n • val M p x n) ⟨by simp only [val_zero, smul_zero], fun n => by
    simp only
    rw [smul_comm, val_succ]
    exact nsmul_eq_of_cast_eq (pow_smul_val x n) (by rw [cast_cmod_succ, cast_cmod])⟩

@[simp] theorem val_zpSmul (c : ℤ_[p]) (x : Tp M p) (n : ℕ) :
    val M p (zpSmul c x) n = cmod c n • val M p x n := rfl

instance instModule : Module ℤ_[p] (Tp M p) where
  smul := zpSmul
  one_smul x := ext fun n => by
    change cmod 1 n • val M p x n = val M p x n
    conv_rhs => rw [← one_smul ℕ (val M p x n)]
    exact (cmod_smul_val 1 (by rw [map_one, Nat.cast_one])).symm
  mul_smul c d x := ext fun n => by
    change cmod (c * d) n • val M p x n = cmod c n • (cmod d n • val M p x n)
    rw [← mul_smul]
    exact (cmod_smul_val (c * d) (by rw [Nat.cast_mul, cast_cmod, cast_cmod, map_mul])).symm
  smul_zero c := ext fun n => by
    change cmod c n • val M p 0 n = val M p 0 n
    rw [map_zero, Pi.zero_apply, smul_zero]
  smul_add c x y := ext fun n => by
    change cmod c n • val M p (x + y) n = val M p (zpSmul c x + zpSmul c y) n
    simp [map_add, smul_add]
  add_smul c d x := ext fun n => by
    change cmod (c + d) n • val M p x n = val M p (zpSmul c x + zpSmul d x) n
    rw [map_add, Pi.add_apply, val_zpSmul, val_zpSmul, ← add_smul]
    exact (cmod_smul_val (c + d) (by rw [Nat.cast_add, cast_cmod, cast_cmod, map_add])).symm
  zero_smul x := ext fun n => by
    change cmod 0 n • val M p x n = val M p 0 n
    rw [map_zero, Pi.zero_apply, ← zero_smul ℕ (val M p x n)]
    exact (cmod_smul_val 0 (by rw [map_zero, Nat.cast_zero])).symm

@[simp] theorem val_smul (c : ℤ_[p]) (x : Tp M p) (n : ℕ) :
    val M p (c • x) n = cmod c n • val M p x n := rfl

instance : ContinuousConstSMul ℤ_[p] (Tp M p) := by
  refine ⟨fun c => continuous_of_isOpen fun n m => ?_⟩
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  exact ⟨_, fun y (hy : val M p y n = val M p x n) => by
    change cmod c n • val M p y n = m
    rw [hy]
    exact hx, isOpen_val_eq, rfl⟩

theorem map_smul_zp {N : Type*} [AddCommGroup N] (f : M →+ N) (c : ℤ_[p]) (x : Tp M p) :
    map f (c • x) = c • map f x :=
  ext fun n => by simp [map_nsmul]

section Rep

variable {Γ : Type*} [Group Γ] (ρ : Representation ℤ Γ M) (p)

/-- The Galois action on `T_p M` as a `ℤ_p`-representation. -/
def tpRepZp : Representation ℤ_[p] Γ (Tp M p) where
  toFun σ :=
    { toFun := tpRep ρ p σ
      map_add' := map_add _
      map_smul' := fun c x => map_smul_zp (ρ σ).toAddMonoidHom c x }
  map_one' := LinearMap.ext fun x => by simp
  map_mul' σ τ := LinearMap.ext fun x => by simp

@[simp] theorem tpRepZp_apply (σ : Γ) (x : Tp M p) : tpRepZp p ρ σ x = tpRep ρ p σ x := rfl

variable [TopologicalSpace Γ]

/-- Cocycles with values in `T_p M` are the same over `ℤ` and over `ℤ_p`. -/
def cocyclesToZp : ContH1.cocycles (tpRep ρ p) →ₗ[ℤ] ContH1.cocycles (tpRepZp p ρ) where
  toFun f := ⟨f.1, f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := Subtype.ext rfl

/-- `H¹(Γ, T_p M)` over `ℤ` maps to `H¹(Γ, T_p M)` over `ℤ_p` (the identity on cocycles). -/
def toH1Zp : ContH1.H1 (tpRep ρ p) →+ ContH1.H1 (tpRepZp p ρ) :=
  ((ContH1.coboundaries (tpRep ρ p)).liftQ
    ((ContH1.mk (tpRepZp p ρ)).toAddMonoidHom.toIntLinearMap ∘ₗ cocyclesToZp p ρ)
    fun x hx => by
      obtain ⟨m, hm⟩ := hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
        LinearMap.toAddMonoidHom_coe, ContH1.mk_eq_zero_iff]
      exact ⟨m, hm⟩).toAddMonoidHom

theorem toH1Zp_mk (f : ContH1.cocycles (tpRep ρ p)) :
    toH1Zp p ρ (ContH1.mk (tpRep ρ p) f) = ContH1.mk (tpRepZp p ρ) (cocyclesToZp p ρ f) :=
  rfl

end Rep

end Kummer

end PadicHodge
