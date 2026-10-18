/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Mult

/-!
# Formal identities: `[m + n]_F = Φ([m]_F, [n]_F)` and `[m]_F ∘ [n]_F = [mn]_F`

For a formal group law `F` of dimension `d` over a commutative ring `R` and families
`f, g : Fin d → R[[τ]]` without constant terms, `addPS F f g = Φ(f, g)`. The axioms of `F` give
the identities of families (`addPS_assoc`, `addPS_comm`, `addPS_zero`, `zero_addPS`;
substituting into the axioms, `MvPowerSeries.subst_comp_subst_apply`), substitution is
compatible with `addPS` (`subst_addPS`), and for `[n]_F` (`mulPS`, [Hong, Ex. 2.2.8]):

* `mulPS_add`: `[m + n]_F(T) = Φ([m]_F(T), [n]_F(T))`;
* `subst_mulPS`: `[m]_F([n]_F(T)) = [mn]_F(T)`; in particular `[p^{v+1}] = [p] ∘ [p^v]`
  (`mulPS_pow_succ`).
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace FGL

variable {R : Type*} [CommRing R] {d : ℕ} (F : FGL R d)

/-- `Φ(f, g)` for families of power series. -/
def addPS {τ : Type*} (f g : Fin d → MvPowerSeries τ R) : Fin d → MvPowerSeries τ R :=
  fun i => (F.Φ i).subst (pairFam f g)

/-- Families without constant term. -/
def NoConst {τ : Type*} (f : Fin d → MvPowerSeries τ R) : Prop := ∀ j, constantCoeff (f j) = 0

theorem noConst_X : NoConst (R := R) (d := d) (fun j => X j) := fun j => constantCoeff_X j

theorem noConst_zero {τ : Type*} : NoConst (0 : Fin d → MvPowerSeries τ R) := fun j => by simp

theorem noConst_addPS {τ : Type*} {f g : Fin d → MvPowerSeries τ R} (hf : NoConst f)
    (hg : NoConst g) : NoConst (F.addPS f g) := fun i =>
  constantCoeff_subst_eq_zero (hasSubst_pairFam hf hg)
    (fun v => by unfold pairFam; split_ifs; exacts [hf _, hg _]) (F.constantCoeff_Φ i)

theorem hasSubst_of_noConst {τ : Type*} {f : Fin d → MvPowerSeries τ R} (hf : NoConst f) :
    HasSubst f := hasSubst_of_constantCoeff_zero hf

theorem subst_zero' {σ τ : Type*} {h : σ → MvPowerSeries τ R} (hh : HasSubst h) :
    (0 : MvPowerSeries σ R).subst h = 0 := by
  rw [← coe_substAlgHom hh, map_zero]

theorem pairFam_subst {σ τ : Type*} {f g : Fin d → MvPowerSeries σ R}
    (h : σ → MvPowerSeries τ R) :
    (fun v => (pairFam f g v).subst h) =
      pairFam (fun j => (f j).subst h) (fun j => (g j).subst h) := by
  funext v
  unfold pairFam
  split_ifs <;> rfl

/-- **Substitution is compatible with `Φ`.** -/
theorem subst_addPS {σ τ : Type*} [Finite σ] {f g : Fin d → MvPowerSeries σ R} (hf : NoConst f)
    (hg : NoConst g) {h : σ → MvPowerSeries τ R} (hh : HasSubst h) (i : Fin d) :
    (F.addPS f g i).subst h = F.addPS (fun j => (f j).subst h) (fun j => (g j).subst h) i := by
  rw [addPS, subst_comp_subst_apply (hasSubst_pairFam hf hg) hh, pairFam_subst]
  rfl

/-- The family `(T, U, V) ↦ (f, g, k)` on `Fin 3 × Fin d`. -/
def tripleFam {τ : Type*} (f g k : Fin d → MvPowerSeries τ R) :
    Fin 3 × Fin d → MvPowerSeries τ R :=
  fun v => if v.1 = 0 then f v.2 else if v.1 = 1 then g v.2 else k v.2

theorem hasSubst_tripleFam {τ : Type*} {f g k : Fin d → MvPowerSeries τ R} (hf : NoConst f)
    (hg : NoConst g) (hk : NoConst k) : HasSubst (tripleFam f g k) :=
  hasSubst_of_constantCoeff_zero fun v => by
    unfold tripleFam; split_ifs
    exacts [hf _, hg _, hk _]

theorem noConst_Xv {n : ℕ} (a : Fin n) : NoConst (Xv (R := R) (d := d) a) :=
  fun _ => constantCoeff_X _

/-- **Associativity for families**: `Φ(Φ(f, g), k) = Φ(f, Φ(g, k))`. -/
theorem addPS_assoc {τ : Type*} {f g k : Fin d → MvPowerSeries τ R} (hf : NoConst f)
    (hg : NoConst g) (hk : NoConst k) :
    F.addPS (F.addPS f g) k = F.addPS f (F.addPS g k) := by
  funext i
  have hb := hasSubst_tripleFam hf hg hk
  have h := congrArg (fun φ => φ.subst (tripleFam f g k)) (F.assoc i)
  beta_reduce at h
  have hX : ∀ (a : Fin 3) (j : Fin d),
      (Xv (R := R) (n := 3) a j).subst (tripleFam f g k) = tripleFam f g k (a, j) :=
    fun a j => subst_X hb _
  have e1 : (F.Φ i).subst (pairFam (fun j => (F.Φ j).subst (pairFam (Xv (R := R) (n := 3) 0)
      (Xv 1))) (Xv 2)) = F.addPS (F.addPS (Xv 0) (Xv 1)) (Xv 2) i := rfl
  have e2 : (F.Φ i).subst (pairFam (Xv (R := R) (n := 3) 0)
      (fun j => (F.Φ j).subst (pairFam (Xv (R := R) (n := 3) 1) (Xv 2)))) =
      F.addPS (Xv 0) (F.addPS (Xv 1) (Xv 2)) i := rfl
  rw [e1, e2, F.subst_addPS (F.noConst_addPS (noConst_Xv 0) (noConst_Xv 1)) (noConst_Xv 2) hb,
    F.subst_addPS (noConst_Xv 0) (F.noConst_addPS (noConst_Xv 1) (noConst_Xv 2)) hb] at h
  have e3 : (fun j => (F.addPS (Xv (R := R) (n := 3) 0) (Xv 1) j).subst (tripleFam f g k)) =
      F.addPS f g := by
    funext j
    rw [F.subst_addPS (noConst_Xv 0) (noConst_Xv 1) hb]
    simp only [hX]
    rfl
  have e4 : (fun j => (F.addPS (Xv (R := R) (n := 3) 1) (Xv 2) j).subst (tripleFam f g k)) =
      F.addPS g k := by
    funext j
    rw [F.subst_addPS (noConst_Xv 1) (noConst_Xv 2) hb]
    simp only [hX]
    rfl
  rw [e3, e4] at h
  simp only [hX] at h
  exact h

/-- **Commutativity for families.** -/
theorem addPS_comm {τ : Type*} {f g : Fin d → MvPowerSeries τ R} (hf : NoConst f)
    (hg : NoConst g) : F.addPS f g = F.addPS g f := by
  funext i
  have hb := hasSubst_pairFam hf hg
  have h := congrArg (fun φ => φ.subst (pairFam f g)) (F.comm i)
  beta_reduce at h
  have e : (F.Φ i).subst (pairFam (Xv (R := R) (n := 2) 1) (Xv 0)) =
      F.addPS (Xv 1) (Xv 0) i := rfl
  rw [e, F.subst_addPS (noConst_Xv 1) (noConst_Xv 0) hb] at h
  have hX : ∀ (a : Fin 2) (j : Fin d), (Xv (R := R) (n := 2) a j).subst (pairFam f g) =
      pairFam f g (a, j) := fun a j => subst_X hb _
  simp only [hX] at h
  exact h.symm

/-- **Unit for families**: `Φ(f, 0) = f`. -/
theorem addPS_zero {τ : Type*} {f : Fin d → MvPowerSeries τ R} (hf : NoConst f) :
    F.addPS f 0 = f := by
  funext i
  have hb := hasSubst_of_noConst hf
  have h := congrArg (fun φ => φ.subst f) (F.unit_right i)
  beta_reduce at h
  rw [subst_X hb] at h
  rw [← h, addPS, subst_comp_subst_apply (hasSubst_pairFam (noConst_X) noConst_zero) hb,
    pairFam_subst]
  congr 2
  · funext j; exact (subst_X hb j).symm
  · funext j; exact (subst_zero' hb).symm

theorem zero_addPS {τ : Type*} {f : Fin d → MvPowerSeries τ R} (hf : NoConst f) :
    F.addPS 0 f = f := by
  rw [F.addPS_comm noConst_zero hf, F.addPS_zero hf]

/-- **`[n]_F(T)`** ([Hong, Ex. 2.2.8]): `[0] = 0`, `[n + 1](T) = Φ([n](T), T)`. -/
def mulPS : ℕ → Fin d → MvPowerSeries (Fin d) R
  | 0 => 0
  | n + 1 => F.addPS (mulPS n) fun j => X j

theorem mulPS_zero : F.mulPS 0 = 0 := rfl

theorem mulPS_succ (n : ℕ) : F.mulPS (n + 1) = F.addPS (F.mulPS n) fun j => X j := rfl

theorem noConst_mulPS (n : ℕ) : NoConst (F.mulPS n) := by
  induction n with
  | zero => exact noConst_zero
  | succ n ih => exact F.noConst_addPS ih noConst_X

theorem constantCoeff_mulPS (n : ℕ) (i : Fin d) : constantCoeff (F.mulPS n i) = 0 :=
  F.noConst_mulPS n i

theorem mulPS_one : F.mulPS 1 = fun j => X j := by
  rw [mulPS_succ, mulPS_zero, F.zero_addPS noConst_X]

/-- **`[m + n]_F = Φ([m]_F, [n]_F)`.** -/
theorem mulPS_add (m n : ℕ) : F.mulPS (m + n) = F.addPS (F.mulPS m) (F.mulPS n) := by
  induction n with
  | zero => rw [add_zero, mulPS_zero, F.addPS_zero (F.noConst_mulPS m)]
  | succ n ih =>
    rw [← add_assoc, mulPS_succ, ih, mulPS_succ,
      F.addPS_assoc (F.noConst_mulPS m) (F.noConst_mulPS n) noConst_X]

/-- **`[m]_F([n]_F(T)) = [mn]_F(T)`.** -/
theorem subst_mulPS (m n : ℕ) (i : Fin d) :
    (F.mulPS m i).subst (F.mulPS n) = F.mulPS (m * n) i := by
  have hb := hasSubst_of_noConst (F.noConst_mulPS n)
  induction m generalizing i with
  | zero =>
    simp only [mulPS_zero, Nat.zero_mul, Pi.zero_apply]
    exact subst_zero' hb
  | succ m ih =>
    rw [mulPS_succ, F.subst_addPS (F.noConst_mulPS m) noConst_X hb, Nat.succ_mul,
      F.mulPS_add]
    congr 1
    · funext j; exact ih j
    · funext j; exact subst_X hb j

theorem mulPS_pow_succ (p v : ℕ) (i : Fin d) :
    F.mulPS (p ^ (v + 1)) i = (F.mulPS p i).subst (F.mulPS (p ^ v)) := by
  rw [subst_mulPS, pow_succ, mul_comm]

end FGL

end PadicHodge
