/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Points

/-!
# The multiplicative formal group law `Ĝ_m`

[Hong, Ex. 2.2.4]: `Φ(t, u) = t + u + tu = (1 + t)(1 + u) − 1` is a formal group law of
dimension `1` over every ring (`FGL.multiplicative`); on points of the open unit disc of `ℂ_p`
the group law is `x +_F y = x + y + xy` (`multiplicative_add_val`), i.e. `x ↦ 1 + x` is
multiplicative.
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace FGL

variable {R : Type*} [CommRing R]

theorem hasSubst_pairFam {τ : Type*} {d : ℕ} {f g : Fin d → MvPowerSeries τ R}
    (hf : ∀ j, constantCoeff (f j) = 0) (hg : ∀ j, constantCoeff (g j) = 0) :
    HasSubst (pairFam f g) :=
  hasSubst_of_constantCoeff_zero fun v => by
    unfold pairFam; split_ifs
    exacts [hf _, hg _]

variable (R) in
/-- `t + u + tu`. -/
def multΦ : MvPowerSeries (Fin 2 × Fin 1) R := X (0, 0) + X (1, 0) + X (0, 0) * X (1, 0)

theorem subst_multΦ {τ : Type*} {a : Fin 2 × Fin 1 → MvPowerSeries τ R} (ha : HasSubst a) :
    (multΦ R).subst a = a (0, 0) + a (1, 0) + a (0, 0) * a (1, 0) := by
  rw [multΦ, subst_add ha, subst_add ha, subst_mul ha, subst_X ha, subst_X ha]

theorem subst_multΦ_pairFam {τ : Type*} {f g : Fin 1 → MvPowerSeries τ R}
    (hf : ∀ j, constantCoeff (f j) = 0) (hg : ∀ j, constantCoeff (g j) = 0) :
    (multΦ R).subst (pairFam f g) = f 0 + g 0 + f 0 * g 0 := by
  rw [subst_multΦ (hasSubst_pairFam hf hg)]
  rfl

theorem constantCoeff_Xv' {n d : ℕ} (a : Fin n) (j : Fin d) :
    constantCoeff (Xv (R := R) a j) = 0 := constantCoeff_X _

variable (R) in
/-- **The multiplicative formal group law `Ĝ_m`** ([Hong, Ex. 2.2.4]). -/
def multiplicative : FGL R 1 where
  Φ _ := multΦ R
  constantCoeff_Φ _ := by simp [multΦ]
  assoc _ := by
    have e : ∀ a b : Fin 3, (multΦ R).subst (pairFam (Xv (R := R) a) (Xv b)) =
        Xv a 0 + Xv b 0 + Xv a 0 * Xv b 0 := fun a b =>
      subst_multΦ_pairFam (constantCoeff_Xv' a) (constantCoeff_Xv' b)
    simp only [e]
    rw [subst_multΦ_pairFam (fun _ => by simp [Xv]) (constantCoeff_Xv' 2),
      subst_multΦ_pairFam (constantCoeff_Xv' 0) (fun _ => by simp [Xv])]
    ring
  unit_right i := by
    rw [subst_multΦ_pairFam (fun j => constantCoeff_X j) (fun _ => by simp)]
    simp only [Pi.zero_apply, add_zero, mul_zero]
    rw [Subsingleton.elim i 0]
  unit_left i := by
    rw [subst_multΦ_pairFam (fun _ => by simp) (fun j => constantCoeff_X j)]
    simp only [Pi.zero_apply, zero_add, zero_mul, add_zero]
    rw [Subsingleton.elim i 0]
  comm _ := by
    rw [subst_multΦ_pairFam (constantCoeff_Xv' 1) (constantCoeff_Xv' 0), multΦ]
    simp only [Xv]
    ring

variable {p : ℕ} [hp : Fact p.Prime] [UniformSpace R] [DiscreteUniformity R]
  [Algebra R (OC p)]

/-- **The group law of `Ĝ_m` on points**: `x +_F y = x + y + xy`. -/
theorem multiplicative_add_val (x y : (multiplicative R).Pt p) :
    (x + y).1 0 = x.1 0 + y.1 0 + x.1 0 * y.1 0 := by
  rw [add_val]
  change eval₂ (algebraMap R (OC p)) _ (multΦ R) = _
  rw [← coe_eval₂Hom continuous_algebraMap_OC
    (hasEval_of_norm_lt_one (norm_pairPt_lt x.2 y.2)), multΦ, map_add, map_add, map_mul,
    coe_eval₂Hom, eval₂_X, eval₂_X]
  rfl

end FGL

end PadicHodge
