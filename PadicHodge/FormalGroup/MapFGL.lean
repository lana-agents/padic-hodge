/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Formal

/-!
# Base change of formal group laws

For a ring map `h : R → S` and a formal group law `F` over `R`, `F.map h` is the formal group
law over `S` with `Φ^h = h(Φ)` (coefficientwise). The axioms follow from
`MvPowerSeries.map_subst` (`map_addPS`: `h(Φ(f, g)) = Φ^h(h(f), h(g))`).
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace FGL

variable {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}

theorem map_pairFam {τ : Type*} (f g : Fin d → MvPowerSeries τ R) :
    (fun v => (pairFam f g v).map h) =
      pairFam (fun j => (f j).map h) (fun j => (g j).map h) := by
  funext v; unfold pairFam; split_ifs <;> rfl

theorem map_Xv {n : ℕ} (a : Fin n) :
    (fun j => (Xv (R := R) (d := d) a j).map h) = Xv (R := S) a := by
  funext j; simp [Xv]

theorem map_X_fam : (fun j => (X j : MvPowerSeries (Fin d) R).map h) = fun j => X j := by
  funext j; simp

theorem noConst_map {τ : Type*} {f : Fin d → MvPowerSeries τ R} (hf : NoConst f) :
    NoConst (fun j => (f j).map h) := fun j => by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hf j,
    map_zero]

/-- `h(Φ(f, g)) = Φ^h(h(f), h(g))`, as a statement about `Φ`-substitutions. -/
theorem map_subst_pairFam {τ : Type*} (Ψ : MvPowerSeries (Fin 2 × Fin d) R)
    {f g : Fin d → MvPowerSeries τ R} (hf : NoConst f) (hg : NoConst g) :
    (Ψ.subst (pairFam f g)).map h =
      (Ψ.map h).subst (pairFam (fun j => (f j).map h) (fun j => (g j).map h)) := by
  rw [MvPowerSeries.map_subst (hasSubst_pairFam hf hg), map_pairFam]

variable (F : FGL R d)

/-- **The base change `F^h` of a formal group law.** -/
def map : FGL S d where
  Φ i := (F.Φ i).map h
  constantCoeff_Φ i := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      F.constantCoeff_Φ, map_zero]
  assoc i := by
    have e := congrArg (MvPowerSeries.map h) (F.assoc i)
    have h01 : NoConst fun j => (F.Φ j).subst (pairFam (Xv (R := R) (d := d) (n := 3) 0) (Xv 1)) :=
      F.noConst_addPS (noConst_Xv 0) (noConst_Xv 1)
    have h12 : NoConst fun j => (F.Φ j).subst (pairFam (Xv (R := R) (d := d) (n := 3) 1) (Xv 2)) :=
      F.noConst_addPS (noConst_Xv 1) (noConst_Xv 2)
    rw [map_subst_pairFam h _ h01 (noConst_Xv 2), map_subst_pairFam h _ (noConst_Xv 0) h12] at e
    have e1 : (fun j => ((F.Φ j).subst (pairFam (Xv (R := R) (n := 3) 0) (Xv 1))).map h) =
        fun j => ((F.Φ j).map h).subst (pairFam (Xv (R := S) (n := 3) 0) (Xv 1)) := by
      funext j
      rw [map_subst_pairFam h _ (noConst_Xv 0) (noConst_Xv 1), map_Xv, map_Xv]
    have e2 : (fun j => ((F.Φ j).subst (pairFam (Xv (R := R) (n := 3) 1) (Xv 2))).map h) =
        fun j => ((F.Φ j).map h).subst (pairFam (Xv (R := S) (n := 3) 1) (Xv 2)) := by
      funext j
      rw [map_subst_pairFam h _ (noConst_Xv 1) (noConst_Xv 2), map_Xv, map_Xv]
    rw [map_Xv, map_Xv, e1, e2] at e
    exact e
  unit_right i := by
    have e := congrArg (MvPowerSeries.map h) (F.unit_right i)
    rw [map_subst_pairFam h _ noConst_X noConst_zero, map_X_fam, map_X] at e
    rw [← e]
    congr 2
    funext j
    simp
  unit_left i := by
    have e := congrArg (MvPowerSeries.map h) (F.unit_left i)
    rw [map_subst_pairFam h _ noConst_zero noConst_X, map_X_fam, map_X] at e
    rw [← e]
    congr 2
    funext j
    simp
  comm i := by
    have e := congrArg (MvPowerSeries.map h) (F.comm i)
    rw [map_subst_pairFam h _ (noConst_Xv 1) (noConst_Xv 0), map_Xv, map_Xv] at e
    exact e

theorem map_Φ (i : Fin d) : (F.map h).Φ i = (F.Φ i).map h := rfl

end FGL

end PadicHodge
