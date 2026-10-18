/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Alpha
import PadicHodge.FormalGroup.MapFGL
import PadicHodge.FormalGroup.LogNat

/-!
# `dα` and the right square of [Hong, Prop. 3.4.9]

Continuing `Alpha.lean`: for `y ∈ T_p(G^∨)(O_{ℂ_p})` the power series `U_y − 1` is a homomorphism
of formal group laws `u_y : F_{O_C} → Ĝ_m` (`charHom`; `F_{O_C} = F.map (R → O_C)`, `FS`), which is
(3.7) of [Hong, Prop. 3.4.9, proof]. Its differential `du_y = (∂U_y/∂T_j(0))_j` defines

* **`dα(z)(y) = ∑_j ∂U_y/∂T_j(0) · z_j`** for `z ∈ t_G(ℂ_p) = ℂ_p^d` (`dalpha`), `ℂ_p`-linear in
  `z` and additive in `y` (`dalpha_mul`);
* **the right square**: `log_{Ĝ_m}(α(x)(y) − 1) = dα(log_F x)(y)` (`logGm_alpha`), from the
  naturality of the logarithm (`FGL.Hom.logF_ptMap`).
-/

noncomputable section

open MvPowerSeries IsLocalRing TensorProduct WithConv

namespace PadicHodge

open FGL

namespace PDivFGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (P : PDivFGL R d p)

local notation "S" => OCd p

/-- The base change `F_{O_{ℂ_p}}`. -/
abbrev FS : FGL S d := P.F.map (algebraMap R S)

/-- `F(m_{ℂ_p}) = F_{O_C}(m_{ℂ_p})`. -/
def toPtS (x : P.F.Pt p) : P.FS.Pt p := ⟨x.1, x.2⟩

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] in
theorem toPtS_add (x y : P.F.Pt p) : P.toPtS (x + y) = P.toPtS x + P.toPtS y := by
  apply FGL.pt_ext
  intro j
  rw [FGL.add_val]
  change (x + y).1 j = FGL.ev p ((P.F.Φ j).map (algebraMap R S)) (pairPt x.1 y.1)
  rw [FGL.ev_map (algebraMap R S) (fun _ => rfl) (norm_pairPt_lt x.2 y.2), FGL.add_val]

/-- `F(m_{ℂ_p}) → F_{O_C}(m_{ℂ_p})` as an additive map. -/
def toPtSHom : P.F.Pt p →+ P.FS.Pt p := AddMonoidHom.mk' P.toPtS P.toPtS_add

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] in
theorem logF_toPtS (x : P.F.Pt p) (i : Fin d) : P.FS.logF (P.toPtS x) i = P.F.logF x i := by
  have h : P.FS.logSeq (P.toPtS x) i = P.F.logSeq x i := by
    funext n
    rw [FGL.logSeq, FGL.logSeq]
    have e : (p ^ n) • P.toPtS x = P.toPtS ((p ^ n) • x) := (map_nsmul P.toPtSHom _ _).symm
    rw [e]
    rfl
  rw [FGL.logF, FGL.logF, h]

variable [hC : IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R)

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] hp in
theorem pairFam_Xv_eq_X {T : Type*} [CommRing T] :
    pairFam (Xv (R := T) (d := d) (n := 2) 0) (Xv 1) = fun v => X v := by
  funext ⟨a, j⟩
  fin_cases a <;> rfl

/-- **`u_y = U_y − 1 : F_{O_C} → Ĝ_m`** ([Hong, Prop. 3.4.9, proof, (3.7)]). -/
def charHom (y : P.pdivGroup.DualTate S) : FGL.Hom P.FS (FGL.multiplicative S) where
  f _ := P.charSeries hpm y - 1
  noConst _ := by rw [map_sub, constantCoeff_charSeries, map_one, sub_self]
  map_add _ := by
    set U := P.charSeries hpm y
    have hΦ : P.FS.addPS (Xv (R := S) (n := 2) 0) (Xv 1) =
        fun j => (P.F.Φ j).map (algebraMap R S) := by
      funext j
      rw [FGL.addPS, pairFam_Xv_eq_X, subst_self]
      rfl
    have hs : HasSubst fun j => (P.F.Φ j).map (algebraMap R S) :=
      hasSubst_of_constantCoeff_zero (FGL.noConst_map _ (fun j => P.F.constantCoeff_Φ j))
    have h0 : constantCoeff (U - 1) = 0 := by
      rw [map_sub, constantCoeff_charSeries, map_one, sub_self]
    have hv : ∀ a : Fin 2, ∀ j : Fin 1,
        constantCoeff ((U - 1).subst (Xv (R := S) (d := d) (n := 2) a)) = 0 := fun a _ =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (FGL.noConst_Xv a))
        (FGL.noConst_Xv a) h0
    have hsub : ∀ {τ : Type} {b : Fin d → MvPowerSeries τ S}, HasSubst b →
        (U - 1).subst b = U.subst b - 1 := fun hb => by
      rw [← coe_substAlgHom hb, map_sub, map_one, coe_substAlgHom]
    rw [hΦ]
    change (U - 1).subst _ = (multΦ S).subst (pairFam (fun _ => (U - 1).subst (Xv 0))
      (fun _ => (U - 1).subst (Xv 1)))
    rw [subst_multΦ_pairFam (hv 0) (hv 1), hsub hs,
      hsub (hasSubst_of_constantCoeff_zero (FGL.noConst_Xv 0)),
      hsub (hasSubst_of_constantCoeff_zero (FGL.noConst_Xv 1)), P.charSeries_groupLike hpm y]
    ring

theorem charHom_ptMap (x : P.F.Pt p) (y : P.pdivGroup.DualTate S) :
    ((P.charHom hpm y).ptMap (P.toPtS x)).1 0 = P.alpha hpm x y - 1 := by
  rw [FGL.Hom.ptMap_val]
  change FGL.ev p (P.charSeries hpm y - 1) x.1 = _
  rw [← evS_apply, map_sub, map_one, evS_apply]
  rfl

/-- The partial derivatives `∂U_y/∂T_j(0) ∈ O_{ℂ_p}`. -/
def dU (y : P.pdivGroup.DualTate S) (j : Fin d) : S :=
  coeff (Finsupp.single j 1) (P.charSeries hpm y)

/-- **`dα(z)(y) = ∑_j ∂U_y/∂T_j(0) z_j`** ([Hong, Prop. 3.4.9, proof]). -/
def dalpha (z : Fin d → ℂ_[p]) (y : P.pdivGroup.DualTate S) : ℂ_[p] :=
  ∑ j, ((OCd.toOC (P.dU hpm y j) : OC p) : ℂ_[p]) * z j

theorem dU_mul (y y' : P.pdivGroup.DualTate S) (j : Fin d) :
    P.dU hpm (y * y') j = P.dU hpm y j + P.dU hpm y' j := by
  have hs : (Finsupp.single j 1 : Fin d →₀ ℕ) ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
  have hne : ((0 : Fin d →₀ ℕ), Finsupp.single j 1) ≠ (Finsupp.single j 1, 0) := fun h =>
    hs (congrArg Prod.fst h).symm
  have h0 : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.single j 1 : Fin d →₀ ℕ),
      q ≠ (0, Finsupp.single j 1) ∧ q ≠ (Finsupp.single j 1, 0) →
        coeff q.1 (P.charSeries hpm y) * coeff q.2 (P.charSeries hpm y') = 0 := by
    intro q hq hne'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    exfalso
    have h1 : q.1 = 0 ∨ q.2 = 0 := by
      by_contra h
      push Not at h
      have := congrArg Finsupp.degree hq
      rw [map_add, Finsupp.degree_single] at this
      have a1 := (Finsupp.degree_eq_zero_iff q.1).not.mpr h.1
      have a2 := (Finsupp.degree_eq_zero_iff q.2).not.mpr h.2
      omega
    rcases h1 with h1 | h1
    · rw [h1, zero_add] at hq
      exact hne'.1 (Prod.ext h1 hq)
    · rw [h1, add_zero] at hq
      exact hne'.2 (Prod.ext hq h1)
  rw [dU, dU, dU, charSeries_mul, MvPowerSeries.coeff_mul, Finset.sum_eq_add _ _ hne h0
    (fun h => absurd (by simp) h) (fun h => absurd (by simp) h)]
  rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_charSeries, constantCoeff_charSeries, one_mul, mul_one, add_comm]

theorem dalpha_mul (z : Fin d → ℂ_[p]) (y y' : P.pdivGroup.DualTate S) :
    P.dalpha hpm z (y * y') = P.dalpha hpm z y + P.dalpha hpm z y' := by
  simp only [dalpha, dU_mul, map_add, Subring.coe_add, add_mul, Finset.sum_add_distrib]

/-- **The right square of [Hong, Prop. 3.4.9]**: `log_{Ĝ_m}(α(x)(y) − 1) = dα(log_F x)(y)`. -/
theorem logGm_alpha (x : P.F.Pt p) (y : P.pdivGroup.DualTate S) :
    (FGL.multiplicative S).logF ((P.charHom hpm y).ptMap (P.toPtS x)) 0 =
      P.dalpha hpm (fun j => P.F.logF x j) y := by
  rw [FGL.Hom.logF_ptMap, dalpha]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [logF_toPtS]
  congr 2
  change ((algebraMap S (OC p) (coeff (Finsupp.single j 1) (P.charSeries hpm y - 1)) : OC p) :
    ℂ_[p]) = _
  rw [map_sub, coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), sub_zero]
  rfl

end PDivFGL

end PadicHodge
