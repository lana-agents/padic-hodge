/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Layers
import PadicHodge.FormalGroup.GaloisAction

/-!
# Torsion points of a formal group as points of the layers `A_v`

For a formal group law `F` over `R` (setting of `FormalGroup/Points.lean`), evaluation at a
point `x ∈ F(m_{ℂ_p})[p^v]` kills `J_v = [p^v]_F(I)`, so it defines an `R`-algebra map
`layerPt v x : A_v = R[[T]]/J_v → O_{ℂ_p}` (`layerPt_mk`: `f ↦ f(x)`). This is the map
`F(m_{ℂ_p})[p^v] → F[p^v](O_{ℂ_p})` of [Hong, Prop. 2.2.10, Cor. 3.2.4]:

* `layerPt_injective`;
* compatible with the closed immersions `A_{v+1} ↠ A_v` (`layerPt_comp_layerIncl`) and with
  multiplication by `p`, `A_v → A_{v+1}` (`layerPt_comp_layerP`);
* Galois-equivariant (`layerPt_galPt`).

Surjectivity (every `O_{ℂ_p}`-point of `A_v` comes from a torsion point) needs the finiteness
of `A_v` over `R` and is not proved here.
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (F : FGL R d)

/-- Evaluation at a point as an `R`-algebra map `R[[T]] → O_{ℂ_p}`. -/
def evAlgHom (x : F.Pt p) : MvPowerSeries (Fin d) R →ₐ[R] OC p :=
  { eval₂Hom (continuous_algebraMap_OC (p := p) (R := R)) (hasEval_of_norm_lt_one x.2) with
    commutes' := fun r => by
      change eval₂Hom (continuous_algebraMap_OC (p := p) (R := R))
        (hasEval_of_norm_lt_one x.2) (algebraMap R _ r) = _
      rw [coe_eval₂Hom (continuous_algebraMap_OC (p := p) (R := R)),
        MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
      exact eval₂_C (algebraMap R (OC p)) x.1 r }

theorem evAlgHom_apply (x : F.Pt p) (f : MvPowerSeries (Fin d) R) :
    F.evAlgHom x f = ev p f x.1 := by
  change eval₂Hom (continuous_algebraMap_OC (p := p) (R := R))
    (hasEval_of_norm_lt_one x.2) f = _
  rw [coe_eval₂Hom]
  rfl

theorem evAlgHom_vanish {v : ℕ} (x : F.torsionBy (p := p) v) :
    ∀ a ∈ F.layerIdeal p v, F.evAlgHom x.1 a = 0 := by
  intro a ha
  have hle : F.layerIdeal p v ≤ RingHom.ker (F.evAlgHom x.1) := by
    rw [layerIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, evAlgHom_apply, ev_mulPS,
      (F.mem_torsionBy).mp x.2, zero_val]
  exact hle ha

/-- **The point `A_v → O_{ℂ_p}` of a `p^v`-torsion point.** -/
def layerPt (v : ℕ) (x : F.torsionBy (p := p) v) : F.Layer p v →ₐ[R] OC p :=
  Ideal.Quotient.liftₐ (F.layerIdeal p v) (F.evAlgHom x.1) (F.evAlgHom_vanish x)

theorem layerPt_mk {v : ℕ} (x : F.torsionBy (p := p) v) (f : MvPowerSeries (Fin d) R) :
    F.layerPt v x (Ideal.Quotient.mk _ f) = ev p f x.1.1 := by
  rw [layerPt, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom,
    evAlgHom_apply]

theorem layerPt_X {v : ℕ} (x : F.torsionBy (p := p) v) (j : Fin d) :
    F.layerPt v x (Ideal.Quotient.mk _ (X j)) = x.1.1 j := by
  rw [layerPt_mk, ev_X]

theorem layerPt_injective (v : ℕ) : Function.Injective (F.layerPt (p := p) v) := by
  intro x y h
  apply Subtype.ext
  refine F.pt_ext fun j => ?_
  rw [← layerPt_X, ← layerPt_X, h]

theorem torsionBy_mono {v : ℕ} {x : F.Pt p} (hx : x ∈ F.torsionBy v) :
    x ∈ F.torsionBy (v + 1) := by
  rw [mem_torsionBy] at *
  rw [pow_succ, mul_nsmul, hx, nsmul_zero]

/-- **Compatibility with `G_v ↪ G_{v+1}`.** -/
theorem layerPt_comp_layerIncl {v : ℕ} (x : F.torsionBy (p := p) v) :
    (F.layerPt v x).comp (F.layerIncl p v) = F.layerPt (v + 1) ⟨x.1, F.torsionBy_mono x.2⟩ := by
  ext y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [AlgHom.comp_apply, layerIncl, Ideal.Quotient.factorₐ_apply_mk, layerPt_mk, layerPt_mk]

theorem p_nsmul_mem_torsionBy {v : ℕ} {x : F.Pt p} (hx : x ∈ F.torsionBy (v + 1)) :
    p • x ∈ F.torsionBy v := by
  rw [mem_torsionBy] at *
  rw [← mul_nsmul, ← pow_succ']
  exact hx

/-- **Compatibility with multiplication by `p`, `G_{v+1} → G_v`.** -/
theorem layerPt_comp_layerP {v : ℕ} (x : F.torsionBy (p := p) (v + 1)) :
    (F.layerPt (v + 1) x).comp (F.layerP p v) =
      F.layerPt v ⟨p • x.1, F.p_nsmul_mem_torsionBy x.2⟩ := by
  ext y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [AlgHom.comp_apply, layerP, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, layerPt_mk,
    layerPt_mk, pSubst, coe_substAlgHom, ev_subst (F.constantCoeff_mulPS p) x.1.2]
  exact congrArg (fun z : OC p => (z : ℂ_[p]))
    (congrArg (ev p f) (funext fun j => F.ev_mulPS p x.1 j))

/-- **Galois equivariance.** -/
theorem layerPt_galPt (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    {v : ℕ} (x : F.torsionBy (p := p) v) (y : F.Layer p v) :
    F.layerPt v ⟨galPt σ x.1, galPt_mem_torsionBy hR σ x.2⟩ y =
      autOC σ (F.layerPt v x y) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [layerPt_mk, layerPt_mk]
  apply Subtype.ext
  rw [autOC_coe, ev_autCp hR σ f x.1.2]
  rfl

end FGL

end PadicHodge
