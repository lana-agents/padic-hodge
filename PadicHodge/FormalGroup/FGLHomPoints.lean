/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.FGLHom
import PadicHodge.FormalGroup.LayerTate
import PadicHodge.FormalGroup.GaloisAction

/-!
# Homomorphisms of formal group laws on points

For a homomorphism of formal group laws `f : F → F'` over `R`:

* `FGL.Hom.ptHom : F(m_{ℂ_p}) →+ F'(m_{ℂ_p})`, `x ↦ f(x)` (additive by `f(Φ(T,U)) =
  Φ'(f(T), f(U))`), Galois-equivariant (`ptMap_galPt`), preserving `p^v`-torsion;
* compatibility with the layers: `layerMap_mk` (`t' ↦ f(t)` is `g ↦ g(f)` on `A'_v`), and
  `layerPt_comp_layerMap`: for `x ∈ F(m)[p^v]`, the point of `F'[p^v]` of `f(x)` is the point of
  `F[p^v]` of `x` composed with `layerMap` — i.e. `FGL.Hom.toPDiv` induces `ptHom` on
  `F(m)[p^∞] = F[p^∞](O_{ℂ_p})`.
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval WithConv

namespace PadicHodge

namespace FGL.Hom

section Points

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d d' : ℕ} {F : FGL R d} {F' : FGL R d'}
  (φ : FGL.Hom F F')

/-- `x ↦ f(x)` on `F(m_{ℂ_p})`. -/
def ptMap (x : F.Pt p) : F'.Pt p :=
  ⟨fun k => ev p (φ.f k) x.1, fun k => norm_ev_lt (φ.noConst k) x.2⟩

theorem ptMap_val (x : F.Pt p) (k : Fin d') : (φ.ptMap x).1 k = ev p (φ.f k) x.1 := rfl

omit [DiscreteUniformity R] in
theorem ev_pairPt_Xv (x y : Fin d → OC p) (a : Fin 2) (j : Fin d) :
    ev p (Xv (R := R) (n := 2) a j) (pairPt x y) = if a = 0 then x j else y j := by
  rw [Xv, ev_X]
  rfl

/-- **`f(x +_F y) = f(x) +_{F'} f(y)`.** -/
theorem ptMap_add (x y : F.Pt p) : φ.ptMap (x + y) = φ.ptMap x + φ.ptMap y := by
  refine F'.pt_ext fun k => ?_
  have hxy := norm_pairPt_lt x.2 y.2
  have h := congrArg (fun g => ev p g (pairPt x.1 y.1)) (φ.map_add k)
  have e3 : ∀ g h' : Fin d' → MvPowerSeries (Fin 2 × Fin d) R,
      F'.addPS g h' k = (F'.Φ k).subst (pairFam g h') := fun _ _ => rfl
  rw [ev_subst (F.noConst_addPS (noConst_Xv 0) (noConst_Xv 1)) hxy, e3,
    ev_pairFam (φ.constantCoeff_subst_Xv 0) (φ.constantCoeff_subst_Xv 1) hxy] at h
  have e1 : (fun j => ev p (F.addPS (Xv (R := R) (n := 2) 0) (Xv 1) j) (pairPt x.1 y.1)) =
      (x + y).1 := by
    funext j
    rw [addPS, ev_pairFam (noConst_Xv 0) (noConst_Xv 1) hxy, add_val]
    congr 2 <;> funext i <;> simp [ev_pairPt_Xv]
  have e2 : ∀ a : Fin 2, (fun l => ev p ((φ.f l).subst (Xv (R := R) (d := d) (n := 2) a))
      (pairPt x.1 y.1)) = fun l => ev p (φ.f l) (if a = 0 then x.1 else y.1) := by
    intro a
    funext l
    rw [ev_subst (noConst_Xv a) hxy]
    congr 1
    funext j
    rw [ev_pairPt_Xv]
    split_ifs <;> rfl
  rw [e1, e2 0, e2 1] at h
  rw [ptMap_val, h, add_val]
  rfl

/-- **The homomorphism `F(m_{ℂ_p}) → F'(m_{ℂ_p})`.** -/
def ptHom : F.Pt p →+ F'.Pt p := AddMonoidHom.mk' φ.ptMap φ.ptMap_add

theorem ptHom_apply (x : F.Pt p) : φ.ptHom x = φ.ptMap x := rfl

theorem ptMap_mem_torsionBy {v : ℕ} {x : F.Pt p} (hx : x ∈ F.torsionBy v) :
    φ.ptMap x ∈ F'.torsionBy v := by
  rw [mem_torsionBy] at *
  rw [← φ.ptHom_apply, ← map_nsmul, hx, map_zero]

/-- **`f` is Galois-equivariant on points.** -/
theorem ptMap_galPt (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : F.Pt p) : φ.ptMap (galPt σ x) = galPt σ (φ.ptMap x) := by
  refine F'.pt_ext fun k => Subtype.ext ?_
  rw [galPt_val, ptMap_val, ptMap_val, ev_autCp hR σ _ x.2]
  rfl

/-- The point of `F'[p^v]` of `f(x)` is the point of `F[p^v]` of `x`, pulled back along
`g ↦ g(f)`. -/
theorem layerPt_subst {v : ℕ} (x : F.torsionBy (p := p) v) (g : MvPowerSeries (Fin d') R) :
    ev p (g.subst φ.f) x.1.1 = ev p g (φ.ptMap x.1).1 := by
  rw [ev_subst φ.noConst x.1.2]
  rfl

end Points

section Layers

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d d' p : ℕ} [hp : Fact p.Prime] {P : PDivFGL R d p} {P' : PDivFGL R d' p}
  (φ : FGL.Hom P.F P'.F)

attribute [local instance] PDivFGL.isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

/-- `layerMap` is `g ↦ g(f)` on representatives. -/
theorem layerMap_mk (v : ℕ) (g : MvPowerSeries (Fin d') R) :
    φ.layerMap v (Ideal.Quotient.mk _ g) = Ideal.Quotient.mk _ (g.subst φ.f) := by
  rw [layerMap, PDivFGL.liftL_mk, ← FGL.evF_of (φ.tnf_fE (P.tnf_t v)), ← P.evF_t,
    FGL.evF_subst (P.tnf_t v) φ.noConst]
  rfl

variable [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]

/-- **`toPDiv` induces `ptHom` on torsion points.** -/
theorem layerPt_comp_layerMap (v : ℕ) (x : P.F.torsionBy (p := p) v) :
    (P.F.layerPt v x).comp (φ.layerMap v) =
      P'.F.layerPt v ⟨φ.ptMap x.1, φ.ptMap_mem_torsionBy x.2⟩ := by
  apply Ideal.Quotient.algHom_ext R
  refine AlgHom.ext fun g => ?_
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, layerMap_mk, FGL.layerPt_mk]
  exact φ.layerPt_subst x g

end Layers

end FGL.Hom

end PadicHodge
