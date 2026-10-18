/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.LayerPDiv
import PadicHodge.FormalGroup.LayerSurj
import PadicHodge.FormalGroup.TateModule

/-!
# `T_p F[p^∞](O_{ℂ_p}) = T_p F`

For a `p`-divisible formal group law `F` over a complete local ring `R` (discrete topology,
`R → O_{ℂ_p}` local), the points `x ∈ F(m_{ℂ_p})[p^v]` give points `layerPt v x` of
`F[p^v] = Spec A_v` (`FormalGroup/LayerPoints.lean`, bijectively by `FormalGroup/LayerSurj.lean`),
and

* `layerPt_comp_mulMap`: `layerPt v x ∘ [n]^* = layerPt v (n · x)`;
* `tateToPDiv`: a compatible system `(x_v) ∈ T_p F = lim F(m_{ℂ_p})[p^v]` gives a point of the
  Tate module of the `p`-divisible group `F[p^∞]` (`PDivFGL.pdivGroup`), and this is a bijection
  (`tateToPDiv_bijective`, `tateEquiv`).
-/

noncomputable section

open MvPowerSeries IsLocalRing PadicHodge.AdicEval WithConv

namespace PadicHodge

namespace PDivFGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (P : PDivFGL R d p)

attribute [local instance] isAdicComplete_free

local notation "𝔪R" => maximalIdeal R

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem mulMap_mk (v n : ℕ) (f : MvPowerSeries (Fin d) R) :
    P.mulMap v n (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (f.subst (P.F.mulPS n)) := by
  rw [mulMap, liftL_mk, ← FGL.evF_of (P.F.tnf_mulE n (P.tnf_t v)), ← evF_t,
    FGL.evF_subst (P.tnf_t v) (P.F.constantCoeff_mulPS n)]
  rfl

/-- `layerPt v x ∘ [n]^* = layerPt v (n · x)`. -/
theorem layerPt_comp_mulMap (v n : ℕ) (x : P.F.torsionBy (p := p) v) :
    (P.F.layerPt v x).comp (P.mulMap v n) =
      P.F.layerPt v ⟨n • x.1, nsmul_mem x.2 n⟩ := by
  apply Ideal.Quotient.algHom_ext R
  ext f
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mulMap_mk, FGL.layerPt_mk]
  rw [FGL.ev_subst (P.F.constantCoeff_mulPS n) x.1.2]
  congr 2
  funext j
  exact Subtype.ext (congrArg Subtype.val (P.F.ev_mulPS n x.1 j))

/-- The point of `F[p^v]` of a `p^v`-torsion point. -/
def ptV (v : ℕ) (x : P.F.torsionBy (p := p) v) : (P.pdivGroup.G v).points (OC p) :=
  toConv (P.F.layerPt v x)

theorem ptV_incl (v : ℕ) (x : P.F.torsionBy (p := p) v) :
    (P.pdivGroup.incl v).mapPoints (OC p) (P.ptV v x) =
      P.ptV (v + 1) ⟨x.1, P.F.torsionBy_mono x.2⟩ := by
  apply WithConv.ofConv_injective
  exact P.F.layerPt_comp_layerIncl x

theorem ptV_pow (v : ℕ) (x : P.F.torsionBy (p := p) v) (n : ℕ) :
    P.ptV v x ^ n = P.ptV v ⟨n • x.1, nsmul_mem x.2 n⟩ := by
  rw [ptV, P.pow_eq v (OC p)]
  apply WithConv.ofConv_injective
  exact P.layerPt_comp_mulMap v n x

/-- **From `T_p F` to the Tate module of `F[p^∞]`.** -/
def tateToPDiv (x : P.F.tate p) : P.pdivGroup.TateModule (OC p) :=
  ⟨fun v => P.ptV v ⟨x.1 v, P.F.tate_mem_torsionBy x.2 v⟩, fun v => by
    rw [ptV_incl, ptV_pow]
    congr 2
    exact (x.2.2 v).symm⟩

theorem tateToPDiv_injective : Function.Injective P.tateToPDiv := by
  intro x y h
  apply Subtype.ext
  funext v
  have := congrArg (fun z => ofConv (z.1 v)) h
  exact congrArg Subtype.val (P.F.layerPt_injective v this)

/-- **`T_p F ≅ T_p F[p^∞](O_{ℂ_p})`.** -/
theorem tateToPDiv_bijective
    (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) :
    Function.Bijective P.tateToPDiv := by
  refine ⟨P.tateToPDiv_injective, fun y => ?_⟩
  choose x hx using fun v => P.layerPt_surjective hR v (ofConv (y.1 v))
  have hxv : ∀ v, P.ptV v (x v) = y.1 v := fun v => by
    rw [ptV, hx v]
  have hstep : ∀ v, p • (x (v + 1)).1 = (x v).1 := by
    intro v
    have h1 := y.2 v
    rw [← hxv, ← hxv, ptV_incl, ptV_pow] at h1
    have h2 := P.F.layerPt_injective (v + 1) (congrArg ofConv h1)
    exact (congrArg Subtype.val h2).symm
  have h0 : (x 0).1 = 0 := by
    have := (x 0).2
    rw [FGL.mem_torsionBy, pow_zero, one_nsmul] at this
    exact this
  refine ⟨⟨fun v => (x v).1, h0, hstep⟩, ?_⟩
  apply Subtype.ext
  funext v
  exact hxv v

/-- **`T_p F ≃ T_p F[p^∞](O_{ℂ_p})`.** -/
def tateEquiv (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) :
    P.F.tate p ≃ P.pdivGroup.TateModule (OC p) :=
  Equiv.ofBijective _ (P.tateToPDiv_bijective hR)

end PDivFGL

end PadicHodge
