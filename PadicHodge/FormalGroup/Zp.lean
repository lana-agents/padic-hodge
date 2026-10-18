/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.AlphaGal
import PadicHodge.FormalGroup.AlphaLog
import PadicHodge.FormalGroup.GmLog

/-!
# `ℤ_p` as a coefficient ring for formal points

The points framework (`FormalGroup/Points.lean`) and `α` (`Alpha.lean`, `AlphaGal.lean`) take a
coefficient ring `R` with the discrete uniformity and an algebra map `R → O_{ℂ_p}`. Here
`ZpD p` is `ℤ_p` with the discrete uniformity, `ℤ_p → ℚ_p → ℂ_p` (with image in `O_{ℂ_p}`), and
all hypotheses of `Alpha.lean`/`AlphaGal.lean` are discharged:

* `ZpD.isAdicComplete_OC`: `O_{ℂ_p}` is complete for `𝔪_{ℤ_p} O_{ℂ_p} = (p)`;
* `ZpD.p_mem`: `p ∈ 𝔪_{ℤ_p}`; `ZpD.norm_lt_one`: `𝔪_{ℤ_p} ↦ m_{ℂ_p}`;
* `ZpD.galFixed`: the coefficients are fixed by `Gal(ℚ̄_p/ℚ_p)`;
* `PDivFGL.alphaZp`, `alphaZp_add`, `alphaZp_mul`, `alphaZp_gal`: `α` for `p`-divisible formal
  group laws over `ℤ_p`, a bimultiplicative Galois-equivariant pairing
  `F(m_{ℂ_p}) × T_p(G^∨)(O_{ℂ_p}) → 1 + m_{ℂ_p}` ([Hong, Prop. 3.4.9] over `K = ℚ_p`).
-/

noncomputable section

open IsLocalRing WithConv

namespace PadicHodge

/-- `ℤ_p` with the discrete uniformity. -/
def ZpD (p : ℕ) [Fact p.Prime] : Type := ℤ_[p]

namespace ZpD

variable {p : ℕ} [hp : Fact p.Prime]

instance : CommRing (ZpD p) := inferInstanceAs (CommRing ℤ_[p])

instance : IsLocalRing (ZpD p) := inferInstanceAs (IsLocalRing ℤ_[p])

instance : UniformSpace (ZpD p) := ⊥

instance : DiscreteUniformity (ZpD p) := ⟨rfl⟩

instance : IsAdicComplete (maximalIdeal (ZpD p)) (ZpD p) :=
  inferInstanceAs (IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p])

/-- The underlying `p`-adic integer. -/
def val (r : ZpD p) : ℤ_[p] := r

/-- `ℤ_p → ℚ_p → ℂ_p` lands in `O_{ℂ_p}`. -/
def toOC : ZpD p →+* OC p :=
  ((algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom (p := p))).codRestrict (OC p) fun r => by
    rw [mem_OC, RingHom.comp_apply, FGL.norm_algebraMap_Qp_Cp]
    exact PadicInt.norm_le_one (val r)

instance : Algebra (ZpD p) (OC p) := toOC.toAlgebra

theorem coe_algebraMap (r : ZpD p) :
    ((algebraMap (ZpD p) (OC p) r : OC p) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] (val r : ℚ_[p]) := rfl

theorem maximalIdeal_eq : maximalIdeal (ZpD p) = Ideal.span {(p : ZpD p)} :=
  PadicInt.maximalIdeal_eq_span_p

theorem p_mem : (p : ZpD p) ∈ maximalIdeal (ZpD p) := by
  rw [maximalIdeal_eq]; exact Ideal.mem_span_singleton_self _

/-- **`O_{ℂ_p}` is complete for `𝔪_{ℤ_p} O_{ℂ_p}`.** -/
instance isAdicComplete_OC :
    IsAdicComplete ((maximalIdeal (ZpD p)).map (algebraMap (ZpD p) (OC p))) (OC p) :=
  OC.isAdicComplete_of_map_eq (by
    rw [maximalIdeal_eq, Ideal.map_span, Set.image_singleton, map_natCast])

/-- `𝔪_{ℤ_p}` maps into `m_{ℂ_p}`. -/
theorem norm_lt_one (r : ZpD p) (hr : r ∈ maximalIdeal (ZpD p)) :
    ‖((algebraMap (ZpD p) (OC p) r : OC p) : ℂ_[p])‖ < 1 := by
  rw [coe_algebraMap, FGL.norm_algebraMap_Qp_Cp]
  exact PadicInt.mem_nonunits.mp hr

/-- The coefficients `ℤ_p` are Galois-fixed. -/
theorem galFixed : FGL.GalFixed p (ZpD p) :=
  FGL.galFixed_of_factors fun r => ⟨(val r : ℚ_[p]), rfl⟩

end ZpD

namespace PDivFGL

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} (P : PDivFGL (ZpD p) d p)

/-- **`α : F(m_{ℂ_p}) × T_p(G^∨)(O_{ℂ_p}) → 1 + m_{ℂ_p}` over `ℤ_p`** ([Hong, Prop. 3.4.9]). -/
def alphaZp (x : P.F.Pt p) (y : P.pdivGroup.DualTate (OCd p)) : OC p :=
  P.alpha ZpD.p_mem x y

theorem alphaZp_add (x x' : P.F.Pt p) (y : P.pdivGroup.DualTate (OCd p)) :
    P.alphaZp (x + x') y = P.alphaZp x y * P.alphaZp x' y :=
  P.alpha_add ZpD.p_mem x x' y

theorem alphaZp_mul (x : P.F.Pt p) (y y' : P.pdivGroup.DualTate (OCd p)) :
    P.alphaZp x (y * y') = P.alphaZp x y * P.alphaZp x y' :=
  P.alpha_mul ZpD.p_mem x y y'

theorem alphaZp_gal (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : P.F.Pt p)
    (y : P.pdivGroup.DualTate (OCd p)) :
    ((P.alphaZp (FGL.galPt σ x) (P.galDual σ (ZpD.galFixed σ) y) : OC p) : ℂ_[p]) =
      autCp σ ((P.alphaZp x y : OC p) : ℂ_[p]) :=
  P.alpha_gal σ (ZpD.galFixed σ) ZpD.p_mem x y

/-- The left square of [Hong, Prop. 3.4.9] over `ℤ_p`: on `p^v`-torsion, `α` is the Cartier
pairing. -/
theorem alphaZp_torsion (v : ℕ) (x : P.F.torsionBy (p := p) v)
    (y : P.pdivGroup.DualTate (OCd p)) :
    P.alphaZp x.1 y =
      (P.groupScheme v).pairing (OCd p) (toConv (toOCd (P.F.layerPt v x))) (y.1 v) :=
  P.alpha_torsion ZpD.p_mem v x y

/-- The right square of [Hong, Prop. 3.4.9] over `ℤ_p`. -/
theorem logGm_alphaZp (x : P.F.Pt p) (y : P.pdivGroup.DualTate (OCd p)) :
    (FGL.multiplicative (OCd p)).logF ((P.charHom ZpD.p_mem y).ptMap (P.toPtS x)) 0 =
      P.dalpha ZpD.p_mem (fun j => P.F.logF x j) y :=
  P.logGm_alpha ZpD.p_mem x y

end PDivFGL

end PadicHodge
