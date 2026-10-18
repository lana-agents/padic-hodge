/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Points

/-!
# Evaluating power series with coefficients in `O_{ℂ_p}` at formal points

The points framework (`FormalGroup/Points.lean`) evaluates power series whose coefficient ring
carries the discrete uniformity (Mathlib's `MvPowerSeries.eval₂_subst` needs it). For
coefficients in `O_{ℂ_p}` itself we use the type synonym `OCd p` of `O_{ℂ_p}` with the discrete
uniformity and `algebraMap (OCd p) (OC p) = id`; evaluation at points of the open polydisc then
converges (bounded coefficients) and all of `Points.lean` applies with `R := OCd p`.

* `ev_map`: evaluating `ι(f)` (`ι : R → OCd p` compatible with `R → O_{ℂ_p}`) equals evaluating
  `f`;
* **`ev_add_of_groupLike`**: if `U ∈ O_{ℂ_p}[[T]]` satisfies `U(Φ(T, T')) = U(T) U(T')`
  (e.g. from `PDivFGL.exists_groupLike` with `S = OCd p`), then
  `U(x +_F y) = U(x) U(y)` on `F(m_{ℂ_p})`: the map `α(·)(u) = U_u(·)` of
  [Hong, Prop. 3.4.9, proof] is a homomorphism `F(m_{ℂ_p}) → O_{ℂ_p}^×` (into `1 + m_{ℂ_p}` when
  `U(0) = 1`).
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

variable (p : ℕ) [hp : Fact p.Prime]

/-- `O_{ℂ_p}` as a coefficient ring with the discrete uniformity. -/
def OCd : Type := OC p

namespace OCd

instance : CommRing (OCd p) := inferInstanceAs (CommRing (OC p))

instance : UniformSpace (OCd p) := ⊥

instance : DiscreteUniformity (OCd p) := ⟨rfl⟩

instance : Algebra (OCd p) (OC p) := (RingHom.id (OC p)).toAlgebra

variable {p}

/-- The identification `OCd p = O_{ℂ_p}` as rings. -/
def toOC : OCd p ≃+* OC p := RingEquiv.refl (OC p)

theorem algebraMap_apply (x : OCd p) : algebraMap (OCd p) (OC p) x = toOC x := rfl

end OCd

namespace FGL

variable {p} {R : Type*} [CommRing R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ}

/-- Evaluation is multiplicative. -/
theorem ev_mul {S σ : Type*} [CommRing S] [UniformSpace S] [DiscreteUniformity S]
    [Algebra S (OC p)] [Finite σ] {a : σ → OC p} (ha : ∀ s, ‖(a s : ℂ_[p])‖ < 1)
    (f g : MvPowerSeries σ S) : ev p (f * g) a = ev p f a * ev p g a := by
  simp only [ev]
  rw [← coe_eval₂Hom continuous_algebraMap_OC (hasEval_of_norm_lt_one ha), map_mul]

/-- **Evaluating `ι(f)` equals evaluating `f`.** -/
theorem ev_map (ι : R →+* OCd p)
    (hι : ∀ r, algebraMap (OCd p) (OC p) (ι r) = algebraMap R (OC p) r)
    {σ : Type*} [Finite σ] {a : σ → OC p} (ha : ∀ s, ‖(a s : ℂ_[p])‖ < 1)
    (f : MvPowerSeries σ R) : ev p (MvPowerSeries.map ι f) a = ev p f a := by
  simp only [ev]
  rw [eval₂_eq_tsum continuous_algebraMap_OC (hasEval_of_norm_lt_one ha),
    eval₂_eq_tsum continuous_algebraMap_OC (hasEval_of_norm_lt_one ha)]
  simp only [coeff_map, hι]

variable (F : FGL R d)

/-- **`U(x +_F y) = U(x) U(y)` for `U(Φ(T, T')) = U(T) U(T')`.** -/
theorem ev_add_of_groupLike (ι : R →+* OCd p)
    (hι : ∀ r, algebraMap (OCd p) (OC p) (ι r) = algebraMap R (OC p) r)
    (U : MvPowerSeries (Fin d) (OCd p))
    (hU : U.subst (fun j => MvPowerSeries.map ι (F.Φ j)) =
      U.subst (Xv (R := OCd p) (d := d) (n := 2) 0) *
        U.subst (Xv (R := OCd p) (d := d) (n := 2) 1))
    (x y : F.Pt p) : ev p U (x + y).1 = ev p U x.1 * ev p U y.1 := by
  have hb := norm_pairPt_lt x.2 y.2
  have h := congrArg (fun f => ev p f (pairPt x.1 y.1)) hU
  have h0 : ∀ j, constantCoeff (MvPowerSeries.map ι (F.Φ j)) = 0 := fun j => by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      F.constantCoeff_Φ, map_zero]
  rw [ev_subst h0 hb, ev_mul hb, ev_subst (constantCoeff_Xv 0) hb,
    ev_subst (constantCoeff_Xv 1) hb] at h
  simp only [Xv, ev_X] at h
  have e : (fun j => ev p (MvPowerSeries.map ι (F.Φ j)) (pairPt x.1 y.1)) = (x + y).1 := by
    funext j
    rw [ev_map ι hι hb, add_val]
  rw [e] at h
  rw [h]
  rfl

end FGL

end PadicHodge
