/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Gm
import PadicHodge.Cyclotomic.LogChi

/-!
# The logarithm of `Ĝ_m` is the `p`-adic logarithm

[Hong, Ex. 3.3.5]: `log_{Ĝ_m}(x) = lim ((1 + x)^{p^n} − 1)/p^n = log(1 + x)`. We check this on
the points of `p ℤ_p ⊆ m_{ℂ_p}`, comparing with the `p`-adic logarithm `logQp` of
`Cyclotomic/LogChi.lean` (`PadicLogVolume.padicLog`, via its limit formula
`PadicLogVolume.tendsto_pow_sub_one_div`): `gm_logF_eq_logQp`.
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)]

theorem norm_algebraMap_Qp_Cp (q : ℚ_[p]) : ‖algebraMap ℚ_[p] ℂ_[p] q‖ = ‖q‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
  exact PadicComplex.norm_extends' p q

theorem continuous_algebraMap_Qp_Cp : Continuous (algebraMap ℚ_[p] ℂ_[p]) := by
  refine Isometry.continuous (Isometry.of_dist_eq fun a b => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_algebraMap_Qp_Cp]

/-- The limit formula for `logQp` on `1 + p ℤ_p`. -/
theorem tendsto_logQp (c : ℤ_[p]) :
    Tendsto (fun n : ℕ => ((1 + (p : ℚ_[p]) * c) ^ (p ^ n) - 1) / (p : ℚ_[p]) ^ n) atTop
      (𝓝 (logQp (1 + (p : ℚ_[p]) * c))) := by
  have h := (continuous_eQ (p := p)).continuousAt.tendsto.comp
    (PadicLogVolume.tendsto_pow_sub_one_div hp.out normV_p_lt_one (normV_symm_sub_one_lt c))
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, map_div₀, map_sub, map_pow, map_one, map_natCast,
    RingEquiv.apply_symm_apply]

/-- **`log_{Ĝ_m}(x) = log(1 + x)`** for `x ∈ p ℤ_p` ([Hong, Ex. 3.3.5]). -/
theorem gm_logF_eq_logQp (c : ℤ_[p]) (x : (multiplicative R).Pt p)
    (hx : ((x.1 0 : OC p) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((p : ℚ_[p]) * c)) :
    (multiplicative R).logF x 0 = algebraMap ℚ_[p] ℂ_[p] (logQp (1 + (p : ℚ_[p]) * c)) := by
  refine tendsto_nhds_unique ((multiplicative R).tendsto_logSeq x 0) ?_
  refine ((continuous_algebraMap_Qp_Cp.tendsto _).comp (tendsto_logQp c)).congr fun n => ?_
  rw [Function.comp_apply, logSeq, gm_nsmul_val, hx]
  simp only [map_div₀, map_sub, map_pow, map_add, map_one, map_natCast]

end FGL

end PadicHodge
