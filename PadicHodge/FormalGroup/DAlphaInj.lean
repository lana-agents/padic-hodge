/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.AlphaInj
import PadicHodge.FormalGroup.LogProps
import PadicHodge.TateSen.Invariants

/-!
# Injectivity of `dα` on `t_G(ℚ_p)` ([Hong, Prop. 3.4.9, proof])

For a `p`-divisible formal group law `P` over `R` with Galois-fixed coefficients (e.g.
`R = ℤ_p`), `dα : t_G(ℂ_p) = ℂ_p^d → Hom(T_p(G^∨), ℂ_p)`, `dα(z)(y) = ∑_j ∂U_y/∂T_j(0) z_j`
(`AlphaLog.lean`), is injective on `t_G(ℚ_p) = ℚ_p^d` (`dalpha_injective_Qp`).

Route (instead of the snake-lemma isomorphism `ker α ≅ ker dα` of [Hong]): for `z ∈ ℚ_p^d` with
`dα(z) = 0`, scale `z` into the polydisc of radius `r = |p|^2 < |p|` on which `log_F` is
bijective ([Hong, Prop. 3.3.6 (2)], `logF_bijOn`), and let `x` be the point with `log_F x = z`;
`x` is `Gal(ℚ̄_p/ℚ_p)`-invariant by uniqueness (`log_F(σx) = σ z = z`). Then `u_y(x) = α(x)(y) − 1`
lies in the same disc of `Ĝ_m` and `log(u_y(x)) = dα(z)(y) = 0` (`logGm_alpha`), so
`α(x)(y) = 1`; by the injectivity of `α` on `G(ℤ_p)` (`eq_zero_of_alpha_eq_one`), `x = 0` and
`z = log_F x = 0`.
-/

noncomputable section

open MvPowerSeries IsLocalRing WithConv

namespace PadicHodge

namespace PDivFGL

open FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (P : PDivFGL R d p)
  [hC : IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R)

local notation "S" => OCd p

omit [UniformSpace R] [DiscreteUniformity R] in
theorem dalpha_smul (c : ℂ_[p]) (z : Fin d → ℂ_[p]) (y : P.pdivGroup.DualTate S) :
    P.dalpha hpm (fun j => c * z j) y = c * P.dalpha hpm z y := by
  simp only [dalpha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R]
  [DiscreteUniformity R] in
theorem bnd_toPtS {x : P.F.Pt p} {r : ℝ} (hx : P.F.Bnd x r) : P.FS.Bnd (P.toPtS x) r := hx

variable (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1)

include hR in
/-- **`dα` is injective on `t_G(ℚ_p) = ℚ_p^d`** ([Hong, Prop. 3.4.9, proof], `K = ℚ_p`). -/
theorem dalpha_injective_Qp (hRG : GalFixed p R) (z : Fin d → ℚ_[p])
    (h : ∀ y, P.dalpha hpm (fun j => algebraMap ℚ_[p] ℂ_[p] (z j)) y = 0) : z = 0 := by
  have hnp := np_pos (p := p)
  set r : ℝ := np p ^ 2
  have hr0 : 0 ≤ r := by positivity
  have hr : r < np p := by
    change np p ^ 2 < np p
    rw [sq]; exact mul_lt_of_lt_one_left hnp np_lt_one
  -- scale `z` into the polydisc of radius `r`
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ‖algebraMap ℚ_[p] ℂ_[p] (z j)‖ ≤ M :=
    ⟨∑ j, ‖algebraMap ℚ_[p] ℂ_[p] (z j)‖, Finset.sum_nonneg fun j _ => norm_nonneg _,
      fun j => Finset.single_le_sum (fun k _ => norm_nonneg (algebraMap ℚ_[p] ℂ_[p] (z k)))
        (Finset.mem_univ j)⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (pow_pos hnp 2) (by linarith : 0 < M + 1))
    (np_lt_one (p := p))
  set τ : Fin d → ℂ_[p] := fun j => (p : ℂ_[p]) ^ n * algebraMap ℚ_[p] ℂ_[p] (z j)
  have hτ : ∀ j, ‖τ j‖ ≤ r := fun j => by
    change ‖(p : ℂ_[p]) ^ n * _‖ ≤ np p ^ 2
    rw [norm_mul, norm_pow]
    have h1 : np p ^ n * (M + 1) < np p ^ 2 := (lt_div_iff₀ (by linarith)).mp hn
    calc np p ^ n * ‖algebraMap ℚ_[p] ℂ_[p] (z j)‖ ≤ np p ^ n * (M + 1) :=
          mul_le_mul_of_nonneg_left ((hM j).trans (by linarith)) (pow_nonneg hnp.le _)
      _ ≤ np p ^ 2 := h1.le
  obtain ⟨x, hxr, hlog⟩ := P.F.exists_logF_eq hr0 hr hτ
  -- `x` is Galois-invariant
  have hfix : ∀ σ, galPt σ x = x := fun σ => by
    refine P.F.logF_injOn hr0 hr (fun j => ?_) hxr fun i => ?_
    · rw [galPt_val, norm_autCp]; exact hxr j
    · rw [logF_galPt hRG, hlog]
      change autCp σ ((p : ℂ_[p]) ^ n * _) = _
      rw [map_mul, map_pow, map_natCast, autCp_algebraMap]
  -- `α(x) = 1`
  have hα : ∀ y, P.alpha hpm x y = 1 := fun y => by
    set u := (P.charHom hpm y).ptMap (P.toPtS x)
    have hu : (FGL.multiplicative S).Bnd u r :=
      (P.charHom hpm y).bnd_ptMap hr0 (hr.trans np_lt_one).le (P.bnd_toPtS hxr)
    have hlu : ∀ i, (FGL.multiplicative S).logF u i = 0 := fun i => by
      rw [Fin.fin_one_eq_zero i, P.logGm_alpha hpm x y]
      have e : (fun j => P.F.logF x j) = fun j => (p : ℂ_[p]) ^ n *
          algebraMap ℚ_[p] ℂ_[p] (z j) := funext hlog
      rw [e, dalpha_smul, h y, mul_zero]
    have hu0 := (FGL.multiplicative S).eq_zero_of_logF_eq_zero hr0 hr hu hlu
    have key : u.1 0 = P.alpha hpm x y - 1 := P.charHom_ptMap hpm x y
    rw [hu0, FGL.zero_val] at key
    exact sub_eq_zero.mp key.symm
  have hx0 := P.eq_zero_of_alpha_eq_one hpm hR hRG x hα hfix
  funext j
  have := hlog j
  rw [hx0, logF_zero] at this
  have hp0 : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hz : algebraMap ℚ_[p] ℂ_[p] (z j) = 0 :=
    (mul_eq_zero.mp this.symm).resolve_left hp0
  rw [Pi.zero_apply]
  exact (FaithfulSMul.algebraMap_injective ℚ_[p] ℂ_[p]) (hz.trans (map_zero _).symm)

end PDivFGL

end PadicHodge
