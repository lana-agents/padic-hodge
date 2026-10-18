/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.GmLog
import PadicHodge.AxSenTate.Basic
import PadicHodge.FormalGroup.GaloisAction

/-!
# Galois invariants of `F(m_{ℂ_p})` and `p`-divisibility over `ℚ_p`

For a formal group law `F` with Galois-fixed coefficients (`FormalGroup/GaloisAction.lean`):

* `galPt_fixed_iff` ([Hong, Lemma 3.4.2] for formal groups): for a finite extension `L/ℚ_p`,
  a point of `F(m_{ℂ_p})` is fixed by `G_L` iff its coordinates lie in `L` (Ax–Sen–Tate,
  `galCp_eq_self_iff_mem`); likewise `ℂ_p^{G_L} = L` for the values of `log_F`
  (`logF_mem_of_fixed`);
* `eq_zero_of_forall_pow_nsmul` (uniform version of [Hong, Lemma 3.4.3]): a point which is
  `p^n · y_n` for all `n`, with all `y_n` in a fixed polydisc of radius `< 1`, is `0`;
  `eq_zero_of_forall_pow_nsmul_Qp`: `⋂_n p^n F(p ℤ_p) = 0`.
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (F : FGL R d)

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
/-- **[Hong, Lemma 3.4.2] for formal groups**: `F(m_{ℂ_p})^{G_L} = F(m_L)`. -/
theorem galPt_fixed_iff (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] (x : F.Pt p) :
    (∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x = x) ↔
      ∀ j, ((x.1 j : OC p) : ℂ_[p]) ∈ cpSubmodule L := by
  constructor
  · intro h j
    refine (galCp_eq_self_iff_mem (L := L) _).mp fun σ => ?_
    have := congrArg (fun z : F.Pt p => ((z.1 j : OC p) : ℂ_[p])) (h σ)
    simp only [galPt_val] at this
    exact this
  · intro h σ
    refine F.pt_ext fun j => Subtype.ext ?_
    rw [galPt_val]
    exact (galCp_eq_self_iff_mem (L := L) _).mpr (h j) σ

/-- The values of `log_F` at `G_L`-fixed points lie in `L`. -/
theorem logF_mem_of_fixed (hR : GalFixed p R) (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] {x : F.Pt p}
    (hx : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x = x) (i : Fin d) :
    F.logF x i ∈ cpSubmodule L := by
  refine (galCp_eq_self_iff_mem (L := L) _).mp fun σ => ?_
  have h := logF_galPt hR (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x i
  rw [hx σ] at h
  exact h.symm

/-- `p^n · y` has radius `≤ r ρ^n`, `ρ = max(|p|, r)`. -/
theorem bnd_pow_nsmul_max {y : F.Pt p} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hy : F.Bnd y r)
    (n : ℕ) : F.Bnd ((p ^ n) • y) (r * max (np p) r ^ n) := by
  set ρ := max (np p) r
  have hρ0 : 0 ≤ ρ := le_max_of_le_left np_pos.le
  have hρ1 : ρ < 1 := max_lt np_lt_one hr1
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    rw [pow_succ, mul_nsmul]
    have hs0 : 0 ≤ r * ρ ^ n := mul_nonneg hr0 (pow_nonneg hρ0 _)
    have hs1 : r * ρ ^ n ≤ r := mul_le_of_le_one_right hr0 (pow_le_one₀ hρ0 hρ1.le)
    refine F.bnd_mono (F.bnd_p_nsmul hs0 (hs1.trans hr1.le) ih) (max_le ?_ ?_)
    · calc np p * (r * ρ ^ n) ≤ ρ * (r * ρ ^ n) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
        _ = r * ρ ^ (n + 1) := by ring
    · calc (r * ρ ^ n) ^ 2 = (r * ρ ^ n) * (r * ρ ^ n) := sq _
        _ ≤ (r * ρ ^ n) * ρ := mul_le_mul_of_nonneg_left (hs1.trans (le_max_right _ _)) hs0
        _ = r * ρ ^ (n + 1) := by ring

/-- **A point divisible by all `p^n` within a fixed polydisc of radius `< 1` is `0`**
(uniform version of [Hong, Lemma 3.4.3]). -/
theorem eq_zero_of_forall_pow_nsmul {x : F.Pt p} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n, ∃ y : F.Pt p, F.Bnd y r ∧ (p ^ n) • y = x) : x = 0 := by
  set ρ := max (np p) r
  have hρ0 : 0 ≤ ρ := le_max_of_le_left np_pos.le
  have hρ1 : ρ < 1 := max_lt np_lt_one hr1
  have hrad : ∀ n, F.rad x ≤ r * ρ ^ n := fun n => by
    obtain ⟨y, hy, rfl⟩ := h n
    exact F.rad_le (mul_nonneg hr0 (pow_nonneg hρ0 _)) (F.bnd_pow_nsmul_max hr0 hr1 hy n)
  have hlim : Tendsto (fun n : ℕ => r * ρ ^ n) atTop (𝓝 0) := by
    rw [← mul_zero r]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul r
  have h0 : F.rad x ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hrad)
  refine F.pt_ext fun j => Subtype.ext ?_
  have := (F.bnd_rad x j).trans h0
  rw [zero_val, ZeroMemClass.coe_zero]
  exact norm_le_zero_iff.mp this

/-- Points of the open disc in `ℚ_p` have absolute value `≤ |p|`. -/
theorem norm_le_np_of_Qp {q : ℚ_[p]} (hq : ‖algebraMap ℚ_[p] ℂ_[p] q‖ < 1) :
    ‖algebraMap ℚ_[p] ℂ_[p] q‖ ≤ np p := by
  have hnp : np p = (p : ℝ) ^ (-1 : ℤ) := by
    rw [np, ← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap_Qp_Cp, Padic.norm_p,
      zpow_neg_one]
  rw [norm_algebraMap_Qp_Cp] at hq ⊢
  rw [hnp, Padic.norm_le_pow_iff_norm_lt_pow_add_one]
  simpa using hq

/-- **[Hong, Lemma 3.4.3] over `ℚ_p`**: `⋂_n p^n F(p ℤ_p) = 0`. -/
theorem eq_zero_of_forall_pow_nsmul_Qp {x : F.Pt p}
    (h : ∀ n, ∃ y : F.Pt p, (∀ j, ∃ q : ℚ_[p], ((y.1 j : OC p) : ℂ_[p]) =
      algebraMap ℚ_[p] ℂ_[p] q) ∧ (p ^ n) • y = x) : x = 0 := by
  refine F.eq_zero_of_forall_pow_nsmul (np_pos (p := p)).le np_lt_one fun n => ?_
  obtain ⟨y, hy, hyx⟩ := h n
  refine ⟨y, fun j => ?_, hyx⟩
  obtain ⟨q, hq⟩ := hy j
  rw [hq] at ⊢
  exact norm_le_np_of_Qp (hq ▸ y.2 j)

end FGL

end PadicHodge
