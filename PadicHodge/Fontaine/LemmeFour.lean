/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.Pullback

/-!
# [Fo, §3 Lemme 4] for invariant differentials

[Fo] J.-M. Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur les
corps locaux*, Invent. Math. 65 (1982), §3.

Let `L/ℚ_p` be finite, `F` a formal group law over `O_L` of dimension `d` and
`ω_c = ∑_l c_l ω_l` (`c ∈ O_L^d`) an invariant differential of `F`.

* **`FGL.exists_pairing_ne_zero`**: if `c ≠ 0`, there is a point `x ∈ F(m_{ℂ_p})` with
  coordinates in `O_K̄` such that `x^* ω_c ≠ 0` in `Ω_{O_K̄/O_L}`.

Since the linear part of `ω_c` is `∑_l c_l dX_l` (`FGL.constantCoeff_invDiff`), no analogue of
[Fo, Lemme 5] is needed: for `c_j ≠ 0`, `|p|^k < |c_j|` and `ζ = ε_{m+1}` the point
`u = (p^k (ζ - 1)) e_j` satisfies `u^* ω_c = y · p^k dζ` with `|y - c_j| ≤ |p|^k`, hence
`|y| = |c_j|`, and `p^k y · dζ ≠ 0` for `m` large by [Fo, Lemme 7]
(`OL.smul_D_zeta_eq_zero_iff`, `OL.dnorm_bot_cyc`).
-/

noncomputable section

open MvPowerSeries KaehlerDifferential IsLocalRing

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

namespace FGL

open OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L] {d : ℕ}
  (F : FGL (OL L) d)

/-- `|ω_{lj}(u) - δ_{lj}| ≤ r` if `|u_s| ≤ r ≤ 1` (the linear part of `ω_l` is `dX_l`). -/
theorem norm_evK_invDiff_sub_le (l j : Fin d) {u : Fin d → OKbar p} (hu : Small u) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hur : ∀ s, ‖(u s : PadicAlgCl p)‖ ≤ r) :
    ‖((evK (F.invDiff l j) u - if l = j then 1 else 0 : OKbar p) : PadicAlgCl p)‖ ≤ r := by
  set g : MvPowerSeries (Fin d) (OL L) := if l = j then 1 else 0
  have hg : evK g u = if l = j then 1 else 0 := by
    simp only [g]
    split_ifs
    · exact map_one (evKHom hu)
    · exact map_zero (evKHom hu)
  rw [← hg, ← evK_sub _ _ hu]
  have h := norm_evK_le (F.invDiff l j - g) hu (k := 1) hr0 hr1 hur fun m hm => by
    by_contra h0
    have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    subst hm0
    apply hm
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, constantCoeff_invDiff]
    simp only [g]
    split_ifs <;> simp
  rwa [pow_one] at h

variable {ε : ℕ → PadicAlgCl p}

/-- **[Fo, §3 Lemme 4] for invariant differentials**: a nonzero invariant differential
`ω_c = ∑_l c_l ω_l` has nonzero pull-back `x^* ω_c ∈ Ω_{O_K̄/O_L}` at some point `x` of
`F(m_{ℂ_p})` with coordinates in `O_K̄`. (The compatible system `ε` of `p`-power roots of unity
only enters the proof.) -/
theorem exists_pairing_ne_zero (hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1)))
    (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1)) (c : Fin d → OL L) (hc : c ≠ 0) :
    ∃ x : F.Pt p, F.IsAlg x ∧
      ∑ l, algebraMap (OL L) (OKbar p) (c l) • F.pairing l x ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  set c' : Fin d → OKbar p := fun l => algebraMap (OL L) (OKbar p) (c l) with hc'
  have hcj : 0 < ‖(c' j : PadicAlgCl p)‖ := by
    rw [hc', ← nrm_eq_norm_OKbar]
    exact nrm_pos hj
  have hcl : ∀ l, ‖(c' l : PadicAlgCl p)‖ ≤ 1 := fun l => (c' l).2
  have hp0 : (0 : ℝ) < ‖(p : PadicAlgCl p)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hp1 : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hcj hp1
  have he0 := norm_eps_one_sub_one_pos hε
  have hdL : 0 < dL L := dnorm_pos
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
    (show 0 < ‖(p : PadicAlgCl p)‖ ^ k * ‖(c' j : PadicAlgCl p)‖ * dL L * ‖ε 1 - 1‖ by positivity)
    hp1
  -- the point `u = (p^k (ζ - 1)) e_j`
  set ζ := epsK hε m
  set x : OKbar p := (p : OKbar p) ^ k * (ζ - 1) with hx
  have hxn : ‖(x : PadicAlgCl p)‖ ≤ ‖(p : PadicAlgCl p)‖ ^ k := by
    rw [hx, Subring.coe_mul, norm_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, norm_pow]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [AddSubgroupClass.coe_sub, Subring.coe_one, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (ζ.2 : ‖(ζ : PadicAlgCl p)‖ ≤ 1) ?_)
    rw [norm_neg, norm_one]
  have hx1 : ‖(x : PadicAlgCl p)‖ ≤ 1 := hxn.trans (pow_le_one₀ hp0.le hp1.le)
  have hxk : ‖(x : PadicAlgCl p)‖ < ‖(c' j : PadicAlgCl p)‖ := hxn.trans_lt hk
  set u : Fin d → OKbar p := Pi.single j x with hu_def
  have hur : ∀ s, ‖(u s : PadicAlgCl p)‖ ≤ ‖(x : PadicAlgCl p)‖ := fun s => by
    rcases eq_or_ne s j with rfl | hs
    · rw [hu_def, Pi.single_eq_same]
    · rw [hu_def, Pi.single_eq_of_ne hs, ZeroMemClass.coe_zero, norm_zero]
      exact norm_nonneg _
  have hu : Small u := fun s => (hur s).trans_lt (hxk.trans_le (hcl j))
  let x0 : F.Pt p := ⟨fun i => incOK L (u i), fun i => by rw [norm_incOK]; exact hu i⟩
  have hx0 : F.coordK x0 = u := F.coordK_eq fun _ => rfl
  refine ⟨x0, ⟨u, fun _ => rfl⟩, ?_⟩
  -- `u^* ω_c = (p^k y) dζ`
  set y : OKbar p := ∑ l, c' l * evK (F.invDiff l j) u with hy
  have hD : D (OL L) (OKbar p) x = ((p : OKbar p) ^ k) • D (OL L) (OKbar p) ζ := by
    rw [hx, D_pow_mul, map_sub, Derivation.map_one_eq_zero, sub_zero]
  have hpb : ∀ l, F.pairing l x0 = evK (F.invDiff l j) u • D (OL L) (OKbar p) x := by
    intro l
    rw [pairing, hx0, pullback, Fintype.sum_eq_single j fun i hi => by
      rw [hu_def, Pi.single_eq_of_ne hi, map_zero, smul_zero], hu_def, Pi.single_eq_same]
  have hsum : ∑ l, c' l • F.pairing l x0 = ((p : OKbar p) ^ k * y) • D (OL L) (OKbar p) ζ := by
    simp_rw [hpb, hD, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [hy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  change ∑ l, c' l • F.pairing l x0 ≠ 0
  rw [hsum]
  -- `|y - c_j| ≤ |x| < |c_j|`, so `|y| ≥ |c_j|`
  have hyc : ‖((y - c' j : OKbar p) : PadicAlgCl p)‖ ≤ ‖(x : PadicAlgCl p)‖ := by
    have e : y - c' j = ∑ l, c' l * (evK (F.invDiff l j) u - if l = j then 1 else 0) := by
      simp only [hy, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e, AddSubmonoidClass.coe_finsetSum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun l _ => ?_
    rw [Subring.coe_mul, norm_mul]
    refine (mul_le_mul_of_nonneg_right (hcl l) (norm_nonneg _)).trans ?_
    rw [one_mul]
    exact F.norm_evK_invDiff_sub_le l j hu (norm_nonneg _) hx1 hur
  have hyn : ‖(c' j : PadicAlgCl p)‖ ≤ ‖(y : PadicAlgCl p)‖ := by
    have h1 : (c' j : PadicAlgCl p) = y - ((y - c' j : OKbar p) : PadicAlgCl p) := by
      rw [AddSubgroupClass.coe_sub]; ring
    have h2 := IsUltrametricDist.norm_add_le_max (y : PadicAlgCl p)
      (-((y - c' j : OKbar p) : PadicAlgCl p))
    rw [← sub_eq_add_neg, ← h1, norm_neg] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · exact absurd (h.trans_lt (hyc.trans_lt hxk)) (lt_irrefl _)
  -- [Fo, Lemme 7]
  rw [Ne, show ζ = zetaK (hε m) from rfl, smul_D_zeta_eq_zero_iff (hε m)]
  intro hle
  have hd := dnorm_bot_cyc (hε m)
  rw [eps_pow hεp m] at hd
  have hn : ‖(((p : OKbar p) ^ k * y : OKbar p) : PadicAlgCl p)‖ =
      ‖(p : PadicAlgCl p)‖ ^ k * ‖(y : PadicAlgCl p)‖ := by
    rw [Subring.coe_mul, norm_mul, SubmonoidClass.coe_pow, Subring.coe_natCast, norm_pow]
  rw [hn] at hle
  have h3 := mul_le_mul_of_nonneg_right hle he0.le
  rw [hd] at h3
  have h4 : ‖(p : PadicAlgCl p)‖ ^ k * ‖(c' j : PadicAlgCl p)‖ * dL L * ‖ε 1 - 1‖ ≤
      ‖(p : PadicAlgCl p)‖ ^ k * ‖(y : PadicAlgCl p)‖ * dL L * ‖ε 1 - 1‖ := by
    gcongr
  have h5 : ‖(p : PadicAlgCl p)‖ ^ (m + 1) ≤ ‖(p : PadicAlgCl p)‖ ^ m :=
    pow_le_pow_of_le_one hp0.le hp1.le m.le_succ
  linarith

end FGL

end PadicHodge
