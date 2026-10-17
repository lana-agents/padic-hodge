/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cyclotomic.Solve

/-!
# The decomposition `\hat{ℚ_p(μ_{p^∞})} = (γ - 1)(…) + ℚ_p(μ_{p^n})`

Let `γ` be a Tate generator at level `n ≥ 1`. Tate's normalised trace
`R_n = rtr γ n M : ℚ_p(μ_{p^M}) → ℚ_p(μ_{p^n})` (the composite of the normalised traces of
`Cyclotomic/Core.lean`) does not depend on the level `M` (`rtr_eq_of_le`). With it:

* `norm_le_of_rtr`: `‖y‖ ≤ p^5 ‖(γ y - y) + R_n y‖` on `ℚ_p(μ_{p^M})`, uniformly in `M`;
* `exists_decomp`: every `c` in the closure of `ℚ_p(μ_{p^∞})` in `ℂ_p` is `γ m - m + r` with
  `m` in the closure and `r ∈ ℚ_p(μ_{p^n})`;
* `eq_zero_of_autCp_sub_eq`: if `γ m - m = r` with `m` in the closure and `r ∈ ℚ_p(μ_{p^n})`,
  then `r = 0`.

These are the inputs for `H¹(Γ, \hat{ℚ_p(μ_{p^∞})}) ≅ ℚ_p` ([BC, §14.3], the case `j = 0`).
-/

noncomputable section

open IntermediateField

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

theorem acomp_add_steps (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M s t : ℕ)
    (y : PadicAlgCl p) : acomp γ n M (s + t) y = acomp γ n (M - s) t (acomp γ n M s y) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change tr γ n (M - (s + t + 1)) (acomp γ n M (s + t) y) =
      tr γ n (M - s - (t + 1)) (acomp γ n (M - s) t (acomp γ n M s y))
    rw [ih, show M - s - (t + 1) = M - (s + t + 1) by omega]

theorem acomp_zero (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M t : ℕ) :
    acomp γ n M t 0 = 0 := by
  have := acomp_sub γ n M t 0 0
  rwa [sub_self, sub_self] at this

theorem acomp_add (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M t : ℕ) (y z : PadicAlgCl p) :
    acomp γ n M t (y + z) = acomp γ n M t y + acomp γ n M t z := by
  have h1 := acomp_sub γ n M t y (-z)
  have h2 := acomp_sub γ n M t 0 z
  rw [zero_sub, acomp_zero, zero_sub] at h2
  rw [sub_neg_eq_add, h2, sub_neg_eq_add] at h1
  exact h1

/-- The normalised trace `R_n : ℚ_p(μ_{p^M}) → ℚ_p(μ_{p^n})`. -/
def rtr (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M : ℕ) (y : PadicAlgCl p) : PadicAlgCl p :=
  acomp γ n M (M - n) y

theorem rtr_sub (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M : ℕ) (y z : PadicAlgCl p) :
    rtr γ n M (y - z) = rtr γ n M y - rtr γ n M z := acomp_sub _ _ _ _ _ _

theorem rtr_add (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M : ℕ) (y z : PadicAlgCl p) :
    rtr γ n M (y + z) = rtr γ n M y + rtr γ n M z := acomp_add _ _ _ _ _ _

theorem rtr_smul (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M : ℕ) (c : ℚ_[p])
    (y : PadicAlgCl p) : rtr γ n M (c • y) = c • rtr γ n M y := acomp_smul _ _ _ _ _ _

theorem rtr_comm (γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n M : ℕ) (y : PadicAlgCl p) :
    rtr γ n M (γ y) = γ (rtr γ n M y) := acomp_comm _ _ _ _ _

section

variable {γ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} {n : ℕ} (hγ : IsTateGen γ n) (hn : 1 ≤ n)
include hγ hn

theorem acomp_of_mem_high {M s : ℕ} (hs : n + s ≤ M) {y : PadicAlgCl p}
    (hy : y ∈ cycField p (M - s)) : acomp γ n M s y = y := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change tr γ n (M - (s + 1)) (acomp γ n M s y) = y
    rw [ih (by omega) (cycField_mono (by omega) hy)]
    exact tr_of_mem hγ hn (by omega) hy

theorem rtr_mem {M : ℕ} (hM : n ≤ M) {y : PadicAlgCl p} (hy : y ∈ cycField p M) :
    rtr γ n M y ∈ cycField p n := by
  have := acomp_mem hγ hn (t := M - n) (by omega) hy
  rwa [show M - (M - n) = n by omega] at this

theorem rtr_of_mem {M : ℕ} (hM : n ≤ M) {y : PadicAlgCl p} (hy : y ∈ cycField p n) :
    rtr γ n M y = y :=
  acomp_of_mem_low hγ hn (by omega) hy

/-- The normalised trace does not depend on the level. -/
theorem rtr_eq_of_le {M M' : ℕ} (hM : n ≤ M) (hMM' : M ≤ M') {y : PadicAlgCl p}
    (hy : y ∈ cycField p M) : rtr γ n M' y = rtr γ n M y := by
  unfold rtr
  have hMM : M' - (M' - M) = M := by omega
  have h1 : acomp γ n M' (M' - M) y = y :=
    acomp_of_mem_high hγ hn (by omega) (by rwa [hMM])
  rw [show M' - n = (M' - M) + (M - n) by omega, acomp_add_steps, h1, hMM]

theorem norm_rtr_le {M : ℕ} (hM : n ≤ M) {y : PadicAlgCl p} (hy : y ∈ cycField p M) :
    ‖rtr γ n M y‖ ≤ p * ‖y‖ :=
  norm_acomp_le hγ hn (by omega) hy

theorem rtr_gal {M : ℕ} (hM : n ≤ M) (y : PadicAlgCl p) (hy : y ∈ cycField p M) :
    rtr γ n M (γ y) = rtr γ n M y := by
  rw [rtr_comm, gal_fix_cycField hγ hn (rtr_mem hγ hn hM hy)]

/-- **Uniform estimate** for `y ↦ (γ y - y) + R_n y`. -/
theorem norm_le_of_rtr {M : ℕ} (hM : n ≤ M) {y : PadicAlgCl p} (hy : y ∈ cycField p M) :
    ‖y‖ ≤ (p : ℝ) ^ 5 * ‖(γ y - y) + rtr γ n M y‖ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) ≤ p := by linarith
  set u := (γ y - y) + rtr γ n M y with hu
  have hRy := rtr_mem hγ hn hM hy
  have humem : u ∈ cycField p M :=
    add_mem (sub_mem (gal_mem_cycField γ hy) hy) (cycField_mono hM hRy)
  have hRu : rtr γ n M u = rtr γ n M y := by
    rw [hu, rtr_add, rtr_sub, rtr_gal hγ hn hM y hy, rtr_of_mem hγ hn hM hRy]; abel
  have h1 : ‖rtr γ n M y‖ ≤ p * ‖u‖ := by
    rw [← hRu]; exact norm_rtr_le hγ hn hM humem
  have h2 : ‖γ y - y‖ ≤ p * ‖u‖ := by
    rw [show γ y - y = u - rtr γ n M y by rw [hu]; abel]
    refine (norm_sub_le_max' _ _).trans (max_le ?_ h1)
    exact le_mul_of_one_le_left (norm_nonneg _) hp1
  have h3 : ‖y - rtr γ n M y‖ ≤ (p : ℝ) ^ 5 * ‖u‖ := by
    refine (norm_sub_acomp_le hγ hn (t := M - n) (by omega) hy).trans ?_
    calc (p : ℝ) ^ 4 * ‖γ y - y‖ ≤ (p : ℝ) ^ 4 * (p * ‖u‖) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (p : ℝ) ^ 5 * ‖u‖ := by ring
  have h4 : (p : ℝ) * ‖u‖ ≤ (p : ℝ) ^ 5 * ‖u‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ 5 := pow_le_pow_right₀ hp1 (by norm_num)
  calc ‖y‖ = ‖rtr γ n M y + (y - rtr γ n M y)‖ := by rw [add_sub_cancel]
    _ ≤ max ‖rtr γ n M y‖ ‖y - rtr γ n M y‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le (h1.trans h4) h3

/-- `y ↦ (γ y - y) + R_n y` is surjective on `ℚ_p(μ_{p^M})`. -/
theorem exists_rtr_eq_of_mem {M : ℕ} (hM : n ≤ M) {z : PadicAlgCl p} (hz : z ∈ cycField p M) :
    ∃ m ∈ cycField p M, (γ m - m) + rtr γ n M m = z := by
  haveI := finiteDimensional_cycField (p := p) M
  let T : cycField p M →ₗ[ℚ_[p]] cycField p M :=
    { toFun := fun y => ⟨(γ y - y) + rtr γ n M y,
        add_mem (sub_mem (gal_mem_cycField γ y.2) y.2) (cycField_mono hM (rtr_mem hγ hn hM y.2))⟩
      map_add' := fun y y' => Subtype.ext (by
        simp only [IntermediateField.coe_add, map_add, rtr_add]; abel)
      map_smul' := fun c y => Subtype.ext (by
        simp only [IntermediateField.coe_smul, RingHom.id_apply]
        have h : γ (c • (y : PadicAlgCl p)) = c • γ y := by
          rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]
        rw [h, rtr_smul, smul_add, smul_sub]) }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have h0 : (γ (y : PadicAlgCl p) - y) + rtr γ n M y = 0 := congrArg Subtype.val hy
    have := norm_le_of_rtr hγ hn hM y.2
    rw [h0, norm_zero, mul_zero] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext (norm_le_zero_iff.mp this)
  obtain ⟨m, hm⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨z, hz⟩
  exact ⟨m, m.2, congrArg Subtype.val hm⟩

/-- **Decomposition**: every `c` in the closure of `ℚ_p(μ_{p^∞})` is `γ m - m + r` with `m` in
the closure and `r ∈ ℚ_p(μ_{p^n})`. -/
theorem exists_decomp {c : ℂ_[p]}
    (hc : c ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p])) :
    ∃ m ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]), ∃ r ∈ cycField p n,
      autCp γ m - m + ((r : PadicAlgCl p) : ℂ_[p]) = c := by
  set C : ℝ := (p : ℝ) ^ 5 with hC
  have hC0 : 0 ≤ C := by positivity
  have happrox : ∀ k : ℕ, ∃ M, n ≤ M ∧ ∃ y ∈ cycField p M, dist c (y : ℂ_[p]) < 1 / (k + 1) := by
    intro k
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hc (1 / (k + 1)) (by positivity)
    obtain ⟨a, ha, rfl⟩ := mem_cpSubmodule.mp hb
    obtain ⟨M, hM⟩ := mem_cycFieldInf.mp ha
    exact ⟨max M n, le_max_right _ _, a, cycField_mono (le_max_left _ _) hM, hd⟩
  choose M hM y hy hyd using happrox
  have hsol : ∀ k, ∃ m ∈ cycField p (M k), (γ m - m) + rtr γ n (M k) m = y k := fun k =>
    exists_rtr_eq_of_mem hγ hn (hM k) (hy k)
  choose m hm hmeq using hsol
  have hdist : ∀ k l N, N ≤ k → N ≤ l →
      dist ((m k : PadicAlgCl p) : ℂ_[p]) (m l) ≤ C * (1 / (N + 1)) := by
    intro k l N hk hl
    rw [dist_eq_norm, ← coe_sub_cp, PadicComplex.norm_extends]
    set K := max (M k) (M l) with hK
    have hnK : n ≤ K := le_trans (hM k) (le_max_left _ _)
    have hmk : m k ∈ cycField p K := cycField_mono (le_max_left _ _) (hm k)
    have hml : m l ∈ cycField p K := cycField_mono (le_max_right _ _) (hm l)
    have h1 := norm_le_of_rtr hγ hn hnK (sub_mem hmk hml)
    have h2 : (γ (m k - m l) - (m k - m l)) + rtr γ n K (m k - m l) = y k - y l := by
      rw [rtr_sub, rtr_eq_of_le hγ hn (hM k) (le_max_left _ _) (hm k),
        rtr_eq_of_le hγ hn (hM l) (le_max_right _ _) (hm l), map_sub, ← hmeq k, ← hmeq l]
      abel
    rw [h2] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    rw [← PadicComplex.norm_extends, coe_sub_cp,
      show ((y k : PadicAlgCl p) : ℂ_[p]) - y l = (c - y l) - (c - y k) by ring]
    have hNk : (N : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hNl : (N : ℝ) + 1 ≤ (l : ℝ) + 1 := by
      have : (N : ℝ) ≤ l := by exact_mod_cast hl
      linarith
    have hk' : dist c (y k : ℂ_[p]) ≤ 1 / (N + 1) :=
      (hyd k).le.trans (one_div_le_one_div_of_le (by positivity) hNk)
    have hl' : dist c (y l : ℂ_[p]) ≤ 1 / (N + 1) :=
      (hyd l).le.trans (one_div_le_one_div_of_le (by positivity) hNl)
    rw [dist_eq_norm] at hk' hl'
    exact (norm_sub_le_max_ultra _ _).trans (max_le hl' hk')
  have hcauchy : CauchySeq fun k => ((m k : PadicAlgCl p) : ℂ_[p]) := by
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => C * (1 / ((N : ℝ) + 1))) hdist ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul C
  obtain ⟨mlim, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hmlim : mlim ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p]) :=
    mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      coe_mem_cpSubmodule (mem_cycFieldInf.mpr ⟨M k, hm k⟩))
  have hcont : Continuous fun x : ℂ_[p] => autCp γ x - x :=
    (continuous_autCp γ).sub continuous_id
  have h1 : Filter.Tendsto (fun k => autCp γ ((m k : PadicAlgCl p) : ℂ_[p]) -
      ((m k : PadicAlgCl p) : ℂ_[p])) Filter.atTop (nhds (autCp γ mlim - mlim)) :=
    (hcont.tendsto mlim).comp hlim
  have h2 : Filter.Tendsto (fun k => ((y k : PadicAlgCl p) : ℂ_[p])) Filter.atTop (nhds c) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]; exact (hyd k).le
  -- the `ℚ_p(μ_{p^n})`-components converge
  have e : ∀ k, ((rtr γ n (M k) (m k) : PadicAlgCl p) : ℂ_[p]) =
      ((y k : PadicAlgCl p) : ℂ_[p]) - (autCp γ ((m k : PadicAlgCl p) : ℂ_[p]) -
        ((m k : PadicAlgCl p) : ℂ_[p])) := fun k => by
    rw [autCp_coe, ← coe_sub_cp, ← coe_sub_cp, ← hmeq k, add_sub_cancel_left]
  have h3 : Filter.Tendsto (fun k => ((rtr γ n (M k) (m k) : PadicAlgCl p) : ℂ_[p]))
      Filter.atTop (nhds (c - (autCp γ mlim - mlim))) := by
    simp only [e]; exact h2.sub h1
  haveI := finiteDimensional_cycField (p := p) n
  have hclosed := isClosed_cpSubmodule (L := cycField p n)
  have hr : c - (autCp γ mlim - mlim) ∈ cpSubmodule (cycField p n) :=
    hclosed.mem_of_tendsto h3 (Filter.Eventually.of_forall fun k =>
      coe_mem_cpSubmodule (rtr_mem hγ hn (hM k) (hm k)))
  obtain ⟨r, hrn, hreq⟩ := mem_cpSubmodule.mp hr
  exact ⟨mlim, hmlim, r, hrn, by rw [hreq]; abel⟩

/-- If `γ m - m = r` with `m` in the closure of `ℚ_p(μ_{p^∞})` and `r ∈ ℚ_p(μ_{p^n})`, then
`r = 0`. -/
theorem eq_zero_of_autCp_sub_eq {m : ℂ_[p]}
    (hm : m ∈ closure (cpSubmodule (cycFieldInf p) : Set ℂ_[p])) {r : PadicAlgCl p}
    (hr : r ∈ cycField p n) (h : autCp γ m - m = (r : ℂ_[p])) : r = 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have key : ∀ ε > 0, ‖r‖ ≤ p * ε := by
    intro ε hε
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hm ε hε
    obtain ⟨y0, hy0, rfl⟩ := mem_cpSubmodule.mp hb
    obtain ⟨M0, hM0⟩ := mem_cycFieldInf.mp hy0
    set K := max M0 n with hK
    have hnK : n ≤ K := le_max_right _ _
    have hy : y0 ∈ cycField p K := cycField_mono (le_max_left _ _) hM0
    set e := γ y0 - y0 - r with he
    have hemem : e ∈ cycField p K :=
      sub_mem (sub_mem (gal_mem_cycField γ hy) hy) (cycField_mono hnK hr)
    have hRe : rtr γ n K e = -r := by
      rw [he, rtr_sub, rtr_sub, rtr_gal hγ hn hnK y0 hy, rtr_of_mem hγ hn hnK hr]; abel
    have hne : ‖e‖ < ε := by
      rw [← PadicComplex.norm_extends]
      have e1 : ((e : PadicAlgCl p) : ℂ_[p]) =
          autCp γ ((y0 : ℂ_[p]) - m) - ((y0 : ℂ_[p]) - m) := by
        rw [he, coe_sub_cp, coe_sub_cp, ← autCp_coe, map_sub, ← h]; ring
      rw [e1]
      have hd' : ‖(y0 : ℂ_[p]) - m‖ < ε := by rw [norm_sub_rev, ← dist_eq_norm]; exact hd
      refine lt_of_le_of_lt (norm_sub_le_max_ultra _ _) (max_lt ?_ hd')
      rw [norm_autCp]; exact hd'
    have := norm_rtr_le hγ hn hnK hemem
    rw [hRe, norm_neg] at this
    exact this.trans (mul_le_mul_of_nonneg_left hne.le hp0.le)
  have h0 : ‖r‖ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := key (‖r‖ / (2 * p)) (by positivity)
    rw [show (p : ℝ) * (‖r‖ / (2 * p)) = ‖r‖ / 2 by field_simp] at this
    linarith
  exact norm_le_zero_iff.mp h0

end

end PadicHodge
