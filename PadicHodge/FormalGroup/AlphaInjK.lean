/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.InvariantsK
import PadicHodge.FormalGroup.DAlphaInj

/-!
# Injectivity of `α` and `dα` over a finite extension `K'/ℚ_p` ([Hong, Prop. 3.4.9, proof])

The arguments of `AlphaInj.lean` and `DAlphaInj.lean` with `ℚ_p` replaced by a finite extension
`L = K'` of `ℚ_p` inside `ℚ̄_p` and `Γ_{ℚ_p}` by `G_L = Gal(ℚ̄_p/L)`; the coefficients of the
`p`-divisible formal group law `P` over `R` only need to be fixed by `G_L` (`GalFixedOver`,
e.g. `R = O_L`, `galFixedOver_of_mem`):

* `PDivFGL.eq_zero_of_alpha_eq_one_K` ([Hong, Prop. 3.4.9], `K = L`): a `G_L`-invariant point
  `x` of `F(m_{ℂ_p})` with `α(x) = 1` is `0`; the per-`σ` divisibility step
  (`exists_p_nsmul_eq_of_alpha_K`) as in `AlphaInj.lean`, then [Hong, Lemma 3.4.2] over `L`
  (`coord_mem_of_fixed`) and [Hong, Lemma 3.4.3] over `L` (`eq_zero_of_forall_pow_nsmul_mem`);
* `PDivFGL.dalpha_injective_K`: `dα` is injective on `t_G(L) = L^d`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Lemma 3.4.2, Lemma 3.4.3, Prop. 3.4.9.
-/

noncomputable section

open MvPowerSeries IsLocalRing WithConv

namespace PadicHodge

namespace PDivFGL

open FFGroupScheme FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (P : PDivFGL R d p)
  [hC : IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R)

local notation "S" => OCd p

omit hC [UniformSpace R] [DiscreteUniformity R] in
/-- `σ` acts bijectively on `T_p(G^∨)(O_{ℂ_p})` if `σ` fixes the coefficients. -/
theorem galDual_galDual_inv_of (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (h1 : CoeffFixed p R σ) (h2 : CoeffFixed p R σ⁻¹) (y : P.pdivGroup.DualTate S) :
    P.galDual σ h1 (P.galDual σ⁻¹ h2 y) = y := by
  apply Subtype.ext
  funext v
  apply WithConv.ofConv_injective
  ext a
  apply Subtype.ext
  change autCp σ (autCp σ⁻¹ ((OCd.toOC (ofConv (y.1 v) a) : OC p) : ℂ_[p])) =
    ((OCd.toOC (ofConv (y.1 v) a) : OC p) : ℂ_[p])
  rw [autCp_apply, autCp_apply, ← autCpHom_mul, mul_inv_cancel, autCpHom_one]

variable (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1)
  (L : IntermediateField ℚ_[p] (PadicAlgCl p))

include hR in
/-- **Divisibility step over `L`**: a `G_L`-invariant `z ∈ ker α` is `p x'` with `x'`
`G_L`-invariant, `x' ∈ ker α`. -/
theorem exists_p_nsmul_eq_of_alpha_K (hRL : GalFixedOver p R L) (z : P.F.Pt p)
    (hz : ∀ y, P.alpha hpm z y = 1)
    (hfix : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) z = z) :
    ∃ x' : P.F.Pt p, (∀ y, P.alpha hpm x' y = 1) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
        galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x' = x') ∧ p • x' = z := by
  obtain ⟨x'', hx''⟩ := P.exists_p_nsmul_eq hR z
  have hp' : ∀ y, P.alpha hpm x'' y ^ p = 1 := fun y => by
    rw [← alpha_nsmul, hx'', hz]
  obtain ⟨t, ht⟩ := P.exists_torsion_alpha_eq hpm hR x'' hp'
  have hunit : ∀ y, IsUnit (P.alpha hpm t.1 y) := fun y =>
    P.isUnit_alpha_torsion hpm 1 t y
  set x' := x'' - t.1
  have hx' : ∀ y, P.alpha hpm x' y = 1 := fun y => by
    have h := P.alpha_add hpm x' t.1 y
    rw [sub_add_cancel, ← ht y] at h
    exact (hunit y).mul_left_cancel (by rw [mul_one, mul_comm]; exact h.symm.trans (by ring))
  have hpx' : p • x' = z := by
    have ht0 : p • t.1 = 0 := by
      have := t.2
      rwa [FGL.mem_torsionBy, pow_one] at this
    rw [nsmul_sub, ht0, sub_zero, hx'']
  refine ⟨x', hx', fun σ₀ => ?_, hpx'⟩
  have h1 : CoeffFixed p R (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀) := hRL σ₀
  have h2 : CoeffFixed p R (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀)⁻¹ := by
    rw [← map_inv]
    exact hRL σ₀⁻¹
  -- `u = σx' − x'` is `p`-torsion and in `ker α`
  set σ := AlgEquiv.restrictScalarsHom ℚ_[p] σ₀
  set u := galPt σ x' - x'
  have hu : u ∈ P.F.torsionBy (p := p) 1 := by
    rw [FGL.mem_torsionBy, pow_one, nsmul_sub, ← galPt_nsmul_of h1, hpx', hfix σ₀, sub_self]
  have hneg : ∀ y, P.alpha hpm (-x') y = 1 := fun y => by
    have h := P.alpha_add hpm x' (-x') y
    rw [add_neg_cancel, alpha_zero, hx', one_mul] at h
    exact h.symm
  have hσ : ∀ y, P.alpha hpm (galPt σ x') y = 1 := fun y => by
    rw [← P.galDual_galDual_inv_of σ h1 h2 y]
    apply Subtype.ext
    rw [P.alpha_gal σ h1 hpm, hx']
    simp
  have hu0 := P.eq_zero_of_alpha_torsion hpm 1 ⟨u, hu⟩ fun y => by
    change P.alpha hpm (galPt σ x' + -x') y = 1
    rw [alpha_add, hσ, hneg, one_mul]
  exact sub_eq_zero.mp hu0

include hR in
/-- **`α` is injective on `G(O_L)`** ([Hong, Prop. 3.4.9, proof], `K = L` finite over `ℚ_p`):
a point of `F(m_{ℂ_p})` fixed by `Gal(ℚ̄_p/L)` with `α(x) = 1` is `0`. -/
theorem eq_zero_of_alpha_eq_one_K [FiniteDimensional ℚ_[p] L] (hRL : GalFixedOver p R L)
    (x : P.F.Pt p) (hx : ∀ y, P.alpha hpm x y = 1)
    (hfix : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) x = x) : x = 0 := by
  have key : ∀ n : ℕ, ∃ z : P.F.Pt p, (∀ y, P.alpha hpm z y = 1) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
        galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ) z = z) ∧ (p ^ n) • z = x := by
    intro n
    induction n with
    | zero => exact ⟨x, hx, hfix, by rw [pow_zero, one_nsmul]⟩
    | succ n ih =>
      obtain ⟨z, hz, hzfix, hzx⟩ := ih
      obtain ⟨z', hz', hz'fix, hz'z⟩ := P.exists_p_nsmul_eq_of_alpha_K hpm hR L hRL z hz hzfix
      exact ⟨z', hz', hz'fix, by rw [pow_succ', mul_nsmul, hz'z, hzx]⟩
  refine P.F.eq_zero_of_forall_pow_nsmul_mem L fun n => ?_
  obtain ⟨z, -, hzfix, hzx⟩ := key n
  exact ⟨z, fun j => coord_mem_of_fixed P.F L hzfix j, hzx⟩

include hR in
/-- **`dα` is injective on `t_G(L) = L^d`** ([Hong, Prop. 3.4.9, proof], `K = L` finite over
`ℚ_p`); as `dalpha_injective_Qp`. -/
theorem dalpha_injective_K [FiniteDimensional ℚ_[p] L] (hRL : GalFixedOver p R L)
    (z : Fin d → L)
    (h : ∀ y, P.dalpha hpm (fun j => (((z j : L) : PadicAlgCl p) : ℂ_[p])) y = 0) : z = 0 := by
  have hnp := np_pos (p := p)
  set r : ℝ := np p ^ 2
  have hr0 : 0 ≤ r := by positivity
  have hr : r < np p := by
    change np p ^ 2 < np p
    rw [sq]; exact mul_lt_of_lt_one_left hnp np_lt_one
  -- scale `z` into the polydisc of radius `r`
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ j, ‖(((z j : L) : PadicAlgCl p) : ℂ_[p])‖ ≤ M :=
    ⟨∑ j, ‖(((z j : L) : PadicAlgCl p) : ℂ_[p])‖, Finset.sum_nonneg fun j _ => norm_nonneg _,
      fun j => Finset.single_le_sum
        (fun k _ => norm_nonneg (((z k : L) : PadicAlgCl p) : ℂ_[p])) (Finset.mem_univ j)⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (pow_pos hnp 2) (by linarith : 0 < M + 1))
    (np_lt_one (p := p))
  set τ : Fin d → ℂ_[p] := fun j => (p : ℂ_[p]) ^ n * (((z j : L) : PadicAlgCl p) : ℂ_[p])
  have hτ : ∀ j, ‖τ j‖ ≤ r := fun j => by
    change ‖(p : ℂ_[p]) ^ n * _‖ ≤ np p ^ 2
    rw [norm_mul, norm_pow]
    have h1 : np p ^ n * (M + 1) < np p ^ 2 := (lt_div_iff₀ (by linarith)).mp hn
    calc np p ^ n * ‖(((z j : L) : PadicAlgCl p) : ℂ_[p])‖ ≤ np p ^ n * (M + 1) :=
          mul_le_mul_of_nonneg_left ((hM j).trans (by linarith)) (pow_nonneg hnp.le _)
      _ ≤ np p ^ 2 := h1.le
  obtain ⟨x, hxr, hlog⟩ := P.F.exists_logF_eq hr0 hr hτ
  -- `x` is `G_L`-invariant
  have hfix : ∀ σ₀ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p,
      galPt (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀) x = x := fun σ₀ => by
    have hzσ : ∀ i, autCp (AlgEquiv.restrictScalarsHom ℚ_[p] σ₀)
        (((z i : L) : PadicAlgCl p) : ℂ_[p]) = (((z i : L) : PadicAlgCl p) : ℂ_[p]) := fun i => by
      rw [autCp_coe]
      congr 1
      exact σ₀.commutes (z i)
    refine P.F.logF_injOn hr0 hr (fun j => ?_) hxr fun i => ?_
    · rw [galPt_val, norm_autCp]; exact hxr j
    · rw [logF_galPt_of (hRL σ₀), hlog]
      change autCp _ ((p : ℂ_[p]) ^ n * _) = _
      rw [map_mul, map_pow, map_natCast, hzσ]
  -- `α(x) = 1`
  have hα : ∀ y, P.alpha hpm x y = 1 := fun y => by
    set u := (P.charHom hpm y).ptMap (P.toPtS x)
    have hu : (FGL.multiplicative S).Bnd u r :=
      (P.charHom hpm y).bnd_ptMap hr0 (hr.trans np_lt_one).le (P.bnd_toPtS hxr)
    have hlu : ∀ i, (FGL.multiplicative S).logF u i = 0 := fun i => by
      rw [Fin.fin_one_eq_zero i, P.logGm_alpha hpm x y]
      have e : (fun j => P.F.logF x j) = fun j => (p : ℂ_[p]) ^ n *
          (((z j : L) : PadicAlgCl p) : ℂ_[p]) := funext hlog
      rw [e, dalpha_smul, h y, mul_zero]
    have hu0 := (FGL.multiplicative S).eq_zero_of_logF_eq_zero hr0 hr hu hlu
    have key : u.1 0 = P.alpha hpm x y - 1 := P.charHom_ptMap hpm x y
    rw [hu0, FGL.zero_val] at key
    exact sub_eq_zero.mp key.symm
  have hx0 := P.eq_zero_of_alpha_eq_one_K hpm hR L hRL x hα hfix
  funext j
  have := hlog j
  rw [hx0, logF_zero] at this
  have hp0 : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hz : (((z j : L) : PadicAlgCl p) : ℂ_[p]) = 0 :=
    (mul_eq_zero.mp this.symm).resolve_left hp0
  have hz' : ((z j : L) : PadicAlgCl p) = 0 := by
    have hn' := PadicComplex.norm_extends (p := p) ((z j : L) : PadicAlgCl p)
    rw [hz, norm_zero] at hn'
    exact norm_eq_zero.mp hn'.symm
  rw [Pi.zero_apply]
  exact Subtype.ext hz'

end PDivFGL

end PadicHodge
