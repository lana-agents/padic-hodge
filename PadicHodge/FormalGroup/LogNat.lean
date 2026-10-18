/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.FGLHomPoints
import PadicHodge.FormalGroup.Filtration

/-!
# Naturality of the logarithm

For a homomorphism of formal group laws `f : F → F'` with differential
`df = (∂f_k/∂T_j(0))_{k,j}` (`FGL.Hom.dmat`):

**`log_{F'}(f(x)) = df · log_F(x)`** (`logF_ptMap`) for all `x ∈ F(m_{ℂ_p})`.

This is the commutativity of the right square in [Hong, Prop. 3.4.9, proof] ("the logarithm
map yields a natural transformation between the functor of `O_{C_K}`-valued formal points and
the functor of tangent space"). Proof: both sides are additive in `x`; on the polydisc of
radius `s ≤ |p|` they differ by at most `s²/|p|` (`norm_logF_sub_le`, and
`|f(y) − df·y| ≤ s²` since `f − df·T` has no monomials of degree `< 2`); and `p^n x` has radius
`≤ |p|^{n−N+1}` for large `n` (`exists_bnd_pow`), so `|p|^n |D(x)| ≤ |p|^{2(n−N)+1}` for the
difference `D`.
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

namespace FGL.Hom

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d d' : ℕ} {F : FGL R d} {F' : FGL R d'}
  (φ : FGL.Hom F F')

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] hp in
/-- The differential `∂f_k/∂T_j(0)`. -/
def dmat (k : Fin d') (j : Fin d) : R := coeff (Finsupp.single j 1) (φ.f k)

/-- The linear part `∑_j (∂f_k/∂T_j(0)) T_j`. -/
def linPart (k : Fin d') : MvPowerSeries (Fin d) R := ∑ j, C (φ.dmat k j) * X j

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] hp in
theorem coeff_linPart (k : Fin d') (m : Fin d →₀ ℕ) :
    coeff m (φ.linPart k) = ∑ j, if m = Finsupp.single j 1 then φ.dmat k j else 0 := by
  classical
  rw [linPart, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, coeff_X]
  split_ifs <;> simp

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] hp in
/-- `f_k − df_k · T` has no monomials of degree `< 2`. -/
theorem two_le_degree (k : Fin d') (m : Fin d →₀ ℕ) (hm : coeff m (φ.f k - φ.linPart k) ≠ 0) :
    2 ≤ m.degree := by
  classical
  by_contra hlt
  apply hm
  rw [map_sub, coeff_linPart]
  rcases Nat.lt_succ_iff.mp (not_le.mp hlt) |>.lt_or_eq with h0 | h1
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    subst hm0
    rw [coeff_zero_eq_constantCoeff_apply, φ.noConst k, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun j _ => if_neg fun h => ?_
    have := congrArg (fun m : Fin d →₀ ℕ => m j) h
    simp at this
  · obtain ⟨j0, rfl⟩ := Finsupp.eq_single_of_degree_eq_one m h1
    rw [Finset.sum_eq_single j0 (fun j _ hj => if_neg fun h => hj ?_) (by simp), if_pos rfl,
      dmat, sub_self]
    have := congrArg (fun m : Fin d →₀ ℕ => m j) h
    simp only [Finsupp.single_eq_same] at this
    by_contra hne
    rw [Finsupp.single_eq_of_ne hne] at this
    exact zero_ne_one this

/-- `c_{kj} = ∂f_k/∂T_j(0) ∈ ℂ_p`. -/
abbrev dC (k : Fin d') (j : Fin d) : ℂ_[p] := ((algebraMap R (OC p) (φ.dmat k j) : OC p) : ℂ_[p])

omit [UniformSpace R] [DiscreteUniformity R] in
theorem norm_dC_le (k : Fin d') (j : Fin d) : ‖φ.dC (p := p) k j‖ ≤ 1 :=
  (algebraMap R (OC p) (φ.dmat k j)).2

/-- `|f(y) − df·y| ≤ s²` on the polydisc of radius `s ≤ 1`. -/
theorem norm_ptMap_sub_le {y : F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : F.Bnd y s)
    (k : Fin d') :
    ‖(((φ.ptMap y).1 k : OC p) : ℂ_[p]) - ∑ j, φ.dC (p := p) k j * ((y.1 j : OC p) : ℂ_[p])‖ ≤
      s ^ 2 := by
  have hE := hasEval_of_norm_lt_one y.2
  have e : (((φ.ptMap y).1 k : OC p) : ℂ_[p]) - ∑ j, φ.dC (p := p) k j * ((y.1 j : OC p) : ℂ_[p]) =
      ((eval₂ (algebraMap R (OC p)) y.1 (φ.f k - φ.linPart k) : OC p) : ℂ_[p]) := by
    rw [← coe_eval₂Hom continuous_algebraMap_OC hE, map_sub, linPart, map_sum]
    simp only [map_mul, coe_eval₂Hom, eval₂_C, eval₂_X]
    rw [ptMap_val, ev]
    push_cast
    rfl
  rw [e]
  exact norm_eval₂_le continuous_algebraMap_OC hE _ hs0 hs1 hy (φ.two_le_degree k)

theorem bnd_ptMap {y : F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy : F.Bnd y s) :
    F'.Bnd (φ.ptMap y) s := fun k => by
  have := norm_eval₂_le continuous_algebraMap_OC (hasEval_of_norm_lt_one y.2) (φ.f k)
    (k := 1) hs0 hs1 hy fun m hm => by
      by_contra h0
      have hm0 : m = 0 := by
        rw [not_le, Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at h0
        exact h0
      rw [hm0, coeff_zero_eq_constantCoeff_apply, φ.noConst k] at hm
      exact hm rfl
  rw [pow_one] at this
  exact this

/-- The defect `log_{F'}(f(x)) − df · log_F(x)`. -/
def defect (k : Fin d') (x : F.Pt p) : ℂ_[p] :=
  F'.logF (φ.ptMap x) k - ∑ j, φ.dC k j * F.logF x j

theorem defect_nsmul (k : Fin d') (n : ℕ) (x : F.Pt p) :
    φ.defect k (n • x) = n * φ.defect k x := by
  rw [defect, defect, ← ptHom_apply, map_nsmul, F'.logF_nsmul, ptHom_apply]
  simp only [F.logF_nsmul, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The local estimate** `|D(y)| ≤ s²/|p|` on the polydisc of radius `s ≤ |p|`. -/
theorem norm_defect_le {y : F.Pt p} {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ np p) (hy : F.Bnd y s)
    (k : Fin d') : ‖φ.defect k y‖ ≤ s ^ 2 / np p := by
  have hs1 : s ≤ 1 := hs.trans np_le_one
  have hnp := np_pos (p := p)
  have hC : 0 ≤ s ^ 2 / np p := by positivity
  have h2 : s ^ 2 ≤ s ^ 2 / np p := le_div_self (sq_nonneg s) hnp np_le_one
  have ha := F'.norm_logF_sub_le hs0 hs (φ.bnd_ptMap hs0 hs1 hy) k
  have hb := (φ.norm_ptMap_sub_le hs0 hs1 hy k).trans h2
  have hc : ‖∑ j, φ.dC k j * ((y.1 j : OC p) : ℂ_[p]) - ∑ j, φ.dC k j * F.logF y j‖ ≤
      s ^ 2 / np p := by
    rw [← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun j _ => ?_
    rw [← mul_sub, norm_mul, norm_sub_rev]
    exact (mul_le_of_le_one_left (norm_nonneg _) (φ.norm_dC_le k j)).trans
      (F.norm_logF_sub_le hs0 hs hy j)
  have e : φ.defect k y = (F'.logF (φ.ptMap y) k - (φ.ptMap y).1 k) +
      ((((φ.ptMap y).1 k : OC p) : ℂ_[p]) - ∑ j, φ.dC (p := p) k j * ((y.1 j : OC p) : ℂ_[p])) +
      (∑ j, φ.dC k j * ((y.1 j : OC p) : ℂ_[p]) - ∑ j, φ.dC k j * F.logF y j) := by
    rw [defect]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)) hc)

/-- **Naturality of the logarithm**: `log_{F'}(f(x)) = df · log_F(x)`. -/
theorem logF_ptMap (x : F.Pt p) (k : Fin d') :
    F'.logF (φ.ptMap x) k = ∑ j, φ.dC k j * F.logF x j := by
  rw [← sub_eq_zero]
  change φ.defect k x = 0
  obtain ⟨N, hN⟩ := F.exists_bnd_pow x
  have hnp := np_pos (p := p)
  have key : ∀ m : ℕ, np p ^ N * ‖φ.defect k x‖ ≤ np p ^ (m + 2) := by
    intro m
    have hb := hN (N + (m + 1)) (by omega)
    rw [show N + (m + 1) - N + 1 = m + 2 by omega] at hb
    have hs : np p ^ (m + 2) ≤ np p := pow_le_of_le_one hnp.le np_le_one (by omega)
    have h := φ.norm_defect_le (pow_nonneg hnp.le _) hs hb k
    rw [φ.defect_nsmul, norm_mul, Nat.cast_pow, norm_pow] at h
    have e : (np p ^ (m + 2)) ^ 2 / np p = np p ^ (N + (m + 1)) * np p ^ (m + 2) / np p ^ N := by
      field_simp
      ring
    rw [e, le_div_iff₀ (pow_pos hnp N)] at h
    have h' : np p ^ (N + (m + 1)) * (np p ^ N * ‖φ.defect k x‖) ≤
        np p ^ (N + (m + 1)) * np p ^ (m + 2) := by
      calc np p ^ (N + (m + 1)) * (np p ^ N * ‖φ.defect k x‖)
          = np p ^ (N + (m + 1)) * ‖φ.defect k x‖ * np p ^ N := by ring
        _ ≤ _ := h
    exact le_of_mul_le_mul_left h' (pow_pos hnp _)
  have hlim : Tendsto (fun m : ℕ => np p ^ (m + 2)) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hnp.le (np_lt_one (p := p))
    exact this.comp (tendsto_add_atTop_nat 2)
  have h0 : np p ^ N * ‖φ.defect k x‖ ≤ 0 := ge_of_tendsto' hlim key
  have h1 : ‖φ.defect k x‖ ≤ 0 := by
    by_contra hc
    exact absurd h0 (not_le.mpr (mul_pos (pow_pos hnp N) (lt_of_not_ge hc)))
  exact norm_le_zero_iff.mp h1

end FGL.Hom

end PadicHodge
