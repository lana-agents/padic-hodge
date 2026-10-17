/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Galois.Basic
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-!
# The ring of integers `O_{ℂ_p}` as a complete linearly topologised ring

`OC p = {x ∈ ℂ_p | |x| ≤ 1}` (a subring, `ℂ_p` being ultrametric) is complete and linearly
topologised (the balls `{|x| < 1/(n+1)}` are ideals, `ballIdeal`), so power series can be
evaluated at topologically nilpotent points with Mathlib's `MvPowerSeries.eval₂`:

* `isTopologicallyNilpotent_of_norm_lt_one`: `|x| < 1` implies `x` topologically nilpotent;
* `norm_le_of_hasSum`: ultrametric bound for an infinite sum;
* `norm_eval₂_le`: if all monomials of `f` have total degree `≥ k` and `|a_s| ≤ r ≤ 1`, then
  `|f(a)| ≤ r^k`.
-/

noncomputable section

open Topology Filter

namespace PadicHodge

variable (p : ℕ) [hp : Fact p.Prime]

/-- The ring of integers `O_{ℂ_p}`. -/
def OC : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

variable {p}

theorem mem_OC {x : ℂ_[p]} : x ∈ OC p ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem norm_OC_le (x : OC p) : ‖(x : ℂ_[p])‖ ≤ 1 := x.2

theorem isClosed_OC : IsClosed (OC p : Set ℂ_[p]) :=
  isClosed_le continuous_norm continuous_const

instance : CompleteSpace (OC p) := (isClosed_OC (p := p)).completeSpace_coe

instance : IsUniformAddGroup (OC p) := .comap (OC p).subtype

/-- The ideal `{x ∈ O_{ℂ_p} | |x| < 1/(n+1)}`. -/
def ballIdeal (n : ℕ) : Ideal (OC p) where
  carrier := {x | ‖(x : ℂ_[p])‖ < 1 / ((n : ℝ) + 1)}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by
    simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, norm_zero]
    positivity
  smul_mem' := fun c {x} hx => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, norm_mul] at *
    calc ‖(c : ℂ_[p])‖ * ‖(x : ℂ_[p])‖ ≤ 1 * ‖(x : ℂ_[p])‖ :=
          mul_le_mul_of_nonneg_right (norm_OC_le c) (norm_nonneg _)
      _ < 1 / ((n : ℝ) + 1) := by rw [one_mul]; exact hx

theorem hasBasis_ballIdeal :
    (𝓝 (0 : OC p)).HasBasis (fun _ : ℕ => True)
      fun n => ((ballIdeal (p := p) n : Ideal (OC p)) : Set (OC p)) := by
  convert Metric.nhds_basis_ball_inv_nat_succ (x := (0 : OC p)) using 2 with n
  ext x
  simp only [SetLike.mem_coe, Metric.mem_ball, dist_zero_right]
  rfl

instance : IsLinearTopology (OC p) (OC p) :=
  IsLinearTopology.mk_of_hasBasis' (OC p) (S := Ideal (OC p)) hasBasis_ballIdeal
    fun I r _ hm => I.mul_mem_left r hm

theorem isTopologicallyNilpotent_of_norm_lt_one {x : OC p} (hx : ‖(x : ℂ_[p])‖ < 1) :
    IsTopologicallyNilpotent x := by
  unfold IsTopologicallyNilpotent
  rw [tendsto_subtype_rng]
  simp only [SubmonoidClass.coe_pow, ZeroMemClass.coe_zero]
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx

/-- **Ultrametric bound for sums.** -/
theorem norm_le_of_hasSum {ι : Type*} {g : ι → ℂ_[p]} {x : ℂ_[p]} (hg : HasSum g x) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, ‖g i‖ ≤ C) : ‖x‖ ≤ C := by
  have hcl : IsClosed {y : ℂ_[p] | ‖y‖ ≤ C} := isClosed_le continuous_norm continuous_const
  refine hcl.mem_of_tendsto hg (Eventually.of_forall fun s => ?_)
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun i _ => h i

section Eval

open MvPowerSeries

variable {σ : Type*} {R : Type*} [CommRing R] [UniformSpace R]
  [IsUniformAddGroup R] [IsTopologicalSemiring R] {φ : R →+* OC p} (hφ : Continuous φ)
  {a : σ → OC p} (ha : HasEval a)

include hφ ha in
/-- **The value of a power series without monomials of degree `< k` at a point of polyradius
`r ≤ 1` has absolute value `≤ r^k`.** -/
theorem norm_eval₂_le (f : MvPowerSeries σ R) {k : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (har : ∀ s, ‖(a s : ℂ_[p])‖ ≤ r)
    (hf : ∀ m : σ →₀ ℕ, coeff m f ≠ 0 → k ≤ m.degree) :
    ‖((eval₂ φ a f : OC p) : ℂ_[p])‖ ≤ r ^ k := by
  have hs := (hasSum_eval₂ hφ ha f).map (OC p).subtype.toAddMonoidHom continuous_subtype_val
  refine norm_le_of_hasSum hs (pow_nonneg hr0 _) fun m => ?_
  simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    map_mul]
  by_cases hm : coeff m f = 0
  · rw [hm, map_zero, map_zero, zero_mul, norm_zero]; exact pow_nonneg hr0 _
  rw [norm_mul]
  have h1 : ‖(OC p).subtype (φ (coeff m f))‖ ≤ 1 := norm_OC_le _
  have h2 : ‖(OC p).subtype (m.prod fun s e => a s ^ e)‖ ≤ r ^ m.degree := by
    rw [map_finsuppProd, Finsupp.prod, norm_prod, Finsupp.degree_apply,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun s _ => norm_nonneg _) fun s _ => ?_
    rw [map_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (har s) _
  calc ‖(OC p).subtype (φ (coeff m f))‖ * ‖(OC p).subtype (m.prod fun s e => a s ^ e)‖
      ≤ 1 * r ^ m.degree := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ ≤ r ^ k := by rw [one_mul]; exact pow_le_pow_of_le_one hr0 hr1 (hf m hm)

end Eval

end PadicHodge
