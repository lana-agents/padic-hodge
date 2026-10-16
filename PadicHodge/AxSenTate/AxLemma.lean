/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Galois.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Ax's lemma: one step

Let `L` be an intermediate field of `ℚ̄_p / ℚ_p` and `α ∈ ℚ̄_p` with `‖σ α - α‖ ≤ c` for all
`σ ∈ G_L`. Let `P` be the minimal polynomial of `α` over `L`, of degree `n`, and `0 ≤ d < n`.
The Hasse derivative `Q = P^{(d)}/d!` has coefficients in `L`, degree `n - d`, leading coefficient
`binom(n, d)`, and `Q(α)` is the coefficient of `X^d` in `P(X + α) = ∏ (X - (σ_i α - α))`, so
`‖Q(α)‖ ≤ c^{n-d}`. Hence some root `β` of `Q` satisfies
`‖binom(n,d)‖ * ‖α - β‖^{n-d} ≤ c^{n-d}`; its degree over `L` is at most `n - d`.

This is the inductive step of the proof of Ax's lemma ([BC, proof of Prop. 2.1.2], quoting
[Ax, Prop. 1]; see `Blueprint.md`).
-/

noncomputable section

open Polynomial

namespace PadicHodge

section Ultra

variable {F : Type*} [NormedField F]

theorem norm_multiset_sum_le_of_forall_le [IsUltrametricDist F] (m : Multiset F) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ x ∈ m, ‖x‖ ≤ C) : ‖m.sum‖ ≤ C := by
  induction m using Multiset.induction_on with
  | empty => simpa using hC
  | cons a m ih =>
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Multiset.mem_cons_self a m))
        (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)))

theorem norm_multiset_prod_le_pow_card (m : Multiset F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ m, ‖x‖ ≤ C) : ‖m.prod‖ ≤ C ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a m))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _) hC

theorem pow_card_le_norm_multiset_prod (m : Multiset F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ m, C ≤ ‖x‖) : C ^ Multiset.card m ≤ ‖m.prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
    exact mul_le_mul (h a (Multiset.mem_cons_self a m))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (pow_nonneg hC _) (norm_nonneg _)

theorem norm_esymm_le [IsUltrametricDist F] (s : Multiset F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ s, ‖x‖ ≤ C) (j : ℕ) : ‖s.esymm j‖ ≤ C ^ j := by
  unfold Multiset.esymm
  refine norm_multiset_sum_le_of_forall_le _ (pow_nonneg hC _) fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨hts, htj⟩ := Multiset.mem_powersetCard.mp ht
  rw [← htj]
  exact norm_multiset_prod_le_pow_card t hC fun y hy => h y (Multiset.mem_of_le hts hy)

/-- The coefficients of `∏ (X - r)` with all `‖r‖ ≤ C` satisfy `‖a_k‖ ≤ C^{n-k}`. -/
theorem norm_coeff_prod_X_sub_C_le [IsUltrametricDist F] (s : Multiset F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ s, ‖x‖ ≤ C) {k : ℕ} (hk : k ≤ Multiset.card s) :
    ‖((s.map fun t => X - Polynomial.C t).prod).coeff k‖ ≤ C ^ (Multiset.card s - k) := by
  rw [Multiset.prod_X_sub_C_coeff s hk, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_esymm_le s hC h _

end Ultra

variable {p : ℕ} [hp : Fact p.Prime]



variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

instance : Algebra.IsAlgebraic L (PadicAlgCl p) := Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) L


/-- Every root of the minimal polynomial of `α` over `L` is a Galois conjugate of `α`. -/
theorem exists_gal_apply_eq_of_aeval_eq_zero {α β : PadicAlgCl p} (hβ : aeval β (minpoly L α) = 0) :
    ∃ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, σ α = β := by
  have h := minpoly.eq_of_root (Algebra.IsAlgebraic.isAlgebraic (R := L) α) hβ
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := L) (E := PadicAlgCl p)).mp h
  exact ⟨σ, hσ⟩

variable {L}

theorem norm_sub_le_of_root {α r : PadicAlgCl p} {c : ℝ}
    (hα : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ‖σ α - α‖ ≤ c)
    (hr : r ∈ ((minpoly L α).map (algebraMap L (PadicAlgCl p))).roots) : ‖r - α‖ ≤ c := by
  have hP : (minpoly L α).map (algebraMap L (PadicAlgCl p)) ≠ 0 :=
    (Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)))
  rw [mem_roots hP, IsRoot.def, eval_map_algebraMap] at hr
  obtain ⟨σ, rfl⟩ := exists_gal_apply_eq_of_aeval_eq_zero L hr
  exact hα σ

theorem hasseDeriv_map_algebraMap (f : L[X]) (d : ℕ) :
    (hasseDeriv d f).map (algebraMap L (PadicAlgCl p)) =
      hasseDeriv d (f.map (algebraMap L (PadicAlgCl p))) := by
  ext n
  simp [hasseDeriv_coeff, coeff_map]

/-- The value at `α` of the `d`-th Hasse derivative of the minimal polynomial of `α` is bounded
by `c^{n-d}` if all conjugates of `α` lie within `c` of `α`. -/
theorem norm_eval_hasseDeriv_minpoly_le {α : PadicAlgCl p} {c : ℝ} (hc : 0 ≤ c)
    (hα : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ‖σ α - α‖ ≤ c) {d : ℕ}
    (hd : d ≤ (minpoly L α).natDegree) :
    ‖(hasseDeriv d ((minpoly L α).map (algebraMap L (PadicAlgCl p)))).eval α‖ ≤
      c ^ ((minpoly L α).natDegree - d) := by
  set P := (minpoly L α).map (algebraMap L (PadicAlgCl p)) with hPdef
  have hmon : P.Monic := (minpoly.monic (Algebra.IsIntegral.isIntegral α)).map _
  have hspl : P.Splits := IsAlgClosed.splits P
  have hdeg : P.natDegree = (minpoly L α).natDegree := natDegree_map _
  have hcard : Multiset.card P.roots = (minpoly L α).natDegree := by
    rw [← hspl.natDegree_eq_card_roots, hdeg]
  have htay : taylor α P =
      ((P.roots.map fun r => r - α).map fun t => X - Polynomial.C t).prod := by
    conv_lhs => rw [hspl.eq_prod_roots_of_monic hmon]
    rw [← taylorAlgHom_apply, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r _ => ?_
    simp only [Function.comp_apply, taylorAlgHom_apply, map_sub, taylor_X, taylor_C, map_sub]
    ring
  rw [← taylor_coeff, htay]
  have := norm_coeff_prod_X_sub_C_le (P.roots.map fun r => r - α) hc
    (fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact norm_sub_le_of_root hα hr)
    (k := d) (by rw [Multiset.card_map, hcard]; exact hd)
  rwa [Multiset.card_map, hcard] at this

/-- **One step of Ax's argument.** If all conjugates of `α` over `L` lie within `c` of `α` and
`d < n = [L(α) : L]`, then there is `β` of degree `≤ n - d` over `L` with
`‖binom(n, d)‖ * ‖α - β‖^{n-d} ≤ c^{n-d}`. -/
theorem exists_root_hasseDeriv {α : PadicAlgCl p} {c : ℝ} (hc : 0 ≤ c)
    (hα : ∀ σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p, ‖σ α - α‖ ≤ c) {d : ℕ}
    (hd : d < (minpoly L α).natDegree) :
    ∃ β : PadicAlgCl p, (minpoly L β).natDegree ≤ (minpoly L α).natDegree - d ∧
      ‖(((minpoly L α).natDegree.choose d : ℕ) : PadicAlgCl p)‖ *
        ‖α - β‖ ^ ((minpoly L α).natDegree - d) ≤ c ^ ((minpoly L α).natDegree - d) := by
  set n := (minpoly L α).natDegree with hn
  set Q : L[X] := hasseDeriv d (minpoly L α) with hQ
  set Qm := Q.map (algebraMap L (PadicAlgCl p)) with hQm
  have hmon : (minpoly L α).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral α)
  have hQm' : Qm = hasseDeriv d ((minpoly L α).map (algebraMap L (PadicAlgCl p))) :=
    hasseDeriv_map_algebraMap _ d
  have hQdeg : Q.natDegree = n - d := natDegree_hasseDeriv _ _
  have hQmdeg : Qm.natDegree = n - d := by rw [hQm, natDegree_map, hQdeg]
  have hlc : Qm.leadingCoeff = ((n.choose d : ℕ) : PadicAlgCl p) := by
    have h1 : (minpoly L α).coeff n = 1 := hmon.coeff_natDegree
    rw [leadingCoeff, hQmdeg, hQm', hasseDeriv_coeff, coeff_map, Nat.sub_add_cancel hd.le,
      h1, map_one, mul_one]
  have hchoose : ((n.choose d : ℕ) : PadicAlgCl p) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hd.le).ne'
  have hQm0 : Qm ≠ 0 := by
    intro h; rw [h, leadingCoeff_zero] at hlc; exact hchoose hlc.symm
  have hspl : Qm.Splits := IsAlgClosed.splits Qm
  have hcard : Multiset.card Qm.roots = n - d := by rw [← hspl.natDegree_eq_card_roots, hQmdeg]
  have hne : Qm.roots ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hcard; omega
  obtain ⟨β, hβ, hmin⟩ := Multiset.exists_min_image (fun b => ‖α - b‖) hne
  refine ⟨β, ?_, ?_⟩
  · have hβQ : aeval β Q = 0 := by
      rw [mem_roots hQm0, IsRoot.def, hQm, eval_map_algebraMap] at hβ
      exact hβ
    have hQ0 : Q ≠ 0 := fun h => hQm0 (by rw [hQm, h, Polynomial.map_zero])
    rw [← hQdeg]
    exact natDegree_le_of_dvd (minpoly.dvd L β hβQ) hQ0
  · have heval := hspl.eval_eq_prod_roots α
    rw [hlc] at heval
    have hb := norm_eval_hasseDeriv_minpoly_le hc hα hd.le
    rw [← hQm', heval, norm_mul] at hb
    refine le_trans ?_ hb
    have := pow_card_le_norm_multiset_prod (Qm.roots.map fun b => α - b) (norm_nonneg (α - β))
      (fun x hx => by
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
        exact hmin b hb)
    rw [Multiset.card_map, hcard] at this
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

end PadicHodge
