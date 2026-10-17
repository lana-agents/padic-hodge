/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.AlmostEtale.Basic

/-!
# Euler's lemma: the trace dual of `O_F[z]`

For `z ∈ ℚ̄_p` with minimal polynomial `g` of degree `d` over `F`, Mathlib's
`Module.Basis.traceDual_powerBasis_eq` computes the trace-dual basis of `1, z, …, z^{d-1}`:
it is `D_i / g'(z)` where `g(X)/(X - z) = ∑ D_i X^i`. In terms of the normalised trace
(`Tr_{F(z)/F} = d · nt_F`):

* `mul_derivative_eq_sum` (expansion in the dual basis): for `y ∈ F(z)`,
  `y g'(z) = ∑_{i<d} Tr(y z^i) D_i`; hence if all `Tr(y z^i) ∈ O_F` then `y g'(z) ∈ O_F[z]`
  (`mul_derivative_mem_adj`);
* `trace_pow_div_derivative` (Euler): `Tr(z^j / g'(z)) = δ_{j, d-1}` for `j < d`; hence
  `Tr(u / g'(z)) ∈ O_F` for `u ∈ O_F[z]` (`trace_div_derivative_mem`).

So the trace dual of `O_F[z]` is `g'(z)^{-1} O_F[z]` (the different of a monogenic order).
-/

noncomputable section

open Polynomial IntermediateField Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K̄" => PadicAlgCl p

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The degree `[F(z) : F]`. -/
abbrev dg (z : PadicAlgCl p) : ℕ := (minpoly F z).natDegree

/-- `g(X) / (X - z)` for the minimal polynomial `g` of `z` over `F`. -/
def mpDiv (z : PadicAlgCl p) : (PadicAlgCl p)[X] := mp F z /ₘ (X - C z)

theorem derivative_mp_ne_zero (z : PadicAlgCl p) : (derivative (mp F z)).eval z ≠ 0 := by
  have hsep : (minpoly F z).Separable := Algebra.IsSeparable.isSeparable F z
  have := hsep.aeval_derivative_ne_zero (minpoly.aeval F z)
  rwa [mp, derivative_map, eval_map_algebraMap]

theorem dg_pos (z : PadicAlgCl p) : 0 < dg F z := minpoly.natDegree_pos (isIntegral_over F z)

theorem finrank_adjoin_eq_dg (z : PadicAlgCl p) : finrank F F⟮z⟯ = dg F z :=
  adjoin.finrank (isIntegral_over F z)

instance (z : PadicAlgCl p) : FiniteDimensional F F⟮z⟯ :=
  adjoin.finiteDimensional (isIntegral_over F z)

/-- `Tr_{F(z)/F} = [F(z) : F] · nt_F` on `F(z)`. -/
theorem coe_trace_adjoin (z : PadicAlgCl p) (y : F⟮z⟯) :
    algebraMap F (PadicAlgCl p) (Algebra.trace F F⟮z⟯ y) =
      (dg F z : PadicAlgCl p) * nt F (algebraMap F⟮z⟯ (PadicAlgCl p) y) := by
  have h1 := Algebra.normalizedTrace_eq_of_finiteDimensional_apply F (K := F⟮z⟯) y
  have h2 := Algebra.normalizedTrace_intermediateField F (PadicAlgCl p) (E := F⟮z⟯) y
  have hd : (finrank F F⟮z⟯ : F) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have h3 : Algebra.trace F F⟮z⟯ y = (finrank F F⟮z⟯ : F) •
      Algebra.normalizedTrace F (PadicAlgCl p) y := by
    rw [h2, h1, smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [h3, nt, smul_eq_mul, finrank_adjoin_eq_dg, map_mul, map_natCast]
  rfl

theorem mpDiv_coeff_mem_adj {z : PadicAlgCl p} (hz : ‖z‖ ≤ 1) (i : ℕ) :
    (mpDiv F z).coeff i ∈ adj (OK F) z := by
  have hX : X - C z ∈ polyOver (adj (OK F) z) :=
    sub_mem (X_mem_polyOver _) (C_mem_polyOver (self_mem_adj _ _))
  have hg : mp F z ∈ polyOver (adj (OK F) z) :=
    polyOver_mono (le_adj _ _) (mp_mem_polyOver F hz)
  exact mem_polyOver.mp (divByMonic_mem_polyOver hg hX (monic_X_sub_C z)).1 i

/-- The image of `minpolyDiv` of the generator of `F⟮z⟯` in `ℚ̄_p[X]` is `mpDiv F z`. -/
theorem map_minpolyDiv_gen (z : PadicAlgCl p) :
    (minpolyDiv F (AdjoinSimple.gen F z)).map (algebraMap F⟮z⟯ (PadicAlgCl p)) = mpDiv F z := by
  rw [minpolyDiv, map_divByMonic _ (monic_X_sub_C _), minpoly_gen, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq, Polynomial.map_sub, map_X, map_C, AdjoinSimple.algebraMap_gen]
  rfl

theorem coe_minpolyDiv_coeff (z : PadicAlgCl p) (i : ℕ) :
    algebraMap F⟮z⟯ (PadicAlgCl p) ((minpolyDiv F (AdjoinSimple.gen F z)).coeff i) =
      (mpDiv F z).coeff i := by
  rw [← map_minpolyDiv_gen F z, coeff_map]

theorem coe_aeval_gen_derivative (z : PadicAlgCl p) :
    algebraMap F⟮z⟯ (PadicAlgCl p)
      (aeval (AdjoinSimple.gen F z) (derivative (minpoly F (AdjoinSimple.gen F z)))) =
      (derivative (mp F z)).eval z := by
  rw [minpoly_gen, mp, derivative_map, eval_map_algebraMap]
  have := aeval_algebraMap_apply (PadicAlgCl p) (AdjoinSimple.gen F z) (derivative (minpoly F z))
  rw [AdjoinSimple.algebraMap_gen] at this
  exact this.symm

theorem mpDiv_coeff_last (z : PadicAlgCl p) : (mpDiv F z).coeff (dg F z - 1) = 1 := by
  have hm := minpolyDiv_monic (R := F) (x := AdjoinSimple.gen F z)
    (Algebra.IsIntegral.isIntegral _)
  have hd := natDegree_minpolyDiv (R := F) (x := AdjoinSimple.gen F z)
  rw [minpoly_gen] at hd
  rw [← coe_minpolyDiv_coeff, show dg F z - 1 = (minpolyDiv F (AdjoinSimple.gen F z)).natDegree
    from hd.symm, coeff_natDegree, hm.leadingCoeff, map_one]

/-- **Expansion in the trace-dual basis.** For `y ∈ F(z)`,
`y g'(z) = ∑_{i<d} Tr(y z^i) D_i` with `g(X)/(X-z) = ∑ D_i X^i`. -/
theorem mul_derivative_eq_sum {z y : PadicAlgCl p} (hy : y ∈ F⟮z⟯) :
    y * (derivative (mp F z)).eval z = ∑ i ∈ Finset.range (dg F z),
      ((dg F z : PadicAlgCl p) * nt F (y * z ^ i)) * (mpDiv F z).coeff i := by
  set pb := adjoin.powerBasis (isIntegral_over F z) with hpb
  set Y : F⟮z⟯ := ⟨y, hy⟩
  have hYy : algebraMap F⟮z⟯ (PadicAlgCl p) Y = y := rfl
  have hgen : pb.gen = AdjoinSimple.gen F z := adjoin.powerBasis_gen _
  have hsum := pb.basis.traceDual.sum_repr Y
  have hg0 := derivative_mp_ne_zero F z
  have hY : y = ∑ i : Fin pb.dim,
      ((dg F z : PadicAlgCl p) * nt F (y * z ^ (i : ℕ))) *
        ((mpDiv F z).coeff i / (derivative (mp F z)).eval z) := by
    calc y = algebraMap F⟮z⟯ (PadicAlgCl p) Y := rfl
      _ = ∑ i : Fin pb.dim, algebraMap F⟮z⟯ (PadicAlgCl p)
            (pb.basis.traceDual.repr Y i • pb.basis.traceDual i) := by
          conv_lhs => rw [← hsum]
          rw [map_sum]
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
            Module.Basis.traceDual_repr_apply, Module.Basis.traceDual_powerBasis_eq,
            Algebra.traceForm_apply, map_div₀, PowerBasis.coe_basis]
          simp only [hgen]
          rw [coe_trace_adjoin, coe_minpolyDiv_coeff, coe_aeval_gen_derivative, map_mul, map_pow,
            hYy, AdjoinSimple.algebraMap_gen]
  have hdim : pb.dim = dg F z := adjoin.powerBasis_dim _
  conv_lhs => rw [hY]
  rw [Finset.sum_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => (dg F z : PadicAlgCl p) * nt F (y * z ^ i) *
    ((mpDiv F z).coeff i / (derivative (mp F z)).eval z) * (derivative (mp F z)).eval z) pb.dim,
    hdim]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- **Euler's lemma.** `Tr_{F(z)/F}(z^j / g'(z)) = δ_{j, d-1}` for `j < d`. -/
theorem trace_pow_div_derivative (z : PadicAlgCl p) {j : ℕ} (hj : j < dg F z) :
    (dg F z : PadicAlgCl p) * nt F (z ^ j / (derivative (mp F z)).eval z) =
      if j = dg F z - 1 then 1 else 0 := by
  set pb := adjoin.powerBasis (isIntegral_over F z) with hpb
  have hgen : pb.gen = AdjoinSimple.gen F z := adjoin.powerBasis_gen _
  have hdim : pb.dim = dg F z := adjoin.powerBasis_dim _
  have hd0 := dg_pos F z
  set last : Fin pb.dim := ⟨dg F z - 1, by omega⟩
  set jj : Fin pb.dim := ⟨j, by omega⟩
  have h := Module.Basis.trace_traceDual_mul pb.basis last jj
  have h2 := congrArg (algebraMap F (PadicAlgCl p)) h
  rw [coe_trace_adjoin] at h2
  rw [Module.Basis.traceDual_powerBasis_eq, PowerBasis.coe_basis] at h2
  simp only [hgen] at h2
  have hc : algebraMap F⟮z⟯ (PadicAlgCl p) ((minpolyDiv F (AdjoinSimple.gen F z)).coeff last /
      aeval (AdjoinSimple.gen F z) (derivative (minpoly F (AdjoinSimple.gen F z))) *
        AdjoinSimple.gen F z ^ (jj : ℕ)) =
      z ^ j / (derivative (mp F z)).eval z := by
    rw [map_mul, map_div₀, coe_minpolyDiv_coeff, coe_aeval_gen_derivative, map_pow,
      AdjoinSimple.algebraMap_gen]
    simp only [last, jj]
    rw [mpDiv_coeff_last]
    ring
  rw [hc] at h2
  rw [h2]
  simp only [last, jj, Fin.ext_iff]
  split_ifs <;> simp

/-- The trace dual of `O_F[z]` contains `g'(z)^{-1} O_F[z]`. -/
theorem trace_div_derivative_mem {z : PadicAlgCl p} (hz : ‖z‖ ≤ 1) {u : PadicAlgCl p}
    (hu : u ∈ adj (OK F) z) :
    (dg F z : PadicAlgCl p) * nt F (u / (derivative (mp F z)).eval z) ∈ OK F := by
  obtain ⟨q, hq, rfl⟩ := mem_adj.mp hu
  have hg := mp_mem_polyOver F hz
  have hm := mp_monic F z
  set r := q %ₘ mp F z with hr
  have hrO : r ∈ polyOver (OK F) := (divByMonic_mem_polyOver hq hg hm).2
  have hrz : q.eval z = r.eval z := by
    have h := modByMonic_add_div q (mp F z)
    have := congrArg (eval z) h
    rw [eval_add, eval_mul, eval_mp, zero_mul, add_zero] at this
    exact this.symm
  have hdeg : r.natDegree < dg F z := by
    change r.natDegree < (minpoly F z).natDegree
    rw [← natDegree_mp]
    refine natDegree_modByMonic_lt _ hm fun h1 => ?_
    have := congrArg natDegree h1
    rw [natDegree_one, natDegree_mp] at this
    have h2 : (minpoly F z).natDegree ≠ 0 := (dg_pos F z).ne'
    omega
  rw [hrz, eval_eq_sum_range' hdeg, Finset.sum_div, nt_sum, Finset.mul_sum]
  refine sum_mem fun j hj => ?_
  rw [mul_div_assoc, nt_mul_left F (mem_polyOver.mp hrO j).1, mul_left_comm,
    trace_pow_div_derivative F z (Finset.mem_range.mp hj)]
  refine mul_mem (mem_polyOver.mp hrO j) ?_
  split_ifs
  · exact one_mem _
  · exact zero_mem _

/-- If `Tr(y z^i) ∈ O_F` for all `i < d`, then `y g'(z) ∈ O_F[z]`. -/
theorem mul_derivative_mem_adj {z y : PadicAlgCl p} (hz : ‖z‖ ≤ 1) (hy : y ∈ F⟮z⟯)
    (h : ∀ i < dg F z, (dg F z : PadicAlgCl p) * nt F (y * z ^ i) ∈ OK F) :
    y * (derivative (mp F z)).eval z ∈ adj (OK F) z := by
  rw [mul_derivative_eq_sum F hy]
  exact sum_mem fun i hi => mul_mem (le_adj _ _ (h i (Finset.mem_range.mp hi)))
    (mpDiv_coeff_mem_adj F hz i)

end PadicHodge
