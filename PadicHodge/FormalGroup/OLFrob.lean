/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DAlphaHTOL
import PadicHodge.Hilbert90.UnrOver
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.Field

/-!
# Frobenius on `O_L` and on finite étale algebras over a local base

* `norm_coeff_minpoly_le_one`: for `z ∈ ℚ̄_p` with `|z| ≤ 1`, the coefficients of the minimal
  polynomial of `z` over `ℚ_p` have absolute value `≤ 1` (the norm on `ℚ̄_p` is the spectral norm,
  `spectralValue_le_one_iff`); hence `z` is integral over `ℤ_p` (`exists_monic_padicInt`,
  `exists_monic_padicInt_of_mem`, of degree `≤ [L:ℚ_p]` when `z ∈ L`).
* `OL.exists_digits`: every element of the residue field `κ_L` of `O_L` is a root of a nonzero
  polynomial `∑_{i ≤ [L:ℚ_p]} c_i X^i` with digits `c_i ∈ {0, …, p - 1}`;
* **`OL.instFiniteResidueField`**: `κ_L` is finite;
* **`OL.exists_frobenius_period_OL`**: `x^{p^N} ≡ x mod 𝔪_L` for some `N ≥ 1` and all `x ∈ O_L`;
  `OL.frobPeriodicMod`: the same in the form `Hilbert90.FrobPeriodicMod L π_L`;
* **`Hilbert90.exists_frobenius_period_local`**: for a local ring `R` with finite residue field,
  `p ∈ 𝔪_R = (π)`, and a finite free étale `R`-algebra `B`, `b^{p^N} ≡ b mod π B` for some
  `N ≥ 1` (generalising `Hilbert90.exists_frobenius_period`).

Standard arguments, written up here.
-/

noncomputable section

open IsLocalRing Polynomial Module

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Integrality of elements of `ℚ̄_p` of absolute value `≤ 1` -/

/-- The coefficients of the minimal polynomial over `ℚ_p` of `z ∈ ℚ̄_p` with `|z| ≤ 1` have
absolute value `≤ 1`. -/
theorem norm_coeff_minpoly_le_one {z : PadicAlgCl p} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖(minpoly ℚ_[p] z).coeff n‖ ≤ 1 := by
  rw [← PadicAlgCl.spectralNorm_eq] at hz
  exact (spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral z))).mp hz n

/-- `z ∈ ℚ̄_p` with `|z| ≤ 1` is integral over `ℤ_p`, with the degree of its minimal
polynomial. -/
theorem exists_monic_padicInt {z : PadicAlgCl p} (hz : ‖z‖ ≤ 1) :
    ∃ P : ℤ_[p][X], P.Monic ∧ P.natDegree = (minpoly ℚ_[p] z).natDegree ∧ aeval z P = 0 := by
  have hl : minpoly ℚ_[p] z ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, norm_coeff_minpoly_le_one hz n⟩, rfl⟩
  obtain ⟨P, hP, hdeg, hmon⟩ :=
    lifts_and_natDegree_eq_and_monic hl (minpoly.monic (Algebra.IsIntegral.isIntegral z))
  refine ⟨P, hmon, hdeg, ?_⟩
  rw [← aeval_map_algebraMap ℚ_[p], hP, minpoly.aeval]

/-- `z ∈ L` with `|z| ≤ 1` is a root of a monic polynomial over `ℤ_p` of degree `≤ [L:ℚ_p]`. -/
theorem exists_monic_padicInt_of_mem (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] {z : PadicAlgCl p} (hzL : z ∈ L) (hz : ‖z‖ ≤ 1) :
    ∃ P : ℤ_[p][X], P.Monic ∧ P.natDegree ≤ finrank ℚ_[p] L ∧ aeval z P = 0 := by
  obtain ⟨P, hmon, hdeg, hP⟩ := exists_monic_padicInt hz
  refine ⟨P, hmon, ?_, hP⟩
  have h := minpoly.natDegree_le (A := ℚ_[p]) (⟨z, hzL⟩ : L)
  rw [IntermediateField.minpoly_eq] at h
  exact hdeg ▸ h

namespace OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem nrm_eq_norm (x : OL L) : nrm x = ‖algebraMap (OL L) (PadicAlgCl p) x‖ := by
  rw [nrm, ← algebraMap_eq, ← algebraMap_qbar_cp, PadicComplex.norm_extends]

theorem algebraMap_qbar_mem (x : OL L) : algebraMap (OL L) (PadicAlgCl p) x ∈ L :=
  (toL x).2

variable (L) in
/-- The polynomial `∑_{i ≤ n} c_i X^i` over the residue field with digits `c_i ∈ {0, …, p-1}`. -/
def digitPoly {n : ℕ} (c : Fin (n + 1) → Fin p) : (ResidueField (OL L))[X] :=
  ∑ i, C (((c i : ℕ) : ResidueField (OL L))) * X ^ (i : ℕ)

theorem coeff_digitPoly {n : ℕ} (c : Fin (n + 1) → Fin p) (i : Fin (n + 1)) :
    (digitPoly L c).coeff i = ((c i : ℕ) : ResidueField (OL L)) := by
  simp [digitPoly, Fin.val_inj]

variable [FiniteDimensional ℚ_[p] L]

/-- Every residue class of `O_L` is a root of a nonzero digit polynomial of degree
`≤ [L:ℚ_p]`. -/
theorem exists_digits (x : OL L) :
    ∃ c : Fin (finrank ℚ_[p] L + 1) → Fin p,
      digitPoly L c ≠ 0 ∧ (digitPoly L c).IsRoot (residue (OL L) x) := by
  classical
  set n := finrank ℚ_[p] L
  set z := algebraMap (OL L) (PadicAlgCl p) x
  have hz : ‖z‖ ≤ 1 := nrm_eq_norm x ▸ nrm_le_one x
  set m := minpoly ℚ_[p] z
  have hmon : m.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral z)
  have hdeg : m.natDegree ≤ n := by
    have h := minpoly.natDegree_le (A := ℚ_[p]) (⟨z, algebraMap_qbar_mem x⟩ : L)
    rwa [IntermediateField.minpoly_eq] at h
  let a : ℕ → ℤ_[p] := fun i => ⟨m.coeff i, norm_coeff_minpoly_le_one hz i⟩
  let c : Fin (n + 1) → Fin p := fun i => ⟨(a i).zmodRepr, PadicInt.zmodRepr_lt_p _⟩
  refine ⟨c, ?_, ?_⟩
  · intro h0
    have h := coeff_digitPoly (L := L) c ⟨m.natDegree, by omega⟩
    have ha : a m.natDegree = 1 := Subtype.ext hmon.coeff_natDegree
    have h1 : (1 : ℤ_[p]).zmodRepr = 1 := by
      simpa using PadicInt.zmodRepr_natCast_of_lt (p := p) hp.out.one_lt
    simp only [h0, coeff_zero, c, ha, h1, Nat.cast_one] at h
    exact zero_ne_one h
  · have h0 : ∑ i : Fin (n + 1), m.coeff i • z ^ (i : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => m.coeff i • z ^ i), ← aeval_eq_sum_range' (by omega),
        minpoly.aeval]
    rw [IsRoot, digitPoly, eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [← residue_eq_zero_iff (R := OL L) ((∑ i : Fin (n + 1), ((c i : ℕ) : OL L) * x ^ (i : ℕ)))
      |>.mpr ?_]
    · simp [map_sum]
    rw [mem_maximalIdeal_iff, nrm_eq_norm]
    simp only [map_sum, map_mul, map_natCast, map_pow]
    rw [← sub_zero (∑ i : Fin (n + 1), _), ← h0, ← Finset.sum_sub_distrib]
    obtain ⟨i, -, hi⟩ :=
      IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty Finset.univ_nonempty
        (fun i : Fin (n + 1) => ((c i : ℕ) : PadicAlgCl p) * z ^ (i : ℕ) - m.coeff i • z ^ (i : ℕ))
    refine hi.trans_lt ?_
    rw [Algebra.smul_def, ← sub_mul, norm_mul, norm_pow]
    have hzi : ‖z‖ ^ (i : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
    have hd : ‖((c i : ℕ) : PadicAlgCl p) - algebraMap ℚ_[p] (PadicAlgCl p) (m.coeff i)‖ < 1 := by
      have hmem := PadicInt.sub_zmodRepr_mem (a i)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PadicInt.not_isUnit_iff] at hmem
      have e : ((c i : ℕ) : PadicAlgCl p) - algebraMap ℚ_[p] (PadicAlgCl p) (m.coeff i) =
          algebraMap ℚ_[p] (PadicAlgCl p) (-(((a i - (a i).zmodRepr : ℤ_[p])) : ℚ_[p])) := by
        simp [c, a]
      rw [e, norm_algebraMap', norm_neg, ← PadicInt.norm_def]
      exact hmem
    calc _ ≤ ‖((c i : ℕ) : PadicAlgCl p) - algebraMap ℚ_[p] (PadicAlgCl p) (m.coeff i)‖ * 1 :=
          mul_le_mul_of_nonneg_left hzi (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hd

/-- **The residue field of `O_L` is finite.** -/
instance instFiniteResidueField : Finite (ResidueField (OL L)) := by
  classical
  let T : (Fin (finrank ℚ_[p] L + 1) → Fin p) → Set (ResidueField (OL L)) :=
    fun c => {y | digitPoly L c ≠ 0 ∧ (digitPoly L c).IsRoot y}
  have hT : ∀ c, (T c).Finite := fun c => by
    by_cases h : digitPoly L c = 0
    · simp [T, h]
    · exact (finite_setOf_isRoot h).subset fun y hy => hy.2
  have hU : (Set.univ : Set (ResidueField (OL L))) ⊆ ⋃ c, T c := fun y _ => by
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨c, hc⟩ := exists_digits x
    exact Set.mem_iUnion.mpr ⟨c, hc⟩
  exact Set.finite_univ_iff.mp ((Set.finite_iUnion hT).subset hU)

variable (L) in
/-- **Frobenius is periodic on `O_L / 𝔪_L`**: `x^{p^N} ≡ x mod 𝔪_L` for all `x ∈ O_L`. -/
theorem exists_frobenius_period_OL :
    ∃ N, 0 < N ∧ ∀ x : OL L, x ^ (p ^ N) - x ∈ maximalIdeal (OL L) := by
  classical
  letI := Fintype.ofFinite (ResidueField (OL L))
  haveI : CharP (ResidueField (OL L)) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out, ← map_natCast (residue (OL L)),
      residue_eq_zero_iff]
    exact p_mem
  obtain ⟨N, -, hcard⟩ := FiniteField.card (ResidueField (OL L)) p
  refine ⟨N, N.pos, fun x => ?_⟩
  rw [← residue_eq_zero_iff, map_sub, map_pow, ← hcard, FiniteField.pow_card, sub_self]

/-- An element of `L` of absolute value `≤ 1` as an element of `O_L`. -/
def ofL (c : L) (hc : ‖(c : PadicAlgCl p)‖ ≤ 1) : OL L :=
  mk ⟨((c : PadicAlgCl p) : ℂ_[p]), by rw [mem_OC, PadicComplex.norm_extends]; exact hc⟩
    (coe_mem_cpSubmodule c.2)

omit [FiniteDimensional ℚ_[p] L] in
theorem algebraMap_ofL (c : L) (hc : ‖(c : PadicAlgCl p)‖ ≤ 1) :
    algebraMap (OL L) (PadicAlgCl p) (ofL c hc) = c := by
  apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  change ((algebraMap (OL L) (PadicAlgCl p) (ofL c hc) : PadicAlgCl p) : ℂ_[p]) = _
  rw [algebraMap_qbar_cp]
  rfl

omit [FiniteDimensional ℚ_[p] L] in
theorem algebraMap_qbar_eq (x : OL L) :
    algebraMap (OL L) (PadicAlgCl p) x = algebraMap L (PadicAlgCl p) (toL x) := rfl

omit [FiniteDimensional ℚ_[p] L] in
theorem norm_algebraMap_le_one (x : OL L) : ‖algebraMap (OL L) (PadicAlgCl p) x‖ ≤ 1 := by
  rw [← nrm_eq_norm]; exact nrm_le_one x

/-- The uniformiser of `O_L` as an element of `L`. -/
abbrev uniformizerL (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] :
    L := toL (uniformizer L)

theorem norm_uniformizerL_lt_one :
    ‖algebraMap L (PadicAlgCl p) (uniformizerL L)‖ < 1 := by
  rw [← algebraMap_qbar_eq, ← nrm_eq_norm]; exact nrm_uniformizer_lt_one

theorem uniformizerL_ne_zero : uniformizerL L ≠ 0 := by
  intro h
  have h1 : nrm (uniformizer L) = 0 := by
    rw [nrm_eq_norm, algebraMap_qbar_eq]
    change ‖algebraMap L (PadicAlgCl p) (uniformizerL L)‖ = 0
    rw [h, map_zero, norm_zero]
  exact uniformizer_ne_zero (nrm_eq_zero_iff.mp h1)

variable (L) in
/-- **Frobenius is periodic modulo `π_L` on `O_L`**, in the form used by
`Hilbert90.unr_adjoin_over`. -/
theorem frobPeriodicMod : Hilbert90.FrobPeriodicMod (p := p) L (uniformizerL L) := by
  obtain ⟨N, hN, hper⟩ := exists_frobenius_period_OL L
  refine ⟨N, hN, fun c hc => ?_⟩
  have h := hper (ofL c hc)
  rw [maximalIdeal_eq, Ideal.mem_span_singleton'] at h
  obtain ⟨e, he⟩ := h
  refine ⟨toL e, norm_algebraMap_le_one e, ?_⟩
  have h2 := congrArg (algebraMap (OL L) (PadicAlgCl p)) he
  rw [map_mul, map_sub, map_pow, algebraMap_ofL] at h2
  change (c : PadicAlgCl p) ^ (p ^ N) - (c : PadicAlgCl p) = _
  rw [← h2, mul_comm]
  rfl

end OL

namespace Hilbert90

/-- **Frobenius is periodic modulo `π`** on a finite free étale algebra `B` over a local ring
`R` with finite residue field, `p ∈ 𝔪_R = (π)`. -/
theorem exists_frobenius_period_local {R : Type*} [CommRing R] [IsLocalRing R]
    [Finite (ResidueField R)] (hpR : (p : R) ∈ maximalIdeal R) (π : R)
    (hπ : maximalIdeal R = Ideal.span {π}) (B : Type*) [CommRing B] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] [Algebra.Etale R B] :
    ∃ N, 0 < N ∧ ∀ a : B, ∃ b : B, a ^ (p ^ N) - a = algebraMap R B π * b := by
  classical
  set I : Ideal B := (maximalIdeal R).map (algebraMap R B)
  have hI : I = Ideal.span {algebraMap R B π} := by
    simp only [I, hπ, Ideal.map_span, Set.image_singleton]
  have hrad : I.IsRadical :=
    Algebra.FormallyUnramified.isRadical_map_isMaximal R B (maximalIdeal R)
  suffices hQ : ∃ N, 0 < N ∧ ∀ x : B ⧸ I, x ^ (p ^ N) = x by
    obtain ⟨N, hN, hx⟩ := hQ
    refine ⟨N, hN, fun a => ?_⟩
    have := hx (Ideal.Quotient.mk I a)
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, hI,
      Ideal.mem_span_singleton'] at this
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by rw [← hb, mul_comm]⟩
  by_cases hnt : Nontrivial (B ⧸ I)
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact ⟨1, one_pos, fun x => Subsingleton.elim _ _⟩
  have hp0 : ((p : ℕ) : B ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem,
      ← map_natCast (algebraMap R B)]
    exact Ideal.mem_map_of_mem _ hpR
  haveI : CharP (B ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0
  haveI : IsReduced (B ⧸ I) := by
    refine ⟨fun x ⟨n, hn⟩ => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hrad ⟨n, hn⟩
  -- `B / I` is finite
  haveI : Finite (B ⧸ I) := by
    let bA := Module.Free.chooseBasis R B
    let ι := Module.Free.ChooseBasisIndex R B
    let s : ResidueField R → R := Function.surjInv (residue_surjective (R := R))
    let f : (ι → ResidueField R) → B ⧸ I := fun c =>
      Ideal.Quotient.mk I (∑ i, s (c i) • bA i)
    refine Finite.of_surjective f fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    set r := bA.repr a
    refine ⟨fun i => residue R (r i), ?_⟩
    rw [Ideal.Quotient.eq]
    have hsum : ∑ i, r i • bA i = a := bA.sum_repr a
    have hdiff : ∑ i, s (residue R (r i)) • bA i - a =
        ∑ i, algebraMap R B (s (residue R (r i)) - r i) * bA i := by
      rw [← hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_sub, sub_mul]
    change ∑ i, s (residue R (r i)) • bA i - a ∈ I
    rw [hdiff]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub,
      Function.surjInv_eq (residue_surjective (R := R)), sub_self]
  -- Frobenius is a permutation of finite order
  have hinj : Function.Injective (frobenius (B ⧸ I) p) := frobenius_inj _ p
  have hbij : Function.Bijective (frobenius (B ⧸ I) p) := hinj.bijective_of_finite
  let σ : Equiv.Perm (B ⧸ I) := Equiv.ofBijective _ hbij
  obtain ⟨N, hN, hσ⟩ := (isOfFinOrder_of_finite σ).exists_pow_eq_one
  refine ⟨N, hN, fun x => ?_⟩
  have := congrArg (fun g : Equiv.Perm (B ⧸ I) => g x) hσ
  simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq] at this
  rw [← iterate_frobenius]
  exact this

end Hilbert90

end PadicHodge
