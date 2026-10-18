/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.AdicEval
import PadicHodge.FormalGroup.Layers

/-!
# The formal inverse `ι(T)` of a formal group law ([Hong, Lemma 2.2.5 (3)])

For a formal group law `F` of dimension `d` over any commutative ring `R` there is a family
`ι(T)` of power series without constant term with `Φ(T, ι(T)) = 0 = Φ(ι(T), T)`
(`FGL.formalInv`, `addPS_formalInv`, `formalInv_addPS`).

Instead of the degree-by-degree construction of [Hong] we take the `(T)`-adic limit of
`y_0 = 0`, `y_{k+1} = y_k − Φ(T, y_k)`; then `Φ(T, y_k) ∈ (T)^{k+1}` (`addPS_invSeq_mem`) because

* `Φ(T, U) − T − U ∈ (T)(U)` (`Φ_sub_mem`: the coefficients of `Φ` on monomials in `T` alone
  or `U` alone are those of `T` resp. `U`, by the unit axioms and `MvPowerSeries.coeff_subst`);
* substitution is `(T)`-adically continuous (`subst_sub_mem_pow`, from
  `AdicEval.algHom_ext` in `R[[T]]/(T)^m`);
* with `e = Φ(T, y_k)`: `Φ(T, y_k − e) ≡ Φ(T, Φ(y_k, −e)) = Φ(e, −e) ≡ 0 mod (T)^{k+2}`.
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace FGL

variable {R : Type*} [CommRing R] {d : ℕ}

/-- The ideal `I = (t_1, …, t_d)` of `R[[T]]`. -/
abbrev augIdeal (R : Type*) [CommRing R] (σ : Type*) : Ideal (MvPowerSeries σ R) :=
  Ideal.span (Set.range X)

theorem constantCoeff_eq_zero_of_mem {σ : Type*} {f : MvPowerSeries σ R}
    (hf : f ∈ augIdeal R σ) : constantCoeff f = 0 := by
  have : augIdeal R σ ≤ RingHom.ker (constantCoeff (σ := σ) (R := R)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact constantCoeff_X i
  exact this hf

/-- **Substitution is `(T)`-adically continuous.** -/
theorem subst_sub_mem_pow {σ : Type*} [Finite σ] (G : MvPowerSeries σ R)
    {a b : σ → MvPowerSeries (Fin d) R} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) {m : ℕ} (hab : ∀ s, a s - b s ∈ augIdeal R (Fin d) ^ m) :
    G.subst a - G.subst b ∈ augIdeal R (Fin d) ^ m := by
  set I := augIdeal R (Fin d)
  haveI : IsHausdorff (I.map (Ideal.Quotient.mk (I ^ m))) (MvPowerSeries (Fin d) R ⧸ I ^ m) := by
    rw [isHausdorff_iff]
    intro x hx
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero] at hx
    have h : x ∈ (I.map (Ideal.Quotient.mk (I ^ m))) ^ m := hx m
    rw [← Ideal.map_pow, Ideal.map_quotient_self] at h
    simpa using h
  have hA := hasSubst_of_constantCoeff_zero ha
  have hB := hasSubst_of_constantCoeff_zero hb
  have key : (Ideal.Quotient.mkₐ R (I ^ m)).comp (substAlgHom hA) =
      (Ideal.Quotient.mkₐ R (I ^ m)).comp (substAlgHom hB) := by
    refine AdicEval.algHom_ext (I.map (Ideal.Quotient.mk (I ^ m))) (fun s => ?_) fun s => ?_
    · rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hA]
      exact Ideal.mem_map_of_mem _ (mem_span_X (ha s))
    · rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_substAlgHom, coe_substAlgHom, subst_X hA,
        subst_X hB, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
      exact hab s
  have := congrArg (fun φ => φ G) key
  simp only [AlgHom.comp_apply, coe_substAlgHom, Ideal.Quotient.mkₐ_eq_mk] at this
  exact Ideal.Quotient.eq.mp this

/-! ### Coefficients of `Φ` on pure monomials -/

/-- The embedding of the `a`-th copy of the variables. -/
def embCopy (a : Fin 2) : Fin d ↪ Fin 2 × Fin d := ⟨fun j => (a, j), fun _ _ h => by simpa using h⟩

theorem coeff_prod_pairFam (a : Fin 2) (d' : Fin 2 × Fin d →₀ ℕ) (e : Fin d →₀ ℕ) :
    coeff e (d'.prod fun s n =>
      (pairFam (if a = 0 then (fun j => (X j : MvPowerSeries (Fin d) R)) else 0)
        (if a = 0 then 0 else fun j => X j) s) ^ n) =
      if d' = Finsupp.embDomain (embCopy a) e then 1 else 0 := by
  classical
  by_cases hsupp : ∀ s ∈ d'.support, s.1 = a
  · -- `d'` lives on the copy `a`
    set e' : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => d' (a, j)
    have hd : d' = Finsupp.embDomain (embCopy a) e' := by
      ext ⟨b, j⟩
      by_cases hb : b = a
      · subst hb
        have : (b, j) = embCopy b j := rfl
        rw [this, Finsupp.embDomain_apply_self]
        rfl
      · rw [Finsupp.embDomain_notin_range]
        · by_contra h
          exact hb (hsupp _ (Finsupp.mem_support_iff.mpr h))
        · rintro ⟨k, hk⟩
          exact hb (congrArg Prod.fst hk).symm
    have hX : ∀ j : Fin d, pairFam (if a = 0 then (fun j => (X j : MvPowerSeries (Fin d) R))
        else 0) (if a = 0 then 0 else fun j => X j) (embCopy a j) = X j := by
      intro j
      fin_cases a <;> simp [embCopy, pairFam]
    have hmono : (e'.prod fun j n => (X j : MvPowerSeries (Fin d) R) ^ n) = monomial e' 1 := by
      have h := congrArg (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin d) (R := R))
        (MvPolynomial.prod_X_pow_eq_monomial (R := R) (s := e'))
      simp only [map_prod, map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coe_X, MvPolynomial.coe_monomial] at h
      exact h
    have hprod : (d'.prod fun s n =>
        (pairFam (if a = 0 then (fun j => (X j : MvPowerSeries (Fin d) R)) else 0)
          (if a = 0 then 0 else fun j => X j) s) ^ n) = monomial e' 1 := by
      rw [hd, Finsupp.prod_embDomain]
      simp only [hX]
      exact hmono
    have hiff : d' = Finsupp.embDomain (embCopy a) e ↔ e' = e := by
      rw [hd, Finsupp.embDomain_inj]
    rw [hprod, coeff_monomial]
    by_cases h : e' = e
    · rw [if_pos h.symm, if_pos (hiff.mpr h)]
    · rw [if_neg (Ne.symm h), if_neg (fun h' => h (hiff.mp h'))]
  · push Not at hsupp
    obtain ⟨s, hs, hsa⟩ := hsupp
    have h0 : (d'.prod fun s n =>
        (pairFam (if a = 0 then (fun j => (X j : MvPowerSeries (Fin d) R)) else 0)
          (if a = 0 then 0 else fun j => X j) s) ^ n) = 0 := by
      apply Finset.prod_eq_zero hs
      have hz : pairFam (if a = 0 then (fun j => (X j : MvPowerSeries (Fin d) R)) else 0)
          (if a = 0 then 0 else fun j => X j) s = 0 := by
        obtain ⟨b, j⟩ := s
        fin_cases a <;> fin_cases b <;> simp_all [pairFam]
      simp only [hz, zero_pow (Finsupp.mem_support_iff.mp hs)]
    rw [h0, map_zero, if_neg]
    rintro rfl
    rw [Finsupp.support_embDomain, Finset.mem_map] at hs
    obtain ⟨k, -, rfl⟩ := hs
    exact hsa rfl

theorem eq_embDomain (a : Fin 2) (m : Fin 2 × Fin d →₀ ℕ)
    (h : ∀ b l, b ≠ a → m (b, l) = 0) :
    m = Finsupp.embDomain (embCopy a) (Finsupp.equivFunOnFinite.symm fun j => m (a, j)) := by
  ext ⟨b, l⟩
  by_cases hb : b = a
  · subst hb
    have : (b, l) = embCopy b l := rfl
    rw [this, Finsupp.embDomain_apply_self]
    rfl
  · rw [Finsupp.embDomain_notin_range]
    · exact h b l hb
    · rintro ⟨k, hk⟩
      exact hb (congrArg Prod.fst hk).symm

variable (F : FGL R d)

theorem coeff_Φ_embCopy (a : Fin 2) (i : Fin d) (e : Fin d →₀ ℕ) :
    coeff (Finsupp.embDomain (embCopy a) e) (F.Φ i) =
      if e = Finsupp.single i 1 then 1 else 0 := by
  classical
  have hu : (F.Φ i).subst (pairFam (if a = 0 then (fun j => (X j : MvPowerSeries (Fin d) R))
      else 0) (if a = 0 then 0 else fun j => X j)) = X i := by
    fin_cases a
    · simpa using F.unit_right i
    · simpa using F.unit_left i
  have hS : HasSubst (pairFam (if a = 0 then (fun j => (X j : MvPowerSeries (Fin d) R))
      else 0) (if a = 0 then 0 else fun j => X j)) :=
    hasSubst_of_constantCoeff_zero fun s => by
      obtain ⟨b, j⟩ := s
      fin_cases a <;> fin_cases b <;> simp [pairFam]
  have := congrArg (coeff e) hu
  rw [coeff_subst hS, finsum_eq_single _ (Finsupp.embDomain (embCopy a) e)] at this
  · rw [coeff_prod_pairFam, if_pos rfl, smul_eq_mul, mul_one] at this
    rw [this, coeff_X]
  · intro d' hd'
    rw [coeff_prod_pairFam, if_neg hd', smul_zero]

/-- **`Φ(T, U) − T − U ∈ (T)(U)`.** -/
theorem Φ_sub_mem (i : Fin d) :
    F.Φ i - X (0, i) - X (1, i) ∈
      Ideal.span (Set.range (Xv (R := R) (d := d) (n := 2) 0)) *
        Ideal.span (Set.range (Xv (R := R) (d := d) (n := 2) 1)) := by
  classical
  set G := F.Φ i - X (0, i) - X (1, i)
  -- `G` vanishes on monomials of a single copy
  have hG : ∀ (a : Fin 2) (e : Fin d →₀ ℕ), coeff (Finsupp.embDomain (embCopy a) e) G = 0 := by
    intro a e
    simp only [G, map_sub, coeff_Φ_embCopy, coeff_X]
    have h0 : ∀ b : Fin 2, (Finsupp.embDomain (embCopy a) e = Finsupp.single (b, i) 1) ↔
        (a = b ∧ e = Finsupp.single i 1) := by
      intro b
      constructor
      · intro h
        have hb : (b, i) ∈ (Finsupp.embDomain (embCopy a) e).support := by
          rw [h]; simp
        rw [Finsupp.support_embDomain, Finset.mem_map] at hb
        obtain ⟨k, -, hk⟩ := hb
        simp only [embCopy, Function.Embedding.coeFn_mk, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        refine ⟨rfl, ?_⟩
        have : Finsupp.single (a, k) 1 = Finsupp.embDomain (embCopy a) (Finsupp.single k 1) := by
          rw [Finsupp.embDomain_single]; rfl
        rw [this, Finsupp.embDomain_inj] at h
        exact h
      · rintro ⟨rfl, rfl⟩
        rw [Finsupp.embDomain_single]; rfl
    simp only [h0]
    by_cases he : e = Finsupp.single i 1 <;> fin_cases a <;> simp [he]
  -- choose a variable of each copy in mixed monomials
  let ch : (Fin 2 × Fin d →₀ ℕ) → Option (Fin d × Fin d) := fun m =>
    if h : (∃ j, m (0, j) ≠ 0) ∧ ∃ k, m (1, k) ≠ 0 then some (h.1.choose, h.2.choose) else none
  let ej : Fin d → Fin d → (Fin 2 × Fin d →₀ ℕ) := fun j k =>
    Finsupp.single (0, j) 1 + Finsupp.single (1, k) 1
  let g : Fin d → Fin d → MvPowerSeries (Fin 2 × Fin d) R := fun j k m =>
    if ch (m + ej j k) = some (j, k) then coeff (m + ej j k) G else 0
  have hgc : ∀ j k m, coeff m (g j k) =
      if ch (m + ej j k) = some (j, k) then coeff (m + ej j k) G else 0 := fun _ _ _ => rfl
  have key : G = ∑ j, ∑ k, X (0, j) * X (1, k) * g j k := by
    ext m
    simp only [map_sum]
    have hXX : ∀ j k (f : MvPowerSeries (Fin 2 × Fin d) R),
        coeff m (X (0, j) * X (1, k) * f) =
          if ej j k ≤ m then coeff (m - ej j k) f else 0 := by
      intro j k f
      rw [X_def, X_def, monomial_mul_monomial, one_mul, coeff_monomial_mul, one_mul]
    simp only [hXX]
    by_cases hm : (∃ j, m (0, j) ≠ 0) ∧ ∃ k, m (1, k) ≠ 0
    · set j0 := hm.1.choose
      set k0 := hm.2.choose
      have hch : ch m = some (j0, k0) := by
        simp only [ch]
        rw [dif_pos hm]
      have hle0 : ej j0 k0 ≤ m := by
        intro s
        have h1 : m (0, j0) ≠ 0 := hm.1.choose_spec
        have h2 : m (1, k0) ≠ 0 := hm.2.choose_spec
        simp only [ej, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
        by_cases hs1 : (0, j0) = s
        · subst hs1; simp; omega
        · by_cases hs2 : (1, k0) = s
          · subst hs2; simp; omega
          · simp [hs1, hs2]
      rw [Finset.sum_eq_single j0, Finset.sum_eq_single k0]
      · rw [if_pos hle0, hgc, tsub_add_cancel_of_le hle0, if_pos hch]
      · intro k _ hk
        split_ifs with hle
        · rw [hgc, tsub_add_cancel_of_le hle, hch, if_neg]
          intro h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact hk h.2.symm
        · rfl
      · simp
      · intro j _ hj
        refine Finset.sum_eq_zero fun k _ => ?_
        split_ifs with hle
        · rw [hgc, tsub_add_cancel_of_le hle, hch, if_neg]
          intro h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact hj h.1.symm
        · rfl
      · simp
    · -- pure monomial: coefficient `0`, and no `ej j k ≤ m`
      have hall : ∀ j k, ¬ ej j k ≤ m := by
        intro j k hle
        apply hm
        refine ⟨⟨j, ?_⟩, ⟨k, ?_⟩⟩
        · have := hle (0, j); simp [ej] at this; omega
        · have := hle (1, k); simp [ej] at this; omega
      simp only [hall, if_false, Finset.sum_const_zero]
      push Not at hm
      by_cases h0 : ∃ j, m (0, j) ≠ 0
      · have h1 := hm h0
        rw [eq_embDomain 0 m fun b l hb => by
          revert hb; fin_cases b <;> simp [h1], hG]
      · push Not at h0
        rw [eq_embDomain 1 m fun b l hb => by
          revert hb; fin_cases b <;> simp [h0], hG]
  rw [key]
  refine Ideal.sum_mem _ fun j _ => Ideal.sum_mem _ fun k _ => ?_
  rw [mul_assoc]
  exact Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩)
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨k, rfl⟩))

/-- **`Φ(a, b) − a − b ∈ (a)(b)`.** -/
theorem addPS_sub_mem {τ : Type*} [Finite τ] {f g : Fin d → MvPowerSeries τ R}
    (hf : NoConst f) (hg : NoConst g) (i : Fin d) :
    F.addPS f g i - f i - g i ∈ Ideal.span (Set.range f) * Ideal.span (Set.range g) := by
  have hS := hasSubst_pairFam hf hg
  have h := Ideal.mem_map_of_mem (substAlgHom (R := R) hS) (F.Φ_sub_mem i)
  simp only [Ideal.map_mul, Ideal.map_span, map_sub, coe_substAlgHom] at h
  rw [subst_X hS, subst_X hS] at h
  have e0 : (fun a => subst (pairFam f g) a) '' Set.range (Xv (R := R) (d := d) (n := 2) 0) =
      Set.range f := by
    ext x
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Xv, subst_X hS, pairFam_zero]
  have e1 : (fun a => subst (pairFam f g) a) '' Set.range (Xv (R := R) (d := d) (n := 2) 1) =
      Set.range g := by
    ext x
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Xv, subst_X hS, pairFam_one]
  rw [e0, e1, pairFam_zero, pairFam_one] at h
  exact h

/-! ### The iteration -/

/-- `y_0 = 0`, `y_{k+1} = y_k − Φ(T, y_k)`. -/
def invSeq : ℕ → Fin d → MvPowerSeries (Fin d) R
  | 0 => 0
  | k + 1 => fun i => invSeq k i - F.addPS (fun j => X j) (invSeq k) i

theorem noConst_invSeq (k : ℕ) : NoConst (F.invSeq k) := by
  induction k with
  | zero => exact noConst_zero
  | succ k ih =>
    intro i
    simp only [invSeq, map_sub, ih i, F.noConst_addPS noConst_X ih i, sub_zero]

theorem mem_aug_of_noConst {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    f ∈ augIdeal R (Fin d) := mem_span_X hf

theorem span_le_pow {f : Fin d → MvPowerSeries (Fin d) R} {n : ℕ}
    (hf : ∀ j, f j ∈ augIdeal R (Fin d) ^ n) :
    Ideal.span (Set.range f) ≤ augIdeal R (Fin d) ^ n := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact hf j

/-- **`Φ(T, y_k) ∈ (T)^{k+1}`.** -/
theorem addPS_invSeq_mem (k : ℕ) (i : Fin d) :
    F.addPS (fun j => X j) (F.invSeq k) i ∈ augIdeal R (Fin d) ^ (k + 1) := by
  set I := augIdeal R (Fin d)
  induction k generalizing i with
  | zero =>
    rw [invSeq, F.addPS_zero noConst_X, zero_add, pow_one]
    exact Ideal.subset_span ⟨i, rfl⟩
  | succ k ih =>
    set y := F.invSeq k
    set e := F.addPS (fun j => X j) y
    have hy := F.noConst_invSeq k
    have he : NoConst e := F.noConst_addPS noConst_X hy
    have hne : NoConst (-e) := fun j => by simp [he j]
    have hyI : ∀ j, y j ∈ I := fun j => mem_aug_of_noConst (hy j)
    have hneI : ∀ j, (-e) j ∈ I ^ (k + 1) := fun j => by
      simpa using neg_mem (ih j)
    -- `y − e ≡ Φ(y, −e)`
    have h1 : ∀ j, F.invSeq (k + 1) j - F.addPS y (-e) j ∈ I ^ (k + 2) := by
      intro j
      have := F.addPS_sub_mem hy hne j
      have hle : Ideal.span (Set.range y) * Ideal.span (Set.range (-e)) ≤ I ^ (k + 2) := by
        rw [show k + 2 = 1 + (k + 1) by ring, pow_add, pow_one]
        exact Ideal.mul_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hyI j))
          (span_le_pow hneI)
      have h2 := neg_mem (hle this)
      convert h2 using 1
      simp only [invSeq, Pi.neg_apply, y, e]
      ring
    -- `Φ(T, y − e) ≡ Φ(T, Φ(y, −e)) = Φ(e, −e)`
    have hc := subst_sub_mem_pow (F.Φ i) (a := pairFam (fun j => X j) (F.invSeq (k + 1)))
      (b := pairFam (fun j => X j) (F.addPS y (-e)))
      (fun s => by
        obtain ⟨b, j⟩ := s
        fin_cases b
        · exact constantCoeff_X j
        · exact F.noConst_invSeq (k + 1) j)
      (fun s => by
        obtain ⟨b, j⟩ := s
        fin_cases b
        · exact constantCoeff_X j
        · exact F.noConst_addPS hy hne j)
      (m := k + 2) (fun s => by
        obtain ⟨b, j⟩ := s
        fin_cases b
        · simp [pairFam]
        · exact h1 j)
    have hassoc : F.addPS (fun j => X j) (F.addPS y (-e)) = F.addPS e (-e) :=
      (F.addPS_assoc noConst_X hy hne).symm
    have h3 : F.addPS e (-e) i ∈ I ^ (k + 2) := by
      have := F.addPS_sub_mem he hne i
      have hle : Ideal.span (Set.range e) * Ideal.span (Set.range (-e)) ≤ I ^ (k + 2) := by
        calc Ideal.span (Set.range e) * Ideal.span (Set.range (-e)) ≤
            I ^ (k + 1) * I ^ (k + 1) := Ideal.mul_mono (span_le_pow ih) (span_le_pow hneI)
          _ = I ^ (k + 1 + (k + 1)) := (pow_add _ _ _).symm
          _ ≤ I ^ (k + 2) := Ideal.pow_le_pow_right (by omega)
      have h4 := hle this
      have : F.addPS e (-e) i = (F.addPS e (-e) i - e i - (-e) i) := by
        simp only [Pi.neg_apply]; ring
      rw [this]
      exact h4
    have : F.addPS (fun j => X j) (F.invSeq (k + 1)) i =
        (F.addPS (fun j => X j) (F.invSeq (k + 1)) i -
          F.addPS (fun j => X j) (F.addPS y (-e)) i) + F.addPS e (-e) i := by
      rw [hassoc]; ring
    rw [this]
    exact Ideal.add_mem _ hc h3

theorem invSeq_sub_mem {m n : ℕ} (hmn : m ≤ n) (i : Fin d) :
    F.invSeq m i - F.invSeq n i ∈ augIdeal R (Fin d) ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have h : F.invSeq n i - F.invSeq (n + 1) i ∈ augIdeal R (Fin d) ^ m := by
      simp only [invSeq, sub_sub_cancel]
      exact Ideal.pow_le_pow_right (by omega) (F.addPS_invSeq_mem n i)
    have := Ideal.add_mem _ ih h
    rwa [sub_add_sub_cancel] at this

/-- **The formal inverse exists** ([Hong, Lemma 2.2.5 (3)]). -/
theorem exists_formalInv : ∃ ι : Fin d → MvPowerSeries (Fin d) R,
    NoConst ι ∧ F.addPS (fun j => X j) ι = 0 := by
  set I := augIdeal R (Fin d)
  have hP : IsPrecomplete I (MvPowerSeries (Fin d) R) := inferInstance
  have hH : IsHausdorff I (MvPowerSeries (Fin d) R) := inferInstance
  rw [isPrecomplete_iff] at hP
  rw [isHausdorff_iff] at hH
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, sub_zero] at hP hH
  choose ι hι using fun i => hP (fun k => F.invSeq k i) fun hmn => F.invSeq_sub_mem hmn i
  have hnc : NoConst ι := fun i => by
    have h := constantCoeff_eq_zero_of_mem (by simpa using hι i 1)
    rw [map_sub, F.noConst_invSeq 1 i, zero_sub, neg_eq_zero] at h
    exact h
  refine ⟨ι, hnc, funext fun i => hH _ fun n => ?_⟩
  have hc := subst_sub_mem_pow (F.Φ i) (a := pairFam (fun j => X j) ι)
    (b := pairFam (fun j => X j) (F.invSeq n))
    (fun s => by
      obtain ⟨b, j⟩ := s
      fin_cases b
      · exact constantCoeff_X j
      · exact hnc j)
    (fun s => by
      obtain ⟨b, j⟩ := s
      fin_cases b
      · exact constantCoeff_X j
      · exact F.noConst_invSeq n j)
    (m := n) (fun s => by
      obtain ⟨b, j⟩ := s
      fin_cases b
      · simp [pairFam]
      · have := neg_mem (hι j n)
        simpa [pairFam] using this)
  have h2 := Ideal.pow_le_pow_right (Nat.le_succ n) (F.addPS_invSeq_mem n i)
  have := Ideal.add_mem _ hc h2
  simp only [addPS] at this ⊢
  rwa [sub_add_cancel] at this

/-- **The formal inverse `ι(T)`.** -/
def formalInv : Fin d → MvPowerSeries (Fin d) R := F.exists_formalInv.choose

theorem noConst_formalInv : NoConst F.formalInv := F.exists_formalInv.choose_spec.1

/-- `Φ(T, ι(T)) = 0`. -/
theorem addPS_formalInv : F.addPS (fun j => X j) F.formalInv = 0 :=
  F.exists_formalInv.choose_spec.2

/-- `Φ(ι(T), T) = 0`. -/
theorem formalInv_addPS : F.addPS F.formalInv (fun j => X j) = 0 := by
  rw [F.addPS_comm F.noConst_formalInv noConst_X, addPS_formalInv]

end FGL

end PadicHodge
