/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Evaluating power series in adically complete algebras

Let `S` be an `R`-algebra which is complete for an ideal `𝔞` (`IsAdicComplete 𝔞 S`), and let
`s : σ → S` (`σ` finite) with `s i ∈ 𝔞`. Then `f ↦ f(s)` is an `R`-algebra map
`R[[X_σ]] → S` (`AdicEval.eval`: the limit of the evaluations of the total-degree truncations,
via Mathlib's `IsAdicComplete.liftAlgHom`). Conversely, `R`-algebra maps `R[[X_σ]] → S` into an
`𝔞`-adically separated `S` are determined by the images of the variables, if these lie in `𝔞`
(`AdicEval.algHom_ext`): a power series is a polynomial modulo `(X_σ)^n`
(`mem_pow_span_X`). No continuity is assumed.

For an ideal `𝔪 ⊆ R` we call `s ∈ S` *topologically nilpotent* (`TopNil 𝔪 s`) if `s^N ∈ 𝔪S`
for some `N`. Finite free `R`-algebras are `𝔪S`-adically complete if `R` is `𝔪`-adically
complete (`isAdicComplete_of_free`), and for topologically nilpotent `s_i` the ideal
`𝔪S + (s_i)` defines the same topology (`exists_pow_evIdeal_le`), so we get evaluation
`evalT` and uniqueness `algHom_ext_topNil` for topologically nilpotent families.
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace AdicEval

variable {R : Type*} [CommRing R]

/-- **A power series without coefficients in total degree `< n` lies in `(X_σ)^n`.** -/
theorem mem_pow_span_X {σ : Type*} [Finite σ] (n : ℕ) (f : MvPowerSeries σ R)
    (hf : ∀ m : σ →₀ ℕ, m.degree < n → coeff m f = 0) :
    f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ n := by
  classical
  have := Fintype.ofFinite σ
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    let ch : (σ →₀ ℕ) → Option σ := fun m =>
      if h : m.support.Nonempty then some h.choose else none
    have hch : ∀ m j, ch m = some j → j ∈ m.support := by
      intro m j h
      simp only [ch] at h
      split_ifs at h with h1
      · cases h; exact h1.choose_spec
    have hch0 : ∀ m : σ →₀ ℕ, m ≠ 0 → ∃ j, ch m = some j := by
      intro m hm
      have h1 : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
      exact ⟨h1.choose, by simp only [ch, dif_pos h1]⟩
    let g : σ → MvPowerSeries σ R := fun j m =>
      if ch (m + Finsupp.single j 1) = some j then coeff (m + Finsupp.single j 1) f else 0
    have hg : ∀ j m, coeff m (g j) =
        if ch (m + Finsupp.single j 1) = some j then coeff (m + Finsupp.single j 1) f else 0 :=
      fun _ _ => rfl
    have key : f = ∑ j, X j * g j := by
      ext m
      rw [map_sum]
      simp only [X_def, coeff_monomial_mul, one_mul, hg]
      by_cases hm : m = 0
      · subst hm
        rw [hf 0 (by simp)]
        refine (Finset.sum_eq_zero fun j _ => ?_).symm
        rw [if_neg]
        rw [Finsupp.single_le_iff]
        simp
      · obtain ⟨j0, hj0⟩ := hch0 m hm
        have hle0 : Finsupp.single j0 1 ≤ m := by
          rw [Finsupp.single_le_iff]
          have := Finsupp.mem_support_iff.mp (hch m j0 hj0)
          omega
        rw [Finset.sum_eq_single j0]
        · rw [if_pos hle0, tsub_add_cancel_of_le hle0, if_pos hj0]
        · intro j _ hj
          by_cases hle : Finsupp.single j 1 ≤ m
          · rw [if_pos hle, tsub_add_cancel_of_le hle, if_neg]
            rw [hj0]
            exact fun h => hj (Option.some_injective _ h).symm
          · rw [if_neg hle]
        · intro h; exact absurd (Finset.mem_univ j0) h
    rw [key, pow_succ']
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) ?_
    refine ih _ fun m hm => ?_
    rw [hg]
    split_ifs
    · apply hf
      rw [map_add, Finsupp.degree_single]
      omega
    · rfl

/-- `f − trunc_n f ∈ (X_σ)^n`. -/
theorem sub_truncTotal_mem {σ : Type*} [Finite σ] (n : ℕ) (f : MvPowerSeries σ R) :
    f - (truncTotal n f : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ n := by
  refine mem_pow_span_X n _ fun m hm => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hm, sub_self]

/-! ### Comparing adic topologies -/

section Compare

variable {S : Type*} [CommRing S]

theorem isHausdorff_of_pow_le {𝔞 𝔟 : Ideal S} [h𝔟 : IsHausdorff 𝔟 S] {K : ℕ}
    (h2 : 𝔞 ^ K ≤ 𝔟) : IsHausdorff 𝔞 S := by
  rw [isHausdorff_iff] at h𝔟 ⊢
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, sub_zero] at h𝔟 ⊢
  intro x hx
  refine h𝔟 x fun n => ?_
  have : 𝔞 ^ (K * n) ≤ 𝔟 ^ n := by
    rw [pow_mul]; exact Ideal.pow_right_mono h2 n
  exact this (hx _)

theorem isAdicComplete_of_le {𝔞 𝔟 : Ideal S} [h𝔟 : IsAdicComplete 𝔟 S] (h1 : 𝔟 ≤ 𝔞)
    {K : ℕ} (h2 : 𝔞 ^ K ≤ 𝔟) : IsAdicComplete 𝔞 S := by
  have hK : 𝔞 ^ (K + 1) ≤ 𝔟 := (Ideal.pow_le_pow_right (Nat.le_succ K)).trans h2
  have hH := isHausdorff_of_pow_le hK
  refine (isAdicComplete_iff _ _).mpr ⟨hH, ?_⟩
  have hP := h𝔟.toIsPrecomplete
  rw [isPrecomplete_iff] at hP ⊢
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hP ⊢
  intro f hf
  have hpow : ∀ n, 𝔞 ^ ((K + 1) * n) ≤ 𝔟 ^ n := fun n => by
    rw [pow_mul]; exact Ideal.pow_right_mono hK n
  obtain ⟨L, hL⟩ := hP (fun k => f ((K + 1) * k)) fun {m n} hmn =>
    hpow m (hf (Nat.mul_le_mul_left _ hmn))
  refine ⟨L, fun n => ?_⟩
  have e : f n - L = (f n - f ((K + 1) * n)) + (f ((K + 1) * n) - L) := by ring
  rw [e]
  refine Ideal.add_mem _ (hf (by nlinarith)) ?_
  exact Ideal.pow_right_mono h1 n (hL n)

end Compare

/-! ### Evaluation -/

section Eval

variable {S : Type*} [CommRing S] [Algebra R S] {σ : Type*} [Finite σ]

omit [Finite σ] in
theorem map_idealOfVars_pow_le {𝔞 : Ideal S} {s : σ → S} (hs : ∀ i, s i ∈ 𝔞) (n : ℕ) :
    MvPolynomial.idealOfVars σ R ^ n ≤ (𝔞 ^ n).comap (MvPolynomial.aeval s) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ n
  rw [MvPolynomial.idealOfVars, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  simpa using hs i

/-- The approximations `f ↦ (trunc_n f)(s) mod 𝔞^n`. -/
def approx (𝔞 : Ideal S) (s : σ → S) (hs : ∀ i, s i ∈ 𝔞) (n : ℕ) :
    MvPowerSeries σ R →ₐ[R] S ⧸ 𝔞 ^ n :=
  letI g : MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ n →ₐ[R] S ⧸ 𝔞 ^ n :=
    Ideal.quotientMapₐ (𝔞 ^ n) (MvPolynomial.aeval (R := R) s)
      (map_idealOfVars_pow_le (R := R) hs n)
  g.comp ((truncTotalAlgHom σ R n).restrictScalars R)

theorem approx_apply (𝔞 : Ideal S) (s : σ → S) (hs : ∀ i, s i ∈ 𝔞) (n : ℕ)
    (f : MvPowerSeries σ R) :
    approx 𝔞 s hs n f = Ideal.Quotient.mk (𝔞 ^ n) (MvPolynomial.aeval s (truncTotal n f)) := by
  simp [approx, Ideal.quotientMapₐ, Ideal.quotientMap_mk]

theorem approx_compat (𝔞 : Ideal S) (s : σ → S) (hs : ∀ i, s i ∈ 𝔞) {m n : ℕ}
    (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (approx 𝔞 s hs n) =
      approx 𝔞 s hs m := by
  ext f
  rw [AlgHom.comp_apply, approx_apply, approx_apply, Ideal.Quotient.factorₐ_apply_mk,
    Ideal.Quotient.eq, ← map_sub]
  exact map_idealOfVars_pow_le hs m
    (truncTotal_sub_truncTotal_mem_pow_idealOfVars hle le_rfl f)

/-- **Evaluation `f ↦ f(s)`** of power series at a family `s` in an ideal `𝔞` of an `𝔞`-adically
complete `R`-algebra. -/
def eval (𝔞 : Ideal S) [IsAdicComplete 𝔞 S] (s : σ → S) (hs : ∀ i, s i ∈ 𝔞) :
    MvPowerSeries σ R →ₐ[R] S :=
  IsAdicComplete.liftAlgHom 𝔞 (approx 𝔞 s hs) (approx_compat 𝔞 s hs)

theorem eval_mk (𝔞 : Ideal S) [IsAdicComplete 𝔞 S] (s : σ → S) (hs : ∀ i, s i ∈ 𝔞) (n : ℕ)
    (f : MvPowerSeries σ R) :
    Ideal.Quotient.mk (𝔞 ^ n) (eval 𝔞 s hs f) =
      Ideal.Quotient.mk (𝔞 ^ n) (MvPolynomial.aeval s (truncTotal n f)) := by
  rw [eval, IsAdicComplete.mk_liftAlgHom, approx_apply]

theorem eval_coe (𝔞 : Ideal S) [IsAdicComplete 𝔞 S] (s : σ → S) (hs : ∀ i, s i ∈ 𝔞)
    (P : MvPolynomial σ R) : eval 𝔞 s hs (P : MvPowerSeries σ R) = MvPolynomial.aeval s P := by
  refine (IsHausdorff.eq_iff_smodEq (I := 𝔞)).mpr fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top]
  rw [SModEq.sub_mem]
  have h1 := Ideal.Quotient.eq.mp (eval_mk 𝔞 s hs n (P : MvPowerSeries σ R))
  have h2 : MvPolynomial.aeval s (truncTotal n (P : MvPowerSeries σ R)) -
      MvPolynomial.aeval s P ∈ 𝔞 ^ n := by
    rw [← map_sub]
    refine map_idealOfVars_pow_le hs n ?_
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro x hx
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ hx, MvPolynomial.coeff_coe, sub_self]
  have := Ideal.add_mem _ h1 h2
  rwa [sub_add_sub_cancel] at this

@[simp] theorem eval_X (𝔞 : Ideal S) [IsAdicComplete 𝔞 S] (s : σ → S) (hs : ∀ i, s i ∈ 𝔞)
    (i : σ) : eval (R := R) 𝔞 s hs (X i) = s i := by
  have e : (X i : MvPowerSeries σ R) = ((MvPolynomial.X i : MvPolynomial σ R) :
      MvPowerSeries σ R) := (MvPolynomial.coe_X (R := R) i).symm
  rw [e, eval_coe, MvPolynomial.aeval_X]

/-- **Uniqueness**: `R`-algebra maps `R[[X_σ]] → S` into an `𝔞`-adically separated `S` that agree
on the variables, with values in `𝔞`, are equal. -/
theorem algHom_ext (𝔞 : Ideal S) [IsHausdorff 𝔞 S] {φ ψ : MvPowerSeries σ R →ₐ[R] S}
    (hφ : ∀ i, φ (X i) ∈ 𝔞) (h : ∀ i, φ (X i) = ψ (X i)) : φ = ψ := by
  have hpoly : φ.comp (MvPolynomial.coeToMvPowerSeries.algHom R) =
      ψ.comp (MvPolynomial.coeToMvPowerSeries.algHom R) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa [MvPolynomial.coeToMvPowerSeries.algHom] using h i
  have hP : ∀ P : MvPolynomial σ R, φ (P : MvPowerSeries σ R) = ψ P := fun P => by
    have := congrArg (fun g => g P) hpoly
    simpa [MvPolynomial.coeToMvPowerSeries.algHom] using this
  have hmap : ∀ (χ : MvPowerSeries σ R →ₐ[R] S), (∀ i, χ (X i) ∈ 𝔞) → ∀ n,
      ∀ r ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ n, χ r ∈ 𝔞 ^ n := by
    intro χ hχ n r hr
    have h1 : Ideal.map χ (Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ n) ≤ 𝔞 ^ n := by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hχ i
    exact h1 (Ideal.mem_map_of_mem _ hr)
  ext f
  refine (IsHausdorff.eq_iff_smodEq (I := 𝔞)).mpr fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top]
  rw [SModEq.sub_mem]
  have e : f = (truncTotal n f : MvPowerSeries σ R) + (f - truncTotal n f) := by ring
  rw [e, map_add, map_add, hP, add_sub_add_left_eq_sub]
  exact Ideal.sub_mem _ (hmap φ hφ n _ (sub_truncTotal_mem n f))
    (hmap ψ (fun i => h i ▸ hφ i) n _ (sub_truncTotal_mem n f))

theorem eval_unique (𝔞 : Ideal S) [IsAdicComplete 𝔞 S] (s : σ → S) (hs : ∀ i, s i ∈ 𝔞)
    (φ : MvPowerSeries σ R →ₐ[R] S) (h : ∀ i, φ (X i) = s i) : φ = eval 𝔞 s hs :=
  algHom_ext 𝔞 (fun i => h i ▸ hs i) fun i => by rw [h, eval_X]

end Eval

/-! ### Topologically nilpotent families -/

section TopNil

variable (𝔪 : Ideal R) {S : Type*} [CommRing S] [Algebra R S]

/-- `s` is topologically nilpotent for the `𝔪`-adic topology: `s^N ∈ 𝔪S` for some `N`. -/
def TopNil (s : S) : Prop := ∃ N, s ^ N ∈ 𝔪.map (algebraMap R S)

variable {𝔪}

theorem TopNil.map {S' : Type*} [CommRing S'] [Algebra R S'] (g : S →ₐ[R] S') {s : S}
    (hs : TopNil 𝔪 s) : TopNil 𝔪 (g s) := by
  obtain ⟨N, hN⟩ := hs
  refine ⟨N, ?_⟩
  rw [← map_pow]
  have := Ideal.mem_map_of_mem (g : S →+* S') hN
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem topNil_of_mem {s : S} (hs : s ∈ 𝔪.map (algebraMap R S)) : TopNil 𝔪 s :=
  ⟨1, by rwa [pow_one]⟩

theorem topNil_zero : TopNil 𝔪 (0 : S) := ⟨1, by simp⟩

variable (𝔪) in
/-- The ideal `𝔪S + (s_i)`. -/
def evIdeal {σ : Type*} (s : σ → S) : Ideal S :=
  𝔪.map (algebraMap R S) ⊔ Ideal.span (Set.range s)

theorem le_evIdeal {σ : Type*} (s : σ → S) : 𝔪.map (algebraMap R S) ≤ evIdeal 𝔪 s :=
  le_sup_left

theorem mem_evIdeal {σ : Type*} (s : σ → S) (i : σ) : s i ∈ evIdeal 𝔪 s :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)

theorem exists_pow_evIdeal_le {σ : Type*} [Finite σ] {s : σ → S} (hs : ∀ i, TopNil 𝔪 (s i)) :
    ∃ K, evIdeal 𝔪 s ^ K ≤ 𝔪.map (algebraMap R S) := by
  have hle : Ideal.span (Set.range s) ≤ (𝔪.map (algebraMap R S)).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hs i
  obtain ⟨K, hK⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (Submodule.fg_span (Set.finite_range s))
  refine ⟨1 + K, Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le ?_ hK)⟩
  rw [pow_one]

theorem isAdicComplete_evIdeal [IsAdicComplete (𝔪.map (algebraMap R S)) S] {σ : Type*}
    [Finite σ] {s : σ → S} (hs : ∀ i, TopNil 𝔪 (s i)) : IsAdicComplete (evIdeal 𝔪 s) S :=
  isAdicComplete_of_le (le_evIdeal s) (exists_pow_evIdeal_le hs).choose_spec

theorem isHausdorff_evIdeal [IsHausdorff (𝔪.map (algebraMap R S)) S] {σ : Type*}
    [Finite σ] {s : σ → S} (hs : ∀ i, TopNil 𝔪 (s i)) : IsHausdorff (evIdeal 𝔪 s) S :=
  isHausdorff_of_pow_le (exists_pow_evIdeal_le hs).choose_spec

/-- **Evaluation at a topologically nilpotent family.** -/
def evalT [IsAdicComplete (𝔪.map (algebraMap R S)) S] {σ : Type*} [Finite σ] (s : σ → S)
    (hs : ∀ i, TopNil 𝔪 (s i)) : MvPowerSeries σ R →ₐ[R] S :=
  haveI := isAdicComplete_evIdeal hs
  eval (evIdeal 𝔪 s) s (mem_evIdeal s)

@[simp] theorem evalT_X [IsAdicComplete (𝔪.map (algebraMap R S)) S] {σ : Type*} [Finite σ]
    (s : σ → S) (hs : ∀ i, TopNil 𝔪 (s i)) (i : σ) : evalT s hs (X i) = s i := by
  rw [evalT, eval_X]

/-- **Uniqueness** for maps sending the variables to topologically nilpotent elements. -/
theorem algHom_ext_topNil [IsHausdorff (𝔪.map (algebraMap R S)) S] {σ : Type*} [Finite σ]
    {φ ψ : MvPowerSeries σ R →ₐ[R] S} (hφ : ∀ i, TopNil 𝔪 (φ (X i)))
    (h : ∀ i, φ (X i) = ψ (X i)) : φ = ψ :=
  haveI := isHausdorff_evIdeal hφ
  algHom_ext (evIdeal 𝔪 fun i => φ (X i)) (fun i => mem_evIdeal (fun i => φ (X i)) i) h

theorem topNil_evalT [IsAdicComplete (𝔪.map (algebraMap R S)) S] {σ : Type*} [Finite σ]
    {s : σ → S} (hs : ∀ i, TopNil 𝔪 (s i)) {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) : TopNil 𝔪 (evalT s hs f) := by
  obtain ⟨K, hK⟩ := exists_pow_evIdeal_le hs
  refine ⟨K, hK (Ideal.pow_mem_pow ?_ K)⟩
  haveI := isAdicComplete_evIdeal hs
  have h1 := sub_truncTotal_mem 1 f
  rw [pow_one] at h1
  have ht : truncTotal 1 f = 0 := by
    ext m
    rw [MvPolynomial.coeff_zero]
    by_cases hm : m.degree < 1
    · rw [coeff_truncTotal _ hm]
      have : m = 0 := by
        ext j
        have := (Finsupp.degree_eq_zero_iff m).mp (by omega)
        simp [this]
      rw [this, coeff_zero_eq_constantCoeff_apply, hf]
    · rw [coeff_truncTotal_eq_zero _ (not_lt.mp hm)]
  rw [ht, MvPolynomial.coe_zero, sub_zero] at h1
  rw [evalT]
  have h2 : Ideal.map (eval (R := R) (evIdeal 𝔪 s) s (mem_evIdeal s))
      (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ≤ evIdeal 𝔪 s := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, eval_X]
    exact mem_evIdeal s i
  exact h2 (Ideal.mem_map_of_mem _ h1)

end TopNil

/-! ### Finite free algebras over complete rings are complete -/

section Free

variable (𝔪 : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]

theorem mem_pow_smul_top_iff {ι : Type*} [Finite ι] (b : Module.Basis ι R M) (n : ℕ) (x : M) :
    x ∈ (𝔪 ^ n • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ 𝔪 ^ n := by
  have := Fintype.ofFinite ι
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr m _ i => ?_) (fun x y hx hy i => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    · rw [map_add, Finsupp.add_apply]
      exact Ideal.add_mem _ (hx i) (hy i)
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isAdicComplete_of_basis [IsAdicComplete 𝔪 R] {ι : Type*} [Finite ι]
    (b : Module.Basis ι R M) : IsAdicComplete 𝔪 M := by
  have := Fintype.ofFinite ι
  have hH : IsHausdorff 𝔪 R := inferInstance
  have hP : IsPrecomplete 𝔪 R := inferInstance
  rw [isHausdorff_iff] at hH
  rw [isPrecomplete_iff] at hP
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, sub_zero] at hH hP
  refine (isAdicComplete_iff _ _).mpr ⟨?_, ?_⟩
  · rw [isHausdorff_iff]
    simp only [SModEq.sub_mem, sub_zero, mem_pow_smul_top_iff 𝔪 b]
    intro x hx
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    exact hH _ fun n => hx n i
  · rw [isPrecomplete_iff]
    simp only [SModEq.sub_mem, mem_pow_smul_top_iff 𝔪 b]
    intro f hf
    choose L hL using fun i => hP (fun n => b.repr (f n) i) fun hmn => by
      have := hf hmn i
      rwa [map_sub, Finsupp.sub_apply] at this
    refine ⟨∑ i, L i • b i, fun n i => ?_⟩
    have e : b.repr (∑ j, L j • b j) i = L i := by
      rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [map_sub, Finsupp.sub_apply, e]
    exact hL i n

/-- **Finite free algebras over an `𝔪`-adically complete ring are `𝔪S`-adically complete.** -/
theorem isAdicComplete_of_free [IsAdicComplete 𝔪 R] (S : Type*) [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] : IsAdicComplete (𝔪.map (algebraMap R S)) S :=
  (IsAdicComplete.map_algebraMap_iff ..).mpr
    (isAdicComplete_of_basis 𝔪 (Module.Free.chooseBasis R S))

end Free

end AdicEval

end PadicHodge
