/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The idempotent of the connected component of a rational point

Let `R` be a local ring with maximal ideal `m`, `B` a finite `R`-algebra and `φ : B → R` an
`R`-point. Write `J = m B` (`fiberIdeal R B`). We call `e ∈ B` a *point idempotent* for `φ`
(`IsPointIdempotent φ e`) if `e` is idempotent, `φ e = 1` and `b e - φ(b) e` lies in the radical
of `J` for every `b`; i.e. modulo `m` the corner `B e` is `k e` plus nilpotents: `Spec (B e)` is
the connected component of `Spec B` through `φ`, and `B e` is local (`isLocalRing_of_...` in
`GroupScheme/Connected.lean`).

* `radical_fiberIdeal_le_jacobson`: `√(m B)` lies in the Jacobson radical of `B` (`B` finite
  over `R`), hence an idempotent in `√(m B)` is `0`;
* `IsPointIdempotent.eq_zero_of_mul_eq`, `IsPointIdempotent.unique`: point idempotents are unique;
* `IsPointIdempotent.tmul`: `e ⊗ e'` is a point idempotent for `φ ⊗ φ'`;
* `isAdicComplete_fiberIdeal`: if `R` is `m`-adically complete and `B` finite free, then `B` is
  `m B`-adically complete, so `(B, m B)` is henselian and idempotents lift from `B / m B`
  (`exists_isIdempotentElem_lift`);
* `exists_isPointIdempotent`: over a complete local ring, point idempotents exist (finite free
  `B`): `B / m B` is artinian, the idempotent of the local factor at `ker φ̄` lifts.

**Deviation from the plan.** The plan asked for a henselian local base ring. Mathlib's
`HenselianLocalRing` only provides lifting of simple roots of polynomials over `R` itself; the
equivalence with "idempotents lift along finite `R`-algebras" ([Stacks 04GG]) is not in Mathlib.
We therefore assume `R` is `m`-adically complete (true for `O_K`, `ℤ_p`, and for fields), where
idempotent lifting follows from Mathlib's `IsAdicComplete.henselianRing` applied to the finite
free algebra `B` itself. Standard argument, written up here.
-/

noncomputable section

open IsLocalRing Polynomial

namespace PadicHodge

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [Algebra R B]

/-- The ideal `m_R B` of the closed fibre. -/
abbrev fiberIdeal [IsLocalRing R] : Ideal B := (maximalIdeal R).map (algebraMap R B)

/-! ### Adic completeness of finite free modules -/

section Complete

variable {R}

theorem isAdicComplete_of_linearEquiv {I : Ideal R} {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M ≃ₗ[R] N) [h : IsAdicComplete I M] :
    IsAdicComplete I N := by
  rw [← AdicCompletion.of_bijective_iff] at h ⊢
  have : ⇑(AdicCompletion.of I N) = AdicCompletion.congr I f ∘ AdicCompletion.of I M ∘ f.symm := by
    funext x; simp [AdicCompletion.map_of]
  rw [this]
  exact (AdicCompletion.congr I f).bijective.comp (h.comp f.symm.bijective)

theorem isAdicComplete_pi_fin (I : Ideal R) [IsAdicComplete I R] (n : ℕ) :
    IsAdicComplete I (Fin n → R) := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : ⇑(AdicCompletion.of I (Fin n → R)) = (AdicCompletion.piEquivFin I n).symm ∘
      (fun x j => AdicCompletion.of I R (x j)) := by
    funext x
    apply (AdicCompletion.piEquivFin I n).injective
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply, AdicCompletion.piEquivFin_apply]
    funext j
    simp [AdicCompletion.pi, AdicCompletion.map_of]
  rw [h]
  exact (AdicCompletion.piEquivFin I n).symm.bijective.comp
    (Function.Bijective.piMap fun _ => AdicCompletion.of_bijective_iff.mpr inferInstance)

variable (R) in
/-- A finite free algebra over an `m`-adically complete local ring is `m B`-adically complete. -/
theorem isAdicComplete_fiberIdeal [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Module.Free R B] [Module.Finite R B] : IsAdicComplete (fiberIdeal R B) B := by
  have := isAdicComplete_pi_fin (maximalIdeal R) (Module.finrank R B)
  have : IsAdicComplete (maximalIdeal R) B :=
    isAdicComplete_of_linearEquiv (Module.finBasis R B).equivFun.symm
  have h1 : IsHausdorff (fiberIdeal R B) B := IsHausdorff.map_algebraMap_iff.mpr inferInstance
  have h2 : IsPrecomplete (fiberIdeal R B) B := IsPrecomplete.map_algebraMap_iff.mpr inferInstance
  constructor

/-- Idempotents of `B / m B` lift to `B` (finite free `B` over a complete local ring). -/
theorem exists_isIdempotentElem_lift [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Module.Free R B] [Module.Finite R B] (ē : B ⧸ fiberIdeal R B) (hē : IsIdempotentElem ē) :
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ē := by
  have := isAdicComplete_fiberIdeal R B
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective ē
  have hmon : (X ^ 2 - X : B[X]).Monic := monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))
  have h1 : (X ^ 2 - X : B[X]).eval a₀ ∈ fiberIdeal R B := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow, sub_eq_zero]
    rw [sq]
    exact hē.eq
  have h2 : IsUnit
      (Ideal.Quotient.mk (fiberIdeal R B) ((X ^ 2 - X : B[X]).derivative.eval a₀)) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (fiberIdeal R B) (2 * a₀ - 1)) ?_
    have : (X ^ 2 - X : B[X]).derivative.eval a₀ = 2 * a₀ - 1 := by
      simp; ring
    rw [this]
    have h2' : (2 * Ideal.Quotient.mk (fiberIdeal R B) a₀ - 1) *
        (2 * Ideal.Quotient.mk (fiberIdeal R B) a₀ - 1) = 1 := by
      linear_combination (4 : B ⧸ fiberIdeal R B) * hē.eq
    simpa [map_ofNat] using h2'
  obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian _ hmon a₀ h1 h2
  refine ⟨a, ?_, Ideal.Quotient.eq.mpr ha'⟩
  have : a ^ 2 - a = 0 := by simpa using ha
  rw [IsIdempotentElem, ← sq]
  exact sub_eq_zero.mp this

end Complete

/-! ### The radical of `m B` -/

section Radical

variable {R B} [IsLocalRing R]

theorem radical_fiberIdeal_le_jacobson [Module.Finite R B] :
    (fiberIdeal R B).radical ≤ Ideal.jacobson ⊥ := by
  intro x hx
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  have : (M.comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hle : fiberIdeal R B ≤ M := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal this]
  exact (hM.isPrime.radical_le_iff.mpr hle) hx

theorem eq_zero_of_isIdempotentElem_of_mem_radical [Module.Finite R B] {g : B}
    (hg : IsIdempotentElem g) (h : g ∈ (fiberIdeal R B).radical) : g = 0 := by
  have h1 : IsUnit (1 - g) := by
    simpa [sub_eq_add_neg, add_comm] using
      Ideal.mem_jacobson_bot.mp (radical_fiberIdeal_le_jacobson h) (-1)
  have : g * (1 - g) = 0 := by rw [mul_sub, mul_one, hg.eq, sub_self]
  exact h1.mul_left_eq_zero.mp this

theorem map_mem_radical_fiberIdeal {C : Type*} [CommRing C] [Algebra R C] (f : B →ₐ[R] C)
    {x : B} (hx : x ∈ (fiberIdeal R B).radical) : f x ∈ (fiberIdeal R C).radical := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [← map_pow]
  have := Ideal.mem_map_of_mem (f : B →+* C) hn
  rwa [fiberIdeal, Ideal.map_map, AlgHom.comp_algebraMap] at this

end Radical

/-! ### Point idempotents -/

variable {R B}

/-- `e` is the idempotent cutting out the connected component of the `R`-point `φ` of `Spec B`:
`e` is idempotent, `φ e = 1` and `b e ≡ φ(b) e` modulo the radical of `m B`. -/
structure IsPointIdempotent [IsLocalRing R] (φ : B →ₐ[R] R) (e : B) : Prop where
  isIdempotentElem : IsIdempotentElem e
  apply_eq_one : φ e = 1
  mul_sub_mem : ∀ b : B, b * e - φ b • e ∈ (fiberIdeal R B).radical

namespace IsPointIdempotent

variable [IsLocalRing R] {φ : B →ₐ[R] R} {e : B}

/-- An idempotent `g ≤ e` with `φ g = 0` vanishes. -/
theorem eq_zero_of_mul_eq [Module.Finite R B] (h : IsPointIdempotent φ e) {g : B}
    (hg : IsIdempotentElem g) (hge : g * e = g) (hφ : φ g = 0) : g = 0 := by
  apply eq_zero_of_isIdempotentElem_of_mem_radical (R := R) hg
  have := h.mul_sub_mem g
  rwa [hφ, zero_smul, sub_zero, hge] at this

theorem mul_eq_left [Module.Finite R B] (h : IsPointIdempotent φ e) {e' : B}
    (h' : IsPointIdempotent φ e') : e * e' = e := by
  have hg : IsIdempotentElem (e * (1 - e')) := h.isIdempotentElem.mul h'.isIdempotentElem.one_sub
  have := h.eq_zero_of_mul_eq hg (by rw [mul_right_comm, h.isIdempotentElem.eq])
    (by simp [h.apply_eq_one, h'.apply_eq_one])
  rw [mul_sub, mul_one, sub_eq_zero] at this
  exact this.symm

/-- Point idempotents are unique. -/
theorem unique [Module.Finite R B] (h : IsPointIdempotent φ e) {e' : B}
    (h' : IsPointIdempotent φ e') : e = e' := by
  rw [← h.mul_eq_left h', mul_comm, h'.mul_eq_left h]

/-- `e ⊗ e'` is a point idempotent for `φ ⊗ φ'`. -/
theorem tmul {C : Type*} [CommRing C] [Algebra R C] {ψ : C →ₐ[R] R} {e' : C}
    (h : IsPointIdempotent φ e) (h' : IsPointIdempotent ψ e') :
    IsPointIdempotent (Algebra.TensorProduct.productMap φ ψ) (e ⊗ₜ[R] e') where
  isIdempotentElem := by
    rw [IsIdempotentElem, Algebra.TensorProduct.tmul_mul_tmul, h.isIdempotentElem.eq,
      h'.isIdempotentElem.eq]
  apply_eq_one := by
    rw [Algebra.TensorProduct.productMap_apply_tmul, h.apply_eq_one, h'.apply_eq_one, mul_one]
  mul_sub_mem x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [add_mul, map_add, add_smul, add_sub_add_comm]
      exact add_mem hx hy
    | tmul a c =>
      set n := a * e - φ a • e
      set n' := c * e' - ψ c • e'
      have key : (a ⊗ₜ[R] c) * (e ⊗ₜ[R] e') -
          Algebra.TensorProduct.productMap φ ψ (a ⊗ₜ[R] c) • (e ⊗ₜ[R] e') =
          n ⊗ₜ[R] (c * e') + (φ a • e) ⊗ₜ[R] n' := by
        simp only [n, n', Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.productMap_apply_tmul, TensorProduct.sub_tmul,
          TensorProduct.tmul_sub, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
        rw [mul_comm (ψ c)]
        abel
      rw [key]
      refine add_mem ?_ ?_
      · have : n ⊗ₜ[R] (c * e') = Algebra.TensorProduct.includeLeft (S := R) n *
            ((1 : B) ⊗ₜ[R] (c * e')) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_right _ _ (map_mem_radical_fiberIdeal _ (h.mul_sub_mem a))
      · have : (φ a • e) ⊗ₜ[R] n' = ((φ a • e) ⊗ₜ[R] (1 : C)) *
            Algebra.TensorProduct.includeRight n' := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_left _ _ (map_mem_radical_fiberIdeal _ (h'.mul_sub_mem c))

end IsPointIdempotent

/-! ### Existence over a complete local ring -/

/-- Over an `m`-adically complete local ring, every `R`-point of a finite free `R`-algebra has a
point idempotent. -/
theorem exists_isPointIdempotent [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Module.Free R B] [Module.Finite R B] (φ : B →ₐ[R] R) : ∃ e, IsPointIdempotent φ e := by
  classical
  set J := fiberIdeal R B
  let k := R ⧸ maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  have : Module.Finite k (B ⧸ J) := Module.Finite.of_restrictScalars_finite R k (B ⧸ J)
  have := IsArtinianRing.of_finite k (B ⧸ J)
  let ψ : B →+* k := (Ideal.Quotient.mk _).comp (φ : B →+* R)
  have hψ : ∀ r : R, ψ (algebraMap R B r) = Ideal.Quotient.mk _ r := by
    intro r; simp [ψ]
  have hJψ : J ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem]
    exact hr
  let ψ' : B ⧸ J →+* k := Ideal.Quotient.lift J ψ hJψ
  have hψ' : Function.Surjective ψ' := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk J (algebraMap R B r), by
      simp only [ψ', Ideal.Quotient.lift_mk, hψ]⟩
  have hM₀ : (RingHom.ker ψ').IsMaximal := RingHom.ker_isMaximal_of_surjective ψ' hψ'
  let p₀ : MaximalSpectrum (B ⧸ J) := ⟨_, hM₀⟩
  let z : (B ⧸ J) ⧸ nilradical (B ⧸ J) :=
    (IsArtinianRing.quotNilradicalEquivPi (B ⧸ J)).symm (Pi.single p₀ 1)
  have hz : IsIdempotentElem z := by
    refine IsIdempotentElem.map ?_ (IsArtinianRing.quotNilradicalEquivPi (B ⧸ J)).symm
    change _ * _ = _
    rw [← Pi.single_mul_left, Pi.single_eq_same, one_mul]
  obtain ⟨ē, hē, hēz⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk (nilradical (B ⧸ J))) (by
      intro x hx; rwa [Ideal.mk_ker] at hx) z (Ideal.Quotient.mk_surjective z) hz
  have hcomp : ∀ p : MaximalSpectrum (B ⧸ J),
      Ideal.Quotient.mk p.asIdeal ē =
        (Pi.single p₀ 1 : ∀ p : MaximalSpectrum (B ⧸ J), (B ⧸ J) ⧸ p.asIdeal) p := by
    intro p
    have := congrArg (fun w => IsArtinianRing.quotNilradicalEquivPi (B ⧸ J) w p) hēz
    simp only [z, AlgEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨e, he, rfl⟩ := exists_isIdempotentElem_lift (R := R) B ē hē
  -- `ψ' ē = 1`
  have h0 : Ideal.Quotient.mk J e - 1 ∈ RingHom.ker ψ' := by
    have := hcomp p₀
    rw [Pi.single_eq_same, ← map_one (Ideal.Quotient.mk p₀.asIdeal), Ideal.Quotient.eq] at this
    exact this
  have hφe : Ideal.Quotient.mk (maximalIdeal R) (φ e) = 1 := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h0
    simpa [ψ', ψ] using h0
  refine ⟨e, he, ?_, ?_⟩
  · have hu : IsUnit (φ e) := by
      by_contra hn
      have hm : φ e ∈ maximalIdeal R := hn
      rw [← Ideal.Quotient.eq_zero_iff_mem, hφe] at hm
      exact one_ne_zero hm
    have := (he.map φ).eq
    exact hu.mul_left_cancel (this.trans (mul_one _).symm)
  · intro b
    have hd : b * e - φ b • e = (b - algebraMap R B (φ b)) * e := by
      rw [sub_mul, Algebra.smul_def]
    rw [hd]
    have hnil : Ideal.Quotient.mk J ((b - algebraMap R B (φ b)) * e) ∈ nilradical (B ⧸ J) := by
      rw [IsArtinianRing.nilradical_eq_iInf, Submodule.mem_iInf]
      intro p
      by_cases hp : p = p₀
      · subst hp
        rw [map_mul]
        refine Ideal.mul_mem_right _ _ ?_
        change _ ∈ RingHom.ker ψ'
        rw [RingHom.mem_ker]
        simp only [ψ', Ideal.Quotient.lift_mk]
        simp [ψ]
      · rw [map_mul]
        refine Ideal.mul_mem_left _ _ ?_
        have := hcomp p
        rw [Pi.single_eq_of_ne hp, Ideal.Quotient.eq_zero_iff_mem] at this
        exact this
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simpa using hn

end PadicHodge
