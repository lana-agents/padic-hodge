/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TatePerfect
import Mathlib.RingTheory.Unramified.Finite

/-!
# Inertia acts trivially on the points of étale group schemes over `ℤ_p`

(The "unramifiedness of `T_p`" input to the Hodge–Tate weight `0` statement for étale
`p`-divisible groups over `O_K`, cf. [Hong, Prop. 3.2.3 (3)], [Stix, §11].) Standard argument,
written up here in the form "rigidity of unramified points":

* `norm_le_one_of_isIntegral`: if `A` is integral over `R` and `R` maps into the unit ball of an
  ultrametric normed field `F`, every `R`-algebra map `A → F` maps into the unit ball;
* `algHom_eq_of_norm_sub_lt_one`: if `A` is formally unramified (and essentially of finite type)
  over `R`, two `R`-algebra maps `f, g : A → F` with `‖f‖ ≤ 1` and `‖f(a) - g(a)‖ < 1` for all `a`
  are equal (take `t ∈ A ⊗_R A` with `(1 ⊗ s - s ⊗ 1) t = 0` and `m(t) = 1`,
  `Algebra.FormallyUnramified.iff_exists_tensorProduct`; then `h = f ⊗ g` has
  `‖h(t) - 1‖ < 1`, so `h(t) ≠ 0`, and `(g(s) - f(s)) h(t) = 0`);
* `IsInertia σ`: `σ` acts trivially on the residue field of `ℚ̄_p`;
  `FFGroupScheme.inertia_comp_eq`: inertia fixes the `ℚ̄_p`-points of a finite étale group scheme
  over `R` (e.g. `ℤ_p`);
* `PDivGroup.galTate_baseChange_eq_of_isInertia`: for a `p`-divisible group over `ℤ_p` with étale
  layers, inertia acts trivially on `T_p` of its generic fibre: the Galois representation is
  unramified.
-/

noncomputable section

open WithConv TensorProduct

namespace PadicHodge

section Rigidity

variable {R A F : Type*} [CommRing R] [CommRing A] [Algebra R A] [NormedField F]
  [IsUltrametricDist F] [Algebra R F]

/-- Integral elements map into the unit ball. -/
theorem norm_le_one_of_isIntegral (hR : ∀ r : R, ‖algebraMap R F r‖ ≤ 1) (f : A →ₐ[R] F)
    {a : A} (ha : IsIntegral R a) : ‖f a‖ ≤ 1 := by
  obtain ⟨P, hP, hPa⟩ := ha
  set x := f a
  have hx : Polynomial.aeval x P = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hPa, map_zero]
  by_contra hlt
  replace hlt := not_le.mp hlt
  rw [hP.as_sum, map_add, map_sum, map_pow, Polynomial.aeval_X] at hx
  have hn : P.natDegree ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Finset.range_zero, Finset.sum_empty, add_zero] at hx
    exact one_ne_zero hx
  have hsum : ‖∑ i ∈ Finset.range P.natDegree, Polynomial.aeval x (Polynomial.C (P.coeff i) *
      Polynomial.X ^ i)‖ ≤ ‖x‖ ^ (P.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, norm_mul, norm_pow]
    calc ‖algebraMap R F (P.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
          gcongr; exact hR _
      _ ≤ ‖x‖ ^ (P.natDegree - 1) := by
          rw [one_mul]
          exact pow_le_pow_right₀ hlt.le (by have := Finset.mem_range.mp hi; omega)
  have h1 : ‖x ^ P.natDegree‖ = ‖x‖ ^ P.natDegree := norm_pow _ _
  rw [add_eq_zero_iff_eq_neg] at hx
  rw [hx, norm_neg] at h1
  have h2 : ‖x‖ ^ (P.natDegree - 1) < ‖x‖ ^ P.natDegree := pow_lt_pow_right₀ hlt (by omega)
  linarith

/-- **Rigidity of unramified points**: two `R`-algebra maps from a formally unramified `R`-algebra
to an ultrametric field that are congruent modulo the maximal ideal of the unit ball agree. -/
theorem algHom_eq_of_norm_sub_lt_one [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    (f g : A →ₐ[R] F) (hf : ∀ a, ‖f a‖ ≤ 1) (hfg : ∀ a, ‖f a - g a‖ < 1) : f = g := by
  obtain ⟨t, ht1, ht2⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let h : A ⊗[R] A →ₐ[R] F := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hclose : ∀ x : A ⊗[R] A, ‖h x - f (Algebra.TensorProduct.lmul' R x)‖ < 1 := by
    intro x
    induction x with
    | zero => simp
    | tmul a b =>
      simp only [h, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        map_mul]
      rw [← mul_sub, norm_mul]
      calc ‖f a‖ * ‖g b - f b‖ ≤ 1 * ‖g b - f b‖ := by gcongr; exact hf a
        _ < 1 := by rw [one_mul, norm_sub_rev]; exact hfg b
    | add x y hx hy =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  have hne : h t ≠ 0 := by
    intro h0
    have := hclose t
    rw [h0, ht2, map_one, zero_sub, norm_neg, norm_one] at this
    exact lt_irrefl _ this
  ext s
  have := congrArg h (ht1 s)
  rw [map_mul, map_zero, map_sub] at this
  simp only [h, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at this
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)).symm

end Rigidity

variable {p : ℕ} [hp : Fact p.Prime]

/-- `σ` lies in the inertia group: it acts trivially on the residue field of `ℚ̄_p`. -/
def IsInertia (σ : PadicAlgCl p → PadicAlgCl p) : Prop :=
  ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1

namespace FFGroupScheme

variable {R : Type*} [CommRing R] [Algebra R (PadicAlgCl p)]

/-- **Inertia fixes the `ℚ̄_p`-points of a finite étale group scheme over `R`**, if `R` maps into
the unit ball of `ℚ̄_p` (e.g. `R = ℤ_p`). -/
theorem inertia_comp_eq (G : FFGroupScheme R) (hG : G.IsEtale)
    (hR : ∀ r : R, ‖algebraMap R (PadicAlgCl p) r‖ ≤ 1)
    (σ : PadicAlgCl p →ₐ[R] PadicAlgCl p) (hσ : IsInertia (p := p) σ)
    (φ : G.A →ₐ[R] PadicAlgCl p) : σ.comp φ = φ := by
  have : Algebra.Etale R G.A := hG
  have hφ : ∀ a, ‖φ a‖ ≤ 1 := fun a =>
    norm_le_one_of_isIntegral hR φ (Algebra.IsIntegral.isIntegral a)
  refine (algHom_eq_of_norm_sub_lt_one φ (σ.comp φ) hφ fun a => ?_).symm
  rw [norm_sub_rev]
  exact hσ _ (hφ a)

end FFGroupScheme

theorem norm_algebraMap_padicInt_le_one (r : ℤ_[p]) :
    ‖algebraMap ℤ_[p] (PadicAlgCl p) r‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one r

namespace PDivGroup

/-- **The Galois representation on `T_p` of (the generic fibre of) a `p`-divisible group over
`ℤ_p` with étale layers is unramified**: inertia acts trivially. -/
theorem galTate_baseChange_eq_of_isInertia (G : PDivGroup ℤ_[p] p) (hG : ∀ v, (G.G v).IsEtale)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : IsInertia (p := p) σ)
    (x : (G.baseChange ℚ_[p]).TateModule (PadicAlgCl p)) :
    (G.baseChange ℚ_[p]).galTate σ x = x := by
  apply Subtype.ext
  funext v
  apply WithConv.ofConv_injective
  set φ : ℚ_[p] ⊗[ℤ_[p]] (G.G v).A →ₐ[ℚ_[p]] PadicAlgCl p := ofConv (x.1 v)
  change (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp φ = φ
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
  have := (G.G v).inertia_comp_eq (hG v) norm_algebraMap_padicInt_le_one
    ((σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).restrictScalars ℤ_[p]) hσ
    ((φ.restrictScalars ℤ_[p]).comp Algebra.TensorProduct.includeRight)
  exact this

end PDivGroup

end PadicHodge
