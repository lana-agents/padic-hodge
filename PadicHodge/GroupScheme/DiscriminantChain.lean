/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.HopfTrace

/-!
# Discriminants of orders in a fixed finite étale algebra

Two facts used in the stabilisation step of [Hong, proof of Prop. 3.5.3] (which replaces the
noetherianity of the integral closure, [AM, Prop. 5.17], by an ascending chain of discriminant
ideals):

* `discIdeal_le_of_bijective_baseChange`: for a map `α : B → A` of finite free `R`-algebras of
  the same rank which becomes bijective after `K ⊗_R -` (`R ↪ K`), `disc(B) ⊆ disc(A)`
  (`disc(B) = det(α)² disc(A)`): the larger order has the smaller discriminant;
* `discIdeal_ne_bot_of_etale`: the discriminant of `B` is nonzero if `Ω ⊗_R B` is étale over a
  separably closed field `Ω ⊇ R` (the trace form of `Ω^X` is the standard one).
-/

noncomputable section

open Module Matrix TensorProduct

namespace PadicHodge

variable {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- **`disc(B) ⊆ disc(A)`** for a map `α : B → A` of finite free algebras of the same rank,
bijective after `K ⊗_R -`. -/
theorem discIdeal_le_of_bijective_baseChange [IsDomain R] [Module.Free R A] [Module.Finite R A]
    [Module.Free R B] [Module.Finite R B] (K : Type*) [CommRing K] [Algebra R K]
    (hrank : finrank R A = finrank R B) (hK : Function.Injective (algebraMap R K))
    (α : B →ₐ[R] A) (hα : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id K K) α)) :
    discIdeal R B ≤ discIdeal R A := by
  classical
  let b := Module.finBasis R B
  let a := Module.finBasisOfFinrankEq R A hrank
  rw [discIdeal_eq_span_discr a, discIdeal_eq_span_discr b, Ideal.span_singleton_le_span_singleton]
  have hTr := trace_algebraMap_of_bijective_baseChange K hK α hα
  set M := a.toMatrix (α ∘ b)
  have h1 : (α ∘ b : Fin (finrank R B) → A) = (a : Fin (finrank R B) → A) ᵥ*
      M.map (algebraMap R A) := by
    funext j
    rw [vecMul, dotProduct]
    conv_lhs => rw [← a.sum_toMatrix_smul_self (α ∘ b) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_apply, Algebra.smul_def, mul_comm]
  have h2 : Algebra.discr R (α ∘ b) = Algebra.discr R b := by
    rw [Algebra.discr_def, Algebra.discr_def]
    congr 1
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Function.comp_apply,
      ← map_mul, hTr]
  rw [h1, Algebra.discr_of_matrix_vecMul] at h2
  exact ⟨M.det ^ 2, by rw [← h2, mul_comm]⟩

/-- The trace form of a finite étale algebra over a separably closed field is nondegenerate. -/
theorem traceForm_nondegenerate_of_etale (Ω C : Type*) [Field Ω] [IsSepClosed Ω] [CommRing C]
    [Algebra Ω C] [Module.Finite Ω C] [Algebra.Etale Ω C] :
    (Algebra.traceForm Ω C).Nondegenerate := by
  have : IsArtinianRing C := IsArtinianRing.of_finite Ω C
  classical
  let X := PrimeSpectrum C
  have : Fintype X := Fintype.ofFinite X
  let e : C ≃ₐ[Ω] (X → Ω) := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω C
  have key : ∀ x : C, (∀ y, Algebra.trace Ω C (x * y) = 0) → x = 0 := by
    intro x hx
    apply e.injective
    funext s
    have h := hx (e.symm (Pi.single s 1))
    rw [← Algebra.trace_eq_of_algEquiv e, map_mul, e.apply_symm_apply, trace_pi_eq_sum] at h
    rw [map_zero, Pi.zero_apply, ← h, Finset.sum_eq_single s]
    · simp
    · intro t _ hts
      simp [hts]
    · simp
  exact ⟨fun x hx => key x hx, fun y hy => key y fun x => by rw [mul_comm]; exact hy x⟩

/-- **The discriminant of `B` is nonzero if `Ω ⊗_R B` is étale** over a separably closed field
`Ω` over `R`. -/
theorem discIdeal_ne_bot_of_etale [Module.Free R B] [Module.Finite R B] (Ω : Type*) [Field Ω]
    [IsSepClosed Ω] [Algebra R Ω] [Algebra.Etale Ω (Ω ⊗[R] B)] [Nontrivial R] :
    discIdeal R B ≠ ⊥ := by
  classical
  let b := Module.finBasis R B
  rw [discIdeal_eq_span_discr b, Ne, Ideal.span_singleton_eq_bot]
  intro h0
  have h1 := discr_baseChange Ω b
  rw [h0, map_zero, Algebra.discr_def, Algebra.traceMatrix_of_basis] at h1
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (traceForm_nondegenerate_of_etale Ω (Ω ⊗[R] B)) h1

end PadicHodge
