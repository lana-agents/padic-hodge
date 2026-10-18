/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.HopfTrace
import PadicHodge.GroupScheme.EtaleQuotientOrder
import PadicHodge.GroupScheme.EtaleQuotientEtale

/-!
# Integrals and traces of `G` from those of its connected component

Over a complete local ring `R`, with `G⁰ = Spec A⁰`, `A⁰ = A/(1 − e₀)`:

* `IsIntegral.map`: a surjective bialgebra map carries integrals to integrals with the same
  counit (e.g. along an isomorphism `G⁰ ≅ F[p^v]`);
* `exists_isIntegral_of_connectedComponent`: an integral `Λ₀` of `A⁰` lifts to the integral
  `e₀ Λ'` of `A` (`Λ'` any preimage), with the same counit;
* **`trace_mem_of_connectedComponent`** (`R` a complete local PID domain, e.g. `O_{K'}`):
  if `Tr_{A⁰/R}(A⁰) ⊆ I` then `Tr_{A/R}(A) ⊆ I`. Proof: `Tr_{A/R} = Tr_{A^{et}/R} ∘ Tr_{A/A^{et}}`
  (`A` is free over `A^{et}`), and after the faithfully flat base change `A^{et} → A` the trace
  of `A/A^{et}` becomes, by the Galois isomorphism `A ⊗_{A^{et}} A ≅ A ⊗_R A⁰`, the trace of
  `A ⊗_R A⁰` over `A`, with values in `I A`; faithful flatness gives `I A ∩ A^{et} = I A^{et}`.

This is the reduction of [Hong, Prop. 3.5.1] to connected `G` (the connected–étale sequence in
[Hong, remark after Prop. 3.5.1], [Haines, Lemma 2.3.2]), in the form needed by
`FFGroupScheme.discIdeal_eq_of_trace_eq_smul`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.5.1 and the remark after it.
-/

noncomputable section

open Module TensorProduct Coalgebra IsLocalRing

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R]

/-- **Integrals along surjective bialgebra maps.** -/
theorem IsIntegral.map {G H : FFGroupScheme R} (f : Hom G H) (hf : Function.Surjective f)
    {Λ : H.A} (hΛ : H.IsIntegral Λ) : G.IsIntegral (f Λ) := by
  intro a
  obtain ⟨b, rfl⟩ := hf a
  rw [← map_mul, hΛ b, map_mul, AlgHomClass.commutes, CoalgHomClass.counit_comp_apply]

theorem counit_map {G H : FFGroupScheme R} (f : Hom G H) (Λ : H.A) :
    counit (R := R) (f Λ) = counit (R := R) Λ :=
  CoalgHomClass.counit_comp_apply f Λ

/-- Traces along bijective algebra maps. -/
theorem trace_map_of_bijective {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : B →ₐ[R] A) (hf : Function.Bijective f) (x : B) :
    Algebra.trace R A (f x) = Algebra.trace R B x :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective f hf) x

variable [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (G : FFGroupScheme R)

/-- **Lifting integrals from `G⁰`**: `Λ = e₀ Λ'` for a preimage `Λ'` of `Λ₀`. -/
theorem exists_isIntegral_of_connectedComponent {Λ₀ : G.connectedComponent.A}
    (hΛ₀ : G.connectedComponent.IsIntegral Λ₀) :
    ∃ Λ : G.A, G.IsIntegral Λ ∧ counit (R := R) Λ = counit (R := R) Λ₀ := by
  obtain ⟨Λ', hΛ'⟩ := G.connectedComponentHom_surjective Λ₀
  have he := G.isPointIdempotent_idemConn
  refine ⟨G.idemConn * Λ', fun a => ?_, ?_⟩
  · have h1 : G.connectedComponentHom (a * Λ' - algebraMap R G.A (counit (R := R) a) * Λ') = 0 := by
      rw [map_sub, map_mul, map_mul, AlgHomClass.commutes, hΛ',
        ← counit_map G.connectedComponentHom a, ← hΛ₀, sub_self]
    have h1' : a * Λ' - algebraMap R G.A (counit (R := R) a) * Λ' ∈ G.connIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.mp h1
    rw [connIdeal, Ideal.mem_span_singleton] at h1'
    obtain ⟨r, hr⟩ := h1'
    have h2 : G.idemConn * (a * Λ' - algebraMap R G.A (counit (R := R) a) * Λ') = 0 := by
      rw [hr, ← mul_assoc, mul_sub, mul_one, he.1.eq, sub_self, zero_mul]
    rw [mul_sub] at h2
    rw [mul_left_comm, sub_eq_zero.mp h2, mul_left_comm]
  · rw [Bialgebra.counit_mul, G.counit_idemConn, one_mul, ← hΛ', counit_map]

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] in
/-- Traces of `B ⊗_R C` over `B`: values in `I B` if `Tr_{C/R}(C) ⊆ I`. -/
theorem trace_baseChange_mem {B C : Type*} [CommRing B] [Algebra R B] [CommRing C]
    [Algebra R C] [Module.Free R C] [Module.Finite R C] {I : Ideal R}
    (hC : ∀ y : C, Algebra.trace R C y ∈ I) (z : B ⊗[R] C) :
    Algebra.trace B (B ⊗[R] C) z ∈ I.map (algebraMap R B) := by
  induction z with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  | tmul b c =>
    have : b ⊗ₜ[R] c = b • (1 ⊗ₜ c : B ⊗[R] C) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, trace_tmul, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hC c))

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- **Traces of `G` from traces of `G⁰`**: if `Tr_{A⁰/R}(A⁰) ⊆ I`, then `Tr_{A/R}(A) ⊆ I`. -/
theorem trace_mem_of_connectedComponent {I : Ideal R}
    (hI : ∀ y : G.connectedComponent.A, Algebra.trace R G.connectedComponent.A y ∈ I)
    (x : G.A) : Algebra.trace R G.A x ∈ I := by
  obtain ⟨b⟩ := G.nonempty_basis_etaleInvariants
  have : Module.Free G.etaleInvariants G.A := .of_basis b
  have := G.faithfullyFlat_etaleInvariants
  rw [← Algebra.trace_trace (S := G.etaleInvariants)]
  -- the trace over `A^{et}` lies in `I A^{et}`
  have h1 : Algebra.trace G.etaleInvariants G.A x ∈ I.map (algebraMap R G.etaleInvariants) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := G.A)
      (I.map (algebraMap R G.etaleInvariants)), Ideal.mem_comap, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← trace_tmul,
      ← Algebra.trace_eq_of_algEquiv G.galoisEquiv]
    exact trace_baseChange_mem hI _
  suffices h : ∀ z, Algebra.trace R G.etaleInvariants
      (z * Algebra.trace G.etaleInvariants G.A x) ∈ I by simpa using h 1
  refine Submodule.span_induction
    (p := fun y _ => ∀ z, Algebra.trace R G.etaleInvariants (z * y) ∈ I) ?_ ?_ ?_ ?_ h1
  · rintro _ ⟨r, hr, rfl⟩ z
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  · simp
  · intro y w _ _ hy hw z
    rw [mul_add, map_add]
    exact Ideal.add_mem _ (hy z) (hw z)
  · intro c y _ hy z
    rw [smul_eq_mul, ← mul_assoc]
    exact hy (z * c)

end FFGroupScheme

end PadicHodge
