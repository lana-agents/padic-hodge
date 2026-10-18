/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.LayerFree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Lifting points along a finite free endomorphism

If a commutative ring `A` is free of finite positive rank over itself via `φ : A → A`
(`FreeVia φ n`, `n > 0`), then every ring map `y : A → K` to an algebraically closed field lifts
along `φ`: `y = x ∘ φ` for some `x : A → K` (`FreeVia.exists_lift`). This is the algebraic input
of [Hong, Prop. 3.2.7] (`p`-divisibility of `F(m_{ℂ_p})` for `p`-divisible `F`: apply it to
`φ = [p]^*`). Proof: `A` is integral over `φ(A)`, so there is a prime `Q` of `A` over
`P = ker y` (going up), and `IsAlgClosed.lift` extends `A/P ↪ K` to the integral extension
`A/Q` of `A/P`.
-/

noncomputable section

namespace PadicHodge

namespace FGL

variable {A : Type*} [CommRing A]

/-- `A` regarded as an `A`-algebra via `φ`. -/
def ViaRing (_φ : A →+* A) : Type _ := A

instance (φ : A →+* A) : CommRing (ViaRing φ) := inferInstanceAs (CommRing A)

instance (φ : A →+* A) : Algebra A (ViaRing φ) := (show A →+* ViaRing φ from φ).toAlgebra

theorem FreeVia.injective {φ : A →+* A} {n : ℕ} (hφ : FreeVia φ n) (hn : 0 < n) :
    Function.Injective φ := by
  obtain ⟨b, hb⟩ := hφ
  rw [injective_iff_map_eq_zero]
  intro c hc
  have key : (∑ i, φ ((Pi.single (⟨0, hn⟩ : Fin n) c : Fin n → A) i) * b i) =
      ∑ i, φ ((0 : Fin n → A) i) * b i := by
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : i = ⟨0, hn⟩
    · subst h; simp [hc]
    · simp [h]
  have := congrFun (hb.1 key) ⟨0, hn⟩
  simpa using this

theorem FreeVia.finite {φ : A →+* A} {n : ℕ} (hφ : FreeVia φ n) :
    Module.Finite A (ViaRing φ) := by
  obtain ⟨b, hb⟩ := hφ
  refine Module.Finite.of_surjective
    (Fintype.linearCombination A (fun i => (b i : ViaRing φ))) fun s => ?_
  obtain ⟨c, hc⟩ := hb.2 s
  refine ⟨c, ?_⟩
  rw [Fintype.linearCombination_apply]
  exact hc

/-- **Lifting along a finite free endomorphism** into an algebraically closed field. -/
theorem FreeVia.exists_lift {K : Type*} [Field K] [IsAlgClosed K] {φ : A →+* A} {n : ℕ}
    (hφ : FreeVia φ n) (hn : 0 < n) (y : A →+* K) : ∃ x : A →+* K, x.comp φ = y := by
  haveI := hφ.finite
  haveI : Algebra.IsIntegral A (ViaRing φ) := Algebra.IsIntegral.of_finite A _
  set P := RingHom.ker y
  haveI : P.IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := ViaRing φ) P ⊥
    (by
      intro a ha
      have h0 : φ a = 0 := ha
      have : a = 0 := hφ.injective hn (by rw [h0, map_zero])
      rw [this]
      exact P.zero_mem)
  haveI : Q.IsPrime := hQ
  haveI : Q.LiesOver P := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ P) K := (RingHom.kerLift y).toAlgebra
  haveI : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  haveI : IsDomain (ViaRing φ ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Module.IsTorsionFree (A ⧸ P) K :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr (RingHom.kerLift_injective y)
  have hinj : Function.Injective (algebraMap (A ⧸ P) (ViaRing φ ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h0 : Ideal.Quotient.mk Q (algebraMap A (ViaRing φ) a) = 0 := hz
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hQP] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h0
  haveI : Module.IsTorsionFree (A ⧸ P) (ViaRing φ ⧸ Q) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
  haveI : Algebra.IsAlgebraic (A ⧸ P) (ViaRing φ ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let L : (ViaRing φ ⧸ Q) →ₐ[A ⧸ P] K := IsAlgClosed.lift
  refine ⟨(L : ViaRing φ ⧸ Q →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h1 : (Ideal.Quotient.mk Q (algebraMap A (ViaRing φ) a)) =
      algebraMap (A ⧸ P) (ViaRing φ ⧸ Q) (Ideal.Quotient.mk P a) := rfl
  change L (Ideal.Quotient.mk Q (algebraMap A (ViaRing φ) a)) = y a
  rw [h1, L.commutes]
  rfl

end FGL

end PadicHodge
