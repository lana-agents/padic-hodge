/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.EtaleInvertible
import PadicHodge.GroupScheme.BaseChange
import PadicHodge.Galois.Basic
import Mathlib.RingTheory.Etale.Field

/-!
# Points of étale group schemes over separably closed fields

* `card_algHom_pi`: the `K`-algebra maps `K^X → K` are the evaluations, so there are `|X|`;
* `FFGroupScheme.card_points_of_isEtale`: for `G` étale over a separably closed field `K`,
  `#G(K) = |G|` (Mathlib: a finite étale `K`-algebra is `K^{Spec A}`,
  `Algebra.FormallyEtale.equivPiOfIsSepClosed`);
* `PDivGroup.card_points_padicAlgCl`: for a `p`-divisible group `G` of height `h` over `ℚ_p`,
  `#G_v(ℚ̄_p) = p^{hv}` (the layers are étale, `PDivGroup.isEtale_of_isUnit`, and étaleness is
  stable under base change); compare [Stix, §11.2] (`T_p(G) ≅ ℤ_p^h`) and [Hong, Lemma 3.4.1].
-/

noncomputable section

open WithConv TensorProduct

namespace PadicHodge

universe u

section AlgHomPi

variable (K : Type*) [Field K] (X : Type*) [Finite X]

theorem exists_eq_evalAlgHom (φ : (X → K) →ₐ[K] K) :
    ∃ x, φ = Pi.evalAlgHom K (fun _ => K) x := by
  classical
  cases nonempty_fintype X
  have hsum : ∑ x, (Pi.single x 1 : X → K) = 1 := by
    ext y
    simp [Finset.sum_apply, Pi.single_apply]
  have hφsum : ∑ x, φ (Pi.single x 1) = 1 := by rw [← map_sum, hsum, map_one]
  obtain ⟨x, hx⟩ : ∃ x, φ (Pi.single x 1) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hφsum
  refine ⟨x, AlgHom.ext fun f => ?_⟩
  have h1 : f * Pi.single x 1 = f x • (Pi.single x 1 : X → K) := by
    ext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  have h2 := congrArg φ h1
  rw [map_mul, map_smul, smul_eq_mul] at h2
  exact mul_right_cancel₀ hx h2

theorem card_algHom_pi : Nat.card ((X → K) →ₐ[K] K) = Nat.card X := by
  classical
  refine (Nat.card_eq_of_bijective (fun x => Pi.evalAlgHom K (fun _ => K) x) ⟨?_, ?_⟩).symm
  · intro x y h
    have := congrArg (fun φ : (X → K) →ₐ[K] K => φ (Pi.single x 1)) h
    by_contra hxy
    simp [Ne.symm hxy] at this
  · intro φ
    obtain ⟨x, hx⟩ := exists_eq_evalAlgHom K X φ
    exact ⟨x, hx.symm⟩

end AlgHomPi

namespace FFGroupScheme

variable {K : Type u} [Field K] [IsSepClosed K]

/-- **An étale group scheme over a separably closed field has `|G|` points.** -/
theorem card_points_of_isEtale (G : FFGroupScheme K) (hG : G.IsEtale) :
    Nat.card (G.points K) = G.order := by
  have : Algebra.Etale K G.A := hG
  have : IsArtinianRing G.A := IsArtinianRing.of_finite K G.A
  classical
  let X := PrimeSpectrum G.A
  have : Fintype X := Fintype.ofFinite X
  let e : G.A ≃ₐ[K] (X → K) := Algebra.FormallyEtale.equivPiOfIsSepClosed K G.A
  have h1 : G.order = Fintype.card X := by
    rw [order, e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]
  have h2 : Nat.card (G.points K) = Nat.card ((X → K) →ₐ[K] K) := by
    refine Nat.card_congr ((WithConv.equiv _).trans ?_)
    exact
      { toFun := fun φ => φ.comp (e.symm : (X → K) →ₐ[K] G.A)
        invFun := fun ψ => ψ.comp (e : G.A →ₐ[K] (X → K))
        left_inv := fun φ => AlgHom.ext fun a => by simp
        right_inv := fun ψ => AlgHom.ext fun f => by simp }
  rw [h2, card_algHom_pi, h1, Nat.card_eq_fintype_card]

end FFGroupScheme

namespace PDivGroup

variable {p : ℕ} [hp : Fact p.Prime]

/-- **`#G_v(ℚ̄_p) = p^{hv}`** for a `p`-divisible group of height `h` over `ℚ_p`. -/
theorem card_points_padicAlgCl (G : PDivGroup ℚ_[p] p) (v : ℕ) :
    Nat.card ((G.G v).points (PadicAlgCl p)) = p ^ (G.height * v) := by
  have hu : IsUnit (p : ℚ_[p]) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hp.out.ne_zero
  have hG : (G.G v).IsEtale := G.isEtale_of_isUnit hu v
  have : Algebra.Etale ℚ_[p] (G.G v).A := hG
  have hGS : ((G.G v).baseChange (PadicAlgCl p)).IsEtale :=
    (inferInstance : Algebra.Etale (PadicAlgCl p) (PadicAlgCl p ⊗[ℚ_[p]] (G.G v).A))
  rw [← Nat.card_congr ((G.G v).baseChangePointsEquiv (S := PadicAlgCl p) (PadicAlgCl p)).toEquiv,
    FFGroupScheme.card_points_of_isEtale _ hGS, FFGroupScheme.order_baseChange, G.order_eq v]

end PDivGroup

end PadicHodge
