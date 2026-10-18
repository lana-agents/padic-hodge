/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TateFree
import PadicHodge.GroupScheme.EtalePoints
import PadicHodge.GroupScheme.BaseChange
import PadicHodge.GroupScheme.EtaleInvertible

/-!
# Faithfulness of `G ↦ T_p G` and of the generic fibre functor

Let `R` be a ring and `Ω` a separably closed field which is an `R`-algebra with `p ≠ 0` in `Ω`
and `R → Ω` injective (e.g. `R = O_K`, `Ω = ℚ̄_p`). For `p`-divisible groups `G`, `H` over `R`:

* `card_points_sepClosed`: `#G_v(Ω) = p^{hv}` (the layers of `G_Ω` are étale since `p` is
  invertible in `Ω`; `FFGroupScheme.card_points_of_isEtale`); hence the quotient maps are
  surjective on `Ω`-points and `T_p G(Ω) → G_v(Ω)` is surjective (`proj_surjective_sepClosed`);
* `eq_of_forall_algHom_eq`: `Ω`-points separate the elements of a finite étale `Ω`-algebra;
* **`Hom.ext_of_mapTate`**: a homomorphism `G → H` is determined by the induced map
  `T_p G(Ω) → T_p H(Ω)` (`A_v` is free over `R`, so `A_v ↪ Ω ⊗_R A_v`, whose `Ω`-points
  separate elements);
* **`Hom.ext_of_baseChange`**: the generic fibre functor is faithful: if `φ_K = ψ_K` for a field
  `R → K → Ω`, then `φ = ψ`. This is the uniqueness part of [Hong, Thm. 3.5.4, proof]
  ("there exists at most one `O_K`-algebra homomorphism `α_v : B_v → A_v` such that
  `α_v ⊗ 1 = α̃_v`") together with the faithfulness part of [Hong, Prop. 2.1.14].
-/

noncomputable section

open WithConv TensorProduct

namespace PadicHodge

universe u

/-- **Points separate elements of a finite étale algebra over a separably closed field.** -/
theorem eq_of_forall_algHom_eq {Ω B : Type*} [Field Ω] [IsSepClosed Ω] [CommRing B]
    [Algebra Ω B] [Module.Finite Ω B] [Algebra.Etale Ω B] {a b : B}
    (h : ∀ y : B →ₐ[Ω] Ω, y a = y b) : a = b := by
  have : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  classical
  let X := PrimeSpectrum B
  have : Fintype X := Fintype.ofFinite X
  let e : B ≃ₐ[Ω] (X → Ω) := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω B
  apply e.injective
  funext x
  exact h ((Pi.evalAlgHom Ω (fun _ : X => Ω) x).comp (e : B →ₐ[Ω] (X → Ω)))

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ} [hp : Fact p.Prime]
  (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω] (hpΩ : (p : Ω) ≠ 0)

include hpΩ

omit hp in
/-- **`#G_v(Ω) = p^{hv}`** for `Ω` separably closed with `p ≠ 0` in `Ω`. -/
theorem card_points_sepClosed (G : PDivGroup R p) (v : ℕ) :
    Nat.card ((G.G v).points Ω) = p ^ (G.height * v) := by
  have hu : IsUnit (p : Ω) := isUnit_iff_ne_zero.mpr hpΩ
  have hG : ((G.G v).baseChange Ω).IsEtale := (G.baseChange Ω).isEtale_of_isUnit hu v
  rw [← Nat.card_congr ((G.G v).baseChangePointsEquiv (S := Ω) Ω).toEquiv,
    FFGroupScheme.card_points_of_isEtale _ hG]
  exact ((G.baseChange Ω).order_eq v)

theorem quot_surjective_sepClosed (G : PDivGroup R p) (v : ℕ) :
    Function.Surjective ((G.quot v).mapPoints Ω) :=
  G.quot_surjective_of_card Ω hp.out.pos (G.card_points_sepClosed Ω hpΩ) v

/-- `T_p G(Ω) → G_v(Ω)` is surjective. -/
theorem proj_surjective_sepClosed (G : PDivGroup R p) (v : ℕ) :
    Function.Surjective (TateModule.proj G Ω v) :=
  TateModule.proj_surjective G Ω (G.quot_surjective_sepClosed Ω hpΩ) v

omit hpΩ [Nontrivial R] hp in
theorem Hom.ext' {G H : PDivGroup R p} {φ ψ : Hom G H} (h : ∀ v, φ.f v = ψ.f v) : φ = ψ := by
  cases φ; cases ψ; congr; funext v; exact h v

/-- **A homomorphism of `p`-divisible groups is determined by its effect on `T_p(Ω)`.** -/
theorem Hom.ext_of_mapTate (hinj : Function.Injective (algebraMap R Ω)) {G H : PDivGroup R p}
    {φ ψ : Hom G H} (h : ∀ x : G.TateModule Ω, φ.mapTate Ω x = ψ.mapTate Ω x) : φ = ψ := by
  refine Hom.ext' fun v => BialgHom.ext fun b => ?_
  have key : ∀ x : (G.G v).points Ω, ofConv x (φ.f v b) = ofConv x (ψ.f v b) := by
    intro x
    obtain ⟨t, rfl⟩ := G.proj_surjective_sepClosed Ω hpΩ v x
    exact congrArg (fun z : H.TateModule Ω => ofConv (z.1 v) b) (h t)
  have hu : IsUnit (p : Ω) := isUnit_iff_ne_zero.mpr hpΩ
  have hG : Algebra.Etale Ω (Ω ⊗[R] (G.G v).A) := (G.baseChange Ω).isEtale_of_isUnit hu v
  apply Algebra.TensorProduct.includeRight_injective (A := Ω) (R := R) hinj
  apply eq_of_forall_algHom_eq (Ω := Ω)
  intro y
  exact key ((G.G v).baseChangePointsEquiv Ω (toConv y))

/-- **Faithfulness of the generic fibre functor** ([Hong, Thm. 3.5.4, uniqueness]): homomorphisms
`G → H` over `R` agreeing after base change to a field `K` (with `R → K → Ω`) are equal. -/
theorem Hom.ext_of_baseChange (hinj : Function.Injective (algebraMap R Ω)) (K : Type u) [Field K]
    [Algebra R K] [Algebra K Ω] [IsScalarTower R K Ω] {G H : PDivGroup R p} {φ ψ : Hom G H}
    (h : φ.baseChange (S := K) = ψ.baseChange (S := K)) : φ = ψ := by
  refine Hom.ext_of_mapTate Ω hpΩ hinj fun x => ?_
  have e1 := Hom.baseChange_mapTate (S := K) G Ω φ ((G.baseChangeTateEquiv Ω).symm x)
  have e2 := Hom.baseChange_mapTate (S := K) G Ω ψ ((G.baseChangeTateEquiv Ω).symm x)
  rw [MulEquiv.apply_symm_apply] at e1 e2
  rw [← e1, ← e2, h]

end PDivGroup

end PadicHodge
