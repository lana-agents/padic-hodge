/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Discriminant
import PadicHodge.GroupScheme.Faithful

/-!
# Traces of finite group schemes with étale generic fibre, and integrals

Let `G = Spec A` be a finite flat commutative group scheme over `R` (`FFGroupScheme R`) and
`R → Ω` an injective map to a separably closed field such that `Ω ⊗_R A` is étale over `Ω`
(e.g. `R = O_{K'}`, `Ω = ℚ̄_p`, `G` killed by a power of `p`). Then `A ⊗ Ω ≅ Ω^{G(Ω)}` and:

* `trace_pi_eq_sum`: `Tr_{K^X/K}(f) = ∑_x f(x)` (traces on finite products of copies of `K`);
* `trace_eq_sum_algHom`: for a finite étale algebra `B` over a separably closed field `Ω`,
  `Tr_{B/Ω}(y) = ∑_{k : B → Ω} k(y)`;
* `FFGroupScheme.algebraMap_trace_eq_sum`: `Tr_{A/R}(x) = ∑_{k ∈ G(Ω)} k(x)` in `Ω`;
* `FFGroupScheme.eq_of_forall_points`: elements of `A` are separated by `G(Ω)`;
* `FFGroupScheme.apply_integral`: an **integral** `Λ ∈ A` (`a Λ = ε(a) Λ` for all `a`) vanishes at
  every point `k ≠ 1` of `G(Ω)` (`Λ = ε(Λ) δ_1`);
* **`FFGroupScheme.trL_mul_comul_integral`** (the trace formula for integrals):
  `(Tr ⊗ id)((x ⊗ 1) Δ(Λ)) = ε(Λ) S(x)` for an integral `Λ`; pointwise this is
  `∑_k k(x) Λ(k l) = ε(Λ) x(l⁻¹)`;
* `FFGroupScheme.antipode_antipode`: `S ∘ S = id`.

These are the analytic-free inputs of the discriminant formula [Hong, Prop. 3.5.1]
(`HopfDisc.lean`): the trace form of `A` factors through the map `Hom_R(A, R) → A`,
`φ ↦ (φ ⊗ id) Δ(Λ)`, up to `ε(Λ) S`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.5.1.
-/

noncomputable section

open Module TensorProduct Coalgebra HopfAlgebra WithConv

namespace PadicHodge

universe u

/-- **Traces on `K^X`**: `Tr_{K^X/K}(f) = ∑_x f(x)`. -/
theorem trace_pi_eq_sum (K : Type*) [CommRing K] (X : Type*) [Fintype X]
    (f : X → K) : Algebra.trace K (X → K) f = ∑ x, f x := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K X), Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  simp

/-- **Traces of finite étale algebras over separably closed fields**:
`Tr_{B/Ω}(y) = ∑_{k : B →ₐ Ω} k(y)`. -/
theorem trace_eq_sum_algHom {Ω B : Type*} [Field Ω] [IsSepClosed Ω] [CommRing B] [Algebra Ω B]
    [Module.Finite Ω B] [Algebra.Etale Ω B] [Fintype (B →ₐ[Ω] Ω)] (y : B) :
    Algebra.trace Ω B y = ∑ k : B →ₐ[Ω] Ω, k y := by
  have : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  classical
  let X := PrimeSpectrum B
  have : Fintype X := Fintype.ofFinite X
  let e : B ≃ₐ[Ω] (X → Ω) := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω B
  rw [← Algebra.trace_eq_of_algEquiv e y, trace_pi_eq_sum]
  refine Fintype.sum_bijective
    (fun x => (Pi.evalAlgHom Ω (fun _ => Ω) x).comp (e : B →ₐ[Ω] (X → Ω))) ⟨?_, ?_⟩ _ _
    (fun x => rfl)
  · intro x x' h
    have := congrArg (fun k : B →ₐ[Ω] Ω => k (e.symm (Pi.single x 1))) h
    by_contra hxx
    simp [Ne.symm hxx] at this
  · intro k
    obtain ⟨x, hx⟩ := exists_eq_evalAlgHom Ω X (k.comp (e.symm : (X → Ω) →ₐ[Ω] B))
    refine ⟨x, AlgHom.ext fun b => ?_⟩
    have := congrArg (fun φ : (X → Ω) →ₐ[Ω] Ω => φ (e b)) hx
    simpa using this.symm

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]
  (G : FFGroupScheme R)

/-- `G(Ω)` is finite when `G_Ω` is étale. -/
theorem finite_points (hG : (G.baseChange Ω).IsEtale) : Finite (G.points Ω) := by
  have : Algebra.Etale Ω (Ω ⊗[R] G.A) := hG
  have : IsArtinianRing (Ω ⊗[R] G.A) := IsArtinianRing.of_finite Ω _
  classical
  let X := PrimeSpectrum (Ω ⊗[R] G.A)
  have : Fintype X := Fintype.ofFinite X
  let e : (Ω ⊗[R] G.A) ≃ₐ[Ω] (X → Ω) := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω _
  have hinj : Function.Injective fun k : G.points Ω =>
      ((ofConv ((G.baseChangePointsEquiv (S := Ω) Ω).symm k)).comp (e.symm : (X → Ω) →ₐ[Ω] _)) := by
    intro k k' h
    have h' : (G.baseChangePointsEquiv (S := Ω) Ω).symm k =
        (G.baseChangePointsEquiv (S := Ω) Ω).symm k' := by
      apply WithConv.ofConv_injective
      refine AlgHom.ext fun y => ?_
      have := congrArg (fun φ : (X → Ω) →ₐ[Ω] Ω => φ (e y)) h
      simpa using this
    exact (G.baseChangePointsEquiv (S := Ω) Ω).symm.injective h'
  have : Finite ((X → Ω) →ₐ[Ω] Ω) := by
    refine Finite.of_surjective (fun x : X => Pi.evalAlgHom Ω (fun _ => Ω) x) fun φ => ?_
    obtain ⟨x, hx⟩ := exists_eq_evalAlgHom Ω X φ
    exact ⟨x, hx.symm⟩
  exact Finite.of_injective _ hinj

/-- **Traces as sums over points**: `Tr_{A/R}(x) = ∑_{k ∈ G(Ω)} k(x)` in `Ω`, for `G_Ω` étale. -/
theorem algebraMap_trace_eq_sum (hG : (G.baseChange Ω).IsEtale) [Fintype (G.points Ω)]
    (x : G.A) : algebraMap R Ω (Algebra.trace R G.A x) = ∑ k : G.points Ω, ofConv k x := by
  have : Algebra.Etale Ω (Ω ⊗[R] G.A) := hG
  classical
  let E : ((Ω ⊗[R] G.A) →ₐ[Ω] Ω) ≃ G.points Ω :=
    (WithConv.equiv _).symm.trans (G.baseChangePointsEquiv (S := Ω) Ω).toEquiv
  have : Fintype ((Ω ⊗[R] G.A) →ₐ[Ω] Ω) := Fintype.ofEquiv _ E.symm
  rw [← trace_tmul, trace_eq_sum_algHom]
  exact Fintype.sum_bijective E E.bijective _ _ (fun k => rfl)

variable {Ω}

/-- **Points separate elements** of `A` when `R → Ω` is injective and `G_Ω` is étale. -/
theorem eq_of_forall_points (hinj : Function.Injective (algebraMap R Ω))
    (hG : (G.baseChange Ω).IsEtale) {a b : G.A}
    (h : ∀ k : G.points Ω, ofConv k a = ofConv k b) : a = b := by
  have : Algebra.Etale Ω (Ω ⊗[R] G.A) := hG
  have hi : Function.Injective (Algebra.TensorProduct.includeRight : G.A →ₐ[R] Ω ⊗[R] G.A) := by
    have h1 : Function.Injective ((Algebra.linearMap R Ω).rTensor G.A) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hinj
    intro x y hxy
    have h2 : (Algebra.linearMap R Ω).rTensor G.A (1 ⊗ₜ x) =
        (Algebra.linearMap R Ω).rTensor G.A (1 ⊗ₜ y) := by
      simpa using hxy
    have h3 := h1 h2
    have h4 := congrArg (TensorProduct.lid R G.A) h3
    simpa using h4
  apply hi
  refine eq_of_forall_algHom_eq (Ω := Ω) fun y => ?_
  exact h (G.baseChangePointsEquiv (S := Ω) Ω (toConv y))

/-! ### Integrals -/

/-- An **integral** of `A`: `a Λ = ε(a) Λ` for all `a` (the functions supported at the unit). -/
def IsIntegral (Λ : G.A) : Prop := ∀ a : G.A, a * Λ = algebraMap R G.A (counit a) * Λ

variable {G}

open scoped Classical in
/-- An integral vanishes at every point `k ≠ 1` (over a field), and `1(Λ) = ε(Λ)`. -/
theorem apply_integral {S : Type*} [Field S] [Algebra R S] {Λ : G.A} (hΛ : G.IsIntegral Λ)
    (k : G.points S) : ofConv k Λ = if k = 1 then algebraMap R S (counit Λ) else 0 := by
  split_ifs with hk
  · subst hk; rfl
  · have : ∃ a, ofConv k a ≠ algebraMap R S (counit a) := by
      by_contra h
      push Not at h
      exact hk (WithConv.ofConv_injective (AlgHom.ext h))
    obtain ⟨a, ha⟩ := this
    have h1 := congrArg (fun y => ofConv k y) (hΛ a)
    rw [map_mul, map_mul, AlgHom.commutes] at h1
    have h2 : (ofConv k a - algebraMap R S (counit a)) * ofConv k Λ = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr ha)

variable (G)

/-- `(Tr ⊗ id) : A ⊗ A → A`. -/
def trL : G.A ⊗[R] G.A →ₗ[R] G.A :=
  (TensorProduct.lid R G.A).toLinearMap ∘ₗ (Algebra.trace R G.A).rTensor G.A

theorem trL_tmul (a b : G.A) : G.trL (a ⊗ₜ b) = Algebra.trace R G.A a • b := rfl

variable {G}

theorem apply_trL (hG : (G.baseChange Ω).IsEtale) [Fintype (G.points Ω)] (l : G.points Ω)
    (w : G.A ⊗[R] G.A) :
    ofConv l (G.trL w) = ∑ k : G.points Ω,
      Algebra.TensorProduct.lift (ofConv k) (ofConv l) (fun _ _ => .all _ _) w := by
  induction w with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, ← Finset.sum_add_distrib]; simp
  | tmul a b =>
    rw [trL_tmul, map_smul, Algebra.smul_def, algebraMap_trace_eq_sum Ω G hG, Finset.sum_mul]
    rfl

/-- **The trace formula for integrals**: `(Tr ⊗ id)((x ⊗ 1) Δ(Λ)) = ε(Λ) S(x)`. -/
theorem trL_mul_comul_integral (hinj : Function.Injective (algebraMap R Ω))
    (hG : (G.baseChange Ω).IsEtale) {Λ : G.A} (hΛ : G.IsIntegral Λ) (x : G.A) :
    G.trL ((x ⊗ₜ 1) * comul (R := R) Λ) = counit (R := R) Λ • antipode R x := by
  have : Finite (G.points Ω) := G.finite_points Ω hG
  classical
  have : Fintype (G.points Ω) := Fintype.ofFinite _
  refine G.eq_of_forall_points hinj hG fun l => ?_
  rw [apply_trL hG]
  have h1 : ∀ k : G.points Ω, Algebra.TensorProduct.lift (ofConv k) (ofConv l)
      (fun _ _ => .all _ _) ((x ⊗ₜ 1) * comul (R := R) Λ) =
      ofConv k x * (if k * l = 1 then algebraMap R Ω (counit Λ) else 0) := by
    intro k
    rw [map_mul, Algebra.TensorProduct.lift_tmul, map_one, mul_one, ← apply_integral hΛ (k * l),
      AlgHom.convMul_apply]
  simp_rw [h1, mul_eq_one_iff_eq_inv, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [map_smul, Algebra.smul_def, mul_comm]
  rfl

/-- **`S ∘ S = id`** (pointwise: `(l⁻¹)⁻¹ = l`). -/
theorem antipode_antipode (hinj : Function.Injective (algebraMap R Ω))
    (hG : (G.baseChange Ω).IsEtale) (x : G.A) : antipode R (antipode R x) = x :=
  G.eq_of_forall_points hinj hG fun l => by
    change ofConv (l⁻¹⁻¹) x = _
    rw [inv_inv]

end FFGroupScheme

end PadicHodge
