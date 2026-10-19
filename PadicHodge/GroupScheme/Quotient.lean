/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.HaarIntegral
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Quotients of finite flat group schemes: the Galois property

Let `H = Spec C → G = Spec A` be a closed immersion of finite flat commutative group schemes over
a commutative ring `R`, i.e. a bialgebra map `i : A → C` (`Hom H G`) which is surjective. `H`
acts on `G` by translation, with coaction `ρ = (id ⊗ i) ∘ Δ : A → A ⊗_R C` (`Hom.coact`), and
the candidate for the coordinate ring of `G/H` is the ring of invariants
`B = A^H = {a | ρ(a) = a ⊗ 1}` (`Hom.invariants`).

This file proves, **over an arbitrary commutative base ring**, the Galois property of `A/B`
(the affine core of [Hong, Thm. 1.1.9]):

* `Hom.can_bijective`: the map `can : A ⊗_B A → A ⊗_R C`, `x ⊗ y ↦ (x ⊗ 1) ρ(y)`, is an
  isomorphism (`G ×_{G/H} G ≅ G × H`), `Hom.canEquiv`;
* `Hom.projective_invariants`: `A` is a finitely generated projective `B`-module.

The argument is the Kreimer–Takeuchi argument for Hopf–Galois extensions ([Böhm, *Galois theory
for Hopf algebroids*, arXiv:math/0409513, Introduction and §4], quoting Kreimer–Takeuchi,
Thm. 1.7: for a finitely generated projective Hopf algebra, surjectivity of `can` implies its
bijectivity and projectivity of `A` over the coinvariants), written up here in the commutative
case using integrals:

1. `can` is surjective: `1 ⊗ i(y) = ∑ (S y₁ ⊗ 1) ρ(y₂)` (`lift_antipode_coact`; in the group
   `G(A ⊗ C)`: `i₁⁻¹ ρ = i₁⁻¹ i₁ (i₂ ∘ i) = i₂ ∘ i`).
2. By `exists_invariant_forms` (Larson–Sweedler, `HaarIntegral.lean`) there are `H`-invariant
   forms `tⱼ : C → R` and `Λⱼ ∈ C` with `∑ⱼ tⱼ(Λⱼ x) = ε(x)`. The maps
   `trⱼ = (id ⊗ tⱼ) ∘ ρ : A → B` are `B`-linear (`Hom.trace_mem`, `Hom.trace_mul`).
3. Write `1 ⊗ Λⱼ = ∑ₛ (xₛ ⊗ 1) ρ(yₛ)` (by 1). Then `a = ∑ⱼ ∑ₛ xₛ trⱼ(yₛ a)` (**dual basis**,
   `Hom.sum_sum_mul_trace`), so `A` is a direct summand of a finite free `B`-module.
4. If `can(u) = 0` then `u = ∑ⱼ ∑ₛ Eⱼ,ₛ(u) ⊗ xₛ` with `Eⱼ,ₛ(u) = (id ⊗ tⱼ)(can(u) ρ(yₛ)) = 0`
   (`Hom.sum_sum_E_tmul`), so `can` is injective.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 1.1.9 (Grothendieck), stated without
  proof; [Stix, *A course on finite flat group schemes and p-divisible groups*, §6, Thm. 17–20]
  for a proof of the general quotient theorem (characteristic polynomials, Noetherian base).
* G. Böhm, *Galois theory for Hopf algebroids*, arXiv:math/0409513 (statement of the
  Kreimer–Takeuchi theorem).
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] {G H : FFGroupScheme R}

namespace Hom

variable (i : Hom H G)

/-- The coaction `ρ = (id ⊗ i) ∘ Δ : A → A ⊗ C` of `H` on `G` by translation. -/
def coact : G.A →ₐ[R] G.A ⊗[R] H.A :=
  (Algebra.TensorProduct.map (AlgHom.id R G.A) (i : G.A →ₐ[R] H.A)).comp
    (Bialgebra.comulAlgHom R G.A)

theorem coact_apply (a : G.A) :
    i.coact a = TensorProduct.map LinearMap.id (i : G.A →ₗ[R] H.A) (comul a) := rfl

/-- The `H`-invariant functions `B = A^H = {a | ρ(a) = a ⊗ 1}`. -/
def invariants : Subalgebra R G.A :=
  AlgHom.equalizer i.coact Algebra.TensorProduct.includeLeft

theorem mem_invariants {a : G.A} : a ∈ i.invariants ↔ i.coact a = a ⊗ₜ[R] 1 :=
  AlgHom.mem_equalizer _ _ a

/-- `(f ⊗ g) ∘ ρ = f * (g ∘ i)` (convolution in `G(T)`). -/
theorem lift_comp_coact {T : Type*} [CommRing T] [Algebra R T] (f : G.A →ₐ[R] T)
    (g : H.A →ₐ[R] T) :
    (Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)).comp i.coact =
      ofConv (toConv f * toConv (g.comp (i : G.A →ₐ[R] H.A))) := by
  have h : (Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)).comp
      (Algebra.TensorProduct.map (AlgHom.id R G.A) (i : G.A →ₐ[R] H.A)) =
      (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f
        (g.comp (i : G.A →ₐ[R] H.A))) :=
    Algebra.TensorProduct.ext' fun a b => by simp
  rw [AlgHom.convMul_def, coact, ← AlgHom.comp_assoc, h]
  rfl

/-- `∑ (S y₁ ⊗ 1) ρ(y₂) = 1 ⊗ i(y)`: in the group `G(A ⊗ C)`, `i₁⁻¹ ρ = i₂ ∘ i`. -/
theorem lift_antipode_coact (y : G.A) :
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] H.A).comp
        (HopfAlgebra.antipodeAlgHom R G.A)) i.coact (fun _ _ => .all _ _) (comul y) =
      1 ⊗ₜ i y := by
  let j₁ : G.points (G.A ⊗[R] H.A) := toConv Algebra.TensorProduct.includeLeft
  let j₂ : G.points (G.A ⊗[R] H.A) :=
    toConv ((Algebra.TensorProduct.includeRight : H.A →ₐ[R] G.A ⊗[R] H.A).comp
      (i : G.A →ₐ[R] H.A))
  have hc : toConv i.coact = j₁ * j₂ := by
    apply WithConv.ofConv_injective
    rw [← i.lift_comp_coact, Algebra.TensorProduct.lift_includeLeft_includeRight]
    rfl
  have h : j₁⁻¹ * toConv i.coact = j₂ := by rw [hc, inv_mul_cancel_left]
  have h' := congrArg (fun f : G.points (G.A ⊗[R] H.A) => (ofConv f : G.A →ₐ[R] _) y) h
  rw [AlgHom.convMul_apply] at h'
  exact h'

/-- A homomorphism of finite flat group schemes commutes with the antipodes. -/
theorem map_antipode (a : G.A) : i (antipode R a) = antipode R (i a) := by
  have h := map_inv (i.mapPoints H.A) (toConv (AlgHom.id R H.A))
  have h' := congrArg (fun f : G.points H.A => (ofConv f : G.A →ₐ[R] H.A) a) h
  exact h'.symm

/-- Counit law: `(id ⊗ ε)(ρ(a)) = a`. -/
theorem rid_counit_coact (a : G.A) :
    TensorProduct.rid R G.A ((counit (R := R) (A := H.A)).lTensor G.A (i.coact a)) = a := by
  have : ∀ w : G.A ⊗[R] G.A, TensorProduct.rid R G.A ((counit (R := R) (A := H.A)).lTensor G.A
      (TensorProduct.map LinearMap.id (i : G.A →ₗ[R] H.A) w)) =
      TensorProduct.rid R G.A ((counit (R := R) (A := G.A)).lTensor G.A w) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp
  rw [coact_apply, this, lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

/-- Comodule coassociativity: `(ρ ⊗ id) ρ = (id ⊗ Δ) ρ` (up to associativity). -/
theorem rTensor_coact_coact (a : G.A) :
    i.coact.toLinearMap.rTensor H.A (i.coact a) =
      (TensorProduct.assoc R G.A H.A H.A).symm
        ((comul (R := R) (A := H.A)).lTensor G.A (i.coact a)) := by
  set ι : G.A →ₗ[R] H.A := (i : G.A →ₗ[R] H.A)
  have hΔ : (comul (R := R) (A := H.A)) ∘ₗ ι = TensorProduct.map ι ι ∘ₗ comul := by
    exact (CoalgHomClass.map_comp_comul i).symm
  have h1 : ∀ w : G.A ⊗[R] G.A, i.coact.toLinearMap.rTensor H.A
      (TensorProduct.map LinearMap.id ι w) =
      TensorProduct.map (TensorProduct.map LinearMap.id ι) ι (comul.rTensor G.A w) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rfl
  have h2 : ∀ w : G.A ⊗[R] G.A, (comul (R := R) (A := H.A)).lTensor G.A
      (TensorProduct.map LinearMap.id ι w) =
      TensorProduct.map LinearMap.id (TensorProduct.map ι ι) (comul.lTensor G.A w) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.lTensor_tmul]
      rw [← LinearMap.comp_apply comul ι, hΔ, LinearMap.comp_apply]
  have h3 : ∀ v : G.A ⊗[R] (G.A ⊗[R] G.A),
      (TensorProduct.assoc R G.A H.A H.A).symm
        (TensorProduct.map LinearMap.id (TensorProduct.map ι ι) v) =
      TensorProduct.map (TensorProduct.map LinearMap.id ι) ι
        ((TensorProduct.assoc R G.A G.A G.A).symm v) := by
    intro v
    induction v with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x z =>
      induction z with
      | zero => simp
      | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
      | tmul y z => rfl
  rw [coact_apply, h1, h2, h3, coassoc_symm_apply]

/-! ### The traces `trⱼ = (id ⊗ tⱼ) ∘ ρ` -/

/-- `tr_t = (id ⊗ t) ∘ ρ : A → A` for a linear form `t` on `C`. -/
def trace (t : H.A →ₗ[R] R) : G.A →ₗ[R] G.A :=
  (TensorProduct.rid R G.A).toLinearMap ∘ₗ t.lTensor G.A ∘ₗ i.coact.toLinearMap

theorem trace_apply (t : H.A →ₗ[R] R) (a : G.A) :
    i.trace t a = TensorProduct.rid R G.A (t.lTensor G.A (i.coact a)) := rfl

theorem mul_rid_lTensor (t : H.A →ₗ[R] R) (x : G.A) (w : G.A ⊗[R] H.A) :
    x * TensorProduct.rid R G.A (t.lTensor G.A w) =
      TensorProduct.rid R G.A (t.lTensor G.A ((x ⊗ₜ 1) * w)) := by
  induction w with
  | zero => simp
  | add y z hy hz => rw [map_add, map_add, mul_add, hy, hz, mul_add, map_add, map_add]
  | tmul y c => simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- For an `H`-invariant form `t`, `tr_t(a)` is `H`-invariant. -/
theorem trace_mem {t : H.A →ₗ[R] R}
    (ht : ∀ y, TensorProduct.rid R H.A (t.lTensor H.A (comul (R := R) y)) =
      algebraMap R H.A (t y)) (a : G.A) : i.trace t a ∈ i.invariants := by
  rw [mem_invariants]
  have h1 : ∀ w : G.A ⊗[R] H.A, i.coact (TensorProduct.rid R G.A (t.lTensor G.A w)) =
      TensorProduct.rid R (G.A ⊗[R] H.A)
        (t.lTensor (G.A ⊗[R] H.A) (i.coact.toLinearMap.rTensor H.A w)) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x c => simp
  have h2 : ∀ w : G.A ⊗[R] H.A, TensorProduct.rid R (G.A ⊗[R] H.A)
      (t.lTensor (G.A ⊗[R] H.A) ((TensorProduct.assoc R G.A H.A H.A).symm
        ((comul (R := R) (A := H.A)).lTensor G.A w))) =
      TensorProduct.rid R G.A (t.lTensor G.A w) ⊗ₜ 1 := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, add_tmul]
    | tmul x c =>
      have hc := ht c
      have key : ∀ v : H.A ⊗[R] H.A, TensorProduct.rid R (G.A ⊗[R] H.A)
          (t.lTensor (G.A ⊗[R] H.A) ((TensorProduct.assoc R G.A H.A H.A).symm (x ⊗ₜ v))) =
          x ⊗ₜ TensorProduct.rid R H.A (t.lTensor H.A v) := by
        intro v
        induction v with
        | zero => simp
        | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
        | tmul y z => simp [TensorProduct.smul_tmul']
      rw [LinearMap.lTensor_tmul, key, hc, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [trace_apply, h1, rTensor_coact_coact, h2]

/-- `tr_t` is `B`-linear. -/
theorem trace_mul (t : H.A →ₗ[R] R) {b : G.A} (hb : b ∈ i.invariants) (a : G.A) :
    i.trace t (b * a) = b * i.trace t a := by
  rw [trace_apply, trace_apply, map_mul, (i.mem_invariants).mp hb, mul_rid_lTensor]

/-! ### The Galois map `can : A ⊗_B A → A ⊗_R C` -/

/-- `A ⊗_B A`, the coordinate ring of `G ×_{G/H} G`. -/
abbrev AB : Type u := G.A ⊗[i.invariants] G.A

/-- The coaction as a `B`-algebra map (`B` is coinvariant). -/
def coactB : G.A →ₐ[i.invariants] G.A ⊗[R] H.A :=
  { i.coact with
    commutes' := fun b => by
      change i.coact (b : G.A) = (b : G.A) ⊗ₜ 1
      exact i.mem_invariants.mp b.2 }

/-- **The Galois map** `can : A ⊗_B A → A ⊗_R C`, `x ⊗ y ↦ (x ⊗ 1) ρ(y)`
(`G ×_{G/H} G → G × H`), a map of `A`-algebras. -/
def can : i.AB →ₐ[G.A] G.A ⊗[R] H.A :=
  Algebra.TensorProduct.lift (Algebra.ofId G.A _) i.coactB (fun _ _ => .all _ _)

theorem can_tmul (x y : G.A) : i.can (x ⊗ₜ y) = (x ⊗ₜ 1) * i.coact y := by
  simp [can, coactB, Algebra.TensorProduct.algebraMap_apply]

/-- The first factor `A → A ⊗_B A`. -/
def inl : G.A →ₐ[R] i.AB := Algebra.TensorProduct.includeLeft

/-- The second factor `A → A ⊗_B A`. -/
def inr : G.A →ₐ[R] i.AB :=
  (Algebra.TensorProduct.includeRight : G.A →ₐ[i.invariants] i.AB).restrictScalars R

/-- The map `A ⊗_R A → A ⊗_B A`. -/
def θ : G.A ⊗[R] G.A →ₐ[R] i.AB :=
  Algebra.TensorProduct.lift i.inl i.inr (fun _ _ => .all _ _)

theorem θ_tmul (x y : G.A) : i.θ (x ⊗ₜ y) = x ⊗ₜ y := by
  simp [θ, inl, inr, Algebra.TensorProduct.tmul_mul_tmul]

theorem can_θ_map_antipode (v : G.A ⊗[R] G.A) :
    i.can (i.θ (TensorProduct.map (antipode R) LinearMap.id v)) =
      Algebra.TensorProduct.lift
        ((Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] H.A).comp
          (HopfAlgebra.antipodeAlgHom R G.A)) i.coact (fun _ _ => .all _ _) v := by
  induction v with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, θ_tmul, can_tmul,
      Algebra.TensorProduct.lift_tmul]
    rfl

theorem tmul_mem_range_can (x : G.A) (y : G.A) : x ⊗ₜ i y ∈ i.can.range := by
  have h1 : (1 : G.A) ⊗ₜ i y ∈ i.can.range :=
    ⟨_, (i.can_θ_map_antipode (comul y)).trans (i.lift_antipode_coact y)⟩
  have h2 : x ⊗ₜ[R] (1 : H.A) ∈ i.can.range := ⟨x ⊗ₜ 1, by
    change i.can (x ⊗ₜ 1) = _
    rw [can_tmul, map_one, mul_one]⟩
  have := mul_mem h2 h1
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this

/-- `can` is surjective (for a closed immersion `H → G`). -/
theorem can_surjective (hi : Function.Surjective i) : Function.Surjective i.can := by
  intro z
  suffices z ∈ i.can.range from this
  induction z with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul x c =>
    obtain ⟨y, rfl⟩ := hi c
    exact i.tmul_mem_range_can x y

/-! ### The dual basis -/

/-- The data of the dual basis: `H`-invariant forms `tⱼ` and finite families `(xₛ, yₛ)ₛ∈Sⱼ` with
`∑ⱼ (id ⊗ tⱼ)((∑ₛ (xₛ ⊗ 1) ρ(yₛ)) w) = (id ⊗ ε)(w)`. -/
theorem exists_dualBasisData (hi : Function.Surjective i) :
    ∃ (ι : Type u) (_ : Fintype ι) (t : ι → (H.A →ₗ[R] R)) (S : ι → Finset (G.A × G.A)),
      (∀ j y, TensorProduct.rid R H.A ((t j).lTensor H.A (comul (R := R) y)) =
        algebraMap R H.A (t j y)) ∧
      ∀ w : G.A ⊗[R] H.A, ∑ j, TensorProduct.rid R G.A ((t j).lTensor G.A
        ((∑ s ∈ S j, (s.1 ⊗ₜ[R] (1 : H.A)) * i.coact s.2) * w)) =
        TensorProduct.rid R G.A ((counit (R := R) (A := H.A)).lTensor G.A w) := by
  obtain ⟨ι, _, t, Λ, ht, hΛ⟩ := exists_invariant_forms H
  choose y hy using fun j => hi (Λ j)
  choose S hS using fun j =>
    TensorProduct.exists_finset (R := R) (TensorProduct.map (antipode R) LinearMap.id
      (comul (R := R) (y j)))
  refine ⟨ι, inferInstance, t, S, ht, fun w => ?_⟩
  have hsum : ∀ j, ∑ s ∈ S j, (s.1 ⊗ₜ[R] (1 : H.A)) * i.coact s.2 = 1 ⊗ₜ Λ j := by
    intro j
    rw [← hy j, ← i.lift_antipode_coact, ← i.can_θ_map_antipode, hS j, map_sum, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [θ_tmul, can_tmul]
  simp_rw [hsum]
  induction w with
  | zero => simp
  | add x z hx hz => simp only [mul_add, map_add, Finset.sum_add_distrib, hx, hz]
  | tmul x c =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul]
    rw [← Finset.sum_smul, hΛ]

/-- `B`-linear traces `A → B`, `a ↦ tr_t(y a)`. -/
def traceB {t : H.A →ₗ[R] R}
    (ht : ∀ y, TensorProduct.rid R H.A (t.lTensor H.A (comul (R := R) y)) =
      algebraMap R H.A (t y)) (y : G.A) : G.A →ₗ[i.invariants] i.invariants where
  toFun a := ⟨i.trace t (y * a), i.trace_mem ht _⟩
  map_add' a a' := Subtype.ext (by simp [mul_add])
  map_smul' b a := Subtype.ext (by
    change i.trace t (y * ((b : G.A) * a)) = (b : G.A) * i.trace t (y * a)
    rw [mul_left_comm, i.trace_mul t b.2])

theorem coe_traceB {t : H.A →ₗ[R] R}
    (ht : ∀ y, TensorProduct.rid R H.A (t.lTensor H.A (comul (R := R) y)) =
      algebraMap R H.A (t y)) (y a : G.A) : (i.traceB ht y a : G.A) = i.trace t (y * a) := rfl

theorem sum_sum_mul_trace {ι : Type*} [Fintype ι] {t : ι → (H.A →ₗ[R] R)}
    {S : ι → Finset (G.A × G.A)}
    (hS : ∀ w : G.A ⊗[R] H.A, ∑ j, TensorProduct.rid R G.A ((t j).lTensor G.A
        ((∑ s ∈ S j, (s.1 ⊗ₜ[R] (1 : H.A)) * i.coact s.2) * w)) =
        TensorProduct.rid R G.A ((counit (R := R) (A := H.A)).lTensor G.A w)) (a : G.A) :
    ∑ j, ∑ s ∈ S j, s.1 * i.trace (t j) (s.2 * a) = a := by
  conv_rhs => rw [← i.rid_counit_coact a, ← hS]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [trace_apply, mul_rid_lTensor, show i.coact (s.2 * a) = i.coact s.2 * i.coact a from
    map_mul _ _ _, mul_assoc]

/-- **`A` is a finitely generated projective module over the invariants `B`** (dual basis). -/
theorem projective_invariants (hi : Function.Surjective i) :
    Module.Projective i.invariants G.A := by
  obtain ⟨ι, _, t, S, ht, hS⟩ := i.exists_dualBasisData hi
  refine Module.projective_def'.mpr ⟨∑ j, ∑ s ∈ S j,
    Finsupp.lsingle (R := i.invariants) s.1 ∘ₗ i.traceB (ht j) s.2, ?_⟩
  ext a
  simp only [LinearMap.comp_apply, LinearMap.coe_sum, Finset.sum_apply, map_sum,
    Finsupp.lsingle_apply, Finsupp.linearCombination_single, id, LinearMap.id_apply]
  conv_rhs => rw [← i.sum_sum_mul_trace hS a]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
  change (i.trace (t j) (s.2 * a)) * s.1 = _
  rw [mul_comm]

/-- **`can` is injective**: `u = ∑ⱼ ∑ₛ (id ⊗ tⱼ)(can(u) ρ(yₛ)) ⊗ xₛ`. -/
theorem can_injective (hi : Function.Surjective i) : Function.Injective i.can := by
  obtain ⟨ι, _, t, S, ht, hS⟩ := i.exists_dualBasisData hi
  let E : ι → G.A → i.AB → G.A := fun j y u =>
    TensorProduct.rid R G.A ((t j).lTensor G.A (i.can u * i.coact y))
  have key : ∀ u, ∑ j, ∑ s ∈ S j, E j s.2 u ⊗ₜ[i.invariants] s.1 = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp [E]
    | add u v hu hv =>
      conv_rhs => rw [← hu, ← hv]
      simp only [E, map_add, add_mul, TensorProduct.add_tmul, Finset.sum_add_distrib]
    | tmul p q =>
      have hE : ∀ j y, E j y (p ⊗ₜ q) =
          (i.traceB (ht j) q y : G.A) * p := by
        intro j y
        simp only [E, can_tmul, mul_assoc, ← map_mul, ← mul_rid_lTensor, coe_traceB,
          trace_apply, mul_comm p]
      simp_rw [hE]
      have h1 : ∀ (b : i.invariants) (x : G.A),
          ((b : G.A) * p) ⊗ₜ[i.invariants] x = p ⊗ₜ[i.invariants] ((b : G.A) * x) := by
        intro b x
        rw [show (b : G.A) * p = b • p from rfl, show (b : G.A) * x = b • x from rfl,
          TensorProduct.smul_tmul]
      simp_rw [h1, ← TensorProduct.tmul_sum]
      congr 1
      conv_rhs => rw [← i.sum_sum_mul_trace hS q]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => ?_
      rw [coe_traceB, mul_comm, mul_comm q]
  intro u v huv
  rw [← key u, ← key v]
  simp only [E, huv]

/-- **The Galois isomorphism** `A ⊗_B A ≅ A ⊗_R C` (`G ×_{G/H} G ≅ G × H`). -/
def canEquiv (hi : Function.Surjective i) : i.AB ≃ₐ[G.A] G.A ⊗[R] H.A :=
  AlgEquiv.ofBijective i.can ⟨i.can_injective hi, i.can_surjective hi⟩

theorem canEquiv_tmul (hi : Function.Surjective i) (x y : G.A) :
    i.canEquiv hi (x ⊗ₜ y) = (x ⊗ₜ 1) * i.coact y := i.can_tmul x y

end Hom

end FFGroupScheme

end PadicHodge
