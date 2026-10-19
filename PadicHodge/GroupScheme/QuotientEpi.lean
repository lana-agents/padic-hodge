/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.QuotientPoints

/-!
# A homomorphism with kernel `H` identifies `G/H` with its image

Let `R` be a local principal ideal domain, `i : H → G` a closed immersion of finite flat
commutative group schemes over `R` and `f : G → X` a homomorphism whose kernel is `H` on points
with values in every `R`-algebra (`f(g) = 1 ↔ g ∈ i(H(T))`). Then the image of
`f^* : O(X) → O(G)` is exactly the algebra of invariants `B = O(G)^H = O(G/H)`
(**`FFGroupScheme.Hom.range_eq_invariants`**), i.e. `G/H → X` is a closed immersion. This is
the step "`G_{v+t}/G_v ↪ G_t` is a closed embedding" of [Hong, proof of Lemma 2.1.5 (iii)]
(the map is a monomorphism, and a monomorphism of finite flat group schemes is a closed
immersion), used for the Cartier dual of a `p`-divisible group ([Hong, Prop. 2.1.7]).

Proof (standard arguments, written up here). Let `C = f^*(O(X)) ⊆ B ⊆ A = O(G)`.

* In `A ⊗_C A` the two factor inclusions `g₁, g₂ ∈ G(A ⊗_C A)` have the same image in `X`,
  so `g₂ = g₁ · i(h)` for some `h ∈ H(A ⊗_C A)`; evaluating at an invariant `b` gives
  `b ⊗ 1 = 1 ⊗ b` (`Hom.tmul_eq_tmul_of_mem_invariants`).
* `A` is free of positive rank over `B` (`Hom.nonempty_basis_invariants`), so `B → A` has a
  `B`-linear retraction `r` with `r(1) = 1` (`Module.Basis.exists_retraction`: the coordinates of
  `1` generate the unit ideal, otherwise `1 ∈ 𝔪 A` for a maximal ideal `𝔪` of `B`); applying
  `r ⊗ r` gives `b ⊗ 1 = 1 ⊗ b` in `B ⊗_C B`, i.e. `C → B` is an epimorphism of rings.
* **A finite injective epimorphism of commutative rings is surjective**
  (`algebraMap_surjective_of_tmul_eq`, [Stacks, Tag 04VM]): `N = B/C` satisfies `B ⊗_C N = 0`,
  and for a prime `P` in the support of `N`, `κ(P) ⊗_C (B ⊗_C N) ≅ (κ(P) ⊗ B) ⊗_{κ(P)} (κ(P) ⊗ N)`
  would be nonzero.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Lemma 2.1.5, Prop. 2.1.7.
* [Stacks] The Stacks project, Tag 04VM.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

/-! ### A retraction of `B → A` for `A` free of positive rank -/

/-- If `A` is a free `B`-algebra with a nonempty basis, then `B → A` has a `B`-linear retraction
`r` with `r(1) = 1`. -/
theorem _root_.Module.Basis.exists_retraction_one {B A : Type*} [CommRing B] [CommRing A]
    [Algebra B A] {ι : Type*} [Finite ι] [Nonempty ι] (b : Module.Basis ι B A) :
    ∃ r : A →ₗ[B] B, r 1 = 1 := by
  classical
  have := Fintype.ofFinite ι
  set c : ι → B := fun i => b.repr 1 i
  have hspan : (1 : B) ∈ Ideal.span (Set.range c) := by
    by_contra hne
    have hI : Ideal.span (Set.range c) ≠ ⊤ := fun h => hne (h ▸ Submodule.mem_top)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have h1 : (1 : A) = ∑ i, c i • b i := (b.sum_repr 1).symm
    have h2 : b i₀ = ∑ i, c i • (b i₀ * b i) := by
      conv_lhs => rw [← mul_one (b i₀), h1, Finset.mul_sum]
      simp only [mul_smul_comm]
    have h3 := congrArg (fun z => b.repr z i₀) h2
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Module.Basis.repr_self, Finsupp.single_eq_same] at h3
    have : (1 : B) ∈ m := by
      rw [h3]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hle (Ideal.subset_span ⟨i, rfl⟩))
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr this)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hspan
  refine ⟨∑ i, β i • b.coord i, ?_⟩
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    smul_eq_mul]
  exact hβ

/-! ### Finite epimorphisms are surjective -/

/-- **A finite injective epimorphism of commutative rings is surjective** ([Stacks, Tag 04VM]):
if `C → B` is injective, `B` is a finite `C`-module and `b ⊗ 1 = 1 ⊗ b` in `B ⊗_C B` for all
`b`, then `C → B` is surjective. -/
theorem algebraMap_surjective_of_tmul_eq {C B : Type*} [CommRing C] [CommRing B] [Algebra C B]
    (hinj : Function.Injective (algebraMap C B)) [Module.Finite C B]
    (hepi : ∀ b : B, b ⊗ₜ[C] (1 : B) = (1 : B) ⊗ₜ b) :
    Function.Surjective (algebraMap C B) := by
  set N := B ⧸ LinearMap.range (Algebra.linearMap C B)
  -- `B ⊗_C N = 0`
  have hzero : ∀ z : B ⊗[C] N, z = 0 := by
    intro z
    induction z with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul b n =>
      obtain ⟨b', rfl⟩ := Submodule.mkQ_surjective _ n
      have h1 : b ⊗ₜ[C] b' = (b * b') ⊗ₜ[C] (1 : B) := by
        have := congrArg (fun w : B ⊗[C] B => (b ⊗ₜ[C] (1 : B)) * w) (hepi b')
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
        exact this.symm
      have h2 := congrArg (LinearMap.lTensor B (Submodule.mkQ
        (LinearMap.range (Algebra.linearMap C B)))) h1
      simp only [LinearMap.lTensor_tmul] at h2
      rw [h2]
      have : Submodule.mkQ (LinearMap.range (Algebra.linearMap C B)) (1 : B) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨1, by rw [Algebra.linearMap_apply, map_one]⟩
      rw [this, TensorProduct.tmul_zero]
  -- `N = 0`
  haveI : Module.Finite C N := Module.Finite.quotient C (LinearMap.range (Algebra.linearMap C B))
  have hN : Subsingleton N := by
    rw [← Module.support_eq_empty_iff (R := C)]
    refine Set.eq_empty_of_forall_notMem fun P hP => ?_
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hP
    have hB : P ∈ Module.support C B := by
      rw [Module.support_eq_zeroLocus]
      have : Module.annihilator C B = ⊥ := by
        refine (Submodule.eq_bot_iff _).mpr fun c hc => hinj ?_
        rw [Module.mem_annihilator] at hc
        rw [Algebra.algebraMap_eq_smul_one, hc, map_zero]
      rw [this]
      exact fun x hx => (Submodule.mem_bot C).mpr hx ▸ Submodule.zero_mem _
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hB
    set κ := P.asIdeal.ResidueField
    have hpos : 0 < Module.finrank κ ((κ ⊗[C] B) ⊗[κ] (κ ⊗[C] N)) := by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
    have e := (TensorProduct.AlgebraTensorModule.distribBaseChange C κ B N).symm
    have hsub : Subsingleton (κ ⊗[C] (B ⊗[C] N)) := by
      refine ⟨fun x y => ?_⟩
      have : ∀ w : κ ⊗[C] (B ⊗[C] N), w = 0 := by
        intro w
        induction w with
        | zero => rfl
        | add x y hx hy => rw [hx, hy, add_zero]
        | tmul a z => rw [hzero z, TensorProduct.tmul_zero]
      rw [this x, this y]
    have : Subsingleton ((κ ⊗[C] B) ⊗[κ] (κ ⊗[C] N)) := e.toEquiv.subsingleton
    rw [Module.finrank_zero_of_subsingleton] at hpos
    exact lt_irrefl 0 hpos
  intro b
  have : Submodule.mkQ (LinearMap.range (Algebra.linearMap C B)) b = 0 := Subsingleton.elim _ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc⟩

namespace FFGroupScheme

namespace Hom

variable {R : Type u} [CommRing R] {G H X : FFGroupScheme R} (i : Hom H G) (f : Hom G X)

/-- The image `C = f^*(O(X)) ⊆ O(G)`. -/
abbrev imageAlg : Subalgebra R G.A := (f : X.A →ₐ[R] G.A).range

/-- **Invariants are `C`-epimorphic**: if the kernel of `f : G → X` is `H` on all points, then
`b ⊗ 1 = 1 ⊗ b` in `A ⊗_C A` for every `H`-invariant `b`, `C = f^*(O(X))`. -/
theorem tmul_eq_tmul_of_mem_invariants
    (hker : ∀ (T : Type u) [CommRing T] [Algebra R T] (g : G.points T),
      f.mapPoints T g = 1 → ∃ h, i.mapPoints T h = g)
    {b : G.A} (hb : b ∈ i.invariants) :
    b ⊗ₜ[f.imageAlg] (1 : G.A) = (1 : G.A) ⊗ₜ b := by
  set C := f.imageAlg
  let T := G.A ⊗[C] G.A
  let g₁ : G.points T := toConv (Algebra.TensorProduct.includeLeft : G.A →ₐ[R] T)
  let g₂ : G.points T :=
    toConv ((Algebra.TensorProduct.includeRight : G.A →ₐ[C] T).restrictScalars R)
  have hC : ∀ c : C, (c : G.A) ⊗ₜ[C] (1 : G.A) = (1 : G.A) ⊗ₜ (c : G.A) := by
    intro c
    have h1 : (c : G.A) = c • (1 : G.A) := by rw [Algebra.smul_def, mul_one]; rfl
    rw [h1, TensorProduct.smul_tmul]
  have hf : f.mapPoints T g₁ = f.mapPoints T g₂ := by
    apply WithConv.ofConv_injective
    ext x
    change (f x) ⊗ₜ[C] (1 : G.A) = (1 : G.A) ⊗ₜ[C] (f x)
    exact hC ⟨f x, x, rfl⟩
  have h1 : f.mapPoints T (g₁⁻¹ * g₂) = 1 := by
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  obtain ⟨h, hh⟩ := hker T (g₁⁻¹ * g₂) h1
  have h2 : g₂ = g₁ * i.mapPoints T h := by rw [hh, mul_inv_cancel_left]
  have h3 := congrArg (fun z : G.points T => ofConv z b) h2
  have h4 : ofConv (g₁ * i.mapPoints T h) b =
      (Algebra.TensorProduct.lift (ofConv g₁) (ofConv h) (fun _ _ => .all _ _)) (i.coact b) := by
    rw [← AlgHom.comp_apply, i.lift_comp_coact]
    rfl
  rw [h4, (i.mem_invariants).mp hb, Algebra.TensorProduct.lift_tmul, map_one, mul_one] at h3
  exact h3.symm

/-- `C = f^*(O(X))` lies in the invariants if `f` is trivial on `H`. -/
theorem imageAlg_le_invariants (htriv : ∀ x, i (f x) = algebraMap R H.A (counit (R := R) x)) :
    f.imageAlg ≤ i.invariants := by
  rintro _ ⟨x, rfl⟩
  exact mem_invariants_of_trivial i f htriv x

variable [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]

/-- **`f^*(O(X)) = O(G)^H`** for `f : G → X` with kernel `H` (on points with values in every
`R`-algebra): the induced `G/H → X` is a closed immersion ([Hong, proof of Lemma 2.1.5 (iii)]). -/
theorem range_eq_invariants (hi : Function.Surjective i) (hH : 0 < H.order)
    (htriv : ∀ x, i (f x) = algebraMap R H.A (counit (R := R) x))
    (hker : ∀ (T : Type u) [CommRing T] [Algebra R T] (g : G.points T),
      f.mapPoints T g = 1 → ∃ h, i.mapPoints T h = g) :
    f.imageAlg = i.invariants := by
  set C := f.imageAlg
  set B := i.invariants
  have hCB : C ≤ B := imageAlg_le_invariants i f htriv
  refine le_antisymm hCB fun b hb => ?_
  letI : Algebra C B := (Subalgebra.inclusion hCB).toRingHom.toAlgebra
  haveI : IsScalarTower C B G.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the retraction `r : A → B`
  obtain ⟨bas⟩ := nonempty_basis_invariants hi
  haveI : Nonempty (Fin H.order) := ⟨⟨0, hH⟩⟩
  obtain ⟨r, hr1⟩ := bas.exists_retraction_one
  have hrB : ∀ y : B, r (y : G.A) = y := by
    intro y
    have h' : (y : G.A) = y • (1 : G.A) := by rw [Algebra.smul_def, mul_one]; rfl
    rw [h', r.map_smul, hr1, smul_eq_mul, mul_one]
  let rC : G.A →ₗ[C] B := r.restrictScalars C
  -- `C → B` is an epimorphism
  have hepi : ∀ y : B, y ⊗ₜ[C] (1 : B) = (1 : B) ⊗ₜ y := by
    intro y
    have h := tmul_eq_tmul_of_mem_invariants i f hker y.2
    have := congrArg (TensorProduct.map rC rC) h
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul] at this
    have e1 : rC (1 : G.A) = 1 := hr1
    have e2 : rC (y : G.A) = y := hrB y
    rwa [e1, e2] at this
  haveI : Module.Finite R B := Module.Finite.of_injective (Subalgebra.val B).toLinearMap
    Subtype.val_injective
  haveI : Module.Finite C B := Module.Finite.of_restrictScalars_finite R C B
  have hinj : Function.Injective (algebraMap C B) := fun x y hxy =>
    Subtype.val_injective (congrArg (fun z : B => (z : G.A)) hxy)
  obtain ⟨c, hc⟩ := algebraMap_surjective_of_tmul_eq hinj hepi ⟨b, hb⟩
  have : (c : G.A) = b := congrArg Subtype.val hc
  rw [← this]
  exact c.2

/-- In particular every invariant comes from `O(X)`. -/
theorem exists_eq_of_mem_invariants (hi : Function.Surjective i) (hH : 0 < H.order)
    (htriv : ∀ x, i (f x) = algebraMap R H.A (counit (R := R) x))
    (hker : ∀ (T : Type u) [CommRing T] [Algebra R T] (g : G.points T),
      f.mapPoints T g = 1 → ∃ h, i.mapPoints T h = g) {b : G.A} (hb : b ∈ i.invariants) :
    ∃ x, f x = b := by
  rw [← range_eq_invariants i f hi hH htriv hker] at hb
  exact hb

end Hom

end FFGroupScheme

end PadicHodge
