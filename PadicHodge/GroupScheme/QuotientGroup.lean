/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Quotient
import PadicHodge.GroupScheme.EtaleQuotientOrder

/-!
# The quotient `G/H` of a finite flat group scheme by a closed finite flat subgroup

**[Hong, Thm. 1.1.9] (Grothendieck)** over a local principal ideal domain `R` (e.g. `O_{K'}`,
`ℤ_p`, or a field such as `K'`): let `i : H → G` be a closed immersion of finite flat
commutative group schemes (`i : O(G) → O(H)` a surjective bialgebra map). Then

* the invariants `B = A^H` (`Hom.invariants`) form a finite free sub-Hopf algebra of `A`
  (`Hom.quotient i = G/H`, `Hom.quotientHom i : G → G/H`);
* `A` is free of rank `|H|` over `B` (`Hom.nonempty_basis_invariants`), and
  **`|G| = |H| · |G/H|`** (`Hom.order_eq_mul`);
* **`0 → H → G → G/H` is exact on points** with values in any `R`-algebra `T`
  (`Hom.mapPoints_quotientHom_eq_one_iff`; injectivity of `H(T) → G(T)` is
  `Hom.mapPoints_injective_of_surjective`).

The Hopf algebra structure on `B` is the argument of `EtaleQuotient.lean` (there for `H = G⁰`),
with flatness of `B` from torsion-freeness over the PID `R`. The rank uses the Galois isomorphism
`A ⊗_B A ≅ A ⊗_R C` and projectivity of `A` over `B` from `Quotient.lean` (Kreimer–Takeuchi via
integrals), lying over for the integral extension `B ⊆ A`, and Stacks 02M9 over the semilocal `B`.
The kernel: if `i(a) = 0` then `a = ∑ xₛ (trⱼ(yₛ a) - ε(trⱼ(yₛ a)))` with
`ε ∘ trⱼ = tⱼ ∘ i` (dual basis), so `ker i = A · B⁺`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 1.1.9.
* [Stix] J. Stix, *A course on finite flat group schemes and p-divisible groups*, §6, Thm. 20.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct IsLocalRing

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] {G H : FFGroupScheme R}

namespace Hom

variable (i : Hom H G)

/-! ### Invariants and the counit -/

/-- On `B`, `i = ε`. -/
theorem apply_of_mem_invariants {a : G.A} (ha : a ∈ i.invariants) :
    i a = algebraMap R H.A (counit (R := R) a) := by
  set ι : G.A →ₗ[R] H.A := (i : G.A →ₗ[R] H.A)
  have key : ∀ x : G.A ⊗[R] G.A,
      TensorProduct.lid R _ ((counit (R := R) (A := G.A)).rTensor _
        (TensorProduct.map LinearMap.id ι x)) =
      ι (TensorProduct.lid R _ ((counit (R := R) (A := G.A)).rTensor _ x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ι]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h := congrArg (fun z => TensorProduct.lid R _ ((counit (R := R) (A := G.A)).rTensor _ z))
    ((i.mem_invariants).mp ha)
  change TensorProduct.lid R _ ((counit (R := R) (A := G.A)).rTensor _
    (TensorProduct.map LinearMap.id ι (comul a))) = _ at h
  rw [key, Coalgebra.rTensor_counit_comul] at h
  simp only [TensorProduct.lid_tmul, one_smul, LinearMap.rTensor_tmul] at h
  rw [Algebra.algebraMap_eq_smul_one]
  exact h

theorem antipode_mem_invariants {a : G.A} (ha : a ∈ i.invariants) :
    antipode R a ∈ i.invariants := by
  rw [mem_invariants] at ha ⊢
  set ι : G.A →ₗ[R] H.A := (i : G.A →ₗ[R] H.A)
  change TensorProduct.map LinearMap.id ι (comul (antipode R a)) = _
  change TensorProduct.map LinearMap.id ι (comul a) = _ at ha
  rw [comul_antipode]
  have : ∀ x : G.A ⊗[R] G.A, TensorProduct.map LinearMap.id ι
      (TensorProduct.map (antipode R) (antipode R) x) =
      TensorProduct.map (antipode R) (antipode R) (TensorProduct.map LinearMap.id ι x) := by
    intro x
    induction x with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply]
      exact congrArg _ (i.map_antipode y)
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this, ha, TensorProduct.map_tmul, HopfAlgebra.antipode_one]

/-! ### `B` as a kernel -/

/-- `a ↦ ρ(a) - a ⊗ 1`, whose kernel is `B`. -/
def defect : G.A →ₗ[R] G.A ⊗[R] H.A :=
  i.coact.toLinearMap -
    (Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] H.A).toLinearMap

theorem exact_defect : Function.Exact i.invariants.val.toLinearMap i.defect := by
  intro a
  simp only [defect, LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply,
    Algebra.TensorProduct.includeLeft_apply]
  constructor
  · intro h
    exact ⟨⟨a, (i.mem_invariants).mpr h⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact (i.mem_invariants).mp b.2

theorem lTensor_defect_comul {a : G.A} (ha : a ∈ i.invariants) :
    i.defect.lTensor G.A (comul (R := R) a) = 0 := by
  set π : G.A →ₗ[R] H.A := (i : G.A →ₗ[R] H.A)
  have h1 : ∀ x : (G.A ⊗[R] G.A) ⊗[R] G.A,
      (TensorProduct.map LinearMap.id π).lTensor G.A (TensorProduct.assoc R _ _ _ x) =
      TensorProduct.assoc R _ _ _ (π.lTensor _ x) := by
    intro x
    induction x with
    | zero => simp
    | tmul x z =>
      induction x with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h2 : ∀ x : G.A ⊗[R] G.A,
      (Algebra.TensorProduct.includeLeft : G.A →ₐ[R] G.A ⊗[R] H.A).toLinearMap.lTensor G.A x =
        TensorProduct.assoc R _ _ _ (x ⊗ₜ 1) := by
    intro x
    induction x with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  rw [mem_invariants] at ha
  simp only [defect, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero, h2]
  have hc : i.coact.toLinearMap = TensorProduct.map LinearMap.id π ∘ₗ comul := rfl
  have ha' : π.lTensor G.A (comul (R := R) a) = a ⊗ₜ 1 := ha
  rw [hc, LinearMap.lTensor_comp, LinearMap.comp_apply, ← coassoc_apply, h1,
    ← LinearMap.comp_apply (π.lTensor _), LinearMap.lTensor_comp_rTensor,
    ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, ha', LinearMap.rTensor_tmul]

theorem rTensor_defect_comul {a : G.A} (ha : a ∈ i.invariants) :
    i.defect.rTensor G.A (comul (R := R) a) = 0 := by
  have h : ∀ x : G.A ⊗[R] G.A, i.defect.rTensor G.A (TensorProduct.comm R _ _ x) =
      TensorProduct.comm R _ _ (i.defect.lTensor G.A x) := by
    intro x
    induction x with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [← comm_comul (R := R) a, h, i.lTensor_defect_comul ha, map_zero]

/-- The antipode of `B`. -/
def antipodeQ : i.invariants →ₗ[R] i.invariants where
  toFun b := ⟨antipode R (b : G.A), i.antipode_mem_invariants b.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

/-! ### Finiteness and freeness of `B` -/

variable [IsDomain R] [IsPrincipalIdealRing R]

instance : Module.Finite R i.invariants := by
  have : IsNoetherian R G.A := isNoetherian_of_isNoetherianRing_of_finite R G.A
  exact Module.Finite.of_injective i.invariants.val.toLinearMap Subtype.val_injective

instance : Module.Free R i.invariants := Module.free_of_finite_type_torsion_free'

/-! ### The comultiplication of `B` -/

/-- The inclusion `B ⊗ B → A ⊗ A`. -/
abbrev incl2 : i.invariants ⊗[R] i.invariants →ₐ[R] G.A ⊗[R] G.A :=
  Algebra.TensorProduct.map i.invariants.val i.invariants.val

theorem incl2_injective : Function.Injective i.incl2 :=
  TensorProduct.map_injective_of_flat_flat (R := R) i.invariants.val.toLinearMap
    i.invariants.val.toLinearMap Subtype.val_injective Subtype.val_injective

theorem comul_mem_range_incl2 {a : G.A} (ha : a ∈ i.invariants) :
    comul (R := R) a ∈ i.incl2.range := by
  obtain ⟨z, hz⟩ := mem_range_map_of_lTensor_eq_zero_of_rTensor_eq_zero i.exact_defect
    Subtype.val_injective (i.lTensor_defect_comul ha) (i.rTensor_defect_comul ha)
  exact ⟨z, hz⟩

/-- The comultiplication `B → B ⊗ B`: the restriction of `Δ`. -/
def comulQ : i.invariants →ₐ[R] i.invariants ⊗[R] i.invariants :=
  (AlgEquiv.ofInjective i.incl2 i.incl2_injective).symm.toAlgHom.comp
    (((Bialgebra.comulAlgHom R G.A).comp i.invariants.val).codRestrict i.incl2.range
      fun b => i.comul_mem_range_incl2 b.2)

theorem incl2_comulQ (b : i.invariants) : i.incl2 (i.comulQ b) = comul (R := R) (b : G.A) := by
  rw [← AlgEquiv.ofInjective_apply _ i.incl2_injective]
  simp [comulQ]

/-- The counit of `B`. -/
def counitQ : i.invariants →ₐ[R] R := (Bialgebra.counitAlgHom R G.A).comp i.invariants.val

/-- The inclusion `B ⊗ (B ⊗ B) → A ⊗ (A ⊗ A)`. -/
abbrev incl3 : i.invariants ⊗[R] (i.invariants ⊗[R] i.invariants) →ₗ[R]
    G.A ⊗[R] (G.A ⊗[R] G.A) :=
  TensorProduct.map i.invariants.val.toLinearMap i.incl2.toLinearMap

theorem incl3_injective : Function.Injective i.incl3 :=
  TensorProduct.map_injective_of_flat_flat (R := R) _ _ Subtype.val_injective i.incl2_injective

theorem coassoc_Q :
    (Algebra.TensorProduct.assoc R R R i.invariants i.invariants i.invariants).toAlgHom.comp
      ((Algebra.TensorProduct.map i.comulQ (.id R i.invariants)).comp i.comulQ) =
    (Algebra.TensorProduct.map (.id R i.invariants) i.comulQ).comp i.comulQ := by
  set ι := i.invariants.val.toLinearMap
  have L1 : ∀ y : (i.invariants ⊗[R] i.invariants) ⊗[R] i.invariants,
      i.incl3 ((Algebra.TensorProduct.assoc R R R i.invariants i.invariants
        i.invariants).toAlgHom y) =
      TensorProduct.assoc R G.A G.A G.A (TensorProduct.map i.incl2.toLinearMap ι y) := by
    intro y
    induction y with
    | zero => simp
    | tmul x z =>
      induction x with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have L2 : ∀ y : i.invariants ⊗[R] i.invariants,
      TensorProduct.map i.incl2.toLinearMap ι
        (Algebra.TensorProduct.map i.comulQ (.id R i.invariants) y) =
      (comul (R := R) (A := G.A)).rTensor G.A (i.incl2 y) := by
    intro y
    induction y with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, incl2_comulQ, LinearMap.rTensor_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have L3 : ∀ y : i.invariants ⊗[R] i.invariants,
      i.incl3 (Algebra.TensorProduct.map (.id R i.invariants) i.comulQ y) =
      (comul (R := R) (A := G.A)).lTensor G.A (i.incl2 y) := by
    intro y
    induction y with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, TensorProduct.map_tmul,
        AlgHom.toLinearMap_apply, incl2_comulQ, LinearMap.lTensor_tmul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  refine AlgHom.ext fun b => i.incl3_injective ?_
  simp only [AlgHom.comp_apply]
  rw [L1, L2, L3, incl2_comulQ, coassoc_apply]

theorem rTensor_counit_Q :
    (Algebra.TensorProduct.map i.counitQ (.id R i.invariants)).comp i.comulQ =
    (Algebra.TensorProduct.lid R i.invariants).symm := by
  have L : ∀ y : i.invariants ⊗[R] i.invariants,
      (Algebra.TensorProduct.lid R i.invariants
        (Algebra.TensorProduct.map i.counitQ (.id R i.invariants) y) : G.A) =
      TensorProduct.lid R G.A ((counit (R := R) (A := G.A)).rTensor G.A (i.incl2 y)) := by
    intro y
    induction y with
    | zero => simp
    | tmul a b => simp [counitQ]
    | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  refine AlgHom.ext fun b => (Algebra.TensorProduct.lid R i.invariants).injective ?_
  refine Subtype.val_injective ?_
  simp only [AlgHom.comp_apply]
  rw [L, incl2_comulQ, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]
  exact congrArg Subtype.val (AlgEquiv.apply_symm_apply _ b).symm

theorem lTensor_counit_Q :
    (Algebra.TensorProduct.map (.id R i.invariants) i.counitQ).comp i.comulQ =
    (Algebra.TensorProduct.rid R R i.invariants).symm := by
  have L : ∀ y : i.invariants ⊗[R] i.invariants,
      (Algebra.TensorProduct.rid R R i.invariants
        (Algebra.TensorProduct.map (.id R i.invariants) i.counitQ y) : G.A) =
      TensorProduct.rid R G.A ((counit (R := R) (A := G.A)).lTensor G.A (i.incl2 y)) := by
    intro y
    induction y with
    | zero => simp
    | tmul a b => simp [counitQ]
    | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  refine AlgHom.ext fun b => (Algebra.TensorProduct.rid R R i.invariants).injective ?_
  refine Subtype.val_injective ?_
  simp only [AlgHom.comp_apply]
  rw [L, incl2_comulQ, lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]
  exact congrArg Subtype.val (AlgEquiv.apply_symm_apply _ b).symm

/-! ### The Hopf algebra `B` and the quotient `G/H` -/

instance instBialgebraQ : Bialgebra R i.invariants :=
  Bialgebra.ofAlgHom i.comulQ i.counitQ i.coassoc_Q i.rTensor_counit_Q i.lTensor_counit_Q

theorem comul_Q (b : i.invariants) : comul (R := R) b = i.comulQ b := rfl

theorem counit_Q (b : i.invariants) : counit (R := R) b = counit (R := R) (b : G.A) := rfl

instance instHopfAlgebraQ : HopfAlgebra R i.invariants where
  __ := i.instBialgebraQ
  antipode := i.antipodeQ
  mul_antipode_rTensor_comul := by
    have L : ∀ y : i.invariants ⊗[R] i.invariants,
        (LinearMap.mul' R i.invariants (i.antipodeQ.rTensor _ y) : G.A) =
        LinearMap.mul' R G.A ((antipode R (A := G.A)).rTensor G.A (i.incl2 y)) := by
      intro y
      induction y with
      | zero => simp
      | tmul a b => simp [antipodeQ]
      | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
    ext b
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
    erw [L, comul_Q, incl2_comulQ, mul_antipode_rTensor_comul_apply]
    rfl
  mul_antipode_lTensor_comul := by
    have L : ∀ y : i.invariants ⊗[R] i.invariants,
        (LinearMap.mul' R i.invariants (i.antipodeQ.lTensor _ y) : G.A) =
        LinearMap.mul' R G.A ((antipode R (A := G.A)).lTensor G.A (i.incl2 y)) := by
      intro y
      induction y with
      | zero => simp
      | tmul a b => simp [antipodeQ]
      | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
    ext b
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply]
    erw [L, comul_Q, incl2_comulQ, mul_antipode_lTensor_comul_apply]
    rfl

instance instIsCocommQ : IsCocomm R i.invariants where
  comm_comp_comul := by
    have L : ∀ y : i.invariants ⊗[R] i.invariants,
        i.incl2 (TensorProduct.comm R _ _ y) = TensorProduct.comm R _ _ (i.incl2 y) := by
      intro y
      induction y with
      | zero => simp
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    ext b
    refine i.incl2_injective ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [comul_Q, L, incl2_comulQ, comm_comul]

/-- **The quotient `G/H = Spec A^H`.** -/
def quotient : FFGroupScheme R where
  A := i.invariants

/-- The quotient map `G → G/H`: the inclusion `A^H → A`. -/
def quotientHom : Hom G i.quotient :=
  BialgHom.ofAlgHom (A := i.invariants) i.invariants.val (AlgHom.ext fun _ => rfl)
    (AlgHom.ext fun b => i.incl2_comulQ b)

@[simp] theorem quotientHom_apply (b : i.quotient.A) :
    i.quotientHom b = Subtype.val (b : i.invariants) := rfl

theorem quotientHom_injective : Function.Injective i.quotientHom := Subtype.val_injective

/-! ### Rank and order -/

variable [IsLocalRing R]

instance : Module.Finite i.invariants G.A := Module.Finite.of_restrictScalars_finite R _ _

instance : Finite (MaximalSpectrum i.invariants) := by
  have := finite_primeSpectrum_of_isLocalRing (R := R)
  have : Finite (PrimeSpectrum i.invariants) :=
    Algebra.QuasiFinite.finite_primeSpectrum R i.invariants
  exact Finite.of_injective _ MaximalSpectrum.toPrimeSpectrum_injective

variable {i}

omit [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] in
/-- `A` has rank `|H|` at every prime of `B` (from the Galois isomorphism). -/
theorem rankAtStalk_invariants (hi : Function.Surjective i) (q : PrimeSpectrum i.invariants) :
    Module.rankAtStalk (R := i.invariants) G.A q = H.order := by
  have := i.projective_invariants hi
  have : FaithfulSMul i.invariants G.A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  obtain ⟨p, rfl⟩ := Algebra.IsIntegral.comap_surjective i.invariants G.A q
  rw [← Module.rankAtStalk_baseChange (S := G.A),
    Module.rankAtStalk_eq_of_equiv (i.canEquiv hi).toLinearEquiv, Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- **`A` is free of rank `|H|` over `B = A^H`.** -/
theorem nonempty_basis_invariants (hi : Function.Surjective i) :
    Nonempty (Module.Basis (Fin H.order) i.invariants G.A) := by
  have := i.projective_invariants hi
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ _ fun P => ?_
  letI := Ideal.Quotient.field P.1
  rw [← Module.finrank_baseChange (R := P.1.ResidueField),
    (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).finrank_eq,
    ← rankAtStalk_invariants hi ⟨P.1, P.2.isPrime⟩, Module.rankAtStalk_eq]

/-- **[Hong, Thm. 1.1.9]: `|G| = |H| · |G/H|`.** -/
theorem order_eq_mul (hi : Function.Surjective i) : G.order = H.order * i.quotient.order := by
  obtain ⟨b⟩ := nonempty_basis_invariants hi
  have : Module.Free i.invariants G.A := .of_basis b
  have : Nontrivial G.A := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg (counit (R := R) (A := G.A)) h
    rw [map_zero, Bialgebra.counit_one] at this
    exact zero_ne_one this
  change Module.finrank R G.A = Module.finrank R H.A * Module.finrank R i.invariants
  rw [← Module.finrank_mul_finrank R i.invariants G.A, Module.finrank_eq_card_basis b,
    Fintype.card_fin, mul_comm]
  rfl

/-! ### Exactness of `0 → H → G → G/H` on points -/

omit [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] in
variable (i) in
/-- `ε ∘ tr_t = t ∘ i`. -/
theorem counit_trace (t : H.A →ₗ[R] R) (a : G.A) :
    counit (R := R) (i.trace t a) = t (i a) := by
  have key : ∀ w : G.A ⊗[R] G.A, counit (R := R) (TensorProduct.rid R G.A
      (t.lTensor G.A (TensorProduct.map LinearMap.id (i : G.A →ₗ[R] H.A) w))) =
      t (i (TensorProduct.lid R G.A ((counit (R := R) (A := G.A)).rTensor G.A w))) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [mul_comm]
  rw [trace_apply, coact_apply, key, rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

omit [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] in
/-- **`ker i = A · B⁺`**: an element killed by `i` lies in the ideal generated by the
`b - ε(b)`, `b ∈ B`. -/
theorem mem_span_of_apply_eq_zero (hi : Function.Surjective i) {a : G.A} (ha : i a = 0) :
    a ∈ Ideal.span {x | ∃ b ∈ i.invariants, x = b - algebraMap R G.A (counit (R := R) b)} := by
  obtain ⟨ι, _, t, S, ht, hS⟩ := i.exists_dualBasisData hi
  rw [← i.sum_sum_mul_trace hS a]
  refine Ideal.sum_mem _ fun j _ => Ideal.sum_mem _ fun s _ => ?_
  have h0 : counit (R := R) (i.trace (t j) (s.2 * a)) = 0 := by
    rw [counit_trace, map_mul, ha, mul_zero, map_zero]
  have : i.trace (t j) (s.2 * a) = i.trace (t j) (s.2 * a) -
      algebraMap R G.A (counit (R := R) (i.trace (t j) (s.2 * a))) := by
    rw [h0, map_zero, sub_zero]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, i.trace_mem (ht j) _, rfl⟩)

omit [IsLocalRing R] in
/-- **Exactness of `H(T) → G(T) → (G/H)(T)`**: a point of `G` maps to `1` in `G/H` iff it comes
from `H`. -/
theorem mapPoints_quotientHom_eq_one_iff (hi : Function.Surjective i) {T : Type*} [CommRing T]
    [Algebra R T] (g : G.points T) :
    i.quotientHom.mapPoints T g = 1 ↔ ∃ h : H.points T, i.mapPoints T h = g := by
  constructor
  · intro hg
    have hB : ∀ b ∈ i.invariants, ofConv g b = algebraMap R T (counit (R := R) b) := by
      intro b hb
      exact congrArg (fun f : i.quotient.points T => (ofConv f : i.quotient.A →ₐ[R] T)
        (⟨b, hb⟩ : i.invariants)) hg
    have hker : RingHom.ker (i : G.A →ₐ[R] H.A).toRingHom ≤
        RingHom.ker (ofConv g : G.A →ₐ[R] T).toRingHom := by
      intro a ha
      have hspan := mem_span_of_apply_eq_zero hi ha
      rw [RingHom.mem_ker]
      refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker (ofConv g : G.A →ₐ[R] T)) hspan
      rintro x ⟨b, hb, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hB b hb, AlgHom.commutes, sub_self]
    refine ⟨toConv (AlgHom.liftOfSurjective (i : G.A →ₐ[R] H.A) hi (ofConv g) hker), ?_⟩
    apply WithConv.ofConv_injective
    exact AlgHom.liftOfSurjective_comp _ hi _ hker
  · rintro ⟨h, rfl⟩
    apply WithConv.ofConv_injective
    ext b
    change ofConv h (i (Subtype.val (show i.invariants from b))) =
      algebraMap R T (counit (R := R) (Subtype.val (show i.invariants from b)))
    rw [apply_of_mem_invariants i (show i.invariants from b).2, AlgHom.commutes]

omit [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] in
/-- `H(T) → G(T)` is injective for a closed immersion `H → G`. -/
theorem mapPoints_injective_of_surjective (hi : Function.Surjective i) {T : Type*} [CommRing T]
    [Algebra R T] : Function.Injective (i.mapPoints T) := by
  intro h h' hh
  apply WithConv.ofConv_injective
  ext c
  obtain ⟨a, rfl⟩ := hi c
  exact congrArg (fun f : G.points T => (ofConv f : G.A →ₐ[R] T) a) hh

end Hom

end FFGroupScheme

end PadicHodge
