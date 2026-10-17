/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.EtaleQuotientFlat
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# `|G| = |G⁰| · |G^{et}|`

Let `G = Spec A` be a finite flat commutative group scheme over a complete local PID `R`, with
connected component `G⁰ = Spec A⁰` and étale quotient `G^{et} = Spec A^{et}`
(`GroupScheme/EtaleQuotient*.lean`). Standard argument, written up here:

* **Galois isomorphism** (`galoisEquiv`): `A ⊗_{A^{et}} A ≅ A ⊗_R A⁰` as `A`-algebras,
  `x ⊗ y ↦ (x ⊗ 1)(id ⊗ π)(Δ y)` (`G ×_{G^{et}} G ≅ G × G⁰`). The inverse is
  `x ⊗ π(y) ↦ (x ⊗ 1) δ(y)` with `δ = i₁⁻¹ i₂ ∈ G(A ⊗_{A^{et}} A)` (`delta`): the two projections
  `i₁, i₂` agree on `A^{et}`, so `δ` maps to `1` in `G^{et}` and hence factors through `G⁰`
  (`mapPoints_etaleQuotientHom_eq_one_iff`); both composites are checked on points by
  convolution identities (`lift_comp_coactConn`).
* **Rank**: base change of the Galois isomorphism along `A^{et} → A` and faithful flatness of `A`
  over `A^{et}` (`faithfullyFlat_etaleInvariants`) give `rankAtStalk A = |G⁰|` at every prime of
  `A^{et}`; `A^{et}` is semilocal (finite over `R`, which has two primes), so `A` is free of rank
  `|G⁰|` over `A^{et}` (Mathlib `Module.nonempty_basis_of_flat_of_finrank_eq`, Stacks 02M9):
  `nonempty_basis_etaleInvariants`.
* **`order_eq_mul`**: `|G| = |G⁰| · |G^{et}|` by the tower law for ranks.
-/

noncomputable section

open TensorProduct Coalgebra HopfAlgebra WithConv IsLocalRing

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] (G : FFGroupScheme R)

/-- `A ⊗_{A^{et}} A`, the coordinate ring of `G ×_{G^{et}} G`. -/
abbrev AA : Type u := G.A ⊗[G.etaleInvariants] G.A

/-- The first projection `G ×_{G^{et}} G → G`. -/
def inl : G.A →ₐ[R] G.AA := Algebra.TensorProduct.includeLeft

/-- The second projection. -/
def inr : G.A →ₐ[R] G.AA :=
  (Algebra.TensorProduct.includeRight : G.A →ₐ[G.etaleInvariants] G.AA).restrictScalars R

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem inl_eq_inr_of_mem {b : G.A} (hb : b ∈ G.etaleInvariants) : G.inl b = G.inr b := by
  change b ⊗ₜ 1 = 1 ⊗ₜ b
  have : b = (⟨b, hb⟩ : G.etaleInvariants) • (1 : G.A) := by simp [Algebra.smul_def]
  rw [this, TensorProduct.smul_tmul]

/-- The point `δ = i₁⁻¹ i₂ ∈ G(A ⊗_{A^{et}} A)`. -/
def delta : G.points G.AA := (toConv G.inl)⁻¹ * toConv G.inr

theorem mapPoints_delta : G.etaleQuotientHom.mapPoints G.AA G.delta = 1 := by
  rw [delta, map_mul, map_inv, inv_mul_eq_one]
  apply WithConv.ofConv_injective
  ext b
  exact G.inl_eq_inr_of_mem (b : G.etaleInvariants).2

/-- `δ` factors through `G⁰`: the map `ψ : A⁰ → A ⊗_{A^{et}} A` with `ψ ∘ π = δ`. -/
def psi : G.connectedComponent.A →ₐ[R] G.AA :=
  ofConv ((G.mapPoints_etaleQuotientHom_eq_one_iff G.delta).mp G.mapPoints_delta).choose

theorem psi_comp : G.psi.comp (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A) =
    ofConv G.delta :=
  congrArg ofConv
    ((G.mapPoints_etaleQuotientHom_eq_one_iff G.delta).mp G.mapPoints_delta).choose_spec

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem lift_comp_coactConn {T : Type*} [CommRing T] [Algebra R T] (f : G.A →ₐ[R] T)
    (g : G.connectedComponent.A →ₐ[R] T) :
    (Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)).comp G.coactConn =
      ofConv (toConv f * toConv (g.comp (G.connectedComponentHom :
        G.A →ₐ[R] G.connectedComponent.A))) := by
  have h : (Algebra.TensorProduct.lift f g (fun _ _ => .all _ _)).comp
      (Algebra.TensorProduct.map (AlgHom.id R G.A)
        (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A)) =
      (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map f
        (g.comp (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A))) :=
    Algebra.TensorProduct.ext' fun a b => by simp
  rw [AlgHom.convMul_def, coactConn, ← AlgHom.comp_assoc, h]
  rfl

/-- The coaction `A → A ⊗_R A⁰` as an `A^{et}`-algebra map (`A^{et}` is coinvariant). -/
def coactConnEt : G.A →ₐ[G.etaleInvariants] G.A ⊗[R] G.connectedComponent.A :=
  { G.coactConn with
    commutes' := fun b => by
      change G.coactConn (b : G.A) = (b : G.A) ⊗ₜ 1
      exact G.mem_etaleInvariants.mp b.2 }

/-- The Galois map `A ⊗_{A^{et}} A → A ⊗_R A⁰`, `x ⊗ y ↦ (x ⊗ 1) (id ⊗ π)(Δ y)`
(`G ×_{G^{et}} G ≅ G × G⁰`). -/
def galois : G.AA →ₐ[G.A] G.A ⊗[R] G.connectedComponent.A :=
  Algebra.TensorProduct.lift (Algebra.ofId G.A _) G.coactConnEt (fun _ _ => .all _ _)

/-- Its inverse `x ⊗ π(y) ↦ x · δ(y)`, `δ = i₁⁻¹ i₂`. -/
def galoisInv : G.A ⊗[R] G.connectedComponent.A →ₐ[G.A] G.AA :=
  Algebra.TensorProduct.lift (Algebra.ofId G.A G.AA) G.psi (fun _ _ => .all _ _)

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem galois_tmul (x y : G.A) : G.galois (x ⊗ₜ y) = (x ⊗ₜ 1) * G.coactConn y := by
  simp [galois, coactConnEt, Algebra.TensorProduct.algebraMap_apply]

theorem galoisInv_tmul (x : G.A) (z : G.connectedComponent.A) :
    G.galoisInv (x ⊗ₜ z) = (x ⊗ₜ 1) * G.psi z := by
  simp [galoisInv, Algebra.TensorProduct.algebraMap_apply]

theorem galoisInv_restrict :
    (G.galoisInv.restrictScalars R) =
      Algebra.TensorProduct.lift G.inl G.psi (fun _ _ => .all _ _) :=
  Algebra.TensorProduct.ext' fun x z => by
    rw [AlgHom.restrictScalars_apply, galoisInv_tmul, Algebra.TensorProduct.lift_tmul]
    rfl

theorem galoisInv_coactConn (a : G.A) : G.galoisInv (G.coactConn a) = G.inr a := by
  have h := G.lift_comp_coactConn G.inl G.psi
  rw [G.psi_comp, delta, ← galoisInv_restrict] at h
  have h2 := congrArg (fun F => F a) h
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h2
  rw [h2, ← mul_assoc, mul_inv_cancel, one_mul]

theorem galoisInv_galois : G.galoisInv.comp G.galois = AlgHom.id G.A G.AA := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · ext a
    change G.galoisInv (G.galois (1 ⊗ₜ a)) = 1 ⊗ₜ a
    rw [galois_tmul, ← Algebra.TensorProduct.one_def, one_mul, galoisInv_coactConn]
    rfl

theorem galois_galoisInv :
    G.galois.comp G.galoisInv = AlgHom.id G.A (G.A ⊗[R] G.connectedComponent.A) := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · ext z
    obtain ⟨a, rfl⟩ := G.connectedComponentHom_surjective z
    change G.galois (G.galoisInv (1 ⊗ₜ G.connectedComponentHom a)) =
      1 ⊗ₜ G.connectedComponentHom a
    rw [galoisInv_tmul, ← Algebra.TensorProduct.one_def, one_mul]
    have hpsi : G.psi (G.connectedComponentHom a) = ofConv G.delta a :=
      congrArg (fun F => F a) G.psi_comp
    rw [hpsi]
    set g : G.AA →ₐ[R] G.A ⊗[R] G.connectedComponent.A := G.galois.restrictScalars R
    have hd : G.pointsMap g G.delta =
        (toConv Algebra.TensorProduct.includeLeft)⁻¹ * toConv G.coactConn := by
      rw [delta, map_mul, map_inv]
      congr 2
      · apply WithConv.ofConv_injective
        ext x
        change G.galois (x ⊗ₜ 1) = x ⊗ₜ 1
        rw [galois_tmul, map_one, mul_one]
      · apply WithConv.ofConv_injective
        ext x
        change G.galois (1 ⊗ₜ x) = G.coactConn x
        rw [galois_tmul, ← Algebra.TensorProduct.one_def, one_mul]
    have hc : toConv G.coactConn = toConv (Algebra.TensorProduct.includeLeft :
          G.A →ₐ[R] G.A ⊗[R] G.connectedComponent.A) *
        toConv ((Algebra.TensorProduct.includeRight :
          G.connectedComponent.A →ₐ[R] G.A ⊗[R] G.connectedComponent.A).comp
          (G.connectedComponentHom : G.A →ₐ[R] G.connectedComponent.A)) := by
      apply WithConv.ofConv_injective
      rw [← G.lift_comp_coactConn, Algebra.TensorProduct.lift_includeLeft_includeRight]
      rfl
    rw [hc, inv_mul_cancel_left] at hd
    exact congrArg (fun F : G.points (G.A ⊗[R] G.connectedComponent.A) => ofConv F a) hd

/-- **The Galois isomorphism** `A ⊗_{A^{et}} A ≅ A ⊗_R A⁰` (`G ×_{G^{et}} G ≅ G × G⁰`), an
isomorphism of `A`-algebras (`A` acting on the left factors). -/
def galoisEquiv : G.AA ≃ₐ[G.A] G.A ⊗[R] G.connectedComponent.A :=
  AlgEquiv.ofAlgHom G.galois G.galoisInv G.galois_galoisInv G.galoisInv_galois

/-! ### The order formula -/

omit [IsAdicComplete (maximalIdeal R) R] in
/-- A local PID has finitely many primes (`0` and the maximal ideal). -/
theorem finite_primeSpectrum_of_isLocalRing : Finite (PrimeSpectrum R) := by
  refine Finite.of_injective (fun p : PrimeSpectrum R => decide (p.asIdeal = ⊥)) fun p q h => ?_
  have key : ∀ p : PrimeSpectrum R, p.asIdeal ≠ ⊥ → p.asIdeal = maximalIdeal R := fun p hp =>
    IsLocalRing.eq_maximalIdeal (_root_.IsPrime.to_maximal_ideal (hpi := p.isPrime) hp)
  ext1
  by_cases hp : p.asIdeal = ⊥
  · have hq : q.asIdeal = ⊥ := by simpa [hp] using h.symm
    rw [hp, hq]
  · have hq : q.asIdeal ≠ ⊥ := by simpa [hp] using h.symm
    rw [key p hp, key q hq]

instance : Module.Finite G.etaleInvariants G.A := Module.Finite.of_restrictScalars_finite R _ _

instance : Module.Flat G.etaleInvariants G.A := G.flat_etaleInvariants

instance : Finite (MaximalSpectrum G.etaleInvariants) := by
  have := finite_primeSpectrum_of_isLocalRing (R := R)
  have : Finite (PrimeSpectrum G.etaleInvariants) :=
    Algebra.QuasiFinite.finite_primeSpectrum R G.etaleInvariants
  exact Finite.of_injective _ MaximalSpectrum.toPrimeSpectrum_injective

/-- `A` has rank `|G⁰|` at every prime of `A^{et}` (from the Galois isomorphism). -/
theorem rankAtStalk_etaleInvariants (q : PrimeSpectrum G.etaleInvariants) :
    Module.rankAtStalk (R := G.etaleInvariants) G.A q = G.connectedComponent.order := by
  have := G.faithfullyFlat_etaleInvariants
  obtain ⟨p, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := G.etaleInvariants) (B := G.A) q
  rw [← Module.rankAtStalk_baseChange (S := G.A),
    Module.rankAtStalk_eq_of_equiv G.galoisEquiv.toLinearEquiv, Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- **`A` is free of rank `|G⁰|` over `A^{et}`.** -/
theorem nonempty_basis_etaleInvariants :
    Nonempty (Module.Basis (Fin G.connectedComponent.order) G.etaleInvariants G.A) := by
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ _ fun P => ?_
  letI := Ideal.Quotient.field P.1
  rw [← Module.finrank_baseChange (R := P.1.ResidueField),
    (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).finrank_eq,
    ← G.rankAtStalk_etaleInvariants ⟨P.1, P.2.isPrime⟩, Module.rankAtStalk_eq]

/-- **`|G| = |G⁰| · |G^{et}|`.** -/
theorem order_eq_mul : G.order = G.connectedComponent.order * G.etaleQuotient.order := by
  obtain ⟨b⟩ := G.nonempty_basis_etaleInvariants
  have : Module.Free G.etaleInvariants G.A := .of_basis b
  have : Nontrivial G.A := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg (counit (R := R) (A := G.A)) h
    rw [map_zero, Bialgebra.counit_one] at this
    exact zero_ne_one this
  have : Nontrivial G.etaleInvariants := inferInstance
  change Module.finrank R G.A = Module.finrank R G.connectedComponent.A *
    Module.finrank R G.etaleInvariants
  rw [← Module.finrank_mul_finrank R G.etaleInvariants G.A,
    Module.finrank_eq_card_basis b, Fintype.card_fin, mul_comm]
  rfl

end FFGroupScheme

end PadicHodge
