/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.EtaleQuotientEtale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.IdempotentFG

/-!
# `A` is faithfully flat over `A^{et}`

Let `G = Spec A` be a finite flat commutative group scheme over a complete local PID `R`. Since
`G^{et} = Spec A^{et}` is étale (`GroupScheme/EtaleQuotientEtale.lean`), `A` is faithfully flat
over `A^{et}`. Standard argument, written up here:

* `flat_of_formallyUnramified`: if `S` is an unramified `R`-algebra (formally unramified,
  essentially of finite type) and `M` is an `S`-module flat over `R`, then `M` is flat over `S`. The
  diagonal of `S ⊗_R S` is cut out by an idempotent: `ker (m : S ⊗ S → S) = (e)` with `e² = e`
  (Mathlib `KaehlerDifferential.ideal_fg`, `Ideal.isIdempotentElem_iff_of_fg`), so `δ = 1 - e`
  satisfies `m(δ) = 1` and `δ (s ⊗ 1) = δ (1 ⊗ s)`. Then `m ↦ δ · (1 ⊗ m)` is an `S`-linear
  section of `S ⊗_R M → M`, `s ⊗ m ↦ s m`, so `M` is a retract of the flat `S`-module `S ⊗_R M`.
* `FFGroupScheme.flat_etaleInvariants`, `FFGroupScheme.faithfullyFlat_etaleInvariants`: `A` is
  (faithfully) flat over `A^{et}`; faithfulness since `A^{et} → A` is injective and integral, so
  every maximal ideal of `A^{et}` lies under a maximal ideal of `A` (going up).

**Open**: the order formula `|G| = |G⁰| · |G^{et}|`. Plan: the map
`A ⊗_{A^{et}} A → A ⊗_R A⁰`, `x ⊗ y ↦ (x ⊗ 1)(id ⊗ π)(Δ y)` is an isomorphism, with inverse
`x ⊗ π(y) ↦ ∑ x S(y₁) ⊗ y₂`; well-definedness of the inverse amounts to `∑ S(e₀₁) ⊗ e₀₂ = 1` in
`A ⊗_{A^{et}} A`, which holds since the point `i₁⁻¹ i₂ ∈ G(A ⊗_{A^{et}} A)` is trivial on `A^{et}`,
hence kills `A · ker(ε|A^{et}) = (1 - e₀)` (`map_ker_counitEt`). So `A` is finite projective over
`A^{et}` of constant rank `|G⁰|`, and it remains to convert this into
`rank_R A = |G⁰| · rank_R A^{et}` (e.g. after base change to the fraction field of `R`, where
`A^{et}` becomes a product of fields).
-/

noncomputable section

open TensorProduct

namespace PadicHodge

section Diagonal

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [Module S M] [IsScalarTower R S M]

variable (R S) in
/-- `s' ↦ s' • m` as an `R`-linear map `S → M`. -/
def actOn (m : M) : S →ₗ[R] M where
  toFun s := s • m
  map_add' s t := add_smul s t m
  map_smul' r s := smul_assoc r s m

variable (R S M) in
/-- The action `(s ⊗ s') · m = s ⊗ s' m` of `S ⊗_R S` on `M`, with values in `S ⊗_R M`. -/
def diagAct (x : S ⊗[R] S) : M →ₗ[R] S ⊗[R] M where
  toFun m := TensorProduct.map LinearMap.id (actOn R S m) x
  map_add' m m' := by
    induction x with
    | zero => simp
    | tmul s s' => simp [actOn, TensorProduct.tmul_add]
    | add x y hx hy => simp only [map_add, hx, hy]; abel
  map_smul' r m := by
    induction x with
    | zero => simp
    | tmul s s' => simp [actOn, smul_comm s' r m, TensorProduct.tmul_smul]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add, RingHom.id_apply]

theorem diagAct_tmul (s s' : S) (m : M) : diagAct R S M (s ⊗ₜ s') m = s ⊗ₜ (s' • m) := rfl

theorem diagAct_add (x y : S ⊗[R] S) (m : M) :
    diagAct R S M (x + y) m = diagAct R S M x m + diagAct R S M y m :=
  map_add (TensorProduct.map LinearMap.id (actOn R S m)) x y

theorem diagAct_zero (m : M) : diagAct R S M (0 : S ⊗[R] S) m = 0 :=
  map_zero (TensorProduct.map LinearMap.id (actOn R S m))

theorem diagAct_mul_one_tmul (x : S ⊗[R] S) (s : S) (m : M) :
    diagAct R S M (x * (1 ⊗ₜ s)) m = diagAct R S M x (s • m) := by
  induction x with
  | zero => simp [diagAct_zero]
  | tmul t t' => simp [Algebra.TensorProduct.tmul_mul_tmul, diagAct_tmul, mul_smul]
  | add x y hx hy => rw [add_mul, diagAct_add, hx, hy, diagAct_add]

theorem diagAct_mul_tmul_one (x : S ⊗[R] S) (s : S) (m : M) :
    diagAct R S M (x * (s ⊗ₜ 1)) m = s • diagAct R S M x m := by
  induction x with
  | zero => simp [diagAct_zero]
  | tmul t t' => simp [Algebra.TensorProduct.tmul_mul_tmul, diagAct_tmul, smul_tmul', mul_comm]
  | add x y hx hy => rw [add_mul, diagAct_add, hx, hy, diagAct_add, smul_add]

theorem liftBaseChange_diagAct (x : S ⊗[R] S) (m : M) :
    (LinearMap.id : M →ₗ[R] M).liftBaseChange S (diagAct R S M x m) =
      Algebra.TensorProduct.lmul' R x • m := by
  induction x with
  | zero => simp [diagAct_zero]
  | tmul t t' => simp [diagAct_tmul, mul_smul]
  | add x y hx hy => rw [diagAct_add, map_add, hx, hy, map_add, add_smul]

/-- Over an unramified `R`-algebra `S`, an `S`-module that is flat over `R` is flat over `S`. -/
theorem flat_of_formallyUnramified [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] [Module.Flat R M] : Module.Flat S M := by
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal R S = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[S⁄R]
  have hδ : ∀ s : S, (1 - e) * (s ⊗ₜ[R] 1) = (1 - e) * (1 ⊗ₜ s) := by
    intro s
    have hs : s ⊗ₜ[R] (1 : S) - 1 ⊗ₜ s ∈ KaehlerDifferential.ideal R S := by
      simp [RingHom.mem_ker]
    rw [hsp] at hs
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hs
    rw [← sub_eq_zero, ← mul_sub, ← hc, mul_comm c, ← mul_assoc, sub_mul, one_mul, he.eq,
      sub_self, zero_mul]
  have hδ1 : Algebra.TensorProduct.lmul' R (1 - e) = 1 := by
    have : e ∈ KaehlerDifferential.ideal R S := hsp ▸ Ideal.mem_span_singleton_self e
    rw [RingHom.mem_ker] at this
    rw [map_sub, this, map_one, sub_zero]
  let i : M →ₗ[S] S ⊗[R] M :=
    { toFun := fun m => diagAct R S M (1 - e) m
      map_add' := fun m m' => map_add _ m m'
      map_smul' := fun s m => by
        rw [RingHom.id_apply, ← diagAct_mul_one_tmul, ← hδ, diagAct_mul_tmul_one] }
  refine Module.Flat.of_retract i ((LinearMap.id : M →ₗ[R] M).liftBaseChange S) ?_
  ext m
  change (LinearMap.id : M →ₗ[R] M).liftBaseChange S (diagAct R S M (1 - e) m) = m
  rw [liftBaseChange_diagAct, hδ1, one_smul]

end Diagonal

namespace FFGroupScheme

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] (G : FFGroupScheme R)

/-- `A` is flat over `A^{et}`. -/
theorem flat_etaleInvariants : Module.Flat G.etaleInvariants G.A := by
  have : Algebra.Etale R G.etaleInvariants := G.isEtale_etaleQuotient
  exact flat_of_formallyUnramified (R := R)

/-- **`A` is faithfully flat over `A^{et}`.** -/
theorem faithfullyFlat_etaleInvariants : Module.FaithfullyFlat G.etaleInvariants G.A := by
  have := G.flat_etaleInvariants
  have : Module.Finite G.etaleInvariants G.A := Module.Finite.of_restrictScalars_finite R _ _
  refine ⟨fun m hm htop => ?_⟩
  have hker : RingHom.ker (algebraMap G.etaleInvariants G.A) ≤ m := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [show x = 0 from Subtype.ext hx]
    exact zero_mem _
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  have hle : m • (⊤ : Submodule G.etaleInvariants G.A) ≤ Q.restrictScalars G.etaleInvariants :=
    Submodule.smul_le.mpr fun r hr n _ => by
      rw [Submodule.restrictScalars_mem, Algebra.smul_def]
      refine Q.mul_mem_right _ ?_
      rw [← Ideal.mem_comap, hQm]
      exact hr
  rw [htop] at hle
  exact hQ.ne_top ((Ideal.eq_top_iff_one _).mpr (hle Submodule.mem_top))

end FFGroupScheme

end PadicHodge
