/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Alpha
import PadicHodge.FormalGroup.GaloisAction

/-!
# Galois equivariance of `α`

([Hong, Prop. 3.4.9]: "`α` and `dα` are `Γ_K`-equivariant".) Let `σ ∈ Gal(ℚ̄_p/ℚ_p)` fix the
coefficients `R → O_{ℂ_p}` (hypothesis `hR`; for all `σ` if `GalFixed p R`, e.g. `R = ℤ_p`; for
`R = O_{K'}` the `σ ∈ Gal(ℚ̄_p/K')`). Then `σ` acts on `O_{ℂ_p}` by `R`-algebra automorphisms
(`galS`), on `T_p(G^∨)(O_{ℂ_p})` (`galDual`) and on `F(m_{ℂ_p})`
(`FGL.galPt`), and

* `charSeries_gal`: `U_{σy} = σ(U_y)` (coefficientwise), from the uniqueness of `U` and
  `evB_map_gal` (evaluation `S[[T]] → S ⊗ A_v` commutes with `σ ⊗ id`, via `ringHom_ext`);
* **`alpha_gal`**: `α(σx)(σy) = σ(α(x)(y))`.
-/

noncomputable section

open MvPowerSeries IsLocalRing TensorProduct WithConv

namespace PadicHodge

open FGL

namespace AdicEval

/-- **Ring maps out of `R[[X_σ]]` into an `𝔞`-adically separated ring** agreeing on constants and
on the variables (with values in `𝔞`) are equal. -/
theorem ringHom_ext {R S : Type*} [CommRing R] [CommRing S] {σ : Type*} [Finite σ] (𝔞 : Ideal S)
    [IsHausdorff 𝔞 S] {φ ψ : MvPowerSeries σ R →+* S} (hφ : ∀ i, φ (X i) ∈ 𝔞)
    (hX : ∀ i, φ (X i) = ψ (X i)) (hC : ∀ r, φ (C r) = ψ (C r)) : φ = ψ := by
  have hpoly : φ.comp MvPolynomial.coeToMvPowerSeries.ringHom =
      ψ.comp MvPolynomial.coeToMvPowerSeries.ringHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simpa [MvPolynomial.coeToMvPowerSeries.ringHom_apply] using hC r
    · simpa [MvPolynomial.coeToMvPowerSeries.ringHom_apply] using hX i
  have hP : ∀ P : MvPolynomial σ R, φ (P : MvPowerSeries σ R) = ψ P := fun P => by
    have := congrArg (fun g => g P) hpoly
    simpa [MvPolynomial.coeToMvPowerSeries.ringHom_apply] using this
  have hmap : ∀ (χ : MvPowerSeries σ R →+* S), (∀ i, χ (X i) ∈ 𝔞) → ∀ n,
      ∀ r ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ n, χ r ∈ 𝔞 ^ n := by
    intro χ hχ n r hr
    have h1 : Ideal.map χ (Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ n) ≤ 𝔞 ^ n := by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hχ i
    exact h1 (Ideal.mem_map_of_mem _ hr)
  ext f
  refine (IsHausdorff.eq_iff_smodEq (I := 𝔞)).mpr fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top]
  rw [SModEq.sub_mem]
  have e : f = (MvPowerSeries.truncTotal n f : MvPowerSeries σ R) +
      (f - MvPowerSeries.truncTotal n f) := by ring
  rw [e, map_add, map_add, hP, add_sub_add_left_eq_sub]
  exact Ideal.sub_mem _ (hmap φ hφ n _ (sub_truncTotal_mem n f))
    (hmap ψ (fun i => hX i ▸ hφ i) n _ (sub_truncTotal_mem n f))

end AdicEval

namespace PDivFGL

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (P : PDivFGL R d p) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
  (hR : ∀ r : R, autCp σ ((algebraMap R (OC p) r : OC p) : ℂ_[p]) = algebraMap R (OC p) r)

local notation "S" => OCd p

/-- `σ ∈ Gal(ℚ̄_p/ℚ_p)` as an `R`-algebra automorphism of `O_{ℂ_p}`. -/
def galS : S →ₐ[R] S where
  toFun := autOC σ
  map_one' := Subtype.ext (show autCp σ ((1 : OC p) : ℂ_[p]) = ((1 : OC p) : ℂ_[p]) by
    rw [OneMemClass.coe_one, map_one])
  map_mul' a b := Subtype.ext (show autCp σ ((OCd.toOC a * OCd.toOC b : OC p) : ℂ_[p]) =
      autCp σ (OCd.toOC a : ℂ_[p]) * autCp σ (OCd.toOC b : ℂ_[p]) by
    rw [Subring.coe_mul, map_mul])
  map_zero' := Subtype.ext (show autCp σ ((0 : OC p) : ℂ_[p]) = ((0 : OC p) : ℂ_[p]) by
    rw [ZeroMemClass.coe_zero, map_zero])
  map_add' a b := Subtype.ext (show autCp σ ((OCd.toOC a + OCd.toOC b : OC p) : ℂ_[p]) =
      autCp σ (OCd.toOC a : ℂ_[p]) + autCp σ (OCd.toOC b : ℂ_[p]) by
    rw [Subring.coe_add, map_add])
  commutes' r := Subtype.ext (hR r)

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R]
  [DiscreteUniformity R] in
theorem galS_apply (a : S) :
    ((OCd.toOC (galS σ hR a) : OC p) : ℂ_[p]) = autCp σ (OCd.toOC a : ℂ_[p]) :=
  rfl

/-- The Galois action on `T_p(G^∨)(O_{ℂ_p})`. -/
def galDual (y : P.pdivGroup.DualTate S) :
    P.pdivGroup.DualTate S :=
  ⟨fun v => (P.groupScheme v).dual.postComp (galS σ hR) (y.1 v), fun v => by
    beta_reduce
    rw [y.2 v]
    rfl⟩

omit [UniformSpace R] [DiscreteUniformity R] in
theorem charB_gal (y : P.pdivGroup.DualTate S)
    (v : ℕ) : P.charB (P.galDual σ hR y) v =
      Algebra.TensorProduct.map (galS σ hR) (AlgHom.id R (P.A v)) (P.charB y v) :=
  (P.groupScheme v).charOf_postComp S (galS σ hR) (y.1 v)

variable [hC : IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R)

omit [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R] in
/-- **Evaluation `S[[T]] → S ⊗ A_v` commutes with `σ`.** -/
theorem evB_map_gal (v : ℕ)
    (U : MvPowerSeries (Fin d) S) :
    P.evB S v (MvPowerSeries.map (galS σ hR).toRingHom U) =
      Algebra.TensorProduct.map (galS σ hR) (AlgHom.id R (P.A v)) (P.evB S v U) := by
  haveI := AdicEval.isHausdorff_evIdeal (𝔪 := (maximalIdeal R).map (algebraMap R S))
    (P.tnfB S v)
  have key := AdicEval.ringHom_ext (AdicEval.evIdeal ((maximalIdeal R).map (algebraMap R S))
      fun j => (1 : S) ⊗ₜ[R] P.t v j)
    (φ := (P.evB S v).toRingHom.comp (MvPowerSeries.map (galS σ hR).toRingHom))
    (ψ := (Algebra.TensorProduct.map (galS σ hR) (AlgHom.id R (P.A v))).toRingHom.comp
      (P.evB S v).toRingHom)
    (fun i => by
      simp only [RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evB_X]
      exact AdicEval.mem_evIdeal _ i)
    (fun i => by
      simp only [RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evB_X,
        Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply])
    (fun r => by
      simp only [RingHom.comp_apply, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evB_C,
        Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, map_one,
        Algebra.algebraMap_self, RingHom.id_apply])
  exact congrArg (fun g => g U) key

omit [UniformSpace R] [DiscreteUniformity R] in
/-- **`U_{σy} = σ(U_y)`.** -/
theorem charSeries_gal (y : P.pdivGroup.DualTate S) :
    P.charSeries hpm (P.galDual σ hR y) =
      MvPowerSeries.map (galS σ hR).toRingHom (P.charSeries hpm y) :=
  (P.charSeries_unique hpm _ _ fun v => by
    rw [evB_map_gal, evB_charSeries, charB_gal]).symm

omit [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [UniformSpace R] [DiscreteUniformity R]
  hC in
/-- Evaluation of `O_{ℂ_p}`-coefficient power series commutes with `σ` (acting on coefficients
and points). -/
theorem ev_gal {σ' : Type*} [Finite σ']
    (f : MvPowerSeries σ' S) {a : σ' → OC p} (ha : ∀ s, ‖((a s : OC p) : ℂ_[p])‖ < 1) :
    autCp σ ((ev p f a : OC p) : ℂ_[p]) =
      ev p (MvPowerSeries.map (galS σ hR).toRingHom f) (fun s => autOC σ (a s)) := by
  have ha' : ∀ s, ‖((autOC σ (a s) : OC p) : ℂ_[p])‖ < 1 := fun s => by
    rw [autOC_coe, norm_autCp]; exact ha s
  have h1 := ((hasSum_eval₂ continuous_algebraMap_OC (hasEval_of_norm_lt_one ha) f).map
    (OC p).subtype.toAddMonoidHom continuous_subtype_val).map (autCp σ).toAddMonoidHom
    (continuous_autCp σ)
  have h2 := (hasSum_eval₂ continuous_algebraMap_OC (hasEval_of_norm_lt_one ha')
    (MvPowerSeries.map (galS σ hR).toRingHom f)).map
    (OC p).subtype.toAddMonoidHom continuous_subtype_val
  refine h1.unique (h2.congr_fun fun m => ?_)
  simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    Subring.coe_subtype, Subring.coe_mul, map_mul, coe_finsuppProd_OC, map_prod, map_pow,
    autOC_coe, coeff_map]
  rfl

omit [UniformSpace R] [DiscreteUniformity R] in
/-- **Galois equivariance of `α`** ([Hong, Prop. 3.4.9]): `α(σx)(σy) = σ(α(x)(y))`. -/
theorem alpha_gal (x : P.F.Pt p)
    (y : P.pdivGroup.DualTate S) :
    ((P.alpha hpm (galPt σ x) (P.galDual σ hR y) : OC p) : ℂ_[p]) =
      autCp σ ((P.alpha hpm x y : OC p) : ℂ_[p]) := by
  rw [alpha, alpha, charSeries_gal, ev_gal σ hR _ x.2]
  rfl

end PDivFGL

end PadicHodge
