/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.FiniteFlat

/-!
# Constant group schemes

For a finite commutative group `M`, the constant group scheme `M_R = Spec R^M` ([BC, Example
7.1.7(1)]) has coordinate ring the ring of functions `M → R`, with comultiplication
`Δ f = ∑_{m,n} f(mn) e_m ⊗ e_n` (`e_m` the indicator of `m`), counit `f ↦ f(1)` and antipode
`f ↦ f ∘ (·)⁻¹`.

* `constHopf`: this Hopf algebra structure; `FFGroupScheme.const M`, of order `|M|`;
* `constPointsEquiv`: for a domain `S` (more generally: no nontrivial idempotents would do),
  `M_R(S) ≃* M`.
-/

noncomputable section

open TensorProduct Coalgebra

namespace PadicHodge

universe u

variable (R : Type u) [CommRing R] (M : Type) [CommGroup M] [Fintype M] [DecidableEq M]

namespace ConstGS

/-- The indicator function `e_m`. -/
def e (m : M) : M → R := Pi.single m 1

variable {R M}

omit [CommGroup M] [Fintype M] in
theorem e_apply (m x : M) : e R M m x = if x = m then 1 else 0 := Pi.single_apply _ _ _

omit [CommGroup M] in
theorem eq_sum (f : M → R) : f = ∑ m, f m • e R M m := by
  ext x
  simp [Finset.sum_apply, e_apply]

omit [CommGroup M] [Fintype M] in
theorem single_eq_smul_e (k : M) (x : R) : Pi.single k x = x • e R M k := by
  ext y; simp [e_apply, Pi.single_apply]

omit [CommGroup M] [Fintype M] in
theorem e_mul_e (m n : M) : e R M m * e R M n = if m = n then e R M m else 0 := by
  ext x
  simp only [Pi.mul_apply, e_apply]
  by_cases h : m = n <;> by_cases hx : x = m <;> simp_all [e_apply]

variable (R M)

/-- `Δ f = ∑_{m,n} f(mn) e_m ⊗ e_n`. -/
def comul : (M → R) →ₗ[R] (M → R) ⊗[R] (M → R) where
  toFun f := ∑ m, ∑ n, f (m * n) • (e R M m ⊗ₜ e R M n)
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum, smul_smul]

/-- `ε f = f(1)`. -/
def counit : (M → R) →ₗ[R] R := LinearMap.proj 1

variable {R M}

theorem comul_apply (f : M → R) :
    comul R M f = ∑ m, ∑ n, f (m * n) • (e R M m ⊗ₜ e R M n) := rfl

theorem comul_e (k : M) :
    comul R M (e R M k) = ∑ m, ∑ n, (if m * n = k then (1 : R) else 0) • (e R M m ⊗ₜ e R M n) := by
  rw [comul_apply]
  simp only [e_apply]

/-- A triple sum that collapses. -/
theorem sum_sum_ite {A : Type*} [AddCommMonoid A] (k : M) (F : M → M → A) :
    ∑ m, ∑ n, (if m * n = k then F m n else 0) = ∑ m, F m (m⁻¹ * k) := by
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single (m⁻¹ * k)]
  · rw [if_pos (mul_inv_cancel_left m k)]
  · intro n _ hn
    rw [if_neg]
    intro h; apply hn; rw [← h, inv_mul_cancel_left]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem comul_e' (k : M) :
    comul R M (e R M k) = ∑ m, e R M m ⊗ₜ e R M (m⁻¹ * k) := by
  rw [comul_e]
  simp only [ite_smul, one_smul, zero_smul]
  exact sum_sum_ite k (fun m n => e R M m ⊗ₜ e R M n)

theorem comul_single (k : M) (x : R) :
    comul R M (Pi.single k x) = x • comul R M (e R M k) := by
  rw [single_eq_smul_e, map_smul]

omit [Fintype M] in
theorem counit_e (k : M) : counit R M (e R M k) = if k = 1 then 1 else 0 := by
  change e R M k 1 = _
  by_cases h : k = 1 <;> simp [e_apply, h, eq_comm]

theorem coassoc_e (k : M) :
    TensorProduct.assoc R _ _ _ ((comul R M).rTensor _ (comul R M (e R M k))) =
      (comul R M).lTensor _ (comul R M (e R M k)) := by
  rw [comul_e', map_sum, map_sum, map_sum]
  simp only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, comul_e', TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, map_sum, TensorProduct.assoc_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine (Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun b => ?_)).symm
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, mul_inv_rev, mul_assoc]

end ConstGS

open ConstGS

instance constCoalgebra : Coalgebra R (M → R) where
  comul := ConstGS.comul R M
  counit := ConstGS.counit R M
  coassoc := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [single_eq_smul_e]
    simp only [LinearMap.coe_comp, Function.comp_apply, map_smul]
    congr 1
    exact coassoc_e i
  rTensor_counit_comp_comul := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [single_eq_smul_e]
    simp only [LinearMap.coe_comp, Function.comp_apply, map_smul]
    rw [comul_e']
    simp only [map_sum, LinearMap.rTensor_tmul, counit_e, TensorProduct.mk_apply]
    rw [Finset.sum_eq_single 1 (fun b _ hb => by rw [if_neg hb, TensorProduct.zero_tmul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [if_pos rfl, inv_one, one_mul, ← TensorProduct.tmul_smul]
  lTensor_counit_comp_comul := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [single_eq_smul_e]
    simp only [LinearMap.coe_comp, Function.comp_apply, map_smul]
    rw [comul_e']
    simp only [map_sum, LinearMap.lTensor_tmul, counit_e, LinearMap.flip_apply,
      TensorProduct.mk_apply]
    rw [Finset.sum_eq_single i (fun b _ hb => by
        rw [if_neg (fun h => hb (by rw [inv_mul_eq_one] at h; exact h)),
          TensorProduct.tmul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [inv_mul_cancel, if_pos rfl]

namespace ConstGS

variable {R M}

omit [CommGroup M] in
theorem sum_e : ∑ m, e R M m = 1 := by
  ext x; simp [Finset.sum_apply, e_apply]

theorem comul_one' : comul R M 1 = 1 := by
  calc comul R M 1 = (∑ m, e R M m) ⊗ₜ[R] (∑ n, e R M n) := by
        rw [comul_apply, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [TensorProduct.tmul_sum]
        simp
    _ = 1 := by rw [sum_e, Algebra.TensorProduct.one_def]

theorem comul_e_mul_e (i j : M) :
    comul R M (e R M i * e R M j) = comul R M (e R M i) * comul R M (e R M j) := by
  rw [comul_e', comul_e', Finset.sum_mul_sum]
  rw [e_mul_e]
  have key : ∀ m, ∑ n, (e R M m ⊗ₜ[R] e R M (m⁻¹ * i)) * (e R M n ⊗ₜ[R] e R M (n⁻¹ * j)) =
      if i = j then e R M m ⊗ₜ[R] e R M (m⁻¹ * i) else 0 := by
    intro m
    rw [Finset.sum_eq_single m (fun n _ hn => by
        rw [Algebra.TensorProduct.tmul_mul_tmul, e_mul_e, if_neg (Ne.symm hn),
          TensorProduct.zero_tmul])
      (fun h => absurd (Finset.mem_univ _) h)]
    rw [Algebra.TensorProduct.tmul_mul_tmul, e_mul_e, e_mul_e, if_pos rfl]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hij (mul_left_cancel h)), if_neg hij, TensorProduct.tmul_zero]
  simp only [key]
  split_ifs with hij
  · rw [comul_e']
  · rw [map_zero, Finset.sum_const_zero]

theorem comul_mul' (a b : M → R) : comul R M (a * b) = comul R M a * comul R M b := by
  have H : (LinearMap.mul R (M → R)).compr₂ (comul R M) =
      (LinearMap.mul R ((M → R) ⊗[R] (M → R))).compl₁₂ (comul R M) (comul R M) := by
    refine LinearMap.pi_ext fun i x => LinearMap.pi_ext fun j y => ?_
    simp only [single_eq_smul_e, map_smul, LinearMap.smul_apply]
    rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      LinearMap.mul_apply', comul_e_mul_e]
  exact LinearMap.congr_fun₂ H a b

end ConstGS

instance constBialgebra : Bialgebra R (M → R) :=
  Bialgebra.mk' R (M → R) rfl (fun {_ _} => rfl) (comul_one') (fun {a b} => comul_mul' a b)

namespace ConstGS

/-- The antipode `f ↦ f ∘ (·)⁻¹`. -/
def antipode : (M → R) →ₗ[R] (M → R) := LinearMap.funLeft R R (fun m : M => m⁻¹)

omit [Fintype M] in
theorem antipode_e (m : M) : antipode R M (e R M m) = e R M m⁻¹ := by
  ext x
  change e R M m x⁻¹ = e R M m⁻¹ x
  simp only [e_apply, inv_eq_iff_eq_inv]

omit [CommGroup M] in
theorem sum_ite_e (P : Prop) [Decidable P] :
    (∑ m, if P then e R M m else 0) = if P then 1 else 0 := by
  split_ifs <;> simp [sum_e]

theorem sum_ite_e_inv (P : Prop) [Decidable P] :
    (∑ m, if P then e R M m⁻¹ else 0) = if P then 1 else 0 := by
  rw [← sum_ite_e R M P]
  exact Fintype.sum_equiv (Equiv.inv M) _ _ (fun m => rfl)

end ConstGS

open ConstGS in
instance constHopf : HopfAlgebra R (M → R) where
  antipode := ConstGS.antipode R M
  mul_antipode_rTensor_comul := by
    refine LinearMap.pi_ext fun k x => ?_
    rw [single_eq_smul_e]
    simp only [LinearMap.coe_comp, Function.comp_apply, map_smul]
    congr 1
    change LinearMap.mul' R (M → R) ((antipode R M).rTensor _ (comul R M (e R M k))) =
      algebraMap R (M → R) (counit R M (e R M k))
    rw [comul_e', map_sum, map_sum, counit_e]
    simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, antipode_e, e_mul_e]
    have h : ∀ m : M, (m⁻¹ = m⁻¹ * k ↔ k = 1) := fun m => by
      constructor
      · intro h; have := congrArg (m * ·) h; simpa using this.symm
      · rintro rfl; simp
    simp only [h]
    rw [sum_ite_e_inv]
    split_ifs <;> simp
  mul_antipode_lTensor_comul := by
    refine LinearMap.pi_ext fun k x => ?_
    rw [single_eq_smul_e]
    simp only [LinearMap.coe_comp, Function.comp_apply, map_smul]
    congr 1
    change LinearMap.mul' R (M → R) ((antipode R M).lTensor _ (comul R M (e R M k))) =
      algebraMap R (M → R) (counit R M (e R M k))
    rw [comul_e', map_sum, map_sum, counit_e]
    simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply, antipode_e, e_mul_e, mul_inv_rev,
      inv_inv]
    have h : ∀ m : M, (m = k⁻¹ * m) ↔ k = 1 := fun m => by
      constructor
      · intro h; have := congrArg (· * m⁻¹) h; simpa using this.symm
      · rintro rfl; simp
    simp only [h]
    rw [sum_ite_e]
    split_ifs <;> simp

open ConstGS in
instance constIsCocomm : Coalgebra.IsCocomm R (M → R) where
  comm_comp_comul := by
    refine LinearMap.ext fun f => ?_
    change TensorProduct.comm R _ _ (comul R M f) = comul R M f
    rw [comul_apply]
    simp only [map_sum, map_smul, TensorProduct.comm_tmul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by rw [mul_comm]

namespace FFGroupScheme

/-- The constant group scheme `M_R = Spec R^M` ([BC, Example 7.1.7(1)]). -/
def const : FFGroupScheme R where
  A := M → R

theorem order_const [Nontrivial R] : (const R M).order = Fintype.card M :=
  Module.finrank_fintype_fun_eq_card R

section Points

open WithConv ConstGS

variable {R M} (S : Type*) [CommRing S] [IsDomain S] [Algebra R S]

/-- `e_k` as an element of the coordinate ring of `M_R`. -/
def eA (k : M) : (const R M).A := e R M k

/-- A point of `M_R`, as an algebra map on `M → R`. -/
def toAlg (φ : (const R M).points S) : (M → R) →ₐ[R] S := ofConv φ

/-- The point `m ∈ M_R(S)`: evaluation at `m`. -/
def constPt (m : M) : (const R M).points S :=
  toConv ((Algebra.ofId R S).comp (Pi.evalAlgHom R (fun _ : M => R) m))

omit [IsDomain S] in
theorem toAlg_constPt (m : M) (f : M → R) :
    toAlg S (constPt (R := R) S m) f = algebraMap R S (f m) := rfl

omit [IsDomain S] in
/-- Two points agreeing on all `e_k` are equal. -/
theorem points_ext {φ ψ : (const R M).points S}
    (h : ∀ k, toAlg S φ (e R M k) = toAlg S ψ (e R M k)) : φ = ψ := by
  apply WithConv.ofConv_injective
  have : toAlg S φ = toAlg S ψ := by
    refine AlgHom.ext fun f => ?_
    rw [eq_sum f, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, h k]
  exact this

omit [IsDomain S] in
theorem comul_eA (k : M) :
    Coalgebra.comul (R := R) (A := (const R M).A) (eA (R := R) k) =
      ∑ a, eA (R := R) a ⊗ₜ[R] eA (R := R) (a⁻¹ * k) := comul_e' k

omit [IsDomain S] in
theorem toAlg_mul_e (φ ψ : (const R M).points S) (k : M) :
    toAlg S (φ * ψ) (e R M k) =
      ∑ a, toAlg S φ (e R M a) * toAlg S ψ (e R M (a⁻¹ * k)) := by
  change (ofConv (φ * ψ)) (eA (R := R) k) = ∑ a, (ofConv φ) (eA (R := R) a) *
    (ofConv ψ) (eA (R := R) (a⁻¹ * k))
  rw [AlgHom.convMul_apply]
  simp only [comul_eA, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul]

omit [IsDomain S] in
theorem constPt_mul (m n : M) :
    constPt (R := R) S (m * n) = constPt S m * constPt S n := by
  refine points_ext S fun k => ?_
  rw [toAlg_mul_e]
  simp only [toAlg_constPt, e_apply, ← map_mul]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl, one_mul]
    by_cases h : m * n = k
    · rw [if_pos h, if_pos (by rw [← h, inv_mul_cancel_left])]
    · rw [if_neg h, if_neg (fun h' => h (by rw [h', mul_inv_cancel_left]))]
  · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul, map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem constPt_injective [Nontrivial R] : Function.Injective (constPt (R := R) (M := M) S) := by
  intro m n h
  have := congrArg (fun φ => toAlg S φ (e R M m)) h
  rw [toAlg_constPt, toAlg_constPt, e_apply, e_apply] at this
  by_contra hmn
  rw [if_pos rfl, if_neg (Ne.symm hmn), map_zero, map_one] at this
  exact one_ne_zero this

theorem constPt_surjective : Function.Surjective (constPt (R := R) (M := M) S) := by
  intro φ
  set φ' := toAlg S φ
  have hsum : ∑ m, φ' (e R M m) = 1 := by rw [← map_sum, sum_e, map_one]
  have hidem : ∀ m, φ' (e R M m) = 0 ∨ φ' (e R M m) = 1 := fun m => by
    have h : φ' (e R M m) * φ' (e R M m) = φ' (e R M m) := by
      rw [← map_mul, e_mul_e, if_pos rfl]
    have : φ' (e R M m) * (φ' (e R M m) - 1) = 0 := by rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  obtain ⟨m0, hm0⟩ : ∃ m, φ' (e R M m) = 1 := by
    by_contra hne
    push Not at hne
    have : ∑ m, φ' (e R M m) = 0 :=
      Finset.sum_eq_zero fun m _ => (hidem m).resolve_right (hne m)
    rw [hsum] at this
    exact one_ne_zero this
  have hother : ∀ n, n ≠ m0 → φ' (e R M n) = 0 := by
    intro n hn
    have : φ' (e R M n) * φ' (e R M m0) = 0 := by
      rw [← map_mul, e_mul_e, if_neg hn, map_zero]
    rwa [hm0, mul_one] at this
  refine ⟨m0, points_ext S fun k => ?_⟩
  rw [toAlg_constPt, e_apply]
  by_cases hk : m0 = k
  · subst hk; rw [if_pos rfl, map_one, hm0]
  · rw [if_neg hk, map_zero, hother k (Ne.symm hk)]

/-- **Points of the constant group scheme**: `M_R(S) ≃* M` for a domain `S`. -/
def constPointsEquiv [Nontrivial R] : M ≃* (const R M).points S :=
  MulEquiv.ofBijective (MonoidHom.mk' (constPt (R := R) S) (constPt_mul S))
    ⟨constPt_injective S, constPt_surjective S⟩

end Points

end FFGroupScheme

end PadicHodge
