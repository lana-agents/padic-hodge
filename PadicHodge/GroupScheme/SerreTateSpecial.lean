/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.SpecialFibre
import PadicHodge.FormalGroup.DerivStable
import PadicHodge.FormalGroup.AdicEval

/-!
# Coordinates on a connected `p`-divisible group over a field of characteristic `p`

Let `k` be a perfect field of characteristic `p` (e.g. a finite field), and `H = (G_v, i_v)` a
`p`-divisible group over `k` with all layers `G_v = Spec A_v` connected. We prove the special
fibre case of [Hong, Prop. 2.2.13] (`lim_v A_v ≅ k[[t_1, …, t_d]]`) in the following concrete
form, by our own argument (not Hong's order-counting induction via the Frobenius kernels
`H_v = ker φ^v`):

**`PDivGroup.exists_coords`**: there are `d` and surjective `k`-algebra maps
`ρ_v : k[[t_1, …, t_d]] ↠ A_v`, compatible with the transition maps (`i_v^* ∘ ρ_{v+1} = ρ_v`),
with `ker ρ_v ⊆ (t_j^{p^w})_j` for all `w ≤ v`; in particular `⋂_v ker ρ_v = 0`, i.e.
`k[[t]] → lim_v A_v` is injective.

Construction and proof:

* `d = dim_k 𝔪_1/𝔪_1²` (`cotDim`), `y_i ∈ 𝔪_1` lifting a basis (`cotLift`), point derivations
  `ℓ_j : A_1 → k` with `ℓ_j(y_i) = δ_{ij}` (`pointDer`).
* Compatible lifts `y_i^{(v)} ∈ 𝔪_v` (`PDivGroup.coord`); they generate `𝔪_v`, since the cotangent
  spaces of all `A_v` agree with that of `A_1` (`PDivGroup.counitKer_le_of_inclOne`, via the
  Frobenius kernel) and by Nakayama. `ρ_v` is evaluation at `y^{(v)}` (`AdicEval.eval`; `𝔪_v` is
  nilpotent), surjective by Nakayama (`PDivGroup.rho_surjective`).
* Invariant derivations `D_j = (id ⊗ ℓ_j) ∘ Δ` of `A_v` (`invDer`), with `ε ∘ D_j = ℓ_j`; so
  `D_j(y_i^{(v)}) = ρ_v(c_{ij})` with `c_{ij}(0) = δ_{ij}`, and `ker ρ_v` is `∂`-stable for `v ≥ 1`
  (`MvPowerSeries.derivStable_ker`).
* `h^p ∈ ker ρ_{v+1} ⇒ h ∈ ker ρ_v` (`PDivGroup.incl_eq_zero_of_pow_eq_zero`: `[p]^*` kills
  `p`-nilpotents and `quot_v^*` is injective).
* The Frobenius decomposition argument `MvPowerSeries.le_spanXPow_of_derivStable` (here in the
  variant `le_spanXPow_of_derivStable_succ`, needing `∂`-stability only from level `1` on) gives
  `ker ρ_v ⊆ (t_j^{p^w})_j`.

What is not done here: surjectivity of `k[[t]] → lim_v A_v` (closedness of the image), and the
comparison with Hong's statement over a general base `R`.
-/

noncomputable section

open Coalgebra TensorProduct Module MvPowerSeries IsLocalRing

namespace PadicHodge

universe u

/-! ### The cotangent space at the origin and point derivations -/

section Cotangent

variable (k : Type*) [Field k] (A : Type*) [CommRing A] [Bialgebra k A] [Module.Finite k A]

/-- `a ↦ (a - ε(a)) mod 𝔪²`, `𝔪 = ker ε`. -/
def cotProj : A →ₗ[k] A ⧸ counitKer k A ^ 2 :=
  (Ideal.Quotient.mkₐ k (counitKer k A ^ 2)).toLinearMap ∘ₗ
    (LinearMap.id - Algebra.linearMap k A ∘ₗ (counit : A →ₗ[k] k))

/-- The cotangent space `𝔪/𝔪²`, as the range of `cotProj`. -/
abbrev cotSpace : Submodule k (A ⧸ counitKer k A ^ 2) := LinearMap.range (cotProj k A)

/-- `d = dim_k 𝔪/𝔪²`. -/
def cotDim : ℕ := finrank k (cotSpace k A)

/-- A basis of the cotangent space. -/
def cotBasis : Basis (Fin (cotDim k A)) k (cotSpace k A) := Module.finBasis k _

/-- Lifts `y_i ∈ 𝔪` of the basis `cotBasis` of `𝔪/𝔪²`. -/
def cotLift (i : Fin (cotDim k A)) : A :=
  (LinearMap.mem_range.mp (cotBasis k A i).2).choose -
    algebraMap k A (counit (R := k) (LinearMap.mem_range.mp (cotBasis k A i).2).choose)

/-- The point derivations `ℓ_j : A → k` dual to the `y_i`. -/
def pointDer (j : Fin (cotDim k A)) : A →ₗ[k] k :=
  (cotBasis k A).coord j ∘ₗ (cotProj k A).rangeRestrict

variable {k A}

omit [Module.Finite k A] in
theorem cotProj_apply (a : A) :
    cotProj k A a = Ideal.Quotient.mk _ (a - algebraMap k A (counit (R := k) a)) := rfl

omit [Module.Finite k A] in
theorem cotProj_of_mem {m : A} (hm : m ∈ counitKer k A) :
    cotProj k A m = Ideal.Quotient.mk _ m := by
  rw [cotProj_apply, mem_counitKer.mp hm, map_zero, sub_zero]

omit [Module.Finite k A] in
theorem counit_mul' (a b : A) :
    counit (R := k) (a * b) = counit (R := k) a * counit (R := k) b := by
  rw [← Bialgebra.counitAlgHom_apply, map_mul, Bialgebra.counitAlgHom_apply,
    Bialgebra.counitAlgHom_apply]

omit [Module.Finite k A] in
theorem cotProj_mul (a b : A) :
    cotProj k A (a * b) =
      counit (R := k) a • cotProj k A b + counit (R := k) b • cotProj k A a := by
  rw [cotProj_apply, cotProj_apply, cotProj_apply, Algebra.smul_def, Algebra.smul_def,
    ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← map_mul, ← map_mul,
    ← map_add, Ideal.Quotient.eq, counit_mul', map_mul]
  have e : a * b - algebraMap k A (counit (R := k) a) * algebraMap k A (counit (R := k) b) -
      (algebraMap k A (counit (R := k) a) * (b - algebraMap k A (counit (R := k) b)) +
        algebraMap k A (counit (R := k) b) * (a - algebraMap k A (counit (R := k) a))) =
      (a - algebraMap k A (counit (R := k) a)) * (b - algebraMap k A (counit (R := k) b)) := by
    ring
  rw [e, sq]
  exact Ideal.mul_mem_mul (mem_counitKer.mpr (counit_sub_algebraMap a))
    (mem_counitKer.mpr (counit_sub_algebraMap b))

theorem counit_cotLift (i : Fin (cotDim k A)) : counit (R := k) (cotLift k A i) = 0 :=
  counit_sub_algebraMap _

theorem cotProj_cotLift (i : Fin (cotDim k A)) :
    cotProj k A (cotLift k A i) = (cotBasis k A i : A ⧸ counitKer k A ^ 2) := by
  rw [cotProj_of_mem (mem_counitKer.mpr (counit_cotLift i)), cotLift, ← cotProj_apply]
  exact (LinearMap.mem_range.mp (cotBasis k A i).2).choose_spec

theorem pointDer_mul (j : Fin (cotDim k A)) (a b : A) :
    pointDer k A j (a * b) =
      counit (R := k) a * pointDer k A j b + counit (R := k) b * pointDer k A j a := by
  have h : (cotProj k A).rangeRestrict (a * b) = counit (R := k) a • (cotProj k A).rangeRestrict b +
      counit (R := k) b • (cotProj k A).rangeRestrict a :=
    Subtype.ext (by simp [cotProj_mul])
  simp only [pointDer, LinearMap.comp_apply, h, map_add, map_smul, smul_eq_mul]

theorem pointDer_cotLift (i j : Fin (cotDim k A)) :
    pointDer k A j (cotLift k A i) = if i = j then 1 else 0 := by
  have h : (cotProj k A).rangeRestrict (cotLift k A i) = cotBasis k A i :=
    Subtype.ext (cotProj_cotLift i)
  rw [pointDer, LinearMap.comp_apply, h, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_apply]

/-- The `y_i` generate `𝔪` modulo `𝔪²`. -/
theorem counitKer_le_span_cotLift :
    counitKer k A ≤ Ideal.span (Set.range (cotLift k A)) ⊔ counitKer k A ^ 2 := by
  intro m hm
  set c := (cotBasis k A).repr ((cotProj k A).rangeRestrict m)
  set s := ∑ i, c i • cotLift k A i
  have hs : s ∈ Ideal.span (Set.range (cotLift k A)) :=
    Ideal.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ (c i) (Ideal.subset_span ⟨i, rfl⟩)
  have hms : m - s ∈ counitKer k A := by
    rw [mem_counitKer, map_sub, map_sum, mem_counitKer.mp hm, zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun i _ => by rw [map_smul, counit_cotLift, smul_zero]
  have hm2 : m - s ∈ counitKer k A ^ 2 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← cotProj_of_mem hms, map_sub]
    have e := congrArg Subtype.val ((cotBasis k A).sum_repr ((cotProj k A).rangeRestrict m))
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.codRestrict_apply] at e
    rw [sub_eq_zero, ← e]
    simp only [s, map_sum, map_smul, cotProj_cotLift, c]
  have := Submodule.add_mem_sup hs hm2
  rwa [add_sub_cancel] at this

omit [Module.Finite k A] in
theorem finrank_quot_counitKer : finrank k (A ⧸ counitKer k A) = 1 := by
  have hsurj : Function.Surjective (Bialgebra.counitAlgHom k A) := fun c =>
    ⟨algebraMap k A c, by simp⟩
  rw [(Ideal.quotientKerAlgEquivOfSurjective hsurj).toLinearEquiv.finrank_eq, finrank_self]

end Cotangent

/-! ### Invariant derivations -/

section InvDer

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Bialgebra k B]

theorem rid_lTensor_mul (ℓ : B →ₗ[k] k)
    (hℓ : ∀ a b, ℓ (a * b) = counit (R := k) a * ℓ b + counit (R := k) b * ℓ a)
    (x y : B ⊗[k] B) :
    TensorProduct.rid k B (ℓ.lTensor B (x * y)) =
      TensorProduct.rid k B ((counit : B →ₗ[k] k).lTensor B x) *
          TensorProduct.rid k B (ℓ.lTensor B y) +
        TensorProduct.rid k B ((counit : B →ₗ[k] k).lTensor B y) *
          TensorProduct.rid k B (ℓ.lTensor B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, hℓ, Algebra.smul_def, map_add, map_mul]
      ring
    | add y y' hy hy' => simp only [mul_add, map_add, hy, hy']; ring
  | add x x' hx hx' => simp only [add_mul, map_add, hx, hx']; ring

/-- The **invariant derivation** `D = (id ⊗ ℓ) ∘ Δ` attached to a point derivation `ℓ` at the
origin (`ℓ(ab) = ε(a)ℓ(b) + ε(b)ℓ(a)`). -/
def invDer (ℓ : B →ₗ[k] k)
    (hℓ : ∀ a b, ℓ (a * b) = counit (R := k) a * ℓ b + counit (R := k) b * ℓ a) :
    Derivation k B B :=
  Derivation.mk' ((TensorProduct.rid k B).toLinearMap ∘ₗ ℓ.lTensor B ∘ₗ comul) fun a b => by
    have hΔ : comul (R := k) (a * b) = comul a * comul b := by
      exact (Bialgebra.comulAlgHom k B).map_mul a b
    have hE : ∀ c : B, TensorProduct.rid k B ((counit : B →ₗ[k] k).lTensor B (comul c)) = c :=
      fun c => by rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [hΔ, rid_lTensor_mul ℓ hℓ, hE, hE, smul_eq_mul, smul_eq_mul]

theorem invDer_apply (ℓ : B →ₗ[k] k)
    (hℓ : ∀ a b, ℓ (a * b) = counit (R := k) a * ℓ b + counit (R := k) b * ℓ a) (b : B) :
    invDer ℓ hℓ b = TensorProduct.rid k B (ℓ.lTensor B (comul b)) := rfl

/-- `ε ∘ D = ℓ`. -/
theorem counit_invDer (ℓ : B →ₗ[k] k)
    (hℓ : ∀ a b, ℓ (a * b) = counit (R := k) a * ℓ b + counit (R := k) b * ℓ a) (b : B) :
    counit (R := k) (invDer ℓ hℓ b) = ℓ b := by
  have key : ∀ x : B ⊗[k] B, counit (R := k) (TensorProduct.rid k B (ℓ.lTensor B x)) =
      ℓ (TensorProduct.lid k B ((counit : B →ₗ[k] k).rTensor B x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.rid_tmul,
        TensorProduct.lid_tmul, map_smul, smul_eq_mul]
      ring
    | add x x' hx hx' => simp only [map_add, hx, hx']
  rw [invDer_apply, key, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

end InvDer

/-! ### Local rings finite over a field -/

section Local

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Bialgebra k A] [IsLocalRing A]

theorem counitKer_le_maximalIdeal : counitKer k A ≤ maximalIdeal A := by
  intro a ha hu
  have h := hu.map (Bialgebra.counitAlgHom k A)
  rw [RingHom.mem_ker.mp ha] at h
  exact not_isUnit_zero h

end Local

theorem exists_maximalIdeal_pow_eq_bot (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra k A] [Module.Finite k A] : ∃ N, maximalIdeal A ^ N = ⊥ := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  exact ⟨n, hn⟩

theorem isAdicComplete_maximalIdeal (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra k A] [Module.Finite k A] : IsAdicComplete (maximalIdeal A) A := by
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_eq_bot k A
  exact AdicEval.isAdicComplete_of_le (𝔟 := ⊥) bot_le hN.le

/-! ### Power series -/

theorem mem_span_X_of_constantCoeff {σ R : Type*} [CommRing R] [Finite σ]
    {f : MvPowerSeries σ R} (h : constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  have := AdicEval.mem_pow_span_X 1 f fun m hm => by
    have hm0 : m = 0 := by rwa [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hm
    subst hm0
    rwa [coeff_zero_eq_constantCoeff_apply]
  rwa [pow_one] at this

section Main

variable {σ k : Type*} [Field k] [Finite σ] (p : ℕ) [CharP k p] [Fact p.Prime]

/-- Variant of `MvPowerSeries.le_spanXPow_of_derivStable` needing `∂`-stability of `𝔞_v` only
for `v ≥ 1` (the ideal `𝔞_0` is only used through `hfrob 0`). -/
theorem le_spanXPow_of_derivStable_succ [PerfectRing k p]
    (𝔞 : ℕ → Ideal (MvPowerSeries σ k)) (hstab : ∀ v, DerivStable (𝔞 (v + 1)))
    (hX : ∀ v, 𝔞 v ≤ Ideal.span (Set.range X)) (hfrob : ∀ v h, h ^ p ∈ 𝔞 (v + 1) → h ∈ 𝔞 v) :
    ∀ w v, w ≤ v → 𝔞 v ≤ spanXPow σ k (p ^ w) := by
  classical
  have := Fintype.ofFinite σ
  intro w
  induction w with
  | zero =>
    intro v _
    change 𝔞 v ≤ Ideal.span (Set.range fun j => (X j : MvPowerSeries σ k) ^ p ^ 0)
    simpa using hX v
  | succ w ih =>
    intro v hv f hf
    obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
    have hf' : ∑ m : σ → Fin p, map (frobInv (k := k) p) (frobCoeff p f (boxExp m)) ^ p *
        monomial (boxExp m) 1 ∈ 𝔞 (u + 1) := by
      rw [← frob_decomp p f]
      exact hf
    rw [frob_decomp p f]
    refine Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ ?_
    rw [pow_succ']
    exact pow_mem_spanXPow_mul p (ih u (by omega) (hfrob u _
      (pow_mem_of_sum_mem p (hstab u)
        (fun m => map (frobInv (k := k) p) (frobCoeff p f (boxExp m))) hf' m)))

omit [Finite σ] [CharP k p] in
theorem iInf_eq_bot_of_le_spanXPow (𝔞 : ℕ → Ideal (MvPowerSeries σ k))
    (h : ∀ w v, w ≤ v → 𝔞 v ≤ spanXPow σ k (p ^ w)) : ⨅ v, 𝔞 v = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  ext n
  rw [map_zero]
  have hmem := h n.degree n.degree le_rfl (Submodule.mem_iInf _ |>.mp hf n.degree)
  exact coeff_eq_zero_of_mem_spanXPow hmem fun j =>
    lt_of_le_of_lt (Finsupp.le_degree j n) (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)

end Main

/-! ### Coordinates on a connected `p`-divisible group -/

namespace PDivGroup

open FFGroupScheme

variable {k : Type u} [Field k] {p : ℕ} (H : PDivGroup k p)

/-- Compatible lifts `y^{(w+1)}_i ∈ A_{w+1}` of the `y_i = cotLift ∈ A_1`. -/
def coordAux : (w : ℕ) → Fin (cotDim k (H.G 1).A) → (H.G (w + 1)).A
  | 0 => cotLift k (H.G 1).A
  | w + 1 => fun i => Function.surjInv (H.incl_surjective (w + 1)) (coordAux w i)

theorem inclOne_coordAux (w : ℕ) (i : Fin (cotDim k (H.G 1).A)) :
    H.inclOne w (H.coordAux w i) = cotLift k (H.G 1).A i := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [inclOne_succ_apply]
    change H.inclOne w (H.incl (w + 1) (Function.surjInv _ (H.coordAux w i))) = _
    rw [Function.surjInv_eq (H.incl_surjective (w + 1)), ih]

/-- **The coordinates** `y^{(v)}_i ∈ 𝔪_v`, compatible with the transition maps. -/
def coord : (v : ℕ) → Fin (cotDim k (H.G 1).A) → (H.G v).A
  | 0 => fun i => H.incl 0 (H.coordAux 0 i)
  | w + 1 => H.coordAux w

theorem incl_coord (v : ℕ) (i : Fin (cotDim k (H.G 1).A)) :
    H.incl v (H.coord (v + 1) i) = H.coord v i := by
  cases v with
  | zero => rfl
  | succ w => exact Function.surjInv_eq _ _

theorem counit_coord (v : ℕ) (i : Fin (cotDim k (H.G 1).A)) :
    counit (R := k) (H.coord v i) = 0 := by
  cases v with
  | zero =>
    change counit (R := k) (H.incl 0 (H.coordAux 0 i)) = 0
    rw [CoalgHomClass.counit_comp_apply]
    exact counit_cotLift i
  | succ w =>
    change counit (R := k) (H.coordAux w i) = 0
    rw [← H.counit_inclOne w, inclOne_coordAux]
    exact counit_cotLift i

/-- The point derivation `ℓ_j ∘ (A_{w+1} ↠ A_1)` of `A_{w+1}`. -/
def derL (w : ℕ) (j : Fin (cotDim k (H.G 1).A)) : (H.G (w + 1)).A →ₗ[k] k :=
  pointDer k (H.G 1).A j ∘ₗ (H.inclOne w).toLinearMap

theorem derL_mul (w : ℕ) (j : Fin (cotDim k (H.G 1).A)) (a b : (H.G (w + 1)).A) :
    H.derL w j (a * b) =
      counit (R := k) a * H.derL w j b + counit (R := k) b * H.derL w j a := by
  simp only [derL, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, pointDer_mul,
    counit_inclOne]

/-- The invariant derivations `D_j` of `A_{w+1}`. -/
def der (w : ℕ) (j : Fin (cotDim k (H.G 1).A)) : Derivation k (H.G (w + 1)).A (H.G (w + 1)).A :=
  invDer (H.derL w j) (H.derL_mul w j)

theorem counit_der_coord (w : ℕ) (i j : Fin (cotDim k (H.G 1).A)) :
    counit (R := k) (H.der w j (H.coord (w + 1) i)) = if i = j then 1 else 0 := by
  rw [der, counit_invDer, derL, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  change pointDer k (H.G 1).A j (H.inclOne w (H.coordAux w i)) = _
  rw [inclOne_coordAux, pointDer_cotLift]

variable (hconn : ∀ v, (H.G v).IsConnected)
include hconn

/-- **`ρ_v : k[[t_1, …, t_d]] → A_v`**, `t_i ↦ y^{(v)}_i`. -/
def rho (v : ℕ) : MvPowerSeries (Fin (cotDim k (H.G 1).A)) k →ₐ[k] (H.G v).A :=
  letI : IsLocalRing (H.G v).A := hconn v
  letI := isAdicComplete_maximalIdeal k (H.G v).A
  AdicEval.eval (maximalIdeal (H.G v).A) (H.coord v) fun i =>
    counitKer_le_maximalIdeal (k := k) (mem_counitKer.mpr (H.counit_coord v i))

theorem rho_X (v : ℕ) (i : Fin (cotDim k (H.G 1).A)) : H.rho hconn v (X i) = H.coord v i := by
  letI : IsLocalRing (H.G v).A := hconn v
  letI := isAdicComplete_maximalIdeal k (H.G v).A
  exact AdicEval.eval_X _ _ _ i

/-- `i_v^* ∘ ρ_{v+1} = ρ_v`. -/
theorem incl_comp_rho (v : ℕ) :
    (H.incl v : (H.G (v + 1)).A →ₐ[k] (H.G v).A).comp (H.rho hconn (v + 1)) = H.rho hconn v := by
  letI : IsLocalRing (H.G v).A := hconn v
  letI := isAdicComplete_maximalIdeal k (H.G v).A
  exact AdicEval.eval_unique _ _ _ _ fun i => by
    rw [AlgHom.comp_apply, rho_X]
    exact H.incl_coord v i

theorem counit_rho (v : ℕ) (f : MvPowerSeries (Fin (cotDim k (H.G 1).A)) k) :
    counit (R := k) (H.rho hconn v f) = constantCoeff f := by
  set c := constantCoeff f
  have hg : f - algebraMap k _ c ∈ Ideal.span (Set.range X) := by
    refine mem_span_X_of_constantCoeff ?_
    rw [map_sub, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      constantCoeff_C, sub_self]
  have hle : Ideal.span (Set.range (X : _ → MvPowerSeries (Fin (cotDim k (H.G 1).A)) k)) ≤
      (counitKer k (H.G v).A).comap (H.rho hconn v) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_counitKer.mpr (by rw [rho_X]; exact H.counit_coord v i)
  have h := mem_counitKer.mp (hle hg)
  rw [map_sub, map_sub, AlgHom.commutes, sub_eq_zero] at h
  rw [h, Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one]

theorem ker_rho_le_span_X (v : ℕ) :
    RingHom.ker (H.rho hconn v) ≤ Ideal.span (Set.range X) := fun f hf =>
  mem_span_X_of_constantCoeff (by rw [← H.counit_rho hconn v f, RingHom.mem_ker.mp hf, map_zero])

theorem exists_pow_le_ker_rho (v : ℕ) :
    ∃ N, Ideal.span (Set.range X) ^ N ≤ RingHom.ker (H.rho hconn v) := by
  letI : IsLocalRing (H.G v).A := hconn v
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_eq_bot k (H.G v).A
  refine ⟨N, ?_⟩
  have h1 : Ideal.span (Set.range (X : _ → MvPowerSeries (Fin (cotDim k (H.G 1).A)) k)) ≤
      (maximalIdeal (H.G v).A).comap (H.rho hconn v) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change H.rho hconn v (X i) ∈ maximalIdeal (H.G v).A
    rw [rho_X]
    exact counitKer_le_maximalIdeal (k := k) (mem_counitKer.mpr (H.counit_coord v i))
  have := (Ideal.pow_right_mono h1 N).trans (Ideal.le_comap_pow _ N)
  rwa [hN] at this

theorem rho_surjective_succ [Fact p.Prime] [CharP k p] [PerfectRing k p] (w : ℕ) :
    Function.Surjective (H.rho hconn (w + 1)) := by
  letI : IsLocalRing (H.G (w + 1)).A := hconn (w + 1)
  set A := (H.G (w + 1)).A
  have h1 : counitKer k (H.G 1).A ≤ Ideal.span (Set.range (H.inclOne w ∘ H.coordAux w)) ⊔
      counitKer k (H.G 1).A ^ 2 := by
    have : H.inclOne w ∘ H.coordAux w = cotLift k (H.G 1).A := funext (H.inclOne_coordAux w)
    rw [this]
    exact counitKer_le_span_cotLift
  have h2 := H.counitKer_le_of_inclOne w (H.coordAux w) h1
  have hspan : counitKer k A ≤ Ideal.span (Set.range (H.coordAux w)) := by
    haveI : IsNoetherianRing A := isNoetherian_of_tower k inferInstance
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian _)
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm) ?_
    refine h2.trans (sup_le_sup_left ?_ _)
    rw [sq, smul_eq_mul]
    exact Ideal.mul_mono_left counitKer_le_maximalIdeal
  have heq : Ideal.span (H.rho hconn (w + 1) '' Set.range X) = counitKer k A := by
    have hr : H.rho hconn (w + 1) '' Set.range X = Set.range (H.coordAux w) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => H.rho_X hconn (w + 1) i)
    rw [hr]
    refine le_antisymm (Ideal.span_le.mpr ?_) hspan
    rintro _ ⟨i, rfl⟩
    exact mem_counitKer.mpr (H.counit_coord (w + 1) i)
  have hfin := finrank_le_mul_finrank_range_of_algHom (H.rho hconn (w + 1)) (Set.range X)
    fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      rw [rho_X]
      exact counitKer_le_maximalIdeal (k := k) (mem_counitKer.mpr (H.counit_coord (w + 1) i))
  rw [heq, finrank_quot_counitKer, one_mul] at hfin
  have htop : LinearMap.range (H.rho hconn (w + 1)).toLinearMap = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hfin)
  exact LinearMap.range_eq_top.mp htop

/-- **`ρ_v` is surjective.** -/
theorem rho_surjective [Fact p.Prime] [CharP k p] [PerfectRing k p] (v : ℕ) :
    Function.Surjective (H.rho hconn v) := by
  cases v with
  | zero =>
    rw [← H.incl_comp_rho hconn 0, AlgHom.coe_comp]
    exact (H.incl_surjective 0).comp (H.rho_surjective_succ hconn 0)
  | succ w => exact H.rho_surjective_succ hconn w

/-- **`ker ρ_{w+1}` is `∂`-stable.** -/
theorem derivStable_ker_rho [Fact p.Prime] [CharP k p] [PerfectRing k p] (w : ℕ) :
    DerivStable (RingHom.ker (H.rho hconn (w + 1))) := by
  classical
  obtain ⟨N, hN⟩ := H.exists_pow_le_ker_rho hconn (w + 1)
  have hs := H.rho_surjective hconn (w + 1)
  let c : Matrix (Fin (cotDim k (H.G 1).A)) (Fin (cotDim k (H.G 1).A))
      (MvPowerSeries (Fin (cotDim k (H.G 1).A)) k) := fun i j =>
    Function.surjInv hs (H.der w j (H.coord (w + 1) i))
  have hcc : ∀ i j, constantCoeff (c i j) = if i = j then 1 else 0 := by
    intro i j
    change constantCoeff (Function.surjInv hs (H.der w j (H.coord (w + 1) i))) = _
    rw [← H.counit_rho hconn (w + 1), Function.surjInv_eq hs, counit_der_coord]
  have hc : IsUnit c.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det]
    have : (constantCoeff (σ := Fin (cotDim k (H.G 1).A)) (R := k)).mapMatrix c = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hcc, Matrix.one_apply]
    rw [this, Matrix.det_one]
    exact isUnit_one
  refine derivStable_ker (H.rho hconn (w + 1)) hN (fun j => H.der w j) c hc fun i j => ?_
  rw [rho_X]
  exact (Function.surjInv_eq hs _).symm

/-- `h^p ∈ ker ρ_{v+1} ⇒ h ∈ ker ρ_v`. -/
theorem rho_frob [Fact p.Prime] [CharP k p] [PerfectRing k p] (v : ℕ)
    (h : MvPowerSeries (Fin (cotDim k (H.G 1).A)) k)
    (hh : h ^ p ∈ RingHom.ker (H.rho hconn (v + 1))) : h ∈ RingHom.ker (H.rho hconn v) := by
  rw [RingHom.mem_ker, map_pow] at hh
  rw [RingHom.mem_ker, ← H.incl_comp_rho hconn v, AlgHom.comp_apply]
  exact H.incl_eq_zero_of_pow_eq_zero v (hconn (v + 1)) hh

/-- **`ker ρ_v ⊆ (t_j^{p^w})_j` for `w ≤ v`.** -/
theorem ker_rho_le_spanXPow [Fact p.Prime] [CharP k p] [PerfectRing k p] :
    ∀ w v, w ≤ v → RingHom.ker (H.rho hconn v) ≤
      spanXPow (Fin (cotDim k (H.G 1).A)) k (p ^ w) :=
  le_spanXPow_of_derivStable_succ p (fun v => RingHom.ker (H.rho hconn v))
    (H.derivStable_ker_rho hconn) (H.ker_rho_le_span_X hconn) (H.rho_frob hconn)

/-- **`⋂_v ker ρ_v = 0`**: `k[[t_1, …, t_d]] → lim_v A_v` is injective. -/
theorem iInf_ker_rho [Fact p.Prime] [CharP k p] [PerfectRing k p] :
    ⨅ v, RingHom.ker (H.rho hconn v) = ⊥ :=
  iInf_eq_bot_of_le_spanXPow p _ (H.ker_rho_le_spanXPow hconn)

/-- **Coordinates on a connected `p`-divisible group over `k`** ([Hong, Prop. 2.2.13] for the
special fibre, in concrete form; our proof): there are `d` and surjective `k`-algebra maps
`ρ_v : k[[t_1, …, t_d]] ↠ A_v`, compatible with the transition maps `i_v^* : A_{v+1} ↠ A_v`, with
`ker ρ_v ⊆ (t_j^{p^w})_j` for `w ≤ v`; in particular `⋂_v ker ρ_v = 0`. -/
theorem exists_coords [Fact p.Prime] [CharP k p] [PerfectRing k p] :
    ∃ (d : ℕ) (ρ : ∀ v, MvPowerSeries (Fin d) k →ₐ[k] (H.G v).A),
      (∀ v, Function.Surjective (ρ v)) ∧
      (∀ v, (H.incl v : (H.G (v + 1)).A →ₐ[k] (H.G v).A).comp (ρ (v + 1)) = ρ v) ∧
      (∀ w v, w ≤ v → RingHom.ker (ρ v) ≤ spanXPow (Fin d) k (p ^ w)) ∧
      ⨅ v, RingHom.ker (ρ v) = ⊥ :=
  ⟨_, H.rho hconn, H.rho_surjective hconn, H.incl_comp_rho hconn,
    H.ker_rho_le_spanXPow hconn, H.iInf_ker_rho hconn⟩

end PDivGroup

end PadicHodge
