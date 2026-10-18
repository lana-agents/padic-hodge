/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.TatePairing
import PadicHodge.GroupScheme.EtalePoints
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Perfectness of the Cartier pairing over a field

([Stix, §11.2.2], [Hong, Prop. 3.4.6] use that the levelwise Cartier pairings
`G_v(ℚ̄_p) × G_v^∨(ℚ̄_p) → μ_{p^v}` are perfect.) Standard arguments, written up here:

* `Cartier.transposeHom`: `f ↦ f^T = (F ↦ F ∘ f)` is a monoid homomorphism
  `End_R(A) → End_R(A^∨)` for the convolution products (`(f * g)^T = f^T * g^T` since the
  comultiplication of `A^∨` is the transpose of the multiplication of `A`); as `id_A^T = id_{A^∨}`,
  **`[n]_{G^∨} = ([n]_G)^∨`** and `G^∨` is killed by `n` if `G` is (`dual_univPt_pow_eq_one`).
* `FFGroupScheme.pairing_injective_right`: for `S` a field with `#G(S) = |G|`, a point
  `ψ ∈ G^∨(S)` is determined by `⟨·, ψ⟩`. With a basis `(e_i)` of `A`, `⟨φ, ψ⟩ = ∑ φ(e_i) ψ(e_i^*)`;
  the square matrix `(φ(e_i))_{φ, i}` has linearly independent rows (Dedekind's independence of
  characters, `linearIndependent_monoidHom`), so it is invertible.
* `card_monoidHom_le`: `#Hom(M, L) ≤ #M` for a finite monoid `M` and a field `L` (Dedekind).
* `pairingHom_bijective`, `pairingHom'_bijective`: if `#G(S) = #G^∨(S) = |G|`, both maps
  `G^∨(S) → Hom(G(S), S)` and `G(S) → Hom(G^∨(S), S)` are bijective.
* Over `ℚ_p`: the duals `G_v^∨` of the layers of a `p`-divisible group are killed by `p^v`, hence
  étale, `#G_v^∨(ℚ̄_p) = p^{hv}`, and the level-`v` Cartier pairing over `ℚ̄_p` is perfect
  (`PDivGroup.levelPairingHom_bijective`, `PDivGroup.levelPairingHom'_bijective`).
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u v

namespace Cartier

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [HopfAlgebra R A]

/-- The transpose `F ↦ F ∘ f` of an `R`-linear endomorphism of `A`. -/
def transposeLin (f : A →ₗ[R] A) : Dual R A →ₗ[R] Dual R A where
  toFun F := toConv (ofConv F ∘ₗ f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem transposeLin_apply (f : A →ₗ[R] A) (F : Dual R A) (a : A) :
    transposeLin f F a = F (f a) := rfl

theorem ev2_map_transposeLin (f g : A →ₗ[R] A) (x : Dual R A ⊗[R] Dual R A) :
    ev2 R A (TensorProduct.map (transposeLin f) (transposeLin g) x) =
      ev2 R A x ∘ₗ TensorProduct.map f g := by
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, LinearMap.add_comp]
  | tmul F H =>
    refine TensorProduct.ext' fun a b => ?_
    simp

variable [Module.Free R A] [Module.Finite R A]

theorem transposeLin_convMul (f g : WithConv (A →ₗ[R] A)) :
    toConv (transposeLin (ofConv (f * g))) =
      toConv (transposeLin (ofConv f)) * toConv (transposeLin (ofConv g)) := by
  apply WithConv.ofConv_injective
  refine LinearMap.ext fun F => WithConv.ofConv_injective (LinearMap.ext fun a => ?_)
  change ofConv F (LinearMap.mul' R A (TensorProduct.map (ofConv f) (ofConv g) (comul a))) =
    ofConv (LinearMap.mul' R (Dual R A) (TensorProduct.map (transposeLin (ofConv f))
      (transposeLin (ofConv g)) (comulD R A F))) a
  rw [mul'_apply_eq_ev2, ev2_map_transposeLin, LinearMap.comp_apply, ev2_comulD]
  rfl

theorem transposeLin_convOne :
    toConv (transposeLin (ofConv (1 : WithConv (A →ₗ[R] A)))) = 1 := by
  apply WithConv.ofConv_injective
  refine LinearMap.ext fun F => WithConv.ofConv_injective (LinearMap.ext fun a => ?_)
  rw [transposeLin_apply, LinearMap.convOne_apply, LinearMap.convOne_apply]
  change ofConv F (algebraMap R A (counit a)) =
    ofConv (algebraMap R (Dual R A) (ofConv F 1)) a
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Algebra.algebraMap_eq_smul_one]
  change counit a • ofConv F 1 = (ofConv F 1 • ofConv (1 : Dual R A)) a
  rw [LinearMap.smul_apply, LinearMap.convOne_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl

/-- The transpose as a monoid homomorphism `End_R(A) → End_R(A^∨)` (convolution products). -/
def transposeHom : WithConv (A →ₗ[R] A) →* WithConv (Dual R A →ₗ[R] Dual R A) where
  toFun f := toConv (transposeLin (ofConv f))
  map_one' := transposeLin_convOne
  map_mul' := transposeLin_convMul

end Cartier

namespace FFGroupScheme

variable {R : Type u} [CommRing R] (G : FFGroupScheme R)

/-- A point `x ∈ G(S)` is the image of the universal point. -/
theorem postComp_univPt {S : Type*} [CommRing S] [Algebra R S] (x : G.points S) :
    G.postComp (ofConv x) G.univPt = x := rfl

/-- If the universal point is killed by `n`, so is every point. -/
theorem pow_eq_one_of_univPt {n : ℕ} (h : G.univPt ^ n = 1) {S : Type*} [CommRing S]
    [Algebra R S] (x : G.points S) : x ^ n = 1 := by
  rw [← G.postComp_univPt x, ← map_pow, h, map_one]

/-- **`[n]_{G^∨} = ([n]_G)^∨`**: on universal points, the `n`-th power of the identity of `A^∨`
is the transpose of the `n`-th power of the identity of `A`. -/
theorem dual_univPt_pow (n : ℕ) :
    toConv (ofConv (G.dual.univPt ^ n)).toLinearMap =
      Cartier.transposeHom (toConv (ofConv (G.univPt ^ n)).toLinearMap) := by
  rw [AlgHom.toLinearMap_convPow, AlgHom.toLinearMap_convPow, map_pow]
  rfl

/-- **The Cartier dual of a group scheme killed by `n` is killed by `n`.** -/
theorem dual_univPt_pow_eq_one {n : ℕ} (h : G.univPt ^ n = 1) : G.dual.univPt ^ n = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  have := G.dual_univPt_pow n
  rw [h, AlgHom.toLinearMap_convOne, map_one] at this
  exact congrArg ofConv this

/-! ### Injectivity -/

section Field

variable {S : Type v} [Field S] [Algebra R S]

/-- The rows `(φ(e_i))_i` of the points of `G` are linearly independent (Dedekind). -/
theorem linearIndependent_rows {ι : Type*} [Finite ι] (b : Module.Basis ι R G.A) :
    LinearIndependent S (fun φ : G.points S => fun i => ofConv φ (b i)) := by
  classical
  have := Fintype.ofFinite ι
  rw [linearIndependent_iff']
  intro s g hg φ0 hφ0
  have hval : ∀ a : G.A, ∑ φ ∈ s, g φ * ofConv φ a = 0 := by
    intro a
    have hi : ∀ i, ∑ φ ∈ s, g φ * ofConv φ (b i) = 0 := fun i => by
      have := congrFun hg i
      simpa [Finset.sum_apply] using this
    conv_lhs => rw [← b.sum_repr a]
    simp only [map_sum, map_smul]
    simp_rw [Finset.mul_sum, Algebra.smul_def, ← mul_assoc, mul_comm (g _), mul_assoc]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hi]
  let χ : G.points S → (G.A →* S) := fun φ => ((ofConv φ : G.A →ₐ[R] S) : G.A →* S)
  have hχ : Function.Injective χ := by
    intro φ φ' h
    apply WithConv.ofConv_injective
    ext a
    exact DFunLike.congr_fun h a
  have hD := (linearIndependent_monoidHom G.A S).comp χ hχ
  rw [linearIndependent_iff'] at hD
  refine hD s g ?_ φ0 hφ0
  funext a
  simpa [Finset.sum_apply, χ] using hval a

theorem finite_points_of_free {ι : Type*} [Finite ι] (b : Module.Basis ι R G.A) :
    Finite (G.points S) :=
  Cardinal.lt_aleph0_iff_finite.mp (G.linearIndependent_rows (S := S) b).lt_aleph0_of_finite

variable [Nontrivial R]

/-- **Injectivity of the Cartier pairing in the second variable** over a field `S` with
`#G(S) = |G|`. -/
theorem pairing_injective_right (hcard : Nat.card (G.points S) = G.order)
    {ψ ψ' : G.dual.points S} (h : ∀ φ, G.pairing S φ ψ = G.pairing S φ ψ') : ψ = ψ' := by
  classical
  let b := Module.Free.chooseBasis R G.A
  have hfin := G.finite_points_of_free (S := S) b
  have : Fintype (G.points S) := Fintype.ofFinite _
  have hι : Fintype.card (G.points S) = Fintype.card (Module.Free.ChooseBasisIndex R G.A) := by
    rw [← Nat.card_eq_fintype_card, hcard, order, Module.finrank_eq_card_chooseBasisIndex]
  let e := Fintype.equivOfCardEq hι
  let M : Matrix (Module.Free.ChooseBasisIndex R G.A) (Module.Free.ChooseBasisIndex R G.A) S :=
    fun i j => ofConv (e.symm i) (b j)
  have hM : IsUnit M := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact (G.linearIndependent_rows (S := S) b).comp e.symm e.symm.injective
  let c : G.dual.points S → Module.Free.ChooseBasisIndex R G.A → S :=
    fun ψ j => ofConv ψ (toConv (b.coord j))
  have hc : ∀ ψ, M.mulVec (c ψ) = fun i => G.pairing S (e.symm i) ψ := by
    intro ψ
    funext i
    rw [pairing_eq_sum G S b]
    rfl
  have hcc : c ψ = c ψ' := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr hM
    rw [hc, hc]
    funext i
    exact h _
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  refine (G.dualBasis b).ext fun j => ?_
  rw [dualBasis_apply]
  exact congrFun hcc j

end Field

end FFGroupScheme

/-! ### Counting characters -/

theorem finite_monoidHom (M : Type*) [Monoid M] [Finite M] (L : Type*) [Field L] :
    Finite (M →* L) :=
  Cardinal.lt_aleph0_iff_finite.mp (linearIndependent_monoidHom M L).lt_aleph0_of_finite

/-- `#Hom(M, L) ≤ #M` for a finite monoid `M` and a field `L` (Dedekind). -/
theorem card_monoidHom_le (M : Type*) [Monoid M] [Finite M] (L : Type*) [Field L] :
    Nat.card (M →* L) ≤ Nat.card M := by
  have := finite_monoidHom M L
  cases nonempty_fintype (M →* L)
  cases nonempty_fintype M
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc _ ≤ Module.finrank L (M → L) := (linearIndependent_monoidHom M L).fintype_card_le_finrank
    _ = _ := Module.finrank_fintype_fun_eq_card L

namespace FFGroupScheme

variable {R : Type u} [CommRing R] [Nontrivial R] (G : FFGroupScheme R)
  {S : Type v} [Field S] [Algebra R S]

/-- `ψ ↦ ⟨·, ψ⟩`, `G^∨(S) → Hom(G(S), S)`. -/
def pairingHom : G.dual.points S →* (G.points S →* S) := (G.cartierPairingBase S).flip

/-- `φ ↦ ⟨φ, ·⟩`, `G(S) → Hom(G^∨(S), S)`. -/
def pairingHom' : G.points S →* (G.dual.points S →* S) := G.cartierPairingBase S

theorem pairingHom_injective (hcard : Nat.card (G.points S) = G.order) :
    Function.Injective (G.pairingHom (S := S)) :=
  fun _ _ h => G.pairing_injective_right hcard fun φ => DFunLike.congr_fun h φ

omit [Nontrivial R] in
theorem toDualDual_injective : Function.Injective (G.toDualDual S) := by
  intro φ φ' h
  apply WithConv.ofConv_injective
  ext a
  have := DFunLike.congr_fun (congrArg ofConv h) (G.dualDualIso a)
  simpa [toDualDual] using this

theorem pairingHom'_injective (hcard : Nat.card (G.dual.points S) = G.order) :
    Function.Injective (G.pairingHom' (S := S)) := by
  intro φ φ' h
  apply G.toDualDual_injective
  refine G.dual.pairing_injective_right (by rw [hcard, order_dual]) fun ψ => ?_
  rw [← pairing_symm, ← pairing_symm]
  exact DFunLike.congr_fun h ψ

/-- **Perfectness**: if `#G(S) = #G^∨(S) = |G|`, then `G^∨(S) ≅ Hom(G(S), S)`. -/
theorem pairingHom_bijective (hcard : Nat.card (G.points S) = G.order)
    (hcard' : Nat.card (G.dual.points S) = G.order) :
    Function.Bijective (G.pairingHom (S := S)) := by
  have hfin : Finite (G.points S) :=
    G.finite_points_of_free (S := S) (Module.Free.chooseBasis R G.A)
  have := finite_monoidHom (G.points S) S
  refine (G.pairingHom_injective hcard).bijective_of_nat_card_le ?_
  rw [hcard']
  exact (card_monoidHom_le _ S).trans hcard.le

/-- **Perfectness**: if `#G(S) = #G^∨(S) = |G|`, then `G(S) ≅ Hom(G^∨(S), S)`. -/
theorem pairingHom'_bijective (hcard : Nat.card (G.points S) = G.order)
    (hcard' : Nat.card (G.dual.points S) = G.order) :
    Function.Bijective (G.pairingHom' (S := S)) := by
  have hfin : Finite (G.dual.points S) :=
    G.dual.finite_points_of_free (S := S) (Module.Free.chooseBasis R G.dual.A)
  have := finite_monoidHom (G.dual.points S) S
  refine (G.pairingHom'_injective hcard').bijective_of_nat_card_le ?_
  rw [hcard]
  exact (card_monoidHom_le _ S).trans hcard'.le

end FFGroupScheme

/-! ### Over `ℚ_p` -/

namespace FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime]

/-- An étale group scheme over a field `K ⊆ ℚ̄_p` (e.g. `ℚ_p`) has `|G|` points over `ℚ̄_p`. -/
theorem card_points_padicAlgCl_of_isEtale {K : Type} [Field K] [Algebra K (PadicAlgCl p)]
    (G : FFGroupScheme K) (hG : G.IsEtale) :
    Nat.card (G.points (PadicAlgCl p)) = G.order := by
  have : Algebra.Etale K G.A := hG
  have hGS : (G.baseChange (PadicAlgCl p)).IsEtale :=
    (inferInstance : Algebra.Etale (PadicAlgCl p) (PadicAlgCl p ⊗[K] G.A))
  rw [← Nat.card_congr (G.baseChangePointsEquiv (S := PadicAlgCl p) (PadicAlgCl p)).toEquiv,
    FFGroupScheme.card_points_of_isEtale _ hGS, FFGroupScheme.order_baseChange]

end FFGroupScheme

namespace PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [CharZero K] [Algebra K (PadicAlgCl p)]
  (G : PDivGroup K p)

omit hp in
theorem isUnit_p [hp : Fact p.Prime] : IsUnit (p : ℚ_[p]) := by
  rw [isUnit_iff_ne_zero]
  exact_mod_cast hp.out.ne_zero

omit [Algebra K (PadicAlgCl p)] in
/-- `p` is a unit in a field of characteristic `0`. -/
theorem isUnit_p_of_charZero : IsUnit (p : K) := by
  rw [isUnit_iff_ne_zero]
  exact_mod_cast hp.out.ne_zero

omit hp in
/-- The Cartier dual `G_v^∨` is killed by `p^v`. -/
theorem dual_univPt_pow_eq_one {R : Type u} [CommRing R] (H : PDivGroup R p) (v : ℕ) :
    (H.G v).dual.univPt ^ (p ^ v) = 1 :=
  (H.G v).dual_univPt_pow_eq_one (H.pow_eq_one v _ _)

omit [Algebra K (PadicAlgCl p)] in
/-- `G_v^∨` is étale over `K` (e.g. `ℚ_p`). -/
theorem isEtale_dual (v : ℕ) : (G.G v).dual.IsEtale :=
  (G.G v).dual.isEtale_of_univPt_pow_eq_one (n := p ^ v)
    (by rw [Nat.cast_pow]; exact (isUnit_p_of_charZero (p := p) (K := K)).pow v)
    (G.dual_univPt_pow_eq_one v)

/-- **`#G_v^∨(ℚ̄_p) = p^{hv}`.** -/
theorem card_dual_points_padicAlgCl (v : ℕ) :
    Nat.card ((G.G v).dual.points (PadicAlgCl p)) = p ^ (G.height * v) := by
  rw [FFGroupScheme.card_points_padicAlgCl_of_isEtale _ (G.isEtale_dual v),
    FFGroupScheme.order_dual,
    G.order_eq v]

theorem card_points_eq_order (v : ℕ) :
    Nat.card ((G.G v).points (PadicAlgCl p)) = (G.G v).order := by
  rw [G.card_points_padicAlgCl, G.order_eq]

theorem card_dual_points_eq_order (v : ℕ) :
    Nat.card ((G.G v).dual.points (PadicAlgCl p)) = (G.G v).order := by
  rw [G.card_dual_points_padicAlgCl, G.order_eq]

/-- **The level-`v` Cartier pairing over `ℚ̄_p` is perfect**:
`G_v^∨(ℚ̄_p) ≅ Hom(G_v(ℚ̄_p), ℚ̄_p)`. -/
theorem levelPairingHom_bijective (v : ℕ) :
    Function.Bijective ((G.G v).pairingHom (S := PadicAlgCl p)) :=
  (G.G v).pairingHom_bijective (G.card_points_eq_order v) (G.card_dual_points_eq_order v)

/-- **The level-`v` Cartier pairing over `ℚ̄_p` is perfect**:
`G_v(ℚ̄_p) ≅ Hom(G_v^∨(ℚ̄_p), ℚ̄_p)`. -/
theorem levelPairingHom'_bijective (v : ℕ) :
    Function.Bijective ((G.G v).pairingHom' (S := PadicAlgCl p)) :=
  (G.G v).pairingHom'_bijective (G.card_points_eq_order v) (G.card_dual_points_eq_order v)

end PDivGroup

end PadicHodge
