/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.FrobKernel
import PadicHodge.FormalGroup.DualPDivFGL
import PadicHodge.GroupScheme.Frobenius
import PadicHodge.GroupScheme.ConnectedPDiv
import PadicHodge.GroupScheme.DualBaseChange

/-!
# `h ≤ d + d^∨` for `F[p^∞]` over `ℤ_p`

Let `P` be a `p`-divisible formal group law of dimension `d` and height `h` over `ℤ_p`,
`G = F[p^∞]` (`PDivFGL.pdivGroup`) and `G^∨` its Cartier dual (`PDivFGL.dualPDiv`). By
Serre–Tate, the connected part `(G^∨)⁰` is `F'[p^∞]` for a `p`-divisible formal group law `P'`
of some dimension `d'` (`PDivGroup.exists_connPart_iso`). We prove the inequality
**`h ≤ d + d'`** of [Hong, Thm. 2.2.19] (the direction used in [Hong, proof of Thm. 3.4.10]).

Proof. Let `X = G_1 ⊗ 𝔽_p`, connected and killed by `p`, of order `p^h`. By
`FFGroupScheme.order_le_frobKer_mul` (`GroupScheme/Frobenius.lean`),
`p^h ≤ |ker φ_X| · |ker φ_{X^∨}|`, the Frobenius kernels being cut out by `frobKerIdeal`.

* `FFGroupScheme.finrank_baseChange_frobKer_le`: if `O(G)` is a quotient of `R[[T_1, …, T_d]]`
  with `ε(T_j) = 0`, then `|ker φ_{G ⊗ k}| ≤ p^d`, since `R[[T]]/(T_j^p) ⊗ k ↠ O(ker φ)`
  ([Hong, Cor. 1.5.11, Cor. 2.2.18]; `MvPowerSeries.finrank_quot_spanXPow`). For `G_1 = F[p]`
  this gives `|ker φ_X| ≤ p^d` (`PDivFGL.finrank_frobKer_baseChange_le`).
* `finrank_quot_frobKerIdeal_le`: a counit-compatible surjection `D ↠ B / frobKerIdeal` of
  bialgebras gives `|ker φ_B| ≤ |ker φ_D|`.
* `PDivFGL.finrank_frobKer_dual_le`: `X^∨ = (G_1^∨) ⊗ 𝔽_p` (Cartier duality commutes with base
  change, `FFGroupScheme.isBaseChange_dual`), and `1 - e₀ ∈ frobKerIdeal`, so
  `O(F'[p]) ⊗ 𝔽_p ≅ O((G_1^∨)⁰) ⊗ 𝔽_p ↠ O(ker φ_{X^∨})`; hence `|ker φ_{X^∨}| ≤ p^{d'}`.

Main results: `PDivFGL.height_le_add_of_connPart_iso` and
`PDivFGL.exists_connPart_dual_iso_height_le`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 2.2.19, Cor. 2.2.18, Cor. 1.5.11,
  Thm. 3.4.10.
-/

noncomputable section

open Coalgebra WithConv TensorProduct Module MvPowerSeries

namespace PadicHodge

universe u

/-! ### Frobenius kernel ideals under surjections -/

section FrobKer

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime]

theorem frobKerIdeal_le_ker_counit (B : Type*) [CommRing B] [Bialgebra k B] :
    frobKerIdeal k B p ≤ RingHom.ker (Bialgebra.counitAlgHom k B) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, map_pow]
  change counit (R := k) a ^ p = 0
  rw [ha, zero_pow hp.out.ne_zero]

/-- The counit of `B` on `O(ker φ_B) = B ⧸ frobKerIdeal`. -/
def frobKerCounit (B : Type*) [CommRing B] [Bialgebra k B] :
    B ⧸ frobKerIdeal k B p →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (Bialgebra.counitAlgHom k B) fun _ ha =>
    (RingHom.mem_ker).mp (frobKerIdeal_le_ker_counit (p := p) B ha)

theorem frobKerCounit_mk {B : Type*} [CommRing B] [Bialgebra k B] (b : B) :
    frobKerCounit (p := p) B (Ideal.Quotient.mk _ b) = counit (R := k) b := rfl

theorem pow_eq_zero_of_frobKerCounit {B : Type*} [CommRing B] [Bialgebra k B]
    {z : B ⧸ frobKerIdeal k B p} (hz : frobKerCounit (p := p) B z = 0) : z ^ p = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact pow_mem_frobKerIdeal hz

/-- **`|ker φ_B| ≤ |ker φ_D|`** for a counit-compatible surjection `D ↠ B ⧸ frobKerIdeal`. -/
theorem finrank_quot_frobKerIdeal_le {B D : Type*} [CommRing B] [Bialgebra k B] [CommRing D]
    [Bialgebra k D] [Module.Finite k D] (Φ : D →ₐ[k] B ⧸ frobKerIdeal k B p)
    (hΦ : ∀ x, frobKerCounit (p := p) B (Φ x) = counit (R := k) x)
    (hsurj : Function.Surjective Φ) :
    finrank k (B ⧸ frobKerIdeal k B p) ≤ finrank k (D ⧸ frobKerIdeal k D p) := by
  have hle : frobKerIdeal k D p ≤ RingHom.ker Φ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_pow]
    exact pow_eq_zero_of_frobKerCounit ((hΦ a).trans ha)
  let Ψ := Ideal.Quotient.liftₐ (frobKerIdeal k D p) Φ fun x hx => (RingHom.mem_ker).mp (hle hx)
  haveI : Module.Finite k (D ⧸ frobKerIdeal k D p) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k _).toLinearMap Ideal.Quotient.mk_surjective
  have hΨ : Function.Surjective Ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have := LinearMap.finrank_range_le Ψ.toLinearMap
  rwa [LinearMap.range_eq_top.mpr hΨ, finrank_top] at this

end FrobKer

/-! ### The Frobenius kernel of the special fibre of a formal group -/

namespace FFGroupScheme

variable {R : Type u} [CommRing R] {k : Type u} [Field k] [Algebra R k] {p : ℕ}
  [hp : Fact p.Prime]

omit hp in
/-- **`|ker φ_{G ⊗ k}| ≤ p^d`** if `O(G)` is a quotient of `R[[T_1, …, T_d]]` with
`ε(T_j) = 0`: `O(ker φ) = (k ⊗ O(G)) / (a^p : ε(a) = 0)` is a quotient of
`k ⊗ R[[T]]/(T_j^p)` ([Hong, Cor. 1.5.11, Cor. 2.2.18]). -/
theorem finrank_baseChange_frobKer_le [Nontrivial R] (G : FFGroupScheme R) {d : ℕ}
    (ρ : MvPowerSeries (Fin d) R →ₐ[R] G.A) (hρ : Function.Surjective ρ)
    (hρ0 : ∀ j, counit (R := R) (ρ (X j)) = 0) :
    finrank k ((G.baseChange k).A ⧸ frobKerIdeal k (G.baseChange k).A p) ≤ p ^ d := by
  classical
  let I := frobKerIdeal k (G.baseChange k).A p
  let J := spanXPow (Fin d) R p
  let g₀ : MvPowerSeries (Fin d) R →ₐ[R] (G.baseChange k).A ⧸ I :=
    (Ideal.Quotient.mkₐ R I).comp
      ((Algebra.TensorProduct.includeRight : G.A →ₐ[R] k ⊗[R] G.A).comp ρ)
  have hg₀ : ∀ f, g₀ f = Ideal.Quotient.mk I ((1 : k) ⊗ₜ ρ f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker g₀ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, hg₀, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem]
    refine pow_mem_frobKerIdeal ?_
    rw [TensorProduct.counit_tmul, hρ0 j, zero_smul]
  let g : MvPowerSeries (Fin d) R ⧸ J →ₐ[R] (G.baseChange k).A ⧸ I :=
    Ideal.Quotient.liftₐ J g₀ fun x hx => (RingHom.mem_ker).mp (hJ hx)
  let Φ : k ⊗[R] (MvPowerSeries (Fin d) R ⧸ J) →ₐ[k] (G.baseChange k).A ⧸ I :=
    Algebra.TensorProduct.lift (Algebra.ofId k _) g fun _ _ => .all _ _
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul s a =>
      obtain ⟨f, rfl⟩ := hρ a
      refine ⟨s ⊗ₜ Ideal.Quotient.mk J f, ?_⟩
      rw [Algebra.TensorProduct.lift_tmul]
      change algebraMap k _ s * Ideal.Quotient.mk I ((1 : k) ⊗ₜ ρ f) = _
      rw [← Ideal.Quotient.mk_algebraMap, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rfl
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  haveI : Module.Free R (MvPowerSeries (Fin d) R ⧸ J) := Module.Free.of_basis (boxBasis p)
  haveI : Module.Finite R (MvPowerSeries (Fin d) R ⧸ J) := Module.Finite.of_basis (boxBasis p)
  have h1 : finrank k (k ⊗[R] (MvPowerSeries (Fin d) R ⧸ J)) = p ^ d := by
    rw [Module.finrank_baseChange, finrank_quot_spanXPow, Fintype.card_fin]
  have := LinearMap.finrank_range_le Φ.toLinearMap
  rwa [(LinearMap.range_eq_top (f := Φ.toLinearMap)).mpr hsurj, finrank_top, h1] at this

variable {S : Type u} [CommRing S] [Algebra R S]

/-- `ε(f_S) = ε(f)` for the base change `f_S` of `f ∈ A^∨`. -/
theorem counit_dualBC (G : FFGroupScheme R) (f : Cartier.Dual R G.A) :
    counit (R := S) (G.dualBC (S := S) f) = algebraMap R S (counit (R := R) f) := by
  change ofConv (G.dualBC (S := S) f) ((1 : S) ⊗ₜ[R] (1 : G.A)) = algebraMap R S (ofConv f 1)
  rw [dualBC_tmul, Algebra.smul_def, mul_one]

/-- **`|ker φ_{(G ⊗ k)^∨}| ≤ |ker φ_{H ⊗ k}|`** if `O(H) ↠ O((G^∨)⁰)`: `(G ⊗ k)^∨ = G^∨ ⊗ k`
(`isBaseChange_dual`) and `ker φ` lies in the connected component (`1 - e₀ ∈ frobKerIdeal`),
so `O(H) ⊗ k ↠ O(G^∨)⁰ ⊗ k ↠ O(ker φ_{(G ⊗ k)^∨})`. -/
theorem finrank_frobKer_dual_baseChange_le [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (G H : FFGroupScheme R)
    (φ : Hom G.dual.connectedComponent H) (hφ : Function.Surjective φ) :
    finrank k (Cartier.Dual k (k ⊗[R] G.A) ⧸ frobKerIdeal k (Cartier.Dual k (k ⊗[R] G.A)) p) ≤
      finrank k ((H.baseChange k).A ⧸ frobKerIdeal k (H.baseChange k).A p) := by
  let X' := H.baseChange k
  let B := Cartier.Dual k (k ⊗[R] G.A)
  let I := frobKerIdeal k B p
  let Q := B ⧸ I
  let e : Cartier.Dual R G.A := G.dual.idemConn
  -- `f ↦ f_k`, `A^∨ → (k ⊗ A)^∨`
  let β₀ : Cartier.Dual R G.A →+* B :=
    { toFun := fun f => G.dualBC (S := k) f
      map_one' := G.dualBC_one
      map_mul' := G.dualBC_mul
      map_zero' := G.dualBC_zero
      map_add' := G.dualBC_add }
  let β : Cartier.Dual R G.A →+* Q := (Ideal.Quotient.mk I).comp β₀
  have hβ : ∀ f, β f = Ideal.Quotient.mk I (G.dualBC (S := k) f) := fun _ => rfl
  have hc : counit (R := R) (1 - e) = 0 := by
    rw [map_sub, Bialgebra.counit_one]
    exact sub_eq_zero.mpr G.dual.counit_idemConn.symm
  have hβe : β (1 - e) = 0 := by
    have he : IsIdempotentElem (1 - e) :=
      (show IsIdempotentElem e from G.dual.isPointIdempotent_idemConn.isIdempotentElem).one_sub
    have hy : IsIdempotentElem (β₀ (1 - e)) := he.map β₀
    have h0 := pow_mem_frobKerIdeal (R := k) (A := B) (p := p)
      (a := β₀ (1 - e)) (by
        change counit (R := k) (G.dualBC (S := k) (1 - e)) = 0
        rw [counit_dualBC]
        exact (congrArg (algebraMap R k) hc).trans (map_zero _))
    rw [hy.pow_eq hp.out.ne_zero] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h0
  -- descend to the connected component `(G^∨)⁰`
  let γ₀ : Cartier.Dual R G.A ⧸ Ideal.span {1 - e} →+* Q :=
    Ideal.Quotient.lift (Ideal.span {1 - e}) β fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hβe, mul_zero]
  let γ : G.dual.connectedComponent.A →+* Q := γ₀
  have hγ : ∀ f, γ (Ideal.Quotient.mk (Ideal.span {1 - e}) f) = β f := fun _ => rfl
  letI : Algebra R Q := ((algebraMap k Q).comp (algebraMap R k)).toAlgebra
  haveI : @IsScalarTower R k Q Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : H.A →ₐ[R] Q :=
    { γ.comp (φ : H.A →ₐ[R] G.dual.connectedComponent.A).toRingHom with
      commutes' := fun r => by
        change γ (φ (algebraMap R _ r)) = _
        rw [AlgHomClass.commutes]
        change β (algebraMap R (Cartier.Dual R G.A) r) = algebraMap k Q (algebraMap R k r)
        rw [hβ, Algebra.algebraMap_eq_smul_one (A := Cartier.Dual R G.A) r, G.dualBC_smul,
          G.dualBC_one, Algebra.smul_def, mul_one, Ideal.Quotient.mk_algebraMap] }
  have hg : ∀ a, g a = γ (φ a) := fun _ => rfl
  let Φ : X'.A →ₐ[k] Q := Algebra.TensorProduct.lift (Algebra.ofId k Q) g fun _ _ => .all _ _
  have hΦ1 : ∀ a, Φ ((1 : k) ⊗ₜ a) = g a := fun a => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  refine finrank_quot_frobKerIdeal_le (B := B) (D := X'.A) Φ (fun x => ?_) ?_
  · induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
    | tmul s a =>
      rw [Algebra.TensorProduct.lift_tmul, map_mul, hg, TensorProduct.counit_tmul,
        Algebra.ofId_apply, AlgHom.commutes]
      obtain ⟨f, hf⟩ : ∃ f : Cartier.Dual R G.A,
          Ideal.Quotient.mk (Ideal.span {1 - e}) f = φ a := Ideal.Quotient.mk_surjective _
      have h1 : counit (R := R) (show G.dual.A from f) = counit (R := R) a := by
        have h2 := CoalgHomClass.counit_comp_apply φ a
        have h3 := CoalgHomClass.counit_comp_apply G.dual.connectedComponentHom
          (show G.dual.A from f)
        rw [← hf] at h2
        exact h3.symm.trans h2
      rw [← hf, hγ, hβ, frobKerCounit_mk, counit_dualBC, Algebra.smul_def, mul_comm]
      exact congrArg (fun t => algebraMap R k t * _) h1
  · intro z
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
    suffices hF : ∀ F' : Module.Dual k (k ⊗[R] G.A),
        Ideal.Quotient.mk I (toConv F') ∈ LinearMap.range Φ.toLinearMap by
      obtain ⟨x, hx⟩ := hF (ofConv F)
      exact ⟨x, hx⟩
    intro F'
    refine G.isBaseChange_dual.inductionOn F'
      (fun F' => Ideal.Quotient.mk I (toConv F') ∈ LinearMap.range Φ.toLinearMap) ?_ ?_ ?_ ?_
    · rw [toConv_zero, map_zero]
      exact Submodule.zero_mem _
    · intro f
      rw [G.toDual_eq, toConv_ofConv]
      obtain ⟨b, hb⟩ := hφ (Ideal.Quotient.mk (Ideal.span {1 - e}) (toConv f))
      refine ⟨(1 : k) ⊗ₜ b, ?_⟩
      rw [AlgHom.toLinearMap_apply, hΦ1, hg, hb, hγ, hβ]
    · intro s n hn
      beta_reduce at hn ⊢
      rw [toConv_smul]
      change Ideal.Quotient.mkₐ k I (s • toConv n) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ s hn
    · intro n₁ n₂ h₁ h₂
      beta_reduce at h₁ h₂ ⊢
      rw [toConv_add, map_add]
      exact Submodule.add_mem _ h₁ h₂

end FFGroupScheme

/-! ### `h ≤ d + d'` -/

namespace PDivFGL

variable {p : ℕ} [hp : Fact p.Prime]

attribute [local instance] SerreTate.algebraZModD SerreTate.isDomain_zpD isPrincipalIdealRing_zpD

variable {d : ℕ} (P : PDivFGL (ZpD p) d p)

/-- **`|ker φ_{F[p] ⊗ 𝔽_p}| ≤ p^d`** ([Hong, Cor. 2.2.18]). -/
theorem finrank_frobKer_baseChange_le :
    finrank (ZMod p) (((P.groupScheme 1).baseChange (ZMod p)).A ⧸
      frobKerIdeal (ZMod p) ((P.groupScheme 1).baseChange (ZMod p)).A p) ≤ p ^ d :=
  (P.groupScheme 1).finrank_baseChange_frobKer_le (Ideal.Quotient.mkₐ _ _)
    Ideal.Quotient.mk_surjective fun j => P.counit_t 1 j

variable {d' : ℕ} (P' : PDivFGL (ZpD p) d' p)
  (φ : PDivGroup.Hom P.dualPDiv.connPart P'.pdivGroup)
  (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart)

/-- **`|ker φ_{X^∨}| ≤ |ker φ_{F'[p] ⊗ 𝔽_p}|`** for `X = F[p] ⊗ 𝔽_p` and
`(F[p^∞]^∨)⁰ ≅ F'[p^∞]`: `X^∨ = F[p]^∨ ⊗ 𝔽_p` and `ker φ_{X^∨}` lies in the connected
component. -/
theorem finrank_frobKer_dual_le (hφψ : ψ.comp φ = PDivGroup.Hom.id _) :
    finrank (ZMod p) (((P.groupScheme 1).baseChange (ZMod p)).dual.A ⧸
      frobKerIdeal (ZMod p) ((P.groupScheme 1).baseChange (ZMod p)).dual.A p) ≤
    finrank (ZMod p) (((P'.groupScheme 1).baseChange (ZMod p)).A ⧸
      frobKerIdeal (ZMod p) ((P'.groupScheme 1).baseChange (ZMod p)).A p) :=
  (P.groupScheme 1).finrank_frobKer_dual_baseChange_le (P'.groupScheme 1) (φ.f 1)
    fun c => ⟨ψ.f 1 c, congrArg (fun χ => χ.f 1 c) hφψ⟩

/-- **`h ≤ d + d'`** ([Hong, Thm. 2.2.19]): if the connected part of the Cartier dual of
`F[p^∞]` is isomorphic to `F'[p^∞]` with `F'` of dimension `d'`, then `h ≤ d + d'`. -/
theorem height_le_add_of_connPart_iso (hφψ : ψ.comp φ = PDivGroup.Hom.id _) :
    P.height ≤ d + d' := by
  let X := (P.groupScheme 1).baseChange (ZMod p)
  have hconn : X.IsConnected :=
    SerreTate.isConnected_baseChange (H := P.pdivGroup) P.isConnected_groupScheme 1
  have hkill : X.univPt ^ p = 1 := by
    have := (P.pdivGroup.baseChange (ZMod p)).pow_eq_one 1 X.A X.univPt
    rwa [pow_one] at this
  have hord : X.order = p ^ P.height := by
    rw [FFGroupScheme.order_baseChange, P.order_groupScheme 1, mul_one]
  have key := X.order_le_frobKer_mul (ZMod.pow_card (p := p)) hconn hkill
  rw [hord] at key
  have h2 := (P.finrank_frobKer_dual_le P' φ ψ hφψ).trans P'.finrank_frobKer_baseChange_le
  have h3 := key.trans (Nat.mul_le_mul P.finrank_frobKer_baseChange_le h2)
  rw [← pow_add] at h3
  exact (pow_le_pow_iff_right₀ hp.out.one_lt).mp h3

/-- **`h ≤ d + d'`** ([Hong, Thm. 2.2.19], the inequality used in
[Hong, proof of Thm. 3.4.10]): for `P` of dimension `d` and height `h` over `ℤ_p`, the connected
part of `(F[p^∞])^∨` is `F'[p^∞]` for some `P'` of dimension `d'`, and `h ≤ d + d'`. -/
theorem exists_connPart_dual_iso_height_le :
    ∃ (d' : ℕ) (P' : PDivFGL (ZpD p) d' p) (φ : PDivGroup.Hom P.dualPDiv.connPart P'.pdivGroup)
      (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart),
      φ.comp ψ = PDivGroup.Hom.id _ ∧ ψ.comp φ = PDivGroup.Hom.id _ ∧ P.height ≤ d + d' := by
  obtain ⟨d', P', φ, ψ, h1, h2⟩ := P.dualPDiv.exists_connPart_iso
  exact ⟨d', P', φ, ψ, h1, h2, P.height_le_add_of_connPart_iso P' φ ψ h2⟩

end PDivFGL

end PadicHodge
