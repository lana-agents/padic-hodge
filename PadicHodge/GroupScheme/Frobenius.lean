/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.CartierPairingBase
import PadicHodge.GroupScheme.Connected
import PadicHodge.GroupScheme.PDivisibleHom
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.CharP.Algebra

/-!
# The relative Frobenius of a finite flat group scheme in characteristic `p`, and `h ≤ d + d^∨`

Let `k` be a field of characteristic `p` on which `x ↦ x^p` is the identity (e.g. `𝔽_p`; then
all Frobenius twists are trivial, `G^{(p)} = G`), and `G = Spec A` a finite flat commutative group
scheme over `k`, with Cartier dual `G^∨ = Spec A^∨`.

* `frobAlg`: the `p`-power map `a ↦ a^p` of a commutative `k`-algebra, a `k`-algebra map;
  `frobBialg`: for a bialgebra it is a bialgebra map, giving the **relative Frobenius**
  `FFGroupScheme.frob G : G → G = G^{(p)}` ([Hong, Def. 1.5.1, Lemma 1.5.2, Cor. 1.5.4]).
* `frobKerIdeal k A p = (a^p : ε(a) = 0)`, the ideal cutting out the Frobenius kernel `ker φ_G`
  ([Hong, Lemma 1.5.2]: `φ_G` is induced by `a ↦ a^p`, so `ker φ_G = Spec A/(a^p : a ∈ I)` for the
  augmentation ideal `I`); `FFGroupScheme.one_sub_idemConn_mem_frobKerIdeal`: it contains `1 - e₀`,
  i.e. `ker φ_G` lies in the connected component `G⁰`.
* `FFGroupScheme.apply_univPt_pow`: for `f ∈ A^∨` and `d ∈ A`, `f([p]^* d) = ((f ∘ Frob)^p)(d)`
  (convolution power): the universal point `u = ∑ e_i^* ⊗ e_i ∈ A^∨ ⊗ A` satisfies
  `u^p = ∑ (e_i^*)^p ⊗ e_i^p` in the commutative ring `A^∨ ⊗ A` of characteristic `p`. This is the
  half `ψ_G ∘ φ_G = [p]_G` of [Hong, Prop. 1.5.8]. Equivalently `f^p(d^p) = f([p]^* d)`
  (`FFGroupScheme.pow_apply_pow`); so `d^p = 0` implies `[p]^* d = 0`
  (`FFGroupScheme.univPt_pow_apply_eq_zero`).
* If `G` is killed by `p`, the transpose `f ↦ f ∘ Frob` of `φ_G` kills `frobKerIdeal k A^∨ p`
  (`FFGroupScheme.frobKerIdeal_dual_le_ker`), hence
  `rank(φ_G) ≤ dim_k A^∨/frobKerIdeal = |ker φ_{G^∨}|` (`FFGroupScheme.finrank_range_frob_le`).
* `finrank_le_mul_finrank_of_le_map` (Nakayama): for `A` local, finite over `k`, and `R₀ ⊆ A` a
  subalgebra, `dim A ≤ dim (A/I) · dim R₀` whenever `I ⊆ 𝔪 A` for an ideal `𝔪 ⊆ R₀` of elements
  of the maximal ideal of `A`. Applied to `R₀ = Frob(A)`, `I = frobKerIdeal`. Variants:
  `finrank_le_mul_finrank_range_of_algHom` (`dim A ≤ dim A/(φ(K)) · rank φ` for an algebra map
  `φ : D → A` sending `K` into the maximal ideal) and
  `FFGroupScheme.order_le_finrank_mul_finrank_range` (`|G| ≤ |ker f| · |im f|` for `f : G → H`
  with `G` connected).
* **`FFGroupScheme.order_le_frobKer_mul`**: for `G` connected and killed by `p`,
  `|G| ≤ |ker φ_G| · |ker φ_{G^∨}|`, i.e. the inequality `h ≤ d + d^∨` of [Hong, Thm. 2.2.19]
  (with [Hong, Cor. 2.2.18]: `|ker φ_{G_1}| = p^d`); only this inequality is used in
  [Hong, proof of Thm. 3.4.10]. The proof avoids exact sequences of group schemes: it combines
  `|G| ≤ |ker φ_G| · rank(φ_G)` (Nakayama) with `rank(φ_G) ≤ |ker φ_{G^∨}|` (duality and
  `ψ ∘ φ = [p]`).
-/

noncomputable section

open Coalgebra WithConv TensorProduct Module

namespace PadicHodge

universe u

/-! ### The Frobenius kernel ideal -/

/-- The ideal `(a^p : ε(a) = 0)` of a bialgebra `A` over `R`; for `R = k` a field of
characteristic `p` it cuts out the Frobenius kernel `ker φ_G` ([Hong, Lemma 1.5.2]). -/
def frobKerIdeal (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A] (p : ℕ) :
    Ideal A :=
  Ideal.span {x | ∃ a : A, counit (R := R) a = 0 ∧ a ^ p = x}

theorem pow_mem_frobKerIdeal {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
    {p : ℕ} {a : A} (ha : counit (R := R) a = 0) : a ^ p ∈ frobKerIdeal R A p :=
  Ideal.subset_span ⟨a, ha, rfl⟩

/-- The Frobenius kernel lies in the connected component: `1 - e₀ ∈ frobKerIdeal`. -/
theorem FFGroupScheme.one_sub_idemConn_mem_frobKerIdeal {R : Type u} [CommRing R]
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (G : FFGroupScheme R)
    {p : ℕ} (hp : p ≠ 0) : 1 - G.idemConn ∈ frobKerIdeal R G.A p := by
  have h1 : counit (R := R) G.idemConn = 1 := G.isPointIdempotent_idemConn.apply_eq_one
  have h0 : counit (R := R) (1 - G.idemConn) = 0 := by
    rw [map_sub, h1, Bialgebra.counit_one, sub_self]
  have := pow_mem_frobKerIdeal (p := p) h0
  rwa [G.isPointIdempotent_idemConn.isIdempotentElem.one_sub.pow_eq hp] at this

/-! ### The Frobenius of a `k`-algebra -/

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p]

variable (k) in
theorem add_pow_of_algebra {S : Type*} [CommRing S] [Algebra k S] (x y : S) :
    (x + y) ^ p = x ^ p + y ^ p := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact Subsingleton.elim _ _
  · haveI := charP_of_injective_algebraMap (algebraMap k S).injective p
    exact add_pow_char ..

/-- The `p`-power map `x ↦ x^p` of a commutative `k`-algebra, a `k`-algebra map when `c^p = c`
on `k` ([Hong, Lemma 1.5.2]). -/
def frobAlg (hk : ∀ x : k, x ^ p = x) (S : Type*) [CommRing S] [Algebra k S] : S →ₐ[k] S where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.out.ne_zero
  map_add' := add_pow_of_algebra k
  commutes' c := by
    rw [← map_pow, hk]

@[simp]
theorem frobAlg_apply (hk : ∀ x : k, x ^ p = x) {S : Type*} [CommRing S] [Algebra k S] (x : S) :
    frobAlg hk S x = x ^ p := rfl

/-- In `A ⊗ B`, the `p`-power map is `Frob ⊗ Frob`. -/
theorem pow_eq_map_frobAlg (hk : ∀ x : k, x ^ p = x) {A B : Type*} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (x : A ⊗[k] B) :
    x ^ p = Algebra.TensorProduct.map (frobAlg hk A) (frobAlg hk B) x := by
  induction x with
  | zero => rw [map_zero]; exact zero_pow hp.out.ne_zero
  | tmul a b => rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.map_tmul]; rfl
  | add x y hx hy => rw [add_pow_of_algebra k, hx, hy, map_add]

/-- The Frobenius of a bialgebra is a bialgebra map ([Hong, Cor. 1.5.4]). -/
def frobBialg (hk : ∀ x : k, x ^ p = x) (A : Type*) [CommRing A] [Bialgebra k A] :
    A →ₐc[k] A :=
  BialgHom.ofAlgHom (frobAlg hk A)
    (AlgHom.ext fun a => by
      change Bialgebra.counitAlgHom k A (a ^ p) = Bialgebra.counitAlgHom k A a
      rw [map_pow, hk])
    (AlgHom.ext fun a => by
      change Algebra.TensorProduct.map (frobAlg hk A) (frobAlg hk A)
        (Bialgebra.comulAlgHom k A a) = Bialgebra.comulAlgHom k A (a ^ p)
      rw [map_pow, pow_eq_map_frobAlg hk])

@[simp]
theorem frobBialg_apply (hk : ∀ x : k, x ^ p = x) {A : Type*} [CommRing A] [Bialgebra k A]
    (a : A) : frobBialg hk A a = a ^ p := rfl

/-- The transpose `f ↦ f ∘ Frob` of the Frobenius, an algebra endomorphism of `A^∨` for the
convolution product. -/
def frobT (hk : ∀ x : k, x ^ p = x) (A : Type u) [CommRing A] [HopfAlgebra k A] :
    Cartier.Dual k A →ₐ[k] Cartier.Dual k A :=
  Cartier.transposeAlgHom (frobBialg hk A : A →ₗc[k] A)

theorem frobT_apply (hk : ∀ x : k, x ^ p = x) {A : Type u} [CommRing A] [HopfAlgebra k A]
    (f : Cartier.Dual k A) (a : A) : frobT hk A f a = f (a ^ p) := rfl

end Frobenius

/-! ### Nakayama -/

/-- **Nakayama** (dimension form): let `A` be a local ring finite over a field `k`, `R₀ ⊆ A` a
`k`-subalgebra and `J ⊆ R₀` an ideal of elements of the maximal ideal of `A`. If `I ⊆ J A`, then
`dim_k A ≤ dim_k (A/I) · dim_k R₀` (lifts of a basis of `A/I` generate `A` over `R₀`). -/
theorem finrank_le_mul_finrank_of_le_map {k : Type*} [Field k] {A : Type*} [CommRing A]
    [Algebra k A] [Module.Finite k A] [IsLocalRing A] (R₀ : Subalgebra k A) (J : Ideal R₀)
    (hJ : ∀ x ∈ J, (x : A) ∈ IsLocalRing.maximalIdeal A) (I : Ideal A)
    (hI : I ≤ J.map (algebraMap R₀ A)) :
    finrank k A ≤ finrank k (A ⧸ I) * finrank k R₀ := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hnil : ∀ x ∈ J, IsNilpotent x := by
    intro x hx
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
    refine ⟨n, Subtype.ext ?_⟩
    have := Ideal.pow_mem_pow (hJ x hx) n
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    simpa using this
  have hJac : J ≤ Ideal.jacobson ⊥ := fun x hx =>
    Ideal.mem_jacobson_bot.mpr fun y =>
      ((Commute.all x y).isNilpotent_mul_right (hnil x hx)).isUnit_add_one
  haveI : Module.Finite k (A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite R₀ A := Module.Finite.of_restrictScalars_finite k R₀ A
  let bq := Module.finBasis k (A ⧸ I)
  let s : Fin (finrank k (A ⧸ I)) → A := fun j => (Ideal.Quotient.mk_surjective (bq j)).choose
  have hs : ∀ j, Ideal.Quotient.mk I (s j) = bq j :=
    fun j => (Ideal.Quotient.mk_surjective (bq j)).choose_spec
  have htop : (⊤ : Submodule R₀ A) ≤ Submodule.span R₀ (Set.range s) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hJac ?_
    intro a _
    let y : A := ∑ j, bq.repr (Ideal.Quotient.mk I a) j • s j
    have hy : y ∈ Submodule.span R₀ (Set.range s) :=
      Submodule.sum_mem _ fun j _ =>
        Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hay : a - y ∈ J • (⊤ : Submodule R₀ A) := by
      rw [Ideal.smul_top_eq_map]
      refine hI (Ideal.Quotient.eq.mp ?_)
      have : Ideal.Quotient.mkₐ k I y = Ideal.Quotient.mkₐ k I a := by
        simp only [y, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk, hs]
        exact bq.sum_repr _
      exact this.symm
    have := Submodule.add_mem_sup hy hay
    rwa [add_sub_cancel] at this
  let bR := Module.finBasis k R₀
  have hspan : Submodule.span k (Set.range fun q : Fin (finrank k R₀) × Fin (finrank k (A ⧸ I)) =>
      bR q.1 • s q.2) = ⊤ := by
    rw [← Set.range_smul_range, Submodule.span_smul_of_span_eq_top bR.span_eq,
      eq_top_iff.mpr htop, Submodule.restrictScalars_top]
  have := finrank_range_le_card (R := k)
    (fun q : Fin (finrank k R₀) × Fin (finrank k (A ⧸ I)) => bR q.1 • s q.2)
  unfold Set.finrank at this
  rw [hspan, finrank_top, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
  rwa [mul_comm] at this

/-- **Nakayama** for an algebra map: let `A` be a local ring finite over a field `k` and
`φ : D → A` a `k`-algebra map. If `φ` maps `K ⊆ D` into the maximal ideal of `A`, then
`dim_k A ≤ dim_k (A/(φ(K))) · rank(φ)`. -/
theorem finrank_le_mul_finrank_range_of_algHom {k : Type*} [Field k] {A : Type*} [CommRing A]
    [Algebra k A] [Module.Finite k A] [IsLocalRing A] {D : Type*} [CommRing D] [Algebra k D]
    (φ : D →ₐ[k] A) (K : Set D) (hK : ∀ x ∈ K, φ x ∈ IsLocalRing.maximalIdeal A) :
    finrank k A ≤ finrank k (A ⧸ Ideal.span (φ '' K)) *
      finrank k (LinearMap.range φ.toLinearMap) := by
  let R₀ := φ.range
  let J : Ideal R₀ := (IsLocalRing.maximalIdeal A).comap R₀.val
  have hI : Ideal.span (φ '' K) ≤ J.map (algebraMap R₀ A) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Ideal.mem_map_of_mem (algebraMap R₀ A) (I := J) (x := ⟨φ x, x, rfl⟩) (hK x hx)
  have hR : finrank k R₀ = finrank k (LinearMap.range φ.toLinearMap) := by
    have : Subalgebra.toSubmodule R₀ = LinearMap.range φ.toLinearMap :=
      Submodule.ext fun _ => Iff.rfl
    rw [← Subalgebra.finrank_toSubmodule, this]
  rw [← hR]
  exact finrank_le_mul_finrank_of_le_map R₀ J (fun _ hx => hx) _ hI

/-- **`|G| ≤ |ker f| · |im f|`** for a homomorphism `f : G → H` of finite flat group schemes over
a field with `G` connected: `ker f = Spec O(G)/(f^*(I_H))` for the augmentation ideal `I_H`, and
`im f` has coordinate ring `f^*(O(H))`. -/
theorem FFGroupScheme.order_le_finrank_mul_finrank_range {k : Type u} [Field k]
    {G H : FFGroupScheme k} (f : FFGroupScheme.Hom G H) (hG : G.IsConnected) :
    G.order ≤ finrank k (G.A ⧸ Ideal.span ((f : H.A →ₐ[k] G.A) '' {x | counit (R := k) x = 0})) *
      finrank k (LinearMap.range (f : H.A →ₐ[k] G.A).toLinearMap) := by
  haveI : IsLocalRing G.A := hG
  refine finrank_le_mul_finrank_range_of_algHom _ _ fun x (hx : counit (R := k) x = 0) hu => ?_
  have h := hu.map (Bialgebra.counitAlgHom k G.A)
  have he : Bialgebra.counitAlgHom k G.A ((f : H.A →ₐ[k] G.A) x) = 0 :=
    (CoalgHomClass.counit_comp_apply f x).trans hx
  rw [he] at h
  exact not_isUnit_zero h

/-! ### Frobenius and Verschiebung on the universal point -/

namespace FFGroupScheme

theorem hat_pow {R : Type u} [CommRing R] (G : FFGroupScheme R) (S : Type*) [CommRing S]
    [Algebra R S] (φ : G.points S) (n : ℕ) : G.hat S (φ ^ n) = G.hat S φ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, hat_one]
  | succ n ih => rw [pow_succ, pow_succ, hat_mul, ih]

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p]

/-- The relative Frobenius `φ_G : G → G^{(p)} = G` ([Hong, Def. 1.5.1, Lemma 1.5.2,
Cor. 1.5.4]). -/
def frob (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k) : Hom G G := frobBialg hk G.A

/-- `[p]^*(d) = ∑_i (e_i^*)^p(d) e_i^p`: the `p`-th power of the universal point
`u = ∑ e_i^* ⊗ e_i ∈ A^∨ ⊗ A` is `∑ (e_i^*)^p ⊗ e_i^p` (characteristic `p`). -/
theorem univPt_pow_apply (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k) {ι : Type*}
    [Fintype ι] (b : Basis ι k G.A) (d : G.A) :
    ofConv (G.univPt ^ p) d =
      ∑ i, (toConv (b.coord i) ^ p : Cartier.Dual k G.A) d • b i ^ p := by
  have h1 : G.hat G.A (G.univPt ^ p) =
      ∑ i, (toConv (b.coord i) ^ p : Cartier.Dual k G.A) ⊗ₜ[k] (b i ^ p) := by
    rw [hat_pow, hat_eq_sum G G.A b]
    exact (map_sum (frobAlg hk (Cartier.Dual k G.A ⊗[k] G.A)) _ _).trans
      (Finset.sum_congr rfl fun i _ => Algebra.TensorProduct.tmul_pow _ _ _)
  have h2 := congrArg (fun x => Cartier.theta G.A G.A x d) h1
  simp only [theta_hat, map_sum, LinearMap.coe_sum, Finset.sum_apply,
    Cartier.theta_tmul] at h2
  exact h2

/-- **`ψ_G ∘ φ_G = [p]_G`** in dual form ([Hong, Prop. 1.5.8]): for `f ∈ A^∨` and `d ∈ A`,
`f([p]^* d) = ((f ∘ Frob)^p)(d)`. -/
theorem apply_univPt_pow (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k)
    (f : Cartier.Dual k G.A) (d : G.A) :
    f (ofConv (G.univPt ^ p) d) = (frobT hk G.A f ^ p) d := by
  classical
  let b := Module.Free.chooseBasis k G.A
  have hT : frobT hk G.A f = ∑ i, f (b i ^ p) • toConv (b.coord i) := by
    apply WithConv.ofConv_injective
    rw [ofConv_sum]
    exact (b.sum_dual_apply_smul_coord (ofConv (frobT hk G.A f))).symm
  have hTp : frobT hk G.A f ^ p =
      ∑ i, f (b i ^ p) • (toConv (b.coord i) : Cartier.Dual k G.A) ^ p := by
    rw [hT]
    refine (map_sum (frobAlg hk (Cartier.Dual k G.A)) _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [frobAlg_apply, smul_pow, hk]
  rw [hTp, univPt_pow_apply hk G b d, map_sum]
  simp only [map_smul, smul_eq_mul, ofConv_sum, ofConv_smul, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **`f^p(d^p) = f([p]^* d)`** for all `f ∈ A^∨`, `d ∈ A` (convolution power `f^p`;
[Hong, Prop. 1.5.8], `ψ_G ∘ φ_G = [p]_G`). -/
theorem pow_apply_pow (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k)
    (f : Cartier.Dual k G.A) (d : G.A) :
    (f ^ p) (d ^ p) = f (ofConv (G.univPt ^ p) d) := by
  rw [apply_univPt_pow hk G f d, ← map_pow]
  rfl

/-- If `d^p = 0` then `[p]^*(d) = 0`. -/
theorem univPt_pow_apply_eq_zero (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k) {d : G.A}
    (hd : d ^ p = 0) : ofConv (G.univPt ^ p) d = 0 := by
  let b := Module.Free.chooseBasis k G.A
  refine b.forall_coord_eq_zero_iff.mp fun i => ?_
  have := pow_apply_pow hk G (toConv (b.coord i)) d
  rw [hd, map_zero] at this
  exact this.symm

/-- If `G` is killed by `p` and `f(1) = 0`, then `f^p ∘ Frob = 0`. -/
theorem frobT_pow_eq_zero (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k)
    (hG : G.univPt ^ p = 1) (f : Cartier.Dual k G.A) (hf : f 1 = 0) :
    frobT hk G.A (f ^ p) = 0 := by
  apply WithConv.ofConv_injective
  refine LinearMap.ext fun d => ?_
  change (frobT hk G.A (f ^ p)) d = 0
  rw [map_pow, ← apply_univPt_pow hk G f d, hG, AlgHom.convOne_apply,
    Algebra.algebraMap_eq_smul_one, map_smul, hf, smul_zero]

/-- If `G` is killed by `p`, the transpose of `φ_G` kills `frobKerIdeal k A^∨ p`. -/
theorem frobKerIdeal_dual_le_ker (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k)
    (hG : G.univPt ^ p = 1) :
    frobKerIdeal k (Cartier.Dual k G.A) p ≤ RingHom.ker (frobT hk G.A) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  exact frobT_pow_eq_zero hk G hG f hf

/-- **`rank(φ_G) ≤ |ker φ_{G^∨}|`** for `G` killed by `p`. -/
theorem finrank_range_frob_le (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k)
    (hG : G.univPt ^ p = 1) :
    finrank k (LinearMap.range (frobAlg hk G.A).toLinearMap) ≤
      finrank k (G.dual.A ⧸ frobKerIdeal k G.dual.A p) := by
  let J := frobKerIdeal k (Cartier.Dual k G.A) p
  let T' := Ideal.Quotient.liftₐ J (frobT hk G.A) fun x hx => frobKerIdeal_dual_le_ker hk G hG hx
  haveI : Module.Finite k (Cartier.Dual k G.A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k J).toLinearMap Ideal.Quotient.mk_surjective
  have h1 : (frobT hk G.A).toLinearMap = T'.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ k J).toLinearMap :=
    LinearMap.ext fun _ => rfl
  have h2 : finrank k (LinearMap.range (frobT hk G.A).toLinearMap) ≤
      finrank k (Cartier.Dual k G.A ⧸ J) := by
    rw [h1]
    exact (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
      (LinearMap.finrank_range_le _)
  let e := WithConv.linearEquiv k (G.A →ₗ[k] k)
  have h3 : (frobT hk G.A).toLinearMap =
      e.symm.toLinearMap ∘ₗ (frobAlg hk G.A).toLinearMap.dualMap ∘ₗ e.toLinearMap := rfl
  rw [h3, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ e.range,
    LinearEquiv.finrank_map_eq, LinearMap.finrank_range_dualMap_eq_finrank_range] at h2
  exact h2

/-- **`|G| ≤ |ker φ_G| · rank(φ_G)`** for `G` connected (Nakayama). -/
theorem order_le_frobKer_mul_finrank_range (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k)
    (hG : G.IsConnected) :
    G.order ≤ finrank k (G.A ⧸ frobKerIdeal k G.A p) *
      finrank k (LinearMap.range (frobAlg hk G.A).toLinearMap) := by
  haveI : IsLocalRing G.A := hG
  let R₀ := (frobAlg hk G.A).range
  let J : Ideal R₀ := RingHom.ker ((Bialgebra.counitAlgHom k G.A).comp R₀.val)
  have hJ : ∀ x ∈ J, (x : G.A) ∈ IsLocalRing.maximalIdeal G.A := by
    intro x hx hu
    have h := hu.map (Bialgebra.counitAlgHom k G.A)
    rw [show Bialgebra.counitAlgHom k G.A x = 0 from hx] at h
    exact not_isUnit_zero h
  have hI : frobKerIdeal k G.A p ≤ J.map (algebraMap R₀ G.A) := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨a, ha, rfl⟩
    refine Ideal.mem_map_of_mem (algebraMap R₀ G.A) (x := ⟨a ^ p, a, rfl⟩) ?_
    change Bialgebra.counitAlgHom k G.A (a ^ p) = 0
    rw [map_pow]
    change counit (R := k) a ^ p = 0
    rw [ha, zero_pow hp.out.ne_zero]
  have hR : finrank k R₀ = finrank k (LinearMap.range (frobAlg hk G.A).toLinearMap) := by
    have : Subalgebra.toSubmodule R₀ = LinearMap.range (frobAlg hk G.A).toLinearMap :=
      Submodule.ext fun _ => Iff.rfl
    rw [← Subalgebra.finrank_toSubmodule, this]
  rw [← hR]
  exact finrank_le_mul_finrank_of_le_map R₀ J hJ _ hI

/-- **`h ≤ d + d^∨`** ([Hong, Thm. 2.2.19], the inequality used in [Hong, proof of Thm. 3.4.10]):
for a connected finite flat group scheme `G` over `k` killed by `p`,
`|G| ≤ |ker φ_G| · |ker φ_{G^∨}|`, the Frobenius kernels being cut out by `frobKerIdeal`. -/
theorem order_le_frobKer_mul (hk : ∀ x : k, x ^ p = x) (G : FFGroupScheme k)
    (hG : G.IsConnected) (hp1 : G.univPt ^ p = 1) :
    G.order ≤ finrank k (G.A ⧸ frobKerIdeal k G.A p) *
      finrank k (G.dual.A ⧸ frobKerIdeal k G.dual.A p) :=
  (G.order_le_frobKer_mul_finrank_range hk hG).trans
    (Nat.mul_le_mul_left _ (G.finrank_range_frob_le hk hp1))

end FFGroupScheme

end PadicHodge
