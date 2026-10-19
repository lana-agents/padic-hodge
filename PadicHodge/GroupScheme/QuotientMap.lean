/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.QuotientGroup

/-!
# Functoriality of quotients `G/H` and the third isomorphism theorem on points

Over a local PID `R` (e.g. `O_{K'}`), with quotients `G/H` from `QuotientGroup.lean`:

* `Hom.quotientMap`: a homomorphism `f : G → G'` carrying `H` into `H'` (`g : H → H'`) induces
  `G/H → G'/H'` (the restriction `A'^{H'} → A^H` of `f^*`, `quotientMap_apply`);
* for `K ⊆ H ⊆ G` (closed immersions `k : K → H`, `i : H → G`): **`H/K → G/K` is a closed
  immersion** (`subQuot`, `surjective_subQuot`): `A^K → C^K` is onto, via a `B`-linear retraction
  `φ : A → A^K` (`A` free of rank `|K| ≥ 1` over `A^K`, Nakayama), written as
  `φ = ∑ⱼ trⱼ(eⱼ ·)` by the dual basis, and `i ∘ trⱼ^G = trⱼ^H ∘ i`;
* **third isomorphism theorem on points** (`quotQuot : G/K → G/H`,
  `mapPoints_quotQuot_eq_one_iff`): a point of
  `G/K` maps to `1` in `G/H` iff it comes from `H/K`; the key identity is
  `(A^K)^{H/K} = A^H` inside `A` (`mem_invariants_subQuot_iff`).

These are the quotient manipulations in [Hong, proof of Prop. 3.5.3]
(`H_{v₀+v}/H_{v₀} → H_{v₀+v+1}/H_{v₀}`, kernel of `H_{v₀+v+1}/H_{v₀} → H_{v₀+v+1}/H_{v₀+v}`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 1.1.9 and proof of Prop. 3.5.3.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

namespace Hom

variable {R : Type u} [CommRing R] {G H G' H' : FFGroupScheme R}

/-- A homomorphism `f : G → G'` carrying `H` into `H'` maps `H'`-invariants to `H`-invariants. -/
theorem map_mem_invariants (i : Hom H G) (i' : Hom H' G') (f : Hom G G') (g : Hom H H')
    (h : ∀ a, i (f a) = g (i' a)) {a : G'.A} (ha : a ∈ i'.invariants) :
    f a ∈ i.invariants := by
  rw [mem_invariants] at ha ⊢
  have key : ∀ w : G'.A ⊗[R] G'.A, TensorProduct.map LinearMap.id (i : G.A →ₗ[R] H.A)
      (TensorProduct.map (f : G'.A →ₗ[R] G.A) (f : G'.A →ₗ[R] G.A) w) =
      TensorProduct.map (f : G'.A →ₗ[R] G.A) (g : H'.A →ₗ[R] H.A)
        (TensorProduct.map LinearMap.id (i' : G'.A →ₗ[R] H'.A) w) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp [h]
  have hf : comul (R := R) (f a) = TensorProduct.map (f : G'.A →ₗ[R] G.A)
      (f : G'.A →ₗ[R] G.A) (comul a) :=
    (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) a).symm
  rw [coact_apply, hf, key, ← coact_apply, ha]
  simp

variable [IsDomain R] [IsPrincipalIdealRing R]

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem incl2_map {i : Hom H G} {i' : Hom H' G'} (φ : i'.invariants →ₐ[R] i.invariants)
    (f : G'.A →ₐ[R] G.A) (hφ : ∀ b, (φ b : G.A) = f b) (w : i'.invariants ⊗[R] i'.invariants) :
    i.incl2 (Algebra.TensorProduct.map φ φ w) = Algebra.TensorProduct.map f f (i'.incl2 w) := by
  induction w with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [hφ]

/-- **The homomorphism `G/H → G'/H'` induced by `f : G → G'` with `f(H) ⊆ H'`.** -/
def quotientMap (i : Hom H G) (i' : Hom H' G') (f : Hom G G') (g : Hom H H')
    (h : ∀ a, i (f a) = g (i' a)) : Hom i.quotient i'.quotient :=
  let φ : i'.invariants →ₐ[R] i.invariants :=
    ((f : G'.A →ₐ[R] G.A).comp i'.invariants.val).codRestrict i.invariants
      fun b => map_mem_invariants i i' f g h b.2
  BialgHom.ofAlgHom (A := i'.invariants) (B := i.invariants) φ
    (AlgHom.ext fun b => by
      change counit (R := R) (f (b : G'.A)) = counit (R := R) (b : G'.A)
      exact CoalgHomClass.counit_comp_apply f _)
    (AlgHom.ext fun b => i.incl2_injective (by
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
      rw [incl2_map φ (f : G'.A →ₐ[R] G.A) (fun _ => rfl), comul_Q, i'.incl2_comulQ, comul_Q,
        i.incl2_comulQ]
      exact (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) (b : G'.A))))

theorem quotientMap_apply (i : Hom H G) (i' : Hom H' G') (f : Hom G G') (g : Hom H H')
    (h : ∀ a, i (f a) = g (i' a)) (b : i'.quotient.A) :
    Subtype.val (show i.invariants from quotientMap i i' f g h b) =
      f (Subtype.val (show i'.invariants from b)) := rfl

/-! ### A retraction `A → B` -/

/-- A finite free algebra `A` over `B` with `B → A` injective has a `B`-linear retraction
`φ : A → B`, `φ(1) = 1` (Nakayama: `1 ∉ m A` for every maximal ideal `m` of `B`). -/
theorem exists_retraction {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] (hinj : Function.Injective (algebraMap B A)) :
    ∃ φ : A →ₗ[B] B, φ 1 = 1 := by
  classical
  let b := Module.Free.chooseBasis B A
  let β := fun k => b.coord k 1
  have hI : Ideal.span (Set.range β) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hβ : ∀ k, β k ∈ m := fun k => hle (Ideal.subset_span ⟨k, rfl⟩)
    have htop : (⊤ : Submodule B A) ≤ m • ⊤ := by
      intro x _
      have hx : x = ∑ k, β k • (x * b k) := by
        conv_lhs => rw [← mul_one x, ← b.sum_repr 1]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_smul_comm]
        rfl
      rw [hx]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul (hβ k) Submodule.mem_top
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
      Module.Finite.fg_top htop
    have h1 : r = 0 := hinj (by
      rw [map_zero, Algebra.algebraMap_eq_smul_one]
      exact hr0 1 Submodule.mem_top)
    rw [h1, zero_sub, neg_mem_iff] at hr
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr hr)
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hI ▸ Submodule.mem_top :
    (1 : B) ∈ Ideal.span (Set.range β))
  refine ⟨∑ k, γ k • b.coord k, ?_⟩
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact hγ

/-! ### `K ⊆ H ⊆ G`: the closed immersion `H/K → G/K` -/

variable [IsLocalRing R] {K : FFGroupScheme R}

omit [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] in
/-- Traces are compatible with `i : H → G`: `i ∘ tr_t^{G,K} = tr_t^{H,K} ∘ i`. -/
theorem apply_trace_comp (i : Hom H G) (k : Hom K H) (t : K.A →ₗ[R] R) (a : G.A) :
    i (trace (k.comp i : Hom K G) t a) = k.trace t (i a) := by
  have key : ∀ w : G.A ⊗[R] G.A, i (TensorProduct.rid R G.A (t.lTensor G.A
      (TensorProduct.map LinearMap.id ((k.comp i : Hom K G) : G.A →ₗ[R] K.A) w))) =
      TensorProduct.rid R H.A (t.lTensor H.A (TensorProduct.map LinearMap.id
        (k : H.A →ₗ[R] K.A) (TensorProduct.map (i : G.A →ₗ[R] H.A) (i : G.A →ₗ[R] H.A) w))) := by
    intro w
    induction w with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => simp
  have hi : comul (R := R) (i a) = TensorProduct.map (i : G.A →ₗ[R] H.A)
      (i : G.A →ₗ[R] H.A) (comul a) :=
    (LinearMap.congr_fun (CoalgHomClass.map_comp_comul i) a).symm
  rw [trace_apply, trace_apply, coact_apply, coact_apply, key, hi]

/-- The homomorphism `H/K → G/K` (the restriction `A^K → C^K` of `i`). -/
def subQuot (i : Hom H G) (k : Hom K H) : Hom k.quotient (quotient (k.comp i : Hom K G)) :=
  quotientMap k (k.comp i) i (BialgHom.id R K.A) fun _ => rfl

/-- **`H/K → G/K` is a closed immersion**: `A^K → C^K` is surjective. -/
theorem surjective_subQuot {i : Hom H G} {k : Hom K H} (hi : Function.Surjective i)
    (hk : Function.Surjective k) : Function.Surjective (subQuot i k) := by
  set iK : Hom K G := k.comp i
  have hiK : Function.Surjective iK := hk.comp hi
  obtain ⟨b⟩ := nonempty_basis_invariants hiK
  have : Module.Free iK.invariants G.A := .of_basis b
  obtain ⟨φ, hφ⟩ := exists_retraction (B := iK.invariants) (A := G.A) Subtype.val_injective
  obtain ⟨ι, _, t, S, ht, hS⟩ := iK.exists_dualBasisData hiK
  let e : ι → G.A := fun j => ∑ s ∈ S j, (φ s.1 : G.A) * s.2
  have hφe : ∀ a, (φ a : G.A) = ∑ j, iK.trace (t j) (e j * a) := by
    intro a
    conv_lhs => rw [← iK.sum_sum_mul_trace hS a]
    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hmem := iK.trace_mem (ht j) (s.2 * a)
    have : s.1 * iK.trace (t j) (s.2 * a) =
        (⟨iK.trace (t j) (s.2 * a), hmem⟩ : iK.invariants) • s.1 := by
      rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
    rw [this, map_smul, smul_eq_mul, Subalgebra.coe_mul, mul_assoc,
      iK.trace_mul (t j) (φ s.1).2]
    exact mul_comm _ _
  intro c
  set cv : H.A := Subtype.val (show k.invariants from c) with hcv
  have hc : cv ∈ k.invariants := (show k.invariants from c).2
  obtain ⟨a, ha⟩ := hi cv
  have hT : ∀ t a, i (iK.trace t a) = k.trace t (i a) := fun t a => apply_trace_comp i k t a
  have key : i (∑ j, iK.trace (t j) (e j * a)) = cv := by
    rw [map_sum]
    simp_rw [hT, map_mul, ha]
    have h1 : ∀ j, k.trace (t j) (i (e j) * cv) = cv * k.trace (t j) (i (e j)) := by
      intro j
      rw [mul_comm, k.trace_mul (t j) hc]
    simp_rw [h1, ← Finset.mul_sum, ← hT, ← map_sum]
    have h2 : ∑ j, iK.trace (t j) (e j) = 1 := by
      have := hφe 1
      simp only [mul_one] at this
      rw [← this, hφ]
      rfl
    rw [h2, map_one, mul_one]
  exact ⟨show iK.invariants from
    ⟨∑ j, iK.trace (t j) (e j * a), Subalgebra.sum_mem _ fun j _ => iK.trace_mem (ht j) _⟩,
    Subtype.ext key⟩

/-! ### The third isomorphism theorem on points -/

/-- The homomorphism `G/K → G/H` (the inclusion `A^H ⊆ A^K`). -/
def quotQuot (i : Hom H G) (k : Hom K H) : Hom (quotient (k.comp i : Hom K G)) i.quotient :=
  quotientMap (k.comp i) i (BialgHom.id R G.A) k fun _ => rfl

omit [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R] in
theorem mapPoints_eq_one_iff {G₁ G₂ : FFGroupScheme R} (f : Hom G₁ G₂) {S : Type*} [CommRing S]
    [Algebra R S] (y : G₁.points S) :
    f.mapPoints S y = 1 ↔ ∀ x, ofConv y (f x) = algebraMap R S (counit (R := R) x) := by
  constructor
  · intro h x
    exact congrArg (fun z : G₂.points S => (ofConv z : G₂.A →ₐ[R] S) x) h
  · intro h
    apply WithConv.ofConv_injective
    ext x
    exact h x

omit [IsLocalRing R] in
/-- **`(A^K)^{H/K} = A^H`** inside `A`. -/
theorem mem_invariants_subQuot_iff (i : Hom H G) (k : Hom K H)
    (b : invariants (k.comp i : Hom K G)) :
    (show (quotient (k.comp i : Hom K G)).A from b) ∈ (subQuot i k).invariants ↔
      (b : G.A) ∈ i.invariants := by
  let Φ : invariants (k.comp i : Hom K G) ⊗[R] k.invariants →ₗ[R] G.A ⊗[R] H.A :=
    TensorProduct.map (invariants (k.comp i : Hom K G)).val.toLinearMap k.invariants.val.toLinearMap
  have hΦ : Function.Injective Φ :=
    TensorProduct.map_injective_of_flat_flat (R := R) _ _ Subtype.val_injective
      Subtype.val_injective
  let ψ : invariants (k.comp i : Hom K G) →ₗ[R] k.invariants :=
    ((subQuot i k : Hom k.quotient (quotient (k.comp i : Hom K G))) :
      (quotient (k.comp i : Hom K G)).A →ₗ[R] k.quotient.A)
  have hlin : Φ ∘ₗ TensorProduct.map LinearMap.id ψ =
      TensorProduct.map LinearMap.id (i : G.A →ₗ[R] H.A) ∘ₗ
        (incl2 (k.comp i : Hom K G)).toLinearMap :=
    TensorProduct.ext' fun x y => rfl
  have h2 : Φ ((subQuot i k).coact (show (quotient (k.comp i : Hom K G)).A from b)) =
      i.coact (b : G.A) := by
    have := LinearMap.congr_fun hlin (comulQ (k.comp i : Hom K G) b)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, incl2_comulQ] at this
    exact this
  rw [mem_invariants, mem_invariants]
  constructor
  · intro h
    rw [← h2, h]
    rfl
  · intro h
    apply hΦ
    rw [h2, h]
    rfl

/-- **Third isomorphism theorem on points**: a point of `G/K` maps to `1` in `G/H` iff it comes
from `H/K`. -/
theorem mapPoints_quotQuot_eq_one_iff {i : Hom H G} {k : Hom K H} (hi : Function.Surjective i)
    (hk : Function.Surjective k) {S : Type*} [CommRing S] [Algebra R S]
    (y : (quotient (k.comp i : Hom K G)).points S) :
    (quotQuot i k).mapPoints S y = 1 ↔
      ∃ z : k.quotient.points S, (subQuot i k).mapPoints S z = y := by
  rw [← mapPoints_quotientHom_eq_one_iff (surjective_subQuot hi hk), mapPoints_eq_one_iff,
    mapPoints_eq_one_iff]
  constructor
  · intro h x
    have hx := (mem_invariants_subQuot_iff i k (show invariants (k.comp i : Hom K G) from
      Subtype.val (show (subQuot i k).invariants from x))).mp
      (show (subQuot i k).invariants from x).2
    exact h (show i.invariants from ⟨_, hx⟩)
  · intro h x
    have hx := (mem_invariants_subQuot_iff i k (show invariants (k.comp i : Hom K G) from
      ⟨Subtype.val (show i.invariants from x), (Hom.map_mem_invariants (k.comp i) i
        (BialgHom.id R G.A) k (fun _ => rfl) (show i.invariants from x).2)⟩)).mpr
      (show i.invariants from x).2
    exact h (show (subQuot i k).invariants from ⟨_, hx⟩)

end Hom

end FFGroupScheme

end PadicHodge
