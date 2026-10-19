/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.QuotientPoints
import PadicHodge.GroupScheme.Product
import PadicHodge.GroupScheme.ConstPDivTate
import PadicHodge.GroupScheme.TateFree
import PadicHodge.GroupScheme.Faithful
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Galois descent for homomorphisms of étale group schemes over a field `F ⊆ ℚ̄_p`

The fullness part of [Hong, Prop. 2.1.14] (via [Hong, Prop. 1.3.1]): over a field `F` with
`ℚ̄_p / F` Galois, Galois-equivariant homomorphisms of points come from homomorphisms of group
schemes.

* `FFGroupScheme.exists_eq_of_equivariant`: for `G` killed by `n` (`n ≠ 0` in `ℚ̄_p`), a
  `Γ_F`-equivariant function `G(ℚ̄_p) → ℚ̄_p` is evaluation at an element of `O(G)`
  (`ℚ̄_p ⊗_F O(G) ≅ Map(G(ℚ̄_p), ℚ̄_p)`, `evAll_bijective`, and `(ℚ̄_p)^{Γ_F} = F`);
* `FFGroupScheme.homOfEquivariant`: a `Γ_F`-equivariant group homomorphism
  `G(ℚ̄_p) → H(ℚ̄_p)` is induced by a unique homomorphism `G → H`;
* `PDivGroup.TateModule.exists_pow_eq_of_val_eq_one`: `ker(T_p G → G_v) = p^v T_p G`;
* **`PDivGroup.exists_hom_of_galTate`**: a `Γ_F`-equivariant homomorphism
  `T_p G(ℚ̄_p) → T_p H(ℚ̄_p)` is induced by a homomorphism `G → H` of `p`-divisible groups
  over `F`.

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 1.3.1, Prop. 2.1.14.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

/-! ### `ker(T_p G → G_v) = p^v T_p G` -/

namespace PDivGroup

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime] (G : PDivGroup R p)
  (S : Type u) [CommRing S] [Algebra R S]

/-- **`ker(T_p G(S) → G_v(S)) = p^v T_p G(S)`** (when `T_p G(S) ≅ ℤ_p^h` through
`exists_tateEquiv`). -/
theorem TateModule.exists_pow_eq_of_val_eq_one
    (hsurj : ∀ v, Function.Surjective ((G.quot v).mapPoints S))
    (hcard : ∀ w, Nat.card ((G.G w).points S) = p ^ (G.height * w))
    (x : G.TateModule S) (v : ℕ) (hx : x.1 v = 1) : ∃ y : G.TateModule S, y ^ (p ^ v) = x := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨e, he⟩ := G.exists_basis_level_one S (by rw [hcard, mul_one])
  choose t ht using fun i => TateModule.proj_surjective G S hsurj 1 (e i)
  have hbasis : ∀ d : Fin G.height → ℕ, (∀ i, d i < p) → ∏ i, ((t i).1 1) ^ d i = 1 →
      ∀ i, d i = 0 := by
    intro d hd hprod
    apply he d hd
    simpa [← ht] using hprod
  obtain ⟨a, rfl⟩ := (G.phi_bijective S t hcard rfl hbasis).2 x
  have h1 := G.phiLevel_injective S t hbasis v
    (((G.phi_apply S t a v).symm.trans hx).trans (map_one _).symm)
  have hb : ∀ i, ∃ b : ℤ_[p], Multiplicative.toAdd a i = (p : ℤ_[p]) ^ v * b := by
    intro i
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) i
    simp only [toAdd_ofAdd, toAdd_one, Pi.zero_apply] at h2
    have : Multiplicative.toAdd a i ∈ RingHom.ker (PadicInt.toZModPow (p := p) v) := h2
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at this
    exact this
  choose b hb using hb
  refine ⟨G.phi S t (Multiplicative.ofAdd b), ?_⟩
  rw [← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, Pi.smul_apply, hb i, nsmul_eq_mul, Nat.cast_pow, toAdd_ofAdd]

end PDivGroup

namespace FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {F : Type} [Field F] [Algebra F (PadicAlgCl p)]

local notation "Ω" => PadicAlgCl p

/-! ### Points as functions -/

section Points

variable (G : FFGroupScheme F)

/-- The `Ω`-linear extension `Ω ⊗_F O(G) → Ω` of a point `x`. -/
def ptHat (x : G.points Ω) : Ω ⊗[F] G.A →ₐ[Ω] Ω :=
  Algebra.TensorProduct.lift (Algebra.ofId Ω Ω) (ofConv x) (fun _ _ => .all _ _)

theorem ptHat_tmul (x : G.points Ω) (k : Ω) (a : G.A) :
    G.ptHat x (k ⊗ₜ a) = k * ofConv x a := by
  simp [ptHat]

theorem eq_ptHat (y : Ω ⊗[F] G.A →ₐ[Ω] Ω) :
    y = G.ptHat (toConv ((y.restrictScalars F).comp Algebra.TensorProduct.includeRight)) := by
  apply Algebra.TensorProduct.ext'
  intro k a
  rw [ptHat_tmul]
  change y (k ⊗ₜ a) = k * y (1 ⊗ₜ a)
  rw [← smul_eq_mul, ← map_smul, smul_tmul', smul_eq_mul, mul_one]

/-- `Ω ⊗_F O(G) → Map(G(Ω), Ω)`. -/
def evAll : Ω ⊗[F] G.A →ₐ[Ω] (G.points Ω → Ω) :=
  AlgHom.pi fun x => G.ptHat x

/-- `σ ⊗ 1` on `Ω ⊗_F O(G)`. -/
def galSemi (σ : Ω ≃ₐ[F] Ω) : Ω ⊗[F] G.A →ₐ[F] Ω ⊗[F] G.A :=
  Algebra.TensorProduct.map (σ : Ω →ₐ[F] Ω) (AlgHom.id F G.A)

theorem ptHat_galSemi (σ : Ω ≃ₐ[F] Ω) (x : G.points Ω) (c : Ω ⊗[F] G.A) :
    G.ptHat x (G.galSemi σ c) = σ (G.ptHat (galPoints G σ⁻¹ x) c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' h h' => rw [map_add, map_add, map_add, h, h']; exact (map_add _ _ _).symm
  | tmul k a =>
    change G.ptHat x (σ k ⊗ₜ a) = σ (G.ptHat (galPoints G σ⁻¹ x) (k ⊗ₜ a))
    rw [ptHat_tmul, ptHat_tmul, map_mul]
    congr 1
    change _ = σ (σ⁻¹ (ofConv x a))
    rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

variable {G} {n : ℕ} (hn : (n : PadicAlgCl p) ≠ 0) (hG : G.KilledBy n)

include hn hG

theorem eq_of_ptHat_eq {c c' : Ω ⊗[F] G.A} (h : ∀ x : G.points Ω, G.ptHat x c = G.ptHat x c') :
    c = c' := by
  have : Algebra.Etale Ω (Ω ⊗[F] G.A) := hG.isEtale_baseChange Ω hn
  exact eq_of_forall_algHom_eq fun y => by rw [G.eq_ptHat y]; exact h _

/-- **Points separate the elements of `O(G)`.** -/
theorem eq_of_points_eq {a a' : G.A} (h : ∀ x : G.points Ω, ofConv x a = ofConv x a') :
    a = a' := by
  apply Algebra.TensorProduct.includeRight_injective (A := Ω) (R := F) (algebraMap F Ω).injective
  refine eq_of_ptHat_eq hn hG fun x => ?_
  change G.ptHat x (1 ⊗ₜ a) = G.ptHat x (1 ⊗ₜ a')
  rw [ptHat_tmul, ptHat_tmul, h]

/-- **`Ω ⊗_F O(G) ≅ Map(G(Ω), Ω)`.** -/
theorem evAll_bijective : Function.Bijective (G.evAll (p := p)) := by
  have hcard := hG.card_points Ω hn
  have : Nontrivial G.A := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg (counit (R := F) (A := G.A)) h
    rw [map_zero, Bialgebra.counit_one] at this
    exact zero_ne_one this
  have hpos : 0 < G.order := Module.finrank_pos
  have : Finite (G.points Ω) := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype (G.points Ω) := Fintype.ofFinite _
  have hinj : Function.Injective (G.evAll (p := p)) := fun c c' h =>
    eq_of_ptHat_eq hn hG fun x => congrFun h x
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank Ω (Ω ⊗[F] G.A) = Module.finrank Ω (G.points Ω → Ω) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
      hcard]
    rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (G.evAll (p := p)).toLinearMap)).mp hinj

/-- **Galois descent**: a `Γ_F`-equivariant function `G(Ω) → Ω` is evaluation at an element of
`O(G)`. -/
theorem exists_eq_of_equivariant [IsGalois F Ω] (Fn : G.points Ω → Ω)
    (hF : ∀ (σ : Ω ≃ₐ[F] Ω) x, Fn (galPoints G σ x) = σ (Fn x)) :
    ∃ a : G.A, ∀ x : G.points (PadicAlgCl p), ofConv x a = Fn x := by
  obtain ⟨c, hc⟩ := (evAll_bijective hn hG).2 Fn
  have hc' : ∀ x, G.ptHat x c = Fn x := fun x => congrFun hc x
  have hfix : ∀ σ : Ω ≃ₐ[F] Ω, G.galSemi σ c = c := by
    intro σ
    refine eq_of_ptHat_eq hn hG fun x => ?_
    rw [ptHat_galSemi, hc', hc', hF, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  classical
  let b := Module.finBasis F G.A
  let B := Algebra.TensorProduct.basis Ω b
  let k := B.repr c
  have hcsum : c = ∑ i, k i • B i := (B.sum_repr c).symm
  have hk : ∀ σ : Ω ≃ₐ[F] Ω, ∀ i, σ (k i) = k i := by
    intro σ
    have h1 : G.galSemi σ c = ∑ i, σ (k i) • B i := by
      conv_lhs => rw [hcsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.TensorProduct.basis_apply, smul_tmul', smul_tmul', smul_eq_mul, smul_eq_mul,
        mul_one, mul_one]
      rfl
    have h2 := congrArg B.repr (h1.symm.trans (hfix σ))
    intro i
    have h3 := DFunLike.congr_fun h2 i
    rw [B.repr_sum_self] at h3
    exact h3
  choose l hl using fun i => (InfiniteGalois.mem_range_algebraMap_iff_fixed (k i)).mpr
    fun σ => hk σ i
  refine ⟨∑ i, l i • b i, fun x => ?_⟩
  rw [← hc', hcsum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.TensorProduct.basis_apply, map_smul, ptHat_tmul, one_mul, ← hl i,
    smul_eq_mul, Algebra.smul_def]

end Points

/-! ### Homomorphisms from equivariant maps of points -/

section Hom

variable {G H : FFGroupScheme F}

theorem KilledBy.prod {n : ℕ} (hG : G.KilledBy n) (hH : H.KilledBy n) : (G.prod H).KilledBy n := by
  apply (G.prodPointsEquiv H (G.prod H).A).injective
  rw [map_pow, map_one, Prod.pow_def, hG.pow_eq_one, hH.pow_eq_one]
  rfl

variable {n : ℕ} (hn : (n : PadicAlgCl p) ≠ 0) (hG : G.KilledBy n) [IsGalois F (PadicAlgCl p)]
  (τ : G.points (PadicAlgCl p) →* H.points (PadicAlgCl p))
  (hτ : ∀ (σ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p) x, τ (galPoints G σ x) = galPoints H σ (τ x))

include hn hG hτ

theorem exists_algHom_of_equivariant :
    ∃ α : H.A →ₐ[F] G.A, ∀ (x : G.points (PadicAlgCl p)) b, ofConv x (α b) = ofConv (τ x) b := by
  have hF : ∀ b : H.A, ∃ a : G.A, ∀ x : G.points (PadicAlgCl p), ofConv x a = ofConv (τ x) b :=
    fun b =>
    exists_eq_of_equivariant hn hG (fun x => ofConv (τ x) b) fun σ x => by
      rw [hτ]
      rfl
  choose α hα using hF
  have ext : ∀ a a' : G.A, (∀ x : G.points (PadicAlgCl p), ofConv x a = ofConv x a') → a = a' :=
    fun a a' h => eq_of_points_eq hn hG h
  have h1 : α 1 = 1 := ext _ _ fun x => by rw [hα, map_one, map_one]
  have h2 : ∀ b b', α (b * b') = α b * α b' := fun b b' =>
    ext _ _ fun x => by rw [hα, map_mul, map_mul, hα, hα]
  have h3 : α 0 = 0 := ext _ _ fun x => by rw [hα, map_zero, map_zero]
  have h4 : ∀ b b', α (b + b') = α b + α b' := fun b b' =>
    ext _ _ fun x => by rw [hα, map_add, map_add, hα, hα]
  have h5 : ∀ r : F, α (algebraMap F H.A r) = algebraMap F G.A r := fun r =>
    ext _ _ fun x => by rw [hα, AlgHom.commutes, AlgHom.commutes]
  let αh : H.A →ₐ[F] G.A :=
    { toFun := α
      map_one' := h1
      map_mul' := h2
      map_zero' := h3
      map_add' := h4
      commutes' := h5 }
  exact ⟨αh, fun x b => hα b x⟩

/-- **The homomorphism `G → H` induced by a `Γ_F`-equivariant group homomorphism
`G(Ω) → H(Ω)`** ([Hong, Prop. 1.3.1], fullness). -/
def homOfEquivariant : Hom G H :=
  let α := (exists_algHom_of_equivariant hn hG τ hτ).choose
  have hα := (exists_algHom_of_equivariant hn hG τ hτ).choose_spec
  BialgHom.ofAlgHom α
    (AlgHom.ext fun b => (algebraMap F Ω).injective (by
      have h1 := hα 1 b
      rw [map_one] at h1
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.counitAlgHom_apply]
      exact h1))
    (AlgHom.ext fun b => by
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
      refine eq_of_points_eq hn (hG.prod hG) fun z => ?_
      obtain ⟨⟨x, y⟩, rfl⟩ := (G.prodPointsEquiv G Ω).symm.surjective z
      change Algebra.TensorProduct.lift (ofConv x) (ofConv y) (fun _ _ => .all _ _)
          (Algebra.TensorProduct.map α α (comul b)) =
        Algebra.TensorProduct.lift (ofConv x) (ofConv y) (fun _ _ => .all _ _) (comul (α b))
      rw [← AlgHom.convMul_apply, hα, map_mul, AlgHom.convMul_apply]
      have hx : ofConv (τ x) = (ofConv x).comp α := AlgHom.ext fun c => (hα x c).symm
      have hy : ofConv (τ y) = (ofConv y).comp α := AlgHom.ext fun c => (hα y c).symm
      rw [hx, hy]
      induction comul (R := F) b with
      | zero => simp
      | add u w hu hw => rw [map_add, map_add, map_add, hu, hw]
      | tmul u w => simp)

theorem mapPoints_homOfEquivariant (x : G.points Ω) :
    (homOfEquivariant hn hG τ hτ).mapPoints Ω x = τ x := by
  apply WithConv.ofConv_injective
  ext b
  exact (exists_algHom_of_equivariant hn hG τ hτ).choose_spec x b

end Hom

/-- Homomorphisms agreeing on `Ω`-points are equal (`G` killed by `n ≠ 0` in `Ω`). -/
theorem Hom.ext_of_points_qbar {G H : FFGroupScheme F} {n : ℕ} (hn : (n : Ω) ≠ 0)
    (hG : G.KilledBy n) {f g : Hom G H} (h : ∀ x, f.mapPoints Ω x = g.mapPoints Ω x) :
    f = g :=
  BialgHom.ext fun b => eq_of_points_eq hn hG fun x =>
    congrArg (fun z : H.points Ω => ofConv z b) (h x)

end FFGroupScheme

/-! ### `p`-divisible groups -/

namespace PDivGroup

open FFGroupScheme

variable {p : ℕ} [hp : Fact p.Prime] {F : Type} [Field F] [Algebra F (PadicAlgCl p)]
  [IsGalois F (PadicAlgCl p)]

local notation "Ω" => PadicAlgCl p

/-- **Fullness of `T_p` over `F`** ([Hong, Prop. 2.1.14]): a `Γ_F`-equivariant homomorphism
`T_p G(Ω) → T_p H(Ω)` is induced by a homomorphism of `p`-divisible groups `G → H`. -/
theorem exists_hom_of_galTate {G H : PDivGroup F p}
    (τ : G.TateModule Ω →* H.TateModule Ω)
    (hτ : ∀ (σ : Ω ≃ₐ[F] Ω) x, τ (G.galTate σ x) = H.galTate σ (τ x)) :
    ∃ f : Hom G H, ∀ x, f.mapTate Ω x = τ x := by
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hnv : ∀ v, ((p ^ v : ℕ) : Ω) ≠ 0 := fun v => by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hpΩ
  have hkill : ∀ (K : PDivGroup F p) v, (K.G v).KilledBy (p ^ v) := fun K v =>
    KilledBy.of_pow_eq_one fun S _ _ x => K.pow_eq_one v S x
  have hsurj := G.quot_surjective_sepClosed Ω hpΩ
  have hcard := G.card_points_sepClosed Ω hpΩ
  -- the level maps `τ_v`
  have hwd : ∀ v (x x' : G.TateModule Ω), x.1 v = x'.1 v → (τ x).1 v = (τ x').1 v := by
    intro v x x' h
    obtain ⟨y, hy⟩ := TateModule.exists_pow_eq_of_val_eq_one G Ω hsurj hcard (x * x'⁻¹) v
      (by rw [Subgroup.coe_mul, Pi.mul_apply, Subgroup.coe_inv, Pi.inv_apply, h,
        mul_inv_cancel])
    have : (τ x).1 v * ((τ x').1 v)⁻¹ = 1 := by
      have e : (τ (x * x'⁻¹)).1 v = ((τ y).1 v) ^ (p ^ v) := by
        rw [← hy, map_pow]
        rfl
      rw [H.pow_eq_one] at e
      rw [map_mul, map_inv] at e
      exact e
    exact mul_inv_eq_one.mp this
  choose lift hlift using fun v => G.proj_surjective_sepClosed Ω hpΩ v
  have hl : ∀ v b, (lift v b).1 v = b := hlift
  let τv : ∀ v, (G.G v).points Ω →* (H.G v).points Ω := fun v =>
    { toFun := fun z => (τ (lift v z)).1 v
      map_one' := by
        rw [hwd v (lift v 1) 1 (hl v 1), map_one]
        rfl
      map_mul' := fun z z' => by
        rw [hwd v (lift v (z * z')) (lift v z * lift v z') (by
          change (lift v (z * z')).1 v = (lift v z).1 v * (lift v z').1 v
          rw [hl, hl, hl]), map_mul]
        rfl }
  have hτv : ∀ v (x : G.TateModule Ω), τv v (x.1 v) = (τ x).1 v := fun v x =>
    hwd v _ _ (hl v _)
  have hequiv : ∀ v (σ : Ω ≃ₐ[F] Ω) z,
      τv v (galPoints (G.G v) σ z) = galPoints (H.G v) σ (τv v z) := by
    intro v σ z
    obtain ⟨x, rfl⟩ := G.proj_surjective_sepClosed Ω hpΩ v z
    change τv v ((G.galTate σ x).1 v) = galPoints (H.G v) σ (τv v (x.1 v))
    rw [hτv, hτv, hτ]
    rfl
  let f : ∀ v, FFGroupScheme.Hom (G.G v) (H.G v) := fun v =>
    homOfEquivariant (hnv v) (hkill G v) (τv v) (hequiv v)
  have hf : ∀ v z, (f v).mapPoints Ω z = τv v z := fun v z => mapPoints_homOfEquivariant _ _ _ _ z
  refine ⟨⟨f, fun v => ?_⟩, fun x => Subtype.ext (funext fun v => ?_)⟩
  · refine Hom.ext_of_points_qbar (hnv v) (hkill G v) fun z => ?_
    obtain ⟨x, rfl⟩ := G.proj_surjective_sepClosed Ω hpΩ v z
    change (f (v + 1)).mapPoints Ω ((G.incl v).mapPoints Ω (x.1 v)) =
      (H.incl v).mapPoints Ω ((f v).mapPoints Ω (x.1 v))
    rw [hf, hf, x.2 v, hτv, map_pow, hτv, (τ x).2 v]
  · change (f v).mapPoints Ω (x.1 v) = (τ x).1 v
    rw [hf, hτv]

end PDivGroup

end PadicHodge
