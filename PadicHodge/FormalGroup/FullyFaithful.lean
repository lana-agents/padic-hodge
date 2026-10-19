/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.SubPDiv
import PadicHodge.GroupScheme.Product
import PadicHodge.FormalGroup.GenericIso
import PadicHodge.FormalGroup.OLFraction
import PadicHodge.GroupScheme.GaloisDescent
import PadicHodge.TateSen.Invariants

/-!
# [Hong, Thm. 3.5.4] (Tate): the generic fibre functor is fully faithful over `O_{K'}`

For `p`-divisible groups `G`, `H` over `O_L` (`L/ℚ_p` finite), every homomorphism
`f̃ : G_L → H_L` extends uniquely to `f : G → H` (`PDivGroup.Hom.baseChange_bijective_OL`).

[Hong, proof of Thm. 3.5.4]: the graph `Γ(f̃) : G_L → (G × H)_L` (`PDivGroup.Hom.graph`, a
levelwise closed immersion) extends by [Hong, Prop. 3.5.3] (`exists_pdivGroup_closure`,
generic-fibre form, so
[Hong, Prop. 2.1.14] is not needed) to `ι : G' → G × H`; `π₁ ∘ ι` is bijective on
`ℚ̄_p`-points, hence an isomorphism by [Hong, Lemma 3.5.2]
(`bijective_of_mapPoints_bijective_OL`), and `f = π₂ ∘ ι ∘ (π₁ ∘ ι)⁻¹` extends `f̃` (checked on
`ℚ̄_p`-points, `Hom.ext_of_mapTate`). Uniqueness is `Hom.ext_of_baseChange`.

* `FFGroupScheme.graphBC φ : X_S → (X × Y)_S` for `φ : X_S → Y_S`, `z ↦ (z, φ z)`;
* `PDivGroup.Hom.graph`, `PDivGroup.Hom.inv` (levelwise bijective homomorphisms are invertible).

**[Hong, Cor. 3.5.5]** (`PDivGroup.Hom.mapTate_bijective_OL`): `Hom(G, H) → Hom_{ℤ_p[Γ_L]}(T_p G,
T_p H)` is bijective: Thm. 3.5.4 and the fullness of `T_p` over `L` ([Hong, Prop. 2.1.14],
`exists_hom_of_galTate`, Galois descent in `GaloisDescent.lean`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Thm. 3.5.4 and its proof, Cor. 3.5.5.
-/

noncomputable section

open Coalgebra HopfAlgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace FFGroupScheme

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] {X Y : FFGroupScheme R}

/-- The algebra map of the graph: `S ⊗ (A ⊗ B) → S ⊗ A`, `s ⊗ a ⊗ b ↦ (s ⊗ a) φ(1 ⊗ b)`. -/
def graphAlg (φ : Hom (X.baseChange S) (Y.baseChange S)) :
    S ⊗[R] (X.A ⊗[R] Y.A) →ₐ[S] S ⊗[R] X.A :=
  Algebra.TensorProduct.lift (Algebra.ofId S _)
    (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight : X.A →ₐ[R] S ⊗[R] X.A)
      (((φ : S ⊗[R] Y.A →ₐ[S] S ⊗[R] X.A).restrictScalars R).comp
        Algebra.TensorProduct.includeRight) (fun _ _ => .all _ _))
    (fun _ _ => .all _ _)

theorem graphAlg_tmul (φ : Hom (X.baseChange S) (Y.baseChange S)) (s : S) (a : X.A) (b : Y.A) :
    graphAlg φ (s ⊗ₜ (a ⊗ₜ b)) = algebraMap S _ s * ((1 ⊗ₜ a) * φ (1 ⊗ₜ b)) := rfl

/-- The points of the graph: `z ↦ (z, φ z)`. -/
theorem graphAlg_points (φ : Hom (X.baseChange S) (Y.baseChange S)) (T : Type*) [CommRing T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (z : (X.baseChange S).points T) :
    (X.prod Y).baseChangePointsEquiv T (toConv ((ofConv z).comp (graphAlg φ))) =
      (X.prodPointsEquiv Y T).symm
        (X.baseChangePointsEquiv T z, Y.baseChangePointsEquiv T (φ.mapPoints T z)) := by
  apply WithConv.ofConv_injective
  apply Algebra.TensorProduct.ext'
  intro a b
  change ofConv z (graphAlg φ (1 ⊗ₜ (a ⊗ₜ b))) = ofConv z (1 ⊗ₜ a) * ofConv z (φ (1 ⊗ₜ b))
  rw [graphAlg_tmul, map_one, one_mul, map_mul]

/-- **The graph `Γ(φ) : X_S → (X × Y)_S`** of `φ : X_S → Y_S`. -/
def graphBC (φ : Hom (X.baseChange S) (Y.baseChange S)) :
    Hom (X.baseChange S) ((X.prod Y).baseChange S) :=
  homOfPoints (graphAlg φ)
    (fun T _ _ z z' => by
      letI : Algebra R T := Algebra.compHom T (algebraMap R S)
      haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
      apply ((X.prod Y).baseChangePointsEquiv (S := S) T).injective
      rw [map_mul, graphAlg_points, graphAlg_points, graphAlg_points,
        ← map_mul (X.prodPointsEquiv Y T).symm, Prod.mk_mul_mk, map_mul, map_mul, map_mul])
    (by
      apply ((X.prod Y).baseChangePointsEquiv (S := S) S).injective
      rw [graphAlg_points, map_one, map_one, map_one, Prod.mk_one_one, map_one, map_one])

theorem graphBC_points (φ : Hom (X.baseChange S) (Y.baseChange S)) (T : Type*) [CommRing T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] (z : (X.baseChange S).points T) :
    (X.prodPointsEquiv Y T) ((X.prod Y).baseChangePointsEquiv T ((graphBC φ).mapPoints T z)) =
      (X.baseChangePointsEquiv T z, Y.baseChangePointsEquiv T (φ.mapPoints T z)) := by
  rw [← MulEquiv.eq_symm_apply]
  exact graphAlg_points φ T z

theorem graphBC_surjective (φ : Hom (X.baseChange S) (Y.baseChange S)) :
    Function.Surjective (graphBC φ) := by
  intro c
  induction c using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | tmul s a =>
    refine ⟨s ⊗ₜ (a ⊗ₜ 1), ?_⟩
    change graphAlg φ (s ⊗ₜ (a ⊗ₜ 1)) = _
    have h1 : φ (1 ⊗ₜ 1) = 1 := map_one φ
    rw [graphAlg_tmul, h1, mul_one,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one]
    rfl

end FFGroupScheme

namespace PDivGroup

open FFGroupScheme

variable {R : Type u} [CommRing R] [Nontrivial R] {p : ℕ}

/-- **The graph `Γ(φ) : G_S → (G × H)_S`** of a homomorphism `φ : G_S → H_S`. -/
def Hom.graph {S : Type u} [CommRing S] [Algebra R S] [Nontrivial S] {G H : PDivGroup R p}
    (φ : Hom (G.baseChange S) (H.baseChange S)) :
    Hom (G.baseChange S) ((G.prod H).baseChange S) where
  f v := graphBC (φ.f v)
  comm v := FFGroupScheme.Hom.ext_points fun T _ _ x => by
    letI : Algebra R T := Algebra.compHom T (algebraMap R S)
    haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    change (graphBC (φ.f (v + 1))).mapPoints T ((baseChangeHom S (G.incl v)).mapPoints T x) =
      (baseChangeHom S (prodMap (G.incl v) (H.incl v))).mapPoints T
        ((graphBC (φ.f v)).mapPoints T x)
    apply (((G.G (v + 1)).prod (H.G (v + 1))).baseChangePointsEquiv (S := S) T).injective
    apply ((G.G (v + 1)).prodPointsEquiv (H.G (v + 1)) T).injective
    rw [graphBC_points, baseChangePointsEquiv_mapPoints ((G.G v).prod (H.G v)) T
      (prodMap (G.incl v) (H.incl v)), prodPointsEquiv_mapPoints, graphBC_points]
    refine Prod.ext rfl ?_
    change (H.G (v + 1)).baseChangePointsEquiv T ((φ.f (v + 1)).mapPoints T
        (((G.baseChange S).incl v).mapPoints T x)) =
      (H.G (v + 1)).baseChangePointsEquiv T (((H.baseChange S).incl v).mapPoints T
        ((φ.f v).mapPoints T x))
    rw [φ.incl_mapPoints]

theorem Hom.graph_surjective {S : Type u} [CommRing S] [Algebra R S] [Nontrivial S]
    {G H : PDivGroup R p} (φ : Hom (G.baseChange S) (H.baseChange S)) (v : ℕ) :
    Function.Surjective (φ.graph.f v) :=
  graphBC_surjective (φ.f v)

omit [Nontrivial R] in
/-- **The inverse** of a homomorphism of `p`-divisible groups which is bijective at every level. -/
def Hom.inv {G H : PDivGroup R p} (ρ : Hom G H) (hρ : ∀ v, Function.Bijective (ρ.f v)) :
    Hom H G where
  f v := ((BialgEquiv.ofBijective (ρ.f v) (hρ v)).symm : (G.G v).A →ₐc[R] (H.G v).A)
  comm v := BialgHom.ext fun a => (hρ v).1 (by
    have h := congrArg (fun φ : (H.G (v + 1)).A →ₐc[R] (G.G v).A =>
      φ ((BialgEquiv.ofBijective (ρ.f (v + 1)) (hρ (v + 1))).symm a)) (ρ.comm v)
    change G.incl v (ρ.f (v + 1) _) = ρ.f v (H.incl v _) at h
    change ρ.f v (H.incl v ((BialgEquiv.ofBijective (ρ.f (v + 1)) (hρ (v + 1))).symm a)) =
      ρ.f v ((BialgEquiv.ofBijective (ρ.f v) (hρ v)).symm (G.incl v a))
    rw [← h]
    have e1 : ρ.f (v + 1) ((BialgEquiv.ofBijective (ρ.f (v + 1)) (hρ (v + 1))).symm a) = a :=
      (BialgEquiv.ofBijective (ρ.f (v + 1)) (hρ (v + 1))).apply_symm_apply a
    have e2 : ρ.f v ((BialgEquiv.ofBijective (ρ.f v) (hρ v)).symm (G.incl v a)) = G.incl v a :=
      (BialgEquiv.ofBijective (ρ.f v) (hρ v)).apply_symm_apply _
    rw [e1, e2])

omit [Nontrivial R] in
theorem Hom.mapPoints_inv {G H : PDivGroup R p} (ρ : Hom G H)
    (hρ : ∀ v, Function.Bijective (ρ.f v)) (v : ℕ) {T : Type*} [CommRing T] [Algebra R T]
    (x : (H.G v).points T) : (ρ.f v).mapPoints T (((ρ.inv hρ).f v).mapPoints T x) = x := by
  apply WithConv.ofConv_injective
  ext b
  change ofConv x ((BialgEquiv.ofBijective (ρ.f v) (hρ v)).symm (ρ.f v b)) = ofConv x b
  have : (BialgEquiv.ofBijective (ρ.f v) (hρ v)).symm (ρ.f v b) = b :=
    (BialgEquiv.ofBijective (ρ.f v) (hρ v)).symm_apply_apply b
  rw [this]

variable [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L]

local notation "K" => PadicAlgCl p

/-- **[Hong, Thm. 3.5.4] (Tate) over `O_L`**: the generic fibre functor on `p`-divisible groups
over `O_L` is fully faithful, `Hom(G, H) → Hom(G_L, H_L)` is bijective. -/
theorem Hom.baseChange_bijective_OL {G H : PDivGroup (OL L) p} :
    Function.Bijective (fun f : Hom G H => Hom.baseChange (S := L) f) := by
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hLK : Function.Injective (algebraMap L K) := (algebraMap L K).injective
  refine ⟨fun f g h => Hom.ext_of_baseChange K hpK OL.algebraMap_qbar_injective L h,
    fun φ => ?_⟩
  obtain ⟨G', ι, -, he⟩ := PDivGroup.Hom.exists_pdivGroup_closure φ.graph φ.graph_surjective K hpK
  choose e he using he
  -- `ρ = π₁ ∘ ι` and `π₂ ∘ ι` on `ℚ̄_p`-points
  let ρ : Hom G' G := (PDivGroup.fst G H).comp ι
  have key : ∀ v (y : (G'.G v).points K),
      (ρ.f v).mapPoints K y = (G.G v).baseChangePointsEquiv K (e v y) ∧
        ((PDivGroup.snd G H).f v).mapPoints K ((ι.f v).mapPoints K y) =
          (H.G v).baseChangePointsEquiv K ((φ.f v).mapPoints K (e v y)) := by
    intro v y
    have h : (G.G v).prodPointsEquiv (H.G v) K ((ι.f v).mapPoints K y) =
        ((G.G v).baseChangePointsEquiv K (e v y),
          (H.G v).baseChangePointsEquiv K ((φ.f v).mapPoints K (e v y))) := by
      rw [he]
      exact graphBC_points (φ.f v) K (e v y)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have hρpts : ∀ v, Function.Bijective ((ρ.f v).mapPoints K) := by
    intro v
    have : ⇑((ρ.f v).mapPoints K) = (G.G v).baseChangePointsEquiv K ∘ e v :=
      funext fun y => (key v y).1
    rw [this]
    exact (MulEquiv.bijective _).comp (e v).bijective
  have hρ : ∀ v, Function.Bijective (ρ.f v) := ρ.bijective_of_mapPoints_bijective_OL hρpts
  -- `f = π₂ ∘ ι ∘ ρ⁻¹`
  refine ⟨(PDivGroup.snd G H).comp (ι.comp (ρ.inv hρ)), ?_⟩
  refine Hom.ext_of_mapTate K hpK hLK fun x => Subtype.ext (funext fun v => ?_)
  apply ((H.G v).baseChangePointsEquiv (S := L) K).injective
  set w := (G.G v).baseChangePointsEquiv (S := L) K (x.1 v) with hw
  set y := ((ρ.inv hρ).f v).mapPoints K w
  have hy : (ρ.f v).mapPoints K y = w := ρ.mapPoints_inv hρ v w
  have hey : e v y = x.1 v := by
    apply ((G.G v).baseChangePointsEquiv (S := L) K).injective
    rw [← (key v y).1, hy]
  change ((PDivGroup.snd G H).f v).mapPoints K ((ι.f v).mapPoints K y) = _
  rw [(key v y).2, hey]
  rfl

/-- `Hom_{ℤ_p[Γ_L]}(T_p G, T_p H)`: the `Γ_L`-equivariant homomorphisms of the Tate modules
`T_p G(ℚ̄_p) = T_p(G_L)(ℚ̄_p)`. -/
def GalTateHom (G H : PDivGroup (OL L) p) : Type :=
  {τ : (G.baseChange L).TateModule K →* (H.baseChange L).TateModule K //
    ∀ (σ : K ≃ₐ[L] K) x, τ ((G.baseChange L).galTate σ x) = (H.baseChange L).galTate σ (τ x)}

/-- **[Hong, Cor. 3.5.5] over `O_L`**: `Hom(G, H) → Hom_{ℤ_p[Γ_L]}(T_p G, T_p H)` is
bijective. -/
theorem Hom.mapTate_bijective_OL {G H : PDivGroup (OL L) p} :
    Function.Bijective (fun f : Hom G H => (⟨(Hom.baseChange (S := L) f).mapTate K,
      fun σ x => Hom.mapTate_galTate _ σ x⟩ : GalTateHom G H)) := by
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hLK : Function.Injective (algebraMap L K) := (algebraMap L K).injective
  refine ⟨fun f g h => Hom.baseChange_bijective_OL.1 ?_, fun τ => ?_⟩
  · have h' := congrArg Subtype.val h
    exact Hom.ext_of_mapTate K hpK hLK fun x => DFunLike.congr_fun h' x
  · obtain ⟨φ, hφ⟩ := exists_hom_of_galTate (F := L) τ.1 τ.2
    obtain ⟨f, hf⟩ := (Hom.baseChange_bijective_OL (G := G) (H := H)).2 φ
    refine ⟨f, Subtype.ext (MonoidHom.ext fun x => ?_)⟩
    change (Hom.baseChange (S := L) f).mapTate K x = τ.1 x
    have hf' : Hom.baseChange (S := L) f = φ := hf
    rw [hf', hφ]

end PDivGroup

end PadicHodge
