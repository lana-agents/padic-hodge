/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.DAlphaHT
import PadicHodge.FormalGroup.HeightIneq
import Mathlib.RingTheory.Flat.Localization

/-!
# Step (3.10) of Tate's proof and Tate's theorem for `F[p^∞]` over `ℤ_p`

Let `P` be a `p`-divisible formal group law of dimension `d` and height `h` over `ℤ_p`,
`G = F[p^∞]` and `V = V_p(G_{ℚ_p})`. By Serre–Tate the connected part of `G^∨` is `F'[p^∞]`
for a `p`-divisible formal group law `P'` of dimension `d'`, and `h ≤ d + d'`
(`PDivFGL.exists_connPart_dual_iso_height_le`, [Hong, Thm. 2.2.19]).

**Step (3.10)** of [Hong, proof of Thm. 3.4.10] ("switching the roles of `G` and `G^∨`"):
an injective `ℚ_p`-linear map `ℚ_p^{d'} ↪ D_0(V^∨) = Hom_{ℤ_p}(T_p G, ℂ_p)^Γ`
(`PDivFGL.dalphaDual`, `PDivFGL.dalphaDual_injective`). It is the composite of

* `dα_K` for `P'` with values in `D_{-1}(V_p(F'[p^∞]_{ℚ_p}))` (`dalphaKTwist`, (3.9) for `P'`);
* the twist-`0` map induced by the injective `G_{ℚ_p}`-equivariant `ℤ_p`-linear map
  `T_p(F'[p^∞]_{ℚ_p}) → T_p((G^∨)_{ℚ_p}) ≅ T_p((G_{ℚ_p})^∨)` coming from
  `F'[p^∞] ≅ (G^∨)⁰ ↪ G^∨` (`PDivGroup.Hom.tateLin`, `PDivGroup.Hom.mapTate_galTate`,
  `PDivFGL.dualConnTateLin`); injectivity is levelwise (`connPartHom_mapPoints_injective`) and
  survives `ℚ_p ⊗_{ℤ_p} -` by flatness;
* the twist-`(-1)` map `D_{-1}(V_p(G^∨)) → D_0(V^∨)` along `V_p(G^∨) ≅ V^∨ ⊗ ℚ_p(1)`
  (`tateRepDualEquiv`, [Hong, Prop. 3.4.6]).

No double duality and no surjectivity is needed. Together with (3.9) (`dalphaKTwist`), the
orthogonality (3.11) (`bijective_of_finrank_le_add_fin`) and `h ≤ d + d'` this gives:

* **[Hong, Thm. 3.4.10] for `dα_K`** (`PDivFGL.dalphaK_bijective`,
  `PDivFGL.dalphaKTwist_bijective`): `dα_K : t_G(ℚ_p) = ℚ_p^d → Hom_{ℤ_p[Γ]}(T_p(G^∨), ℂ_p)` is
  bijective;
* **[Hong, Cor. 3.4.11]** (`PDivFGL.finrank_DHT_tateRepDual_dual`,
  `PDivFGL.finrank_DHT_tateRep_neg_one`): `d = dim Hom_{ℤ_p[Γ]}(T_p(G^∨), ℂ_p)
  = dim (T_p G ⊗ ℂ_p(-1))^Γ`;
* the dual statements `dim D_0(V^∨) = d'` and `h = d + d'` (`PDivFGL.height_eq_add`, the
  equality of [Hong, Thm. 2.2.19] for `F[p^∞]` over `ℤ_p`).

## References

* [Hong] S. Hong, *Notes on p-adic Hodge theory*, Prop. 3.4.6, Prop. 3.4.9, Thm. 3.4.10,
  Cor. 3.4.11, Thm. 2.2.19.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

/-! ### Morphisms of `p`-divisible groups over a field `F ⊆ ℚ̄_p` on Tate modules -/

namespace PDivGroup

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

variable {F : Type} [Field F] [Algebra F (PadicAlgCl p)]

theorem Hom.mapPoints_galPoints {G H : FFGroupScheme F} (f : FFGroupScheme.Hom G H)
    (σ : K ≃ₐ[F] K) (x : G.points K) :
    f.mapPoints K (galPoints G σ x) = galPoints H σ (f.mapPoints K x) := rfl

variable {G H : PDivGroup F p}

/-- **Morphisms are Galois equivariant on Tate modules.** -/
theorem Hom.mapTate_galTate (φ : Hom G H) (σ : K ≃ₐ[F] K) (x : G.TateModule K) :
    φ.mapTate K (G.galTate σ x) = H.galTate σ (φ.mapTate K x) := rfl

/-- The `ℤ_p`-linear map `T_p G(ℚ̄_p) → T_p H(ℚ̄_p)` induced by a morphism. -/
def Hom.tateLin (φ : Hom G H) :
    Additive (G.TateModule K) →ₗ[ℤ_[p]] Additive (H.TateModule K) where
  toFun x := Additive.ofMul (φ.mapTate K (Additive.toMul x))
  map_add' x y := by
    change Additive.ofMul (φ.mapTate K (Additive.toMul x * Additive.toMul y)) = _
    rw [map_mul]
    rfl
  map_smul' a x := H.addTate_ext _ fun v => by
    change (φ.f v).mapPoints K ((Additive.toMul x).1 v ^ expo a v) =
      ((φ.f v).mapPoints K ((Additive.toMul x).1 v)) ^ expo a v
    rw [map_pow]

theorem Hom.tateLin_galLin [CharZero F] (φ : Hom G H) (σ : K ≃ₐ[F] K)
    (x : Additive (G.TateModule K)) : φ.tateLin (G.galLin σ x) = H.galLin σ (φ.tateLin x) :=
  rfl

end PDivGroup

/-! ### `T_p(F'[p^∞]) ↪ T_p(G^∨)`, over a general coefficient ring -/

namespace PDivFGL

open PDivGroup IsLocalRing

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

local instance : NeZero p := ⟨hp.out.ne_zero⟩

theorem mapPoints_comp {R : Type} [CommRing R] {G H J : FFGroupScheme R}
    (f : FFGroupScheme.Hom G H) (g : FFGroupScheme.Hom H J) (S : Type) [CommRing S]
    [Algebra R S] (x : G.points S) :
    FFGroupScheme.Hom.mapPoints (G := G) (H := J) (BialgHom.comp f g) S x =
      FFGroupScheme.Hom.mapPoints g S (FFGroupScheme.Hom.mapPoints f S x) := rfl

section Gen

variable {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {d : ℕ} (P : PDivFGL R d p)
  (F : Type) [Field F] [CharZero F] [Algebra R F] [Algebra F (PadicAlgCl p)]
  [Algebra R (PadicAlgCl p)] [IsScalarTower R F (PadicAlgCl p)]

/-- `(G^∨)_F(ℚ̄_p) ≃ (G_F)^∨(ℚ̄_p)` on Tate modules, as a `ℤ_p`-linear map. -/
def dualBCTateLin :
    Additive ((P.dualPDiv.baseChange F).TateModule K) →ₗ[ℤ_[p]]
      Additive ((P.pdivGroup.baseChange F).dualPDiv.TateModule K) where
  toFun x := Additive.ofMul (P.dualPDivBaseChangeTateEquiv F K (Additive.toMul x))
  map_add' x y := by
    change Additive.ofMul (P.dualPDivBaseChangeTateEquiv F K
      (Additive.toMul x * Additive.toMul y)) = _
    rw [map_mul]
    rfl
  map_smul' a x := (P.pdivGroup.baseChange F).dualPDiv.addTate_ext _ fun v => by
    change PDivGroup.dualPDivOfBaseChangePointsEquiv F P.dualPDivData K v
        ((Additive.toMul x).1 v ^ expo a v) =
      (PDivGroup.dualPDivOfBaseChangePointsEquiv F P.dualPDivData K v
        ((Additive.toMul x).1 v)) ^ expo a v
    rw [map_pow]

theorem dualBCTateLin_injective : Function.Injective (P.dualBCTateLin F) := by
  intro x y h
  apply Additive.toMul.injective
  apply (P.dualPDivBaseChangeTateEquiv F K).injective
  exact congrArg Additive.toMul h

theorem dualPDivOfBaseChangePointsEquiv_galPoints (v : ℕ) (σ : K ≃ₐ[F] K)
    (y : ((P.dualPDiv.baseChange F).G v).points K) :
    PDivGroup.dualPDivOfBaseChangePointsEquiv F P.dualPDivData K v
        (galPoints ((P.dualPDiv.baseChange F).G v) σ y) =
      galPoints (((P.pdivGroup.baseChange F).dualPDiv).G v) σ
        (PDivGroup.dualPDivOfBaseChangePointsEquiv F P.dualPDivData K v y) := by
  set E := (P.pdivGroup.G v).dualBaseChangePointsEquiv (S := F) (T := K)
  have hE : ∀ z, E (PDivGroup.dualPDivOfBaseChangePointsEquiv F P.dualPDivData K v z) =
      (P.pdivGroup.G v).dual.baseChangePointsEquiv K z := fun z => MulEquiv.apply_symm_apply _ _
  apply E.injective
  rw [hE]
  apply WithConv.ofConv_injective
  ext f
  have h2 : WithConv.ofConv (E (PDivGroup.dualPDivOfBaseChangePointsEquiv F P.dualPDivData K v y))
      f = WithConv.ofConv ((P.pdivGroup.G v).dual.baseChangePointsEquiv K y) f := by rw [hE]
  exact (congrArg σ h2).symm

theorem dualBCTateLin_galLin (σ : K ≃ₐ[F] K)
    (x : Additive ((P.dualPDiv.baseChange F).TateModule K)) :
    P.dualBCTateLin F ((P.dualPDiv.baseChange F).galLin σ x) =
      (P.pdivGroup.baseChange F).dualPDiv.galLin σ (P.dualBCTateLin F x) := by
  apply (P.pdivGroup.baseChange F).dualPDiv.addTate_ext
  intro v
  exact P.dualPDivOfBaseChangePointsEquiv_galPoints F v σ ((Additive.toMul x).1 v)

variable [IsDomain R] [IsPrincipalIdealRing R] {d' : ℕ} (P' : PDivFGL R d' p)
  (φ : PDivGroup.Hom P.dualPDiv.connPart P'.pdivGroup)
  (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart)

/-- The morphism `F'[p^∞] ≅ (G^∨)⁰ ↪ G^∨`. -/
def dualConnHom : PDivGroup.Hom P'.pdivGroup P.dualPDiv :=
  P.dualPDiv.connPartHom.comp ψ

/-- **`T_p(F'[p^∞]_F) → T_p((G_F)^∨)`**, `ℤ_p`-linear. -/
def dualConnTateLin : Additive ((P'.pdivGroup.baseChange F).TateModule K) →ₗ[ℤ_[p]]
    Additive ((P.pdivGroup.baseChange F).dualPDiv.TateModule K) :=
  P.dualBCTateLin F ∘ₗ (Hom.baseChange (S := F) (P.dualConnHom P' ψ)).tateLin

theorem dualConnTateLin_galLin (σ : K ≃ₐ[F] K)
    (x : Additive ((P'.pdivGroup.baseChange F).TateModule K)) :
    P.dualConnTateLin F P' ψ ((P'.pdivGroup.baseChange F).galLin σ x) =
      (P.pdivGroup.baseChange F).dualPDiv.galLin σ (P.dualConnTateLin F P' ψ x) := by
  change P.dualBCTateLin F (Hom.tateLin _ _) = _
  rw [Hom.tateLin_galLin, dualBCTateLin_galLin]
  rfl

include φ in
theorem dualConnTateLin_injective (hφψ : φ.comp ψ = PDivGroup.Hom.id _) :
    Function.Injective (P.dualConnTateLin F P' ψ) := by
  refine (P.dualBCTateLin_injective F).comp ?_
  intro x y h
  apply Additive.toMul.injective
  refine Subtype.ext (funext fun v => ?_)
  have h1 := congrArg (fun z => (Additive.toMul z).1 v) h
  change (FFGroupScheme.baseChangeHom F ((P.dualConnHom P' ψ).f v)).mapPoints K
      ((Additive.toMul x).1 v) =
    (FFGroupScheme.baseChangeHom F ((P.dualConnHom P' ψ).f v)).mapPoints K
      ((Additive.toMul y).1 v) at h1
  apply ((P'.pdivGroup.G v).baseChangePointsEquiv (S := F) K).injective
  have h2 := congrArg ((P.dualPDiv.G v).baseChangePointsEquiv (S := F) K) h1
  rw [FFGroupScheme.baseChangePointsEquiv_mapPoints,
    FFGroupScheme.baseChangePointsEquiv_mapPoints] at h2
  rw [show (P.dualConnHom P' ψ).f v = BialgHom.comp (ψ.f v) (P.dualPDiv.connPartHom.f v) from rfl,
    mapPoints_comp, mapPoints_comp] at h2
  have h3 := P.dualPDiv.connPartHom_mapPoints_injective v K h2
  have hid : ∀ z : (P'.pdivGroup.G v).points K,
      (φ.f v).mapPoints K ((ψ.f v).mapPoints K z) = z := fun z => by
    change ((φ.comp ψ).f v).mapPoints K z = z
    rw [hφψ]
    rfl
  rw [← hid ((P'.pdivGroup.G v).baseChangePointsEquiv K ((Additive.toMul x).1 v)),
    ← hid ((P'.pdivGroup.G v).baseChangePointsEquiv K ((Additive.toMul y).1 v)), h3]

/-- `V_p(F'[p^∞]_F) → V_p((G_F)^∨)`. -/
def dualConnQpLin :
    ℚ_[p] ⊗[ℤ_[p]] Additive ((P'.pdivGroup.baseChange F).TateModule K) →ₗ[ℚ_[p]]
      ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).dualPDiv.TateModule K) :=
  (P.dualConnTateLin F P' ψ).baseChange ℚ_[p]

include φ in
theorem dualConnQpLin_injective (hφψ : φ.comp ψ = PDivGroup.Hom.id _) :
    Function.Injective (P.dualConnQpLin F P' ψ) := by
  haveI : Module.Flat ℤ_[p] ℚ_[p] := IsLocalization.flat ℚ_[p] (nonZeroDivisors ℤ_[p])
  change Function.Injective ((P.dualConnTateLin F P' ψ).baseChange ℚ_[p])
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (P.dualConnTateLin_injective F P' φ ψ hφψ)

/-- `V_p((G_F)^∨) → V^∨`, `rid ∘ tateRepDualEquiv`. -/
def tateRepDualToDual :
    ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).dualPDiv.TateModule K) →ₗ[ℚ_[p]]
      Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).TateModule K)) :=
  (TensorProduct.rid ℚ_[p] _).toLinearMap ∘ₗ
    ((P.pdivGroup.baseChange F).tateRepDualEquiv : _ →ₗ[ℚ_[p]] _)

omit [IsDomain R] [IsPrincipalIdealRing R] [Algebra R (PadicAlgCl p)]
  [IsScalarTower R F (PadicAlgCl p)] in
theorem tateRepDualToDual_injective : Function.Injective (P.tateRepDualToDual F) :=
  (TensorProduct.rid ℚ_[p] _).injective.comp
    (P.pdivGroup.baseChange F).tateRepDualEquiv.injective

/-! The Galois action: `G_L` acts through `ι : G_L → G_F` by representations with
`ρ(σ)(a ⊗ t) = a ⊗ (ι σ) t` on `V_p G_F`, `V_p(G_F^∨)`, `V_p(F'[p^∞]_F)`, `V_p(F'[p^∞]_F^∨)`. -/

variable [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)]
  (L : IntermediateField ℚ_[p] (PadicAlgCl p))
  (ι : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → (PadicAlgCl p ≃ₐ[F] PadicAlgCl p))
  (hι : ∀ σ x, ι σ x = σ x)
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).TateModule (PadicAlgCl p))))
  (hρ : ∀ σ (a : ℚ_[p]) x, ρ σ (a ⊗ₜ x) = a ⊗ₜ (P.pdivGroup.baseChange F).galLin (ι σ) x)
  (ρd : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).dualPDiv.TateModule (PadicAlgCl p))))
  (hρd : ∀ σ (a : ℚ_[p]) y,
    ρd σ (a ⊗ₜ y) = a ⊗ₜ (P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) y)
  (ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive ((P'.pdivGroup.baseChange F).TateModule (PadicAlgCl p))))
  (hρ' : ∀ σ (a : ℚ_[p]) x, ρ' σ (a ⊗ₜ x) = a ⊗ₜ (P'.pdivGroup.baseChange F).galLin (ι σ) x)
  (ρ'd : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive ((P'.pdivGroup.baseChange F).dualPDiv.TateModule (PadicAlgCl p))))
  (hρ'd : ∀ σ (a : ℚ_[p]) y,
    ρ'd σ (a ⊗ₜ y) = a ⊗ₜ (P'.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) y)

omit [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)] in
include hρd hρ' in
theorem dualConnQpLin_gal (σ : K ≃ₐ[L] K)
    (x : ℚ_[p] ⊗[ℤ_[p]] Additive ((P'.pdivGroup.baseChange F).TateModule K)) :
    ρd σ (P.dualConnQpLin F P' ψ x) = chiL L 0 σ • P.dualConnQpLin F P' ψ (ρ' σ x) := by
  rw [chiL_zero, one_smul]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a t =>
    rw [hρ']
    change ρd σ (a ⊗ₜ P.dualConnTateLin F P' ψ t) =
      a ⊗ₜ P.dualConnTateLin F P' ψ ((P'.pdivGroup.baseChange F).galLin (ι σ) t)
    rw [hρd, dualConnTateLin_galLin]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

omit [IsDomain R] [IsPrincipalIdealRing R] [Algebra R (PadicAlgCl p)]
  [IsScalarTower R F (PadicAlgCl p)] in
include hι hρ hρd in
theorem tateRepDualToDual_gal (σ : K ≃ₐ[L] K)
    (x : ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).dualPDiv.TateModule K)) :
    ρ.dual σ (P.tateRepDualToDual F x) = chiL L (-1) σ • P.tateRepDualToDual F (ρd σ x) := by
  have he := LinearMap.congr_fun
    ((P.pdivGroup.baseChange F).tateRepDualEquiv_galVia ι hι hρ hρd σ) x
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at he
  change _ = chiL L (-1) σ • TensorProduct.rid ℚ_[p] _
    ((P.pdivGroup.baseChange F).tateRepDualEquiv (ρd σ x))
  rw [he, rid_tprod_charRep, smul_smul, ← chiL_add, neg_add_cancel, chiL_zero, one_smul]
  rfl

variable [FiniteDimensional ℚ_[p] L]

/-- `D_{-1}(V_p(F'[p^∞]_F)) → D_{-1}(V_p((G_F)^∨))` (twist `0`). -/
def dualConnDHT : DHT ρ' (-1) →ₗ[L] DHT ρd (-1) :=
  DHTtwistMap 0 (P.dualConnQpLin F P' ψ)
    (fun σ x => P.dualConnQpLin_gal F P' ψ L ι ρd hρd ρ' hρ' σ x) (by norm_num)

/-- `D_{-1}(V_p((G_F)^∨)) → D_0(V^∨)` (twist `-1`, `V_p(G^∨) ≅ V^∨ ⊗ ℚ_p(1)`). -/
def dualTwistDHT : DHT ρd (-1) →ₗ[L] DHT ρ.dual 0 :=
  DHTtwistMap (-1) (P.tateRepDualToDual F)
    (fun σ x => P.tateRepDualToDual_gal F L ι hι ρ hρ ρd hρd σ x) (by norm_num)

omit [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)] in
include φ in
theorem dualConnDHT_injective (hφψ : φ.comp ψ = PDivGroup.Hom.id _) :
    Function.Injective (P.dualConnDHT F P' ψ L ι ρd hρd ρ' hρ') :=
  DHTtwistMap_injective 0 _ _ (P.dualConnQpLin_injective F P' φ ψ hφψ)

omit [Algebra R (PadicAlgCl p)] [IsScalarTower R F (PadicAlgCl p)] [IsDomain R]
  [IsPrincipalIdealRing R] in
theorem dualTwistDHT_injective :
    Function.Injective (P.dualTwistDHT F L ι hι ρ hρ ρd hρd) :=
  DHTtwistMap_injective (-1) _ _ (P.tateRepDualToDual_injective F)

variable [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  (hpm : (p : R) ∈ maximalIdeal R)
  (hRF : ∀ r : R, ((algebraMap R (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
    ((algebraMap R (OC p) r : OC p) : ℂ_[p]))
  (hRL : FGL.GalFixedOver p R L)

/-- `dα_K` for `F'` with values in `D_{-1}(V_p(F'[p^∞]_F))`. -/
def dalphaKTwistGen : (Fin d' → L) →ₗ[L] DHT ρ' (-1) :=
  DHTdualDualMap (P'.pdivGroup.baseChange F).tateRepDualEquiv
      ((P'.pdivGroup.baseChange F).tateRepDualEquiv_galVia ι hι hρ' hρ'd) ∘ₗ
    P'.dalphaKGen hpm F hRF L hRL ι hι ρ'd hρ'd

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem dalphaKTwistGen_injective
    (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) :
    Function.Injective (P'.dalphaKTwistGen F L ι hι ρ' hρ' ρ'd hρ'd hpm hRF hRL) :=
  (DHTdualDualMap_injective _
    ((P'.pdivGroup.baseChange F).tateRepDualEquiv_galVia ι hι hρ' hρ'd)).comp
    (P'.dalphaKGen_injective hpm F hRF L hRL ι hι ρ'd hρ'd hR)

/-- **Step (3.10)** ([Hong, proof of Thm. 3.4.10]): `L^{d'} → D_0(V^∨) =
Hom_{ℤ_p}(T_p G, ℂ_p)^{G_L}`, from `dα_K` for `F'` and `F'[p^∞] ≅ (G^∨)⁰ ↪ G^∨`. -/
def dalphaDualGen : (Fin d' → L) →ₗ[L] DHT ρ.dual 0 :=
  P.dualTwistDHT F L ι hι ρ hρ ρd hρd ∘ₗ P.dualConnDHT F P' ψ L ι ρd hρd ρ' hρ' ∘ₗ
    P'.dalphaKTwistGen F L ι hι ρ' hρ' ρ'd hρ'd hpm hRF hRL

include φ in
/-- **Step (3.10) is injective**: `d' ≤ dim D_0(V^∨)`. -/
theorem dalphaDualGen_injective (hφψ : φ.comp ψ = PDivGroup.Hom.id _)
    (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) :
    Function.Injective
      (P.dalphaDualGen F P' ψ L ι hι ρ hρ ρd hρd ρ' hρ' ρ'd hρ'd hpm hRF hRL) :=
  (P.dualTwistDHT_injective F L ι hι ρ hρ ρd hρd).comp
    ((P.dualConnDHT_injective F P' φ ψ L ι ρd hρd ρ' hρ' hφψ).comp
      (P'.dalphaKTwistGen_injective F L ι hι ρ' hρ' ρ'd hρ'd hpm hRF hRL hR))

end Gen

end PDivFGL

/-! ### Tate's theorem for `F[p^∞]` over a general coefficient ring -/

namespace PDivFGL

open PDivGroup IsLocalRing

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

section TateGen

variable {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [IsDomain R] [IsPrincipalIdealRing R]
  [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  [IsAdicComplete ((maximalIdeal R).map (algebraMap R (OC p))) (OC p)]
  {d : ℕ} (P : PDivFGL R d p)
  (F : Type) [Field F] [CharZero F] [Algebra R F] [Algebra F (PadicAlgCl p)]
  [Algebra R (PadicAlgCl p)] [IsScalarTower R F (PadicAlgCl p)]
  [Algebra ℚ_[p] F] [IsScalarTower ℚ_[p] F (PadicAlgCl p)]
  {d' : ℕ} (P' : PDivFGL R d' p)
  (φ : PDivGroup.Hom P.dualPDiv.connPart P'.pdivGroup)
  (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart)
  (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
  (ι : (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) → (PadicAlgCl p ≃ₐ[F] PadicAlgCl p))
  (hι : ∀ σ x, ι σ x = σ x)
  (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).TateModule (PadicAlgCl p))))
  (hρ : ∀ σ (a : ℚ_[p]) x, ρ σ (a ⊗ₜ x) = a ⊗ₜ (P.pdivGroup.baseChange F).galLin (ι σ) x)
  (ρd : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).dualPDiv.TateModule (PadicAlgCl p))))
  (hρd : ∀ σ (a : ℚ_[p]) y,
    ρd σ (a ⊗ₜ y) = a ⊗ₜ (P.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) y)
  (ρ' : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive ((P'.pdivGroup.baseChange F).TateModule (PadicAlgCl p))))
  (hρ' : ∀ σ (a : ℚ_[p]) x, ρ' σ (a ⊗ₜ x) = a ⊗ₜ (P'.pdivGroup.baseChange F).galLin (ι σ) x)
  (ρ'd : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p)
    (ℚ_[p] ⊗[ℤ_[p]] Additive ((P'.pdivGroup.baseChange F).dualPDiv.TateModule (PadicAlgCl p))))
  (hρ'd : ∀ σ (a : ℚ_[p]) y,
    ρ'd σ (a ⊗ₜ y) = a ⊗ₜ (P'.pdivGroup.baseChange F).dualPDiv.galLin (ι σ) y)
  (hpm : (p : R) ∈ maximalIdeal R)
  (hRF : ∀ r : R, ((algebraMap R (PadicAlgCl p) r : PadicAlgCl p) : ℂ_[p]) =
    ((algebraMap R (OC p) r : OC p) : ℂ_[p]))
  (hRL : FGL.GalFixedOver p R L)
  (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1)

include φ hR in
/-- **Tate's theorem** ([Hong, Thm. 3.4.10], the `dα_K` half, and the dual statement) for
`G = F[p^∞]` over `R`, with generic fibre over `F` and `G_L` acting through `ι`: if
`(G^∨)⁰ ≅ F'[p^∞]` (`φ ∘ ψ = id`) and `h ≤ d + d'`, then `dα_K : L^d → D_{-1}(V_p G_F)` and
`L^{d'} → D_0(V_p(G_F)^∨)` are bijective, `dim D_{-1}(V_p G_F) = d`,
`dim D_0(V_p(G_F)^∨) = d'` and `h = d + d'`. -/
theorem tate_dalphaGen (hφψ : φ.comp ψ = PDivGroup.Hom.id _) (hle : P.height ≤ d + d') :
    Function.Bijective (P.dalphaKTwistGen F L ι hι ρ hρ ρd hρd hpm hRF hRL) ∧
      Function.Bijective
        (P.dalphaDualGen F P' ψ L ι hι ρ hρ ρd hρd ρ' hρ' ρ'd hρ'd hpm hRF hRL) ∧
      finrank L (DHT ρ (-1)) = d ∧ finrank L (DHT ρ.dual 0) = d' ∧ P.height = d + d' := by
  have hV : finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive ((P.pdivGroup.baseChange F).TateModule K)) ≤
      d + d' := by
    rw [Module.finrank_baseChange, finrank_tate]
    exact hle
  obtain ⟨b1, b2, e1, e2⟩ := bijective_of_finrank_le_add_fin ρ
    (P.dalphaKTwistGen F L ι hι ρ hρ ρd hρd hpm hRF hRL)
    (P.dalphaDualGen F P' ψ L ι hι ρ hρ ρd hρd ρ' hρ' ρ'd hρ'd hpm hRF hRL)
    (P.dalphaKTwistGen_injective F L ι hι ρ hρ ρd hρd hpm hRF hRL hR)
    (P.dalphaDualGen_injective F P' φ ψ L ι hι ρ hρ ρd hρd ρ' hρ' ρ'd hρ'd hpm hRF hRL hφψ hR)
    hV
  refine ⟨b1, b2, e1, e2, le_antisymm hle ?_⟩
  have := finrank_DHT_add_finrank_DHT_dual_le ρ (q := -1) (q' := 0) (by norm_num)
  rw [e1, e2, Module.finrank_baseChange, finrank_tate] at this
  exact this

end TateGen

/-! ### `R = ℤ_p`, `F = ℚ_p` -/

section Zp

variable {d : ℕ} (P : PDivFGL (ZpD p) d p)

attribute [local instance] SerreTate.algebraZModD SerreTate.isDomain_zpD isPrincipalIdealRing_zpD

variable {d' : ℕ} (P' : PDivFGL (ZpD p) d' p)
  (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart)
  (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]

/-- **Step (3.10)** ([Hong, proof of Thm. 3.4.10]) over `ℤ_p`: `L^{d'} → D_0(V^∨) =
Hom_{ℤ_p}(T_p G, ℂ_p)^{G_L}`, from `dα_K` for `F'` and `F'[p^∞] ≅ (G^∨)⁰ ↪ G^∨`. -/
def dalphaDual : (Fin d' → L) →ₗ[L] DHT (P.genericFibre.tateRep L).dual 0 :=
  P.dalphaDualGen ℚ_[p] P' ψ L (fun σ => σ.restrictScalars ℚ_[p]) (fun _ _ => rfl)
    (P.genericFibre.tateRep L) (fun _ _ _ => rfl) (P.tateRepDual L) (fun _ _ _ => rfl)
    (P'.genericFibre.tateRep L) (fun _ _ _ => rfl) (P'.tateRepDual L) (fun _ _ _ => rfl)
    ZpD.p_mem ZpD.algebraMap_qbar_cp (FGL.galFixedOver_of_galFixed ZpD.galFixed L)

/-- **Tate's theorem** ([Hong, Thm. 3.4.10], the `dα_K` half, and the dual statement) for
`G = F[p^∞]` over `ℤ_p`: with `(G^∨)⁰ ≅ F'[p^∞]`, `F'` of dimension `d'`,
`dα_K : ℚ_p^d → D_{-1}(V_p G)` and `ℚ_p^{d'} → D_0(V_p(G)^∨)` are bijective,
`dim D_{-1}(V_p G) = d`, `dim D_0(V_p(G)^∨) = d'` and `h = d + d'`. -/
theorem tate_dalpha :
    ∃ (d' : ℕ) (P' : PDivFGL (ZpD p) d' p)
      (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart),
      Function.Bijective (P.dalphaKTwist ⊥) ∧ Function.Bijective (P.dalphaDual P' ψ ⊥) ∧
      finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (DHT (P.genericFibre.tateRep ⊥) (-1)) = d ∧
      finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (DHT (P.genericFibre.tateRep ⊥).dual 0) = d' ∧
      P.height = d + d' := by
  obtain ⟨d', P', φ, ψ, hφψ, -, hle⟩ := P.exists_connPart_dual_iso_height_le
  exact ⟨d', P', ψ, P.tate_dalphaGen ℚ_[p] P' φ ψ ⊥ (fun σ => σ.restrictScalars ℚ_[p])
    (fun _ _ => rfl) (P.genericFibre.tateRep ⊥) (fun _ _ _ => rfl) (P.tateRepDual ⊥)
    (fun _ _ _ => rfl) (P'.genericFibre.tateRep ⊥) (fun _ _ _ => rfl) (P'.tateRepDual ⊥)
    (fun _ _ _ => rfl) ZpD.p_mem ZpD.algebraMap_qbar_cp
    (FGL.galFixedOver_of_galFixed ZpD.galFixed ⊥) ZpD.norm_lt_one hφψ hle⟩

/-- **[Hong, Thm. 3.4.10]** (`dα_K` half) for `G = F[p^∞]` over `ℤ_p`:
`dα_K : t_G(ℚ_p) = ℚ_p^d → Hom_{ℤ_p[Γ]}(T_p(G^∨), ℂ_p) = D_0(V_p(G^∨)^∨)` is bijective. -/
theorem dalphaK_bijective : Function.Bijective (P.dalphaK ⊥) := by
  obtain ⟨d', P', ψ, b1, -⟩ := P.tate_dalpha
  refine ⟨P.dalphaK_injective ⊥, fun y => ?_⟩
  obtain ⟨z, hz⟩ := b1.2 (P.genericFibre.DHTdualTateEquivMap ⊥ y)
  exact ⟨z, P.genericFibre.DHTdualTateEquivMap_injective ⊥ hz⟩

/-- `dα_K` with values in `D_{-1}(V_p G)` is bijective. -/
theorem dalphaKTwist_bijective : Function.Bijective (P.dalphaKTwist ⊥) := by
  obtain ⟨d', P', ψ, b1, -⟩ := P.tate_dalpha
  exact b1

/-- **[Hong, Cor. 3.4.11]**, first equality: `d = dim Hom_{ℤ_p[Γ]}(T_p(G^∨), ℂ_p)`. -/
theorem finrank_DHT_tateRepDual_dual :
    finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) (DHT (P.tateRepDual ⊥).dual 0) = d := by
  rw [← (LinearEquiv.ofBijective _ P.dalphaK_bijective).finrank_eq, Module.finrank_fin_fun]

/-- **[Hong, Cor. 3.4.11]**, second equality: `d = dim (T_p G ⊗ ℂ_p(-1))^Γ = dim D_{-1}(V_p G)`. -/
theorem finrank_DHT_tateRep_neg_one :
    finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
      (DHT (P.genericFibre.tateRep ⊥) (-1)) = d := by
  obtain ⟨d', P', ψ, -, -, e1, -⟩ := P.tate_dalpha
  exact e1

end Zp

end PDivFGL

end PadicHodge
