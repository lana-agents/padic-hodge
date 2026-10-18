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

/-! ### Morphisms of `p`-divisible groups over `ℚ_p` on Tate modules -/

namespace PDivGroup

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

theorem Hom.mapPoints_galPoints {G H : FFGroupScheme ℚ_[p]} (f : FFGroupScheme.Hom G H)
    (σ : K ≃ₐ[ℚ_[p]] K) (x : G.points K) :
    f.mapPoints K (galPoints G σ x) = galPoints H σ (f.mapPoints K x) := rfl

variable {G H : PDivGroup ℚ_[p] p}

/-- **Morphisms are Galois equivariant on Tate modules.** -/
theorem Hom.mapTate_galTate (φ : Hom G H) (σ : K ≃ₐ[ℚ_[p]] K) (x : G.TateModule K) :
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

theorem Hom.tateLin_galLin (φ : Hom G H) (σ : K ≃ₐ[ℚ_[p]] K)
    (x : Additive (G.TateModule K)) : φ.tateLin (G.galLin σ x) = H.galLin σ (φ.tateLin x) :=
  rfl

end PDivGroup

/-! ### `T_p(F'[p^∞]) ↪ T_p(G^∨)` -/

namespace PDivFGL

open PDivGroup

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

local instance : NeZero p := ⟨hp.out.ne_zero⟩

attribute [local instance] SerreTate.algebraZModD SerreTate.isDomain_zpD isPrincipalIdealRing_zpD

theorem mapPoints_comp {R : Type} [CommRing R] {G H J : FFGroupScheme R}
    (f : FFGroupScheme.Hom G H) (g : FFGroupScheme.Hom H J) (S : Type) [CommRing S]
    [Algebra R S] (x : G.points S) :
    FFGroupScheme.Hom.mapPoints (G := G) (H := J) (BialgHom.comp f g) S x =
      FFGroupScheme.Hom.mapPoints g S (FFGroupScheme.Hom.mapPoints f S x) := rfl

variable {d : ℕ} (P : PDivFGL (ZpD p) d p)

/-- `(G^∨)_{ℚ_p}(ℚ̄_p) ≃ (G_{ℚ_p})^∨(ℚ̄_p)` on Tate modules, as a `ℤ_p`-linear map. -/
def dualBCTateLin :
    Additive ((P.dualPDiv.baseChange ℚ_[p]).TateModule K) →ₗ[ℤ_[p]] P.TateDualQp where
  toFun x := Additive.ofMul (P.dualPDivBaseChangeTateEquiv K (Additive.toMul x))
  map_add' x y := by
    change Additive.ofMul (P.dualPDivBaseChangeTateEquiv K
      (Additive.toMul x * Additive.toMul y)) = _
    rw [map_mul]
    rfl
  map_smul' a x := P.genericFibre.dualPDiv.addTate_ext _ fun v => by
    change PDivGroup.dualPDivOfBaseChangePointsEquiv P.dualPDivData K v
        ((Additive.toMul x).1 v ^ expo a v) =
      (PDivGroup.dualPDivOfBaseChangePointsEquiv P.dualPDivData K v
        ((Additive.toMul x).1 v)) ^ expo a v
    rw [map_pow]

theorem dualBCTateLin_injective : Function.Injective P.dualBCTateLin := by
  intro x y h
  apply Additive.toMul.injective
  apply (P.dualPDivBaseChangeTateEquiv K).injective
  exact congrArg Additive.toMul h

theorem dualPDivOfBaseChangePointsEquiv_galPoints (v : ℕ) (σ : K ≃ₐ[ℚ_[p]] K)
    (y : ((P.dualPDiv.baseChange ℚ_[p]).G v).points K) :
    PDivGroup.dualPDivOfBaseChangePointsEquiv P.dualPDivData K v
        (galPoints ((P.dualPDiv.baseChange ℚ_[p]).G v) σ y) =
      galPoints ((P.genericFibre.dualPDiv).G v) σ
        (PDivGroup.dualPDivOfBaseChangePointsEquiv P.dualPDivData K v y) := by
  set E := (P.pdivGroup.G v).dualBaseChangePointsEquiv (S := ℚ_[p]) (T := K)
  have hE : ∀ z, E (PDivGroup.dualPDivOfBaseChangePointsEquiv P.dualPDivData K v z) =
      (P.pdivGroup.G v).dual.baseChangePointsEquiv K z := fun z => MulEquiv.apply_symm_apply _ _
  apply E.injective
  rw [hE]
  apply WithConv.ofConv_injective
  ext f
  have h2 : WithConv.ofConv (E (PDivGroup.dualPDivOfBaseChangePointsEquiv P.dualPDivData K v y)) f =
      WithConv.ofConv ((P.pdivGroup.G v).dual.baseChangePointsEquiv K y) f := by rw [hE]
  exact (congrArg σ h2).symm

theorem dualBCTateLin_galLin (σ : K ≃ₐ[ℚ_[p]] K)
    (x : Additive ((P.dualPDiv.baseChange ℚ_[p]).TateModule K)) :
    P.dualBCTateLin ((P.dualPDiv.baseChange ℚ_[p]).galLin σ x) =
      P.genericFibre.dualPDiv.galLin σ (P.dualBCTateLin x) := by
  apply P.genericFibre.dualPDiv.addTate_ext
  intro v
  exact P.dualPDivOfBaseChangePointsEquiv_galPoints v σ ((Additive.toMul x).1 v)

variable {d' : ℕ} (P' : PDivFGL (ZpD p) d' p)
  (φ : PDivGroup.Hom P.dualPDiv.connPart P'.pdivGroup)
  (ψ : PDivGroup.Hom P'.pdivGroup P.dualPDiv.connPart)

/-- The morphism `F'[p^∞] ≅ (G^∨)⁰ ↪ G^∨` over `ℤ_p`. -/
def dualConnHom : PDivGroup.Hom P'.pdivGroup P.dualPDiv :=
  P.dualPDiv.connPartHom.comp ψ

/-- **`T_p(F'[p^∞]_{ℚ_p}) → T_p((G_{ℚ_p})^∨)`**, `ℤ_p`-linear. -/
def dualConnTateLin : Additive (P'.genericFibre.TateModule K) →ₗ[ℤ_[p]] P.TateDualQp :=
  P.dualBCTateLin ∘ₗ (Hom.baseChange (S := ℚ_[p]) (P.dualConnHom P' ψ)).tateLin

theorem dualConnTateLin_galLin (σ : K ≃ₐ[ℚ_[p]] K) (x : Additive (P'.genericFibre.TateModule K)) :
    P.dualConnTateLin P' ψ (P'.genericFibre.galLin σ x) =
      P.genericFibre.dualPDiv.galLin σ (P.dualConnTateLin P' ψ x) := by
  change P.dualBCTateLin (Hom.tateLin _ _) = _
  rw [Hom.tateLin_galLin, dualBCTateLin_galLin]
  rfl

theorem dualConnTateLin_injective (hφψ : φ.comp ψ = PDivGroup.Hom.id _) :
    Function.Injective (P.dualConnTateLin P' ψ) := by
  refine (P.dualBCTateLin_injective).comp ?_
  intro x y h
  apply Additive.toMul.injective
  refine Subtype.ext (funext fun v => ?_)
  have h1 := congrArg (fun z => (Additive.toMul z).1 v) h
  change (FFGroupScheme.baseChangeHom ℚ_[p] ((P.dualConnHom P' ψ).f v)).mapPoints K
      ((Additive.toMul x).1 v) =
    (FFGroupScheme.baseChangeHom ℚ_[p] ((P.dualConnHom P' ψ).f v)).mapPoints K
      ((Additive.toMul y).1 v) at h1
  apply ((P'.pdivGroup.G v).baseChangePointsEquiv (S := ℚ_[p]) K).injective
  have h2 := congrArg ((P.dualPDiv.G v).baseChangePointsEquiv (S := ℚ_[p]) K) h1
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

/-- `V_p(F'[p^∞]_{ℚ_p}) → V_p((G_{ℚ_p})^∨)`. -/
def dualConnQpLin :
    ℚ_[p] ⊗[ℤ_[p]] Additive (P'.genericFibre.TateModule K) →ₗ[ℚ_[p]]
      ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp :=
  (P.dualConnTateLin P' ψ).baseChange ℚ_[p]

theorem dualConnQpLin_injective (hφψ : φ.comp ψ = PDivGroup.Hom.id _) :
    Function.Injective (P.dualConnQpLin P' ψ) := by
  haveI : Module.Flat ℤ_[p] ℚ_[p] := IsLocalization.flat ℚ_[p] (nonZeroDivisors ℤ_[p])
  change Function.Injective ((P.dualConnTateLin P' ψ).baseChange ℚ_[p])
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (P.dualConnTateLin_injective P' φ ψ hφψ)

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem dualConnQpLin_gal (σ : K ≃ₐ[L] K) (x : ℚ_[p] ⊗[ℤ_[p]]
    Additive (P'.genericFibre.TateModule K)) :
    P.tateRepDual L σ (P.dualConnQpLin P' ψ x) =
      chiL L 0 σ • P.dualConnQpLin P' ψ (P'.genericFibre.tateRep L σ x) := by
  rw [chiL_zero, one_smul]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    change a ⊗ₜ P.genericFibre.dualPDiv.galLin _ (P.dualConnTateLin P' ψ t) =
      a ⊗ₜ P.dualConnTateLin P' ψ (P'.genericFibre.galLin _ t)
    rw [dualConnTateLin_galLin]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `V_p((G_{ℚ_p})^∨) → V^∨`, `rid ∘ tateRepDualEquiv`. -/
def tateRepDualToDual : ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp →ₗ[ℚ_[p]]
    Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (P.genericFibre.TateModule K)) :=
  (TensorProduct.rid ℚ_[p] _).toLinearMap ∘ₗ
    (P.genericFibre.tateRepDualEquiv : _ →ₗ[ℚ_[p]] _)

theorem tateRepDualToDual_injective : Function.Injective P.tateRepDualToDual :=
  (TensorProduct.rid ℚ_[p] _).injective.comp P.genericFibre.tateRepDualEquiv.injective

theorem tateRepDualToDual_gal (σ : K ≃ₐ[L] K) (x : ℚ_[p] ⊗[ℤ_[p]] P.TateDualQp) :
    (P.genericFibre.tateRep L).dual σ (P.tateRepDualToDual x) =
      chiL L (-1) σ • P.tateRepDualToDual (P.tateRepDual L σ x) := by
  have he := LinearMap.congr_fun (P.genericFibre.tateRepDualEquiv_gal L σ) x
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at he
  change _ = chiL L (-1) σ • TensorProduct.rid ℚ_[p] _
    (P.genericFibre.tateRepDualEquiv (P.genericFibre.dualPDiv.tateRep L σ x))
  rw [he, rid_tprod_charRep, smul_smul, ← chiL_add, neg_add_cancel, chiL_zero, one_smul]
  rfl

variable [FiniteDimensional ℚ_[p] L]

/-- `D_{-1}(V_p(F'[p^∞])) → D_{-1}(V_p(G^∨))` (twist `0`). -/
def dualConnDHT : DHT (P'.genericFibre.tateRep L) (-1) →ₗ[L] DHT (P.tateRepDual L) (-1) :=
  DHTtwistMap 0 (P.dualConnQpLin P' ψ) (fun σ x => P.dualConnQpLin_gal P' ψ L σ x)
    (by norm_num)

/-- `D_{-1}(V_p(G^∨)) → D_0(V^∨)` (twist `-1`, `V_p(G^∨) ≅ V^∨ ⊗ ℚ_p(1)`). -/
def dualTwistDHT : DHT (P.tateRepDual L) (-1) →ₗ[L] DHT (P.genericFibre.tateRep L).dual 0 :=
  DHTtwistMap (-1) P.tateRepDualToDual (fun σ x => P.tateRepDualToDual_gal L σ x)
    (by norm_num)

theorem dualConnDHT_injective (hφψ : φ.comp ψ = PDivGroup.Hom.id _) :
    Function.Injective (P.dualConnDHT P' ψ L) :=
  DHTtwistMap_injective 0 _ _ (P.dualConnQpLin_injective P' φ ψ hφψ)

theorem dualTwistDHT_injective : Function.Injective (P.dualTwistDHT L) :=
  DHTtwistMap_injective (-1) _ _ P.tateRepDualToDual_injective

/-- **Step (3.10)** ([Hong, proof of Thm. 3.4.10]): `L^{d'} → D_0(V^∨) =
Hom_{ℤ_p}(T_p G, ℂ_p)^{G_L}`, from `dα_K` for `F'` and `F'[p^∞] ≅ (G^∨)⁰ ↪ G^∨`. -/
def dalphaDual : (Fin d' → L) →ₗ[L] DHT (P.genericFibre.tateRep L).dual 0 :=
  P.dualTwistDHT L ∘ₗ P.dualConnDHT P' ψ L ∘ₗ P'.dalphaKTwist L

/-- **Step (3.10) is injective** for `L = ℚ_p`: `d' ≤ dim D_0(V^∨)`. -/
theorem dalphaDual_injective (hφψ : φ.comp ψ = PDivGroup.Hom.id _) :
    Function.Injective (P.dalphaDual P' ψ ⊥) :=
  (P.dualTwistDHT_injective ⊥).comp
    ((P.dualConnDHT_injective P' φ ψ ⊥ hφψ).comp (P'.dalphaKTwist_injective ⊥))

end PDivFGL

/-! ### Tate's theorem for `F[p^∞]` over `ℤ_p` -/

namespace PDivFGL

open PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} (P : PDivFGL (ZpD p) d p)

local notation "K" => PadicAlgCl p

attribute [local instance] SerreTate.algebraZModD SerreTate.isDomain_zpD isPrincipalIdealRing_zpD

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
  have hV : finrank ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] Additive (P.genericFibre.TateModule K)) ≤ d + d' := by
    rw [finrank_tateRep]
    exact hle
  obtain ⟨b1, b2, e1, e2⟩ := bijective_of_finrank_le_add_fin (P.genericFibre.tateRep ⊥)
    (P.dalphaKTwist ⊥) (P.dalphaDual P' ψ ⊥) (P.dalphaKTwist_injective ⊥)
    (P.dalphaDual_injective P' φ ψ hφψ) hV
  refine ⟨d', P', ψ, b1, b2, e1, e2, le_antisymm hle ?_⟩
  have := finrank_DHT_add_finrank_DHT_dual_le (P.genericFibre.tateRep ⊥)
    (q := -1) (q' := 0) (by norm_num)
  rw [e1, e2, finrank_tateRep] at this
  exact this

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

end PDivFGL

end PadicHodge
