/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Cohomology.Kummer
import PadicHodge.FormalGroup.OK
import PadicHodge.FormalGroup.FGLHomPoints
import PadicHodge.FormalGroup.Divisible
import PadicHodge.FormalGroup.SerreTateHom
import PadicHodge.GroupScheme.CartierPerfect
import PadicHodge.TateSen.H1Gamma

/-!
# Kummer maps for formal groups and their `p`-divisible groups over `O_{K'}`

Let `F` be a formal group law over `R` (discrete topology, `R → O_{ℂ_p}`) and `Γ` a closed
subgroup of `Gal(ℚ̄_p/ℚ_p)` fixing the coefficients of `F` (`CoeffFixed`), e.g.
`Γ = G_{K'} = K'.fixingSubgroup` for `R = O_{K'}`. Then `Γ` acts `ℤ`-linearly on
`F(m_{ℂ_p})` (`FGL.galRep`), all stabilisers are closed (`FGL.isClosed_stab`), and the general
construction of `Cohomology/Kummer.lean` applies:

* `PDivFGL.finite_torsion`: `F(m_{ℂ_p})[p]` is finite for a `p`-divisible formal group law
  (it embeds into the points of the finite flat group scheme `F[p]` with values in `ℂ_p`);
* **`PDivFGL.kummer`**: the Kummer map `F(m_{ℂ_p})^Γ → H¹_cont(Γ, T_p F)`,
  `x ↦ [σ ↦ (σ x_n - x_n)_n]` with `p · x_{n+1} = x_n`, `x_0 = x`; here
  `T_p F = lim F(m_{ℂ_p})[p^n]` (`Kummer.Tp`) is identified with the Tate module of the
  `p`-divisible group `F[p^∞]` by `PDivFGL.tateEquiv` (`Kummer.val` has the same underlying
  sequences as `FGL.tate`, `PDivFGL.tpToPDiv`);
* **over `O_{K'}`** (`PDivFGL.kummerOL`, `L = K'` finite over `ℚ_p`, `Γ = L.fixingSubgroup`):
  `κ : F(m_{K'}) → H¹_cont(G_{K'}, T_p F)`, the invariants being exactly the points with
  coordinates in `K'` (`mem_invariants_galRepOL_iff`, Ax–Sen–Tate);
* **functoriality in `F`** (`PDivFGL.map_kummer`): for a homomorphism `f : F → F'` of formal
  group laws, `T_p(f)_* κ_F(x) = κ_{F'}(f(x))`, and `T_p(f)` is `T_p(f[p^∞])` on the Tate
  modules of the `p`-divisible groups (`PDivFGL.tpToPDiv_map`); by Serre–Tate
  (`FGL.Hom.pdivEquiv`) every homomorphism `F[p^∞] → F'[p^∞]` is of this form
  (`PDivFGL.exists_fglHom_tpToPDiv`);
* **base change** `K' ⊆ K''` (`PDivFGL.comap_kummerOL`): restricting `κ_{K'}(x)` to
  `G_{K''} ⊆ G_{K'}` gives `κ_{K''}(x)`.

For a `p`-divisible group `G` over `O_{K'}` the points `G(O_{K'})` that matter for Kummer theory
with `ℚ_p`-coefficients are those of the connected part `G⁰ ≅ F[p^∞]`
(`PDivGroup.exists_connPart_iso_OL`), i.e. `F(m_{K'})`; the Kummer map of `G⁰` is `kummerOL`
for this `F`.
-/

noncomputable section

open IsLocalRing

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

namespace FGL

section Action

variable {R : Type*} [CommRing R] [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)]
  {d : ℕ} (F : FGL R d)

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem galPt_mul (σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : F.Pt p) :
    galPt (σ * τ) x = galPt σ (galPt τ x) :=
  F.pt_ext fun j => Subtype.ext (by
    rw [galPt_val, galPt_val, galPt_val, map_mul]
    rfl)

omit [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] in
theorem galPt_one (x : F.Pt p) : galPt (1 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x = x :=
  F.pt_ext fun j => Subtype.ext (by
    rw [galPt_val, map_one]
    rfl)

variable (Γ : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))

/-- `σ` acting on `F(m_{ℂ_p})` as a `ℤ`-linear map, for `σ` fixing the coefficients. -/
def galLin {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : CoeffFixed p R σ) :
    F.Pt p →ₗ[ℤ] F.Pt p :=
  (AddMonoidHom.mk' (galPt σ) (galPt_add_of hσ)).toIntLinearMap

theorem galLin_apply {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : CoeffFixed p R σ)
    (x : F.Pt p) : F.galLin hσ x = galPt σ x := rfl

theorem galLin_mul_apply {σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : CoeffFixed p R σ)
    (hτ : CoeffFixed p R τ) (x : F.Pt p) :
    (F.galLin hσ * F.galLin hτ) x = galPt σ (galPt τ x) := rfl

theorem galLin_one (h1 : CoeffFixed p R 1) : F.galLin h1 = 1 := by
  refine LinearMap.ext fun x => ?_
  have := galPt_one F x
  exact this

theorem galLin_mul {σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hστ : CoeffFixed p R (σ * τ))
    (hσ : CoeffFixed p R σ) (hτ : CoeffFixed p R τ) :
    F.galLin hστ = F.galLin hσ * F.galLin hτ := by
  refine LinearMap.ext fun x => ?_
  have h1 : F.galLin hστ x = galPt σ (galPt τ x) := by
    have := galPt_mul F σ τ x
    exact this
  rw [h1, F.galLin_mul_apply hσ hτ x]

/-- **The action of `Γ` on `F(m_{ℂ_p})`**, for `Γ` fixing the coefficients of `F`. -/
def galRep (hΓ : ∀ σ ∈ Γ, CoeffFixed p R σ) : Representation ℤ Γ (F.Pt p) where
  toFun σ := F.galLin (hΓ σ σ.2)
  map_one' := F.galLin_one _
  map_mul' _ _ := F.galLin_mul _ _ _

variable {F Γ}

@[simp] theorem galRep_apply (hΓ : ∀ σ ∈ Γ, CoeffFixed p R σ) (σ : Γ) (x : F.Pt p) :
    F.galRep Γ hΓ σ x = galPt (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x := rfl

/-- The stabilisers of points of `F(m_{ℂ_p})` are closed (the orbit maps are continuous). -/
theorem isClosed_stab (hΓ : ∀ σ ∈ Γ, CoeffFixed p R σ) (z : F.Pt p) :
    IsClosed (Kummer.stab (F.galRep Γ hΓ) z : Set Γ) := by
  have e : (Kummer.stab (F.galRep Γ hΓ) z : Set Γ) =
      ⋂ j, {σ : Γ | autCp (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (z.1 j) = z.1 j} := by
    ext σ
    simp only [SetLike.mem_coe, Kummer.mem_stab, galRep_apply, Set.mem_iInter,
      Set.mem_setOf_eq]
    constructor
    · intro h j
      have := congrArg (fun y : F.Pt p => ((y.1 j : OC p) : ℂ_[p])) h
      simpa only [galPt_val] using this
    · intro h
      exact F.pt_ext fun j => Subtype.ext (by rw [galPt_val]; exact h j)
  rw [e]
  exact isClosed_iInter fun j =>
    isClosed_eq ((continuous_autCp_apply _).comp continuous_subtype_val) continuous_const

/-- Homomorphisms of formal group laws are equivariant for `σ` fixing the coefficients. -/
theorem Hom.ptMap_galPt_of {d' : ℕ} {F' : FGL R d'} (φ : FGL.Hom F F')
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : CoeffFixed p R σ) (x : F.Pt p) :
    φ.ptMap (galPt σ x) = galPt σ (φ.ptMap x) := by
  refine F'.pt_ext fun k => Subtype.ext ?_
  rw [galPt_val, Hom.ptMap_val, Hom.ptMap_val, ev_autCp_of hσ _ x.2]
  rfl

/-- Homomorphisms of formal group laws are `Γ`-equivariant. -/
theorem Hom.ptHom_galRep {d' : ℕ} {F' : FGL R d'} (φ : FGL.Hom F F')
    (hΓ : ∀ σ ∈ Γ, CoeffFixed p R σ) (σ : Γ) (m : F.Pt p) :
    φ.ptHom (F.galRep Γ hΓ σ m) = F'.galRep Γ hΓ σ (φ.ptHom m) := by
  have := φ.ptMap_galPt_of (hΓ σ σ.2) m
  exact this

end Action

end FGL

namespace PDivFGL

section General

variable {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (P : PDivFGL R d p)

/-- **`F(m_{ℂ_p})[p]` is finite**: it embeds (`layerPt`) into the `ℂ_p`-points of the finite
flat group scheme `F[p]`. -/
theorem finite_torsion : Finite {y : P.F.Pt p // p • y = 0} := by
  letI : Algebra R ℂ_[p] := ((OC p).subtype.comp (algebraMap R (OC p))).toAlgebra
  let ι : OC p →ₐ[R] ℂ_[p] :=
    { toRingHom := (OC p).subtype
      commutes' := fun _ => rfl }
  haveI : Finite ((P.groupScheme 1).points ℂ_[p]) :=
    (P.groupScheme 1).finite_points_of_free (S := ℂ_[p]) (Module.Free.chooseBasis R (P.A 1))
  refine Finite.of_injective (fun y : {y : P.F.Pt p // p • y = 0} =>
    (WithConv.toConv (ι.comp (P.F.layerPt 1 ⟨y.1, by
      rw [FGL.mem_torsionBy, pow_one]; exact y.2⟩)) : (P.groupScheme 1).points ℂ_[p]))
    fun a b hab => ?_
  have h1 := congrArg WithConv.ofConv hab
  have h2 : P.F.layerPt 1 ⟨a.1, by rw [FGL.mem_torsionBy, pow_one]; exact a.2⟩ =
      P.F.layerPt 1 ⟨b.1, by rw [FGL.mem_torsionBy, pow_one]; exact b.2⟩ := by
    refine AlgHom.ext fun t => Subtype.ext ?_
    exact DFunLike.congr_fun h1 t
  exact Subtype.ext (congrArg Subtype.val (P.F.layerPt_injective 1 h2) :)

variable (Γ : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
  (hΓ : ∀ σ ∈ Γ, FGL.CoeffFixed p R σ)
  (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1)

omit [IsAdicComplete (maximalIdeal R) R] in
include hR in
theorem divisible : ∀ y : P.F.Pt p, ∃ z, p • z = y := P.exists_p_nsmul_eq hR

theorem stabHyp [CompactSpace Γ] : Kummer.StabHyp (P.F.galRep Γ hΓ) p :=
  Kummer.stabHyp_of_finite (FGL.isClosed_stab hΓ) P.finite_torsion

/-- **The Kummer map of a `p`-divisible formal group law**
`κ : F(m_{ℂ_p})^Γ → H¹_cont(Γ, T_p F)`. -/
def kummer [CompactSpace Γ] :
    (P.F.galRep Γ hΓ).invariants →ₗ[ℤ] ContH1.H1 (Kummer.tpRep (P.F.galRep Γ hΓ) p) :=
  Kummer.kummer _ p (P.divisible hR) (P.stabHyp Γ hΓ)

/-- `κ(x)` is computed by any compatible system of `p`-power roots of `x` with open
stabilisers. -/
theorem kummer_eq [CompactSpace Γ] (x : (P.F.galRep Γ hΓ).invariants) {s : ℕ → P.F.Pt p}
    (hs : Kummer.IsDivSeq (P.F.galRep Γ hΓ) p x s) :
    P.kummer Γ hΓ hR x = ContH1.mk (Kummer.tpRep (P.F.galRep Γ hΓ) p) (Kummer.cocycle x.2 hs) :=
  Kummer.kummer_eq _ _ x hs

/-- **Functoriality of the Kummer map in `F`**: `T_p(f)_* κ_F(x) = κ_{F'}(f(x))`. -/
theorem map_kummer [CompactSpace Γ] {d' : ℕ} (P' : PDivFGL R d' p) (φ : FGL.Hom P.F P'.F)
    (x : (P.F.galRep Γ hΓ).invariants) :
    ContH1.map (Kummer.map φ.ptHom) (Kummer.continuous_map φ.ptHom)
        (Kummer.tpMap_equivariant φ.ptHom (φ.ptHom_galRep hΓ))
        (P.kummer Γ hΓ hR x) =
      P'.kummer Γ hΓ hR ⟨φ.ptHom x, Kummer.map_mem_invariants φ.ptHom
        (φ.ptHom_galRep hΓ) x.2⟩ :=
  Kummer.map_kummer _ _ _ _ φ.ptHom (φ.ptHom_galRep hΓ) x

/-- **Compatibility with restriction to a closed subgroup** `Γ' ≤ Γ` (base change
`K' ⊆ K''`). -/
theorem comap_kummer [CompactSpace Γ] (Γ' : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
    [CompactSpace Γ'] (hle : Γ' ≤ Γ) (hΓ' : ∀ σ ∈ Γ', FGL.CoeffFixed p R σ)
    (x : (P.F.galRep Γ hΓ).invariants) :
    ContH1.comap (Kummer.tpRep (P.F.galRep Γ hΓ) p) (Subgroup.inclusion hle)
        (continuous_inclusion hle) (P.kummer Γ hΓ hR x) =
      P.kummer Γ' hΓ' hR ⟨x, fun σ => x.2 (Subgroup.inclusion hle σ)⟩ :=
  Kummer.comap_kummer _ (continuous_inclusion hle) _ _ (P.stabHyp Γ' hΓ') x

end General

section Tate

variable {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [UniformSpace R] [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (P : PDivFGL R d p)

/-- `Kummer.Tp (F(m_{ℂ_p})) = T_p F` (same underlying sequences). -/
def tpToTate (x : Kummer.Tp (P.F.Pt p) p) : P.F.tate p :=
  ⟨Kummer.val _ p x, (FGL.mem_tate (F := P.F)).mpr (Kummer.val_mem x)⟩

/-- **`T_p F ≅ T_p(F[p^∞])(O_{ℂ_p})`**, the map underlying the identification of the coefficients
of `kummer` with the Tate module of the `p`-divisible group `F[p^∞]` (bijective by
`tateToPDiv_bijective`). -/
def tpToPDiv (x : Kummer.Tp (P.F.Pt p) p) : P.pdivGroup.TateModule (OC p) :=
  P.tateToPDiv (P.tpToTate x)

theorem tpToPDiv_bijective (hR : ∀ r ∈ maximalIdeal R, ‖(algebraMap R (OC p) r : ℂ_[p])‖ < 1) :
    Function.Bijective P.tpToPDiv := by
  refine (P.tateToPDiv_bijective hR).comp ⟨fun a b h => Kummer.ext fun n => ?_, fun y => ?_⟩
  · exact congrFun (congrArg Subtype.val h) n
  · exact ⟨Kummer.mk y.1 ((FGL.mem_tate (F := P.F)).mp y.2), rfl⟩

/-- **`T_p(f) = T_p(f[p^∞])`**: the map of Tate modules induced by a homomorphism of formal group
laws is the one induced by the homomorphism `FGL.Hom.toPDiv` of `p`-divisible groups. -/
theorem tpToPDiv_map {d' : ℕ} {P' : PDivFGL R d' p} (φ : FGL.Hom P.F P'.F)
    (x : Kummer.Tp (P.F.Pt p) p) :
    P'.tpToPDiv (Kummer.map φ.ptHom x) = φ.toPDiv.mapTate (OC p) (P.tpToPDiv x) := by
  refine Subtype.ext (funext fun v => ?_)
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun a => ?_
  have h := congrArg (fun f => f a) (φ.layerPt_comp_layerMap v
    ⟨Kummer.val _ p x v, P.F.tate_mem_torsionBy (P.tpToTate x).2 v⟩)
  exact h.symm

/-- **Every homomorphism `ψ : F[p^∞] → F'[p^∞]` of `p`-divisible groups acts on Kummer
coefficients**: by Serre–Tate (`FGL.Hom.pdivEquiv`) `ψ = f[p^∞]` for a homomorphism
`f : F → F'` of formal group laws, and `T_p(f)` (which carries `κ_F` to `κ_{F'}`,
`map_kummer`) is `T_p(ψ)` on the Tate modules of the `p`-divisible groups. -/
theorem exists_fglHom_tpToPDiv {d' : ℕ} {P' : PDivFGL R d' p} (hpm : (p : R) ∈ maximalIdeal R)
    (ψ : PDivGroup.Hom P.pdivGroup P'.pdivGroup) :
    ∃ φ : FGL.Hom P.F P'.F, φ.toPDiv = ψ ∧
      ∀ x, P'.tpToPDiv (Kummer.map φ.ptHom x) = ψ.mapTate (OC p) (P.tpToPDiv x) := by
  obtain ⟨φ, rfl⟩ := (FGL.Hom.pdivEquiv hpm).surjective ψ
  exact ⟨φ, rfl, P.tpToPDiv_map φ⟩

end Tate

section OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L] {d : ℕ}
  (P : PDivFGL (OL L) d p)

/-- `G_{K'} = L.fixingSubgroup` fixes the coefficients `O_{K'}`. -/
theorem coeffFixed_OL : ∀ σ ∈ L.fixingSubgroup, FGL.CoeffFixed p (OL L) σ := fun σ hσ =>
  OL.galFixedOver (IntermediateField.fixingSubgroupEquiv L ⟨σ, hσ⟩)

instance compactSpace_fixingSubgroup : CompactSpace L.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed L).isCompact

/-- The action of `G_{K'} = Gal(ℚ̄_p/K')` on `F(m_{ℂ_p})`. -/
abbrev galRepOL : Representation ℤ L.fixingSubgroup (P.F.Pt p) :=
  P.F.galRep L.fixingSubgroup coeffFixed_OL

/-- **The `G_{K'}`-invariants of `F(m_{ℂ_p})` are `F(m_{K'})`**, the points with coordinates in
`K'` (Ax–Sen–Tate, `FGL.galPt_fixed_iff`). -/
theorem mem_invariants_galRepOL_iff (x : P.F.Pt p) :
    x ∈ P.galRepOL.invariants ↔ ∀ j, ((x.1 j : OC p) : ℂ_[p]) ∈ cpSubmodule L := by
  rw [← P.F.galPt_fixed_iff L x]
  constructor
  · intro h σ
    exact h ((IntermediateField.fixingSubgroupEquiv L).symm σ)
  · intro h σ
    exact h (IntermediateField.fixingSubgroupEquiv L σ)

/-- **The Kummer map over `O_{K'}`**: `κ : F(m_{K'}) → H¹_cont(G_{K'}, T_p F)` for a
`p`-divisible formal group law `F` over `O_{K'}` (`T_p F ≅ T_p(F[p^∞])`, `tpToPDiv`). -/
def kummerOL :
    P.galRepOL.invariants →ₗ[ℤ] ContH1.H1 (Kummer.tpRep P.galRepOL p) :=
  P.kummer L.fixingSubgroup coeffFixed_OL OL.norm_lt_one

/-- **Base change `K' ⊆ K''`**: the restriction of `κ_{K'}(x)` to `G_{K''}` is `κ_{K''}(x)`
for `F` viewed over `O_{K''}` (the action of `G_{K''}` on `F(m_{ℂ_p})` is the restricted one). -/
theorem comap_kummerOL {L'' : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] L''] (hLL : L ≤ L'') (x : P.galRepOL.invariants) :
    ContH1.comap (Kummer.tpRep P.galRepOL p)
        (Subgroup.inclusion (IntermediateField.fixingSubgroup_antitone hLL))
        (continuous_inclusion (IntermediateField.fixingSubgroup_antitone hLL)) (P.kummerOL x) =
      P.kummer L''.fixingSubgroup
        (fun σ hσ => coeffFixed_OL σ (IntermediateField.fixingSubgroup_antitone hLL hσ))
        OL.norm_lt_one
        ⟨x, fun σ => x.2 (Subgroup.inclusion (IntermediateField.fixingSubgroup_antitone hLL) σ)⟩ :=
  P.comap_kummer _ _ _ _ _ _ x

end OL

end PDivFGL

end PadicHodge
