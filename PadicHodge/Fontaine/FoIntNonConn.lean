/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.FoIntLattice
import PadicHodge.Fontaine.HomRep
import PadicHodge.FormalGroup.TateNonConnOL
import PadicHodge.HodgeTate.Splitting

/-!
# (FoInt) for a non-connected `p`-divisible group `H` over `O_{K'}`

Let `H = G` be a `p`-divisible group over `O_L = O_{K'}` (`OL L`) with connected part
`H⁰ ≅ F[p^∞]`, `F` a `p`-divisible formal group law of dimension `d` over `O_L` (`φ`, `ψ`;
`PDivGroup.exists_connPart_iso_OL`). Write `T = T_p H(ℚ̄_p)`, `T_F = T_p F` (`Kummer.Tp`),
`ι : T_F ↪ T` (through `T_p(F[p^∞]_L) ≅ T_p(H⁰_L) ⊆ T`, `fP`), and
`W = Hom_{ℤ_p}(T, ℂ_p) = M ⊗ ℚ`, `M = Hom_{ℤ_p}(T, O_{ℂ_p}) = Hom(T_p H, Ô(1))` (`ℂ_p(1)`
trivialised by `ε`). We restate the (FoInt) package of `Fontaine/FoIntDecomp.lean`,
`Fontaine/FoIntLattice.lean` for `H`:

* **(a) Fontaine's pairing on `T_p H`** (`PDivGroup.rhoH`): `ρ_H(ω_l) : T → ℂ_p` is the unique
  `ℤ_p`-linear map with `ρ_H(ω_l)(σ x) = χ(σ) σ(ρ_H(ω_l)(x))` extending Fontaine's
  `ρ(ω_l) = rhoZp` on `T_F` (`rhoH_comp_iF`, `rhoH_gal`, uniqueness `rhoH_unique`, also for every
  finite `K'' ⊇ K'`, i.e. it is the *same* map for every tame `K''`). Fontaine's `ρ_H`
  ([Fo, §5.6], `u ↦ u^*ω`) restricts to `ρ` on `T_p(H⁰)` and is `G_{K'}`-equivariant, so it *is*
  this map. Existence: the obstruction lies in `H¹(G_L, ℂ_p(-1))^r = 0` (Tate), i.e.
  `D_1(V^∨) → D_1(V_F^∨)` is onto because the étale quotient `V^{et} = V / V_F` is Hodge–Tate of
  weight `0` (`TateNonConnOL`: `isHodgeTate_etRepOL`) — `exists_DHT_lift` applied to
  `0 → (V^{et})^∨ → V^∨ → V_F^∨ → 0`. `p^N ρ_H` is integral for some `N` (`exists_pow_rhoH`).
* **(b) Decomposition** (`isCompl_V0H_V1H`): `W = V₀ ⊕ V₁` with `V₀ = ∑ ℂ_p ρ_H(ω_l)` (dimension
  `d`, `finrank_V0H`) and `V₁ = {f | f ∘ ι ∈ V₁(F)}` (`V1H`, dimension `h - d`), where
  `V₁(F) = ℂ_p · Hom_{G_L}(T_F, ℂ_p)` is the `ℂ_p(1)`-isotypic part for `F`. `V₁` contains the
  `ℂ_p(1)`-isotypic part of `W` (`isEquiv_mem_V1H`) and the étale classes
  `ker(W → W_F) = Hom(T / T_F, ℂ_p)` (`ker_restr_le_V1H`), which are themselves spanned by
  `G_L`-equivariant maps (`ker_restr_le_span_isEquiv`); so `V₁` is an extension of `ℂ_p(1)`-isotypic
  pieces. That `V₁` *equals* the `ℂ_p(1)`-isotypic part of `W` is Tate's Hodge–Tate decomposition
  for the non-connected `H`, which needs `h = d + d^∨` for `H` and its Cartier dual
  ([Hong, Thm. 2.2.19, Thm. 3.4.12]); the Cartier dual of a non-connected `p`-divisible group over
  `O_L` is not available here, and it is not needed for the weight argument of [LocAn] §9.
* **(c) Cokernel / lattice bound** (`exists_lattice_H`): there are `N`, `c` with
  `p^c M ⊆ p^N ρ_H(O_{ℂ_p}^d) + (M ∩ V₁)`.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

namespace PDivGroup

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "K" => PadicAlgCl p

variable [FiniteDimensional ℚ_[p] L]

local instance instNormalL'' : Normal L (PadicAlgCl p) :=
  Normal.tower_top_of_normal ℚ_[p] L (PadicAlgCl p)

omit [FiniteDimensional ℚ_[p] L] in
/-- Shortcut instance (avoids a slow search through normed-space instances on `L`). -/
local instance (priority := high) instModuleDHT'' {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) (q : ℤ) :
    Module L (DHT ρ q) :=
  (DHT ρ q).module

omit [FiniteDimensional ℚ_[p] L] in
/-- Shortcut instance (avoids a slow search through normed-space instances on `L`). -/
local instance (priority := high) instAddCommGroupDHT'' {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) (q : ℤ) :
    AddCommGroup (DHT ρ q) :=
  (DHT ρ q).addCommGroup

variable (G : PDivGroup (OL L) p)

/-- The `G_L`-action on `T / T⁰` as a `ℤ_p`-representation. -/
def etRepZ : Representation ℤ_[p] (K ≃ₐ[L] K) G.EtTateOL where
  toFun := G.galQOL
  map_one' := G.galQ_oneOL
  map_mul' := G.galQ_mulOL

/-- `ℂ_p ⊗ V^{et}` is trivial: `dim_L D_0((V^{et})^∨) = rank(T / T⁰)`, and
`D_q((V^{et})^∨) = 0` for `q ≠ 0`. -/
theorem finrank_DHT_etRepOL_dual (q : ℤ) (hq : q ≠ 0) : finrank L (DHT G.etRepOL.dual q) = 0 := by
  have h0 := G.isHodgeTate_etRepOL.2
  rw [count_htWeights] at h0
  have h := finrank_DHT_add_finrank_DHT_dual_le G.etRepOL (q := 0) (q' := q) (by simpa using hq)
  omega

theorem finrank_dual_etRepOL_le : finrank ℚ_[p] (Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] G.EtTateOL)) ≤
    finrank L (DHT G.etRepOL.dual 0) := by
  have hHT := isHodgeTate_dual _ G.isHodgeTate_etRepOL.1
  have hS : Function.support (fun q => finrank L (DHT G.etRepOL.dual q)) ⊆ ({0} : Finset ℤ) := by
    intro q hq
    by_contra h0
    exact hq (G.finrank_DHT_etRepOL_dual q (by simpa using h0))
  have h1 := htDim_eq_sum G.etRepOL.dual hS
  rw [Finset.sum_singleton] at h1
  unfold IsHodgeTate at hHT
  rw [h1] at hHT
  exact hHT.ge

theorem finrank_E_etRepZ_zero : finrank ℤ_[p] G.EtTateOL ≤ finrank L (HomRep.E G.etRepZ 0) := by
  rw [HomRep.finrank_E G.etRepZ (ρ := G.etRepOL) (fun _ => rfl)]
  refine le_trans ?_ G.finrank_dual_etRepOL_le
  rw [Subspace.dual_finrank_eq, Module.finrank_baseChange]

variable {G} {d : ℕ} (P : PDivFGL (OL L) d p) (φ : Hom G.connPart P.pdivGroup)
  (ψ : Hom P.pdivGroup G.connPart)

/-- `T_p(F[p^∞]_L) → T_p(H⁰_L) → T_p(H_L)`. -/
def fP : Additive (P.genericFibreOL.TateModule K) →ₗ[ℤ_[p]]
    Additive ((G.baseChange L).TateModule K) :=
  G.connTateLinOL ∘ₗ (Hom.baseChange (S := L) ψ).tateLin

theorem fP_galLin (σ : K ≃ₐ[L] K) (y : Additive (P.genericFibreOL.TateModule K)) :
    fP P ψ (P.genericFibreOL.galLin σ y) = (G.baseChange L).galLin σ (fP P ψ y) := rfl

include φ in
theorem fP_injective (hφψ : φ.comp ψ = Hom.id _) : Function.Injective (fP P ψ) :=
  G.connTateLin_injectiveOL.comp
    (Function.LeftInverse.injective (tateLin_baseChange_comp_eqOL φ ψ hφψ))

include φ in
theorem range_fP (hψφ : ψ.comp φ = Hom.id _) : LinearMap.range (fP P ψ) = G.connTateOL := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨(Hom.baseChange (S := L) φ).tateLin y, ?_⟩
    change G.connTateLinOL _ = _
    rw [tateLin_baseChange_comp_eqOL ψ φ hψφ]

/-- `ι : T_p F → T_p H(ℚ̄_p)`. -/
def iF : Kummer.Tp (P.F.Pt p) p →ₗ[ℤ_[p]] Additive ((G.baseChange L).TateModule K) :=
  fP P ψ ∘ₗ P.tpLinEquiv.toLinearMap

theorem iF_tpRep (σ : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p) :
    iF P ψ (Kummer.tpRep P.galRepOL p σ x) =
      (G.baseChange L).galLin (IntermediateField.fixingSubgroupEquiv L σ) (iF P ψ x) := by
  change fP P ψ (P.tpLinEquiv _) = _
  rw [P.tpLinEquiv_tpRep, fP_galLin]
  rfl

/-- The restriction `W = Hom_{ℤ_p}(T_p H, ℂ_p) → W_F = Hom_{ℤ_p}(T_p F, ℂ_p)`, `f ↦ f ∘ ι`. -/
def restr : (Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p]) →ₗ[ℂ_[p]] P.WT where
  toFun f := f ∘ₗ iF P ψ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restr_apply (f : Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p])
    (x : Kummer.Tp (P.F.Pt p) p) : restr P ψ f x = f (iF P ψ x) := rfl

variable {ε : ℕ → PadicAlgCl p} (hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1)))
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

omit [FiniteDimensional ℚ_[p] L] in
theorem chiL_one_eq_chi (σ : K ≃ₐ[L] K) :
    algebraMap ℚ_[p] ℂ_[p] (chiL L 1 σ) =
      algebraMap ℚ_[p] ℂ_[p] ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) := by
  simp [chiL, chiPow_apply]

include hεp in
/-- `ρ(ω_l)` on `T_p(F[p^∞]_L)` has weight `1`. -/
theorem rhoZp_symm_mem_E_one (l : Fin d) :
    HomRep.ofW P.genericFibreOL.galRepZ
        (P.rhoZp hε hεp l ∘ₗ P.tpLinEquiv.symm.toLinearMap) ∈
      HomRep.E P.genericFibreOL.galRepZ 1 := by
  rw [HomRep.mem_E_one_iff]
  intro σ y
  obtain ⟨x, rfl⟩ := P.tpLinEquiv.surjective y
  have h := P.tpLinEquiv_tpRep ((IntermediateField.fixingSubgroupEquiv L).symm σ) x
  rw [MulEquiv.apply_symm_apply] at h
  change P.rhoZp hε hεp l (P.tpLinEquiv.symm (P.genericFibreOL.galLin σ (P.tpLinEquiv x))) =
    _ * galCp L σ (P.rhoZp hε hεp l (P.tpLinEquiv.symm (P.tpLinEquiv x)))
  rw [← h, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    PDivFGL.rhoZp_apply, PDivFGL.rhoZp_apply, P.rho_tpRep hεp, MulEquiv.apply_symm_apply,
    chiL_one_eq_chi]

/-! ### Existence of `ρ_H` -/

include φ in
/-- The lift of `ρ(ω_l)` along `0 → T_p(F[p^∞]_L) → T_p H → T / T⁰ → 0`
(`HomRep.exists_lift_E_one`; `V^{et}` is Hodge–Tate of weight `0`). -/
theorem exists_rhoH (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _) (l : Fin d) :
    ∃ f : Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p],
      HomRep.ofW (G.baseChange L).galRepZ f ∈ HomRep.E (G.baseChange L).galRepZ 1 ∧
      f ∘ₗ fP P ψ = P.rhoZp hε hεp l ∘ₗ P.tpLinEquiv.symm.toLinearMap := by
  have hex0 : Function.Exact (fP P ψ) G.connTateOL.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, range_fP P φ ψ hψφ]
  exact HomRep.exists_lift_E_one (act := (G.baseChange L).galRepZ)
    (act' := P.genericFibreOL.galRepZ) (act'' := G.etRepZ)
    (ρ := (G.baseChange L).tateRepOver) (ρ' := P.tateRepOL) (ρ'' := G.etRepOL)
    (hρ := fun _ => rfl) (hρ' := fun _ => rfl) (hρ'' := fun _ => rfl) (fP P ψ) G.connTateOL.mkQ
    (fP_injective P φ ψ hφψ) (Submodule.mkQ_surjective _) hex0 (fun σ x => fP_galLin P ψ σ x)
    (fun σ x => (galQ_mkOL G σ x).symm)
    (continuous_dual (fun φ v => (G.baseChange L).continuous_tateRepOver φ v))
    (isHodgeTate_dual _ G.isHodgeTate_etRepOL.1)
    (Submodule.finrank_eq_zero.mp (G.finrank_DHT_etRepOL_dual 1 one_ne_zero))
    _ (rhoZp_symm_mem_E_one P hε hεp l)

variable (hφψ : φ.comp ψ = Hom.id _) (hψφ : ψ.comp φ = Hom.id _)

/-- **Fontaine's pairing on `T_p H`**: `ρ_H(ω_l) : T_p H(ℚ̄_p) → ℂ_p`, the `G_L`-equivariant
(`ℂ_p(1)`-valued) extension of `ρ(ω_l)` on `T_p F`. -/
def rhoH (l : Fin d) : Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p] :=
  Classical.choose (exists_rhoH P φ ψ hε hεp hφψ hψφ l)

theorem rhoH_mem_E (l : Fin d) :
    HomRep.ofW (G.baseChange L).galRepZ (rhoH P φ ψ hε hεp hφψ hψφ l) ∈
      HomRep.E (G.baseChange L).galRepZ 1 :=
  (Classical.choose_spec (exists_rhoH P φ ψ hε hεp hφψ hψφ l)).1

theorem rhoH_comp_fP (l : Fin d) :
    rhoH P φ ψ hε hεp hφψ hψφ l ∘ₗ fP P ψ = P.rhoZp hε hεp l ∘ₗ P.tpLinEquiv.symm.toLinearMap :=
  (Classical.choose_spec (exists_rhoH P φ ψ hε hεp hφψ hψφ l)).2

/-- **`ρ_H` extends `ρ`**: `ρ_H(ω_l) ∘ ι = ρ(ω_l)`. -/
theorem rhoH_comp_iF (l : Fin d) :
    restr P ψ (rhoH P φ ψ hε hεp hφψ hψφ l) = P.rhoZp hε hεp l := by
  refine LinearMap.ext fun x => ?_
  have h := LinearMap.congr_fun (rhoH_comp_fP P φ ψ hε hεp hφψ hψφ l) (P.tpLinEquiv x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  exact h

/-- **`ρ_H` is `G_L`-equivariant**: `ρ_H(ω_l)(σ x) = χ(σ) σ(ρ_H(ω_l)(x))`. -/
theorem rhoH_gal (l : Fin d) (σ : K ≃ₐ[L] K) (x : Additive ((G.baseChange L).TateModule K)) :
    rhoH P φ ψ hε hεp hφψ hψφ l ((G.baseChange L).galLin σ x) =
      algebraMap ℚ_[p] ℂ_[p] (chiL L 1 σ) * galCp L σ (rhoH P φ ψ hε hεp hφψ hψφ l x) :=
  (HomRep.mem_E_one_iff _ _).mp (rhoH_mem_E P φ ψ hε hεp hφψ hψφ l) σ x

/-! ### Uniqueness: the étale quotient has no weight-`j` classes, `j ≠ 0` -/

omit [FiniteDimensional ℚ_[p] L] in
theorem chiL_resGal {L' : IntermediateField ℚ_[p] K} (h : L ≤ L') (j : ℤ) (σ : K ≃ₐ[L'] K) :
    chiL L j (HomRep.resGal h σ) = chiL L' j σ := rfl

include hψφ in
/-- A map `T_p H → ℂ_p` vanishing on `T_p(H⁰)` with `f(σ x) = χ(σ)^j σ(f x)` on `G_{L'}`
(`L ⊆ L'` finite, `j ≠ 0`) is zero. -/
theorem eq_zero_of_comp_fP (f : Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p])
    (hf0 : f ∘ₗ fP P ψ = 0) {L' : IntermediateField ℚ_[p] K} [FiniteDimensional ℚ_[p] L']
    (hLL' : L ≤ L') {j : ℤ} (hj : j ≠ 0)
    (hf : ∀ (σ : K ≃ₐ[L'] K) x, f ((G.baseChange L).galLin (HomRep.resGal hLL' σ) x) =
      algebraMap ℚ_[p] ℂ_[p] (chiL L' j σ) * galCp L' σ (f x)) : f = 0 := by
  have hle : G.connTateOL ≤ LinearMap.ker f := by
    rw [← range_fP P φ ψ hψφ]
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun hf0 y
  set fb := G.connTateOL.liftQ f hle
  have hfb : fb = 0 := by
    refine HomRep.eq_zero_of_isTwist G.etRepZ G.finrank_E_etRepZ_zero hLL' hj fb ?_
    intro σ q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    change fb (G.galQOL _ (G.connTateOL.mkQ x)) = _
    rw [galQ_mkOL]
    exact hf σ x
  refine LinearMap.ext fun x => ?_
  have := LinearMap.congr_fun hfb (G.connTateOL.mkQ x)
  exact this

/-- **Uniqueness of `ρ_H`**, also over every finite `L' ⊇ L` (e.g. a tame `K''/K'`): a map
`f : T_p H → ℂ_p` with `f ∘ ι = ρ(ω_l)` and `f(σ x) = χ(σ) σ(f x)` for `σ ∈ G_{L'}` is
`ρ_H(ω_l)`. -/
theorem rhoH_unique (l : Fin d) (f : Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p])
    (hfr : restr P ψ f = P.rhoZp hε hεp l) {L' : IntermediateField ℚ_[p] K}
    [FiniteDimensional ℚ_[p] L'] (hLL' : L ≤ L')
    (hf : ∀ (σ : K ≃ₐ[L'] K) x, f ((G.baseChange L).galLin (HomRep.resGal hLL' σ) x) =
      algebraMap ℚ_[p] ℂ_[p] (chiL L' 1 σ) * galCp L' σ (f x)) :
    f = rhoH P φ ψ hε hεp hφψ hψφ l := by
  have h0 := eq_zero_of_comp_fP P φ ψ hψφ (f - rhoH P φ ψ hε hεp hφψ hψφ l) ?_ hLL' one_ne_zero ?_
  · exact sub_eq_zero.mp h0
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := P.tpLinEquiv.surjective y
    have h1 := LinearMap.congr_fun hfr x
    have h2 := LinearMap.congr_fun (rhoH_comp_iF P φ ψ hε hεp hφψ hψφ l) x
    rw [restr_apply] at h1 h2
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.zero_apply]
    change f (iF P ψ x) - rhoH P φ ψ hε hεp hφψ hψφ l (iF P ψ x) = 0
    rw [h1, h2, sub_self]
  · intro σ x
    rw [LinearMap.sub_apply, LinearMap.sub_apply, hf, rhoH_gal, HomRep.galCp_resGal, chiL_resGal,
      map_sub, mul_sub]

/-! ### (b): the decomposition `W = V₀ ⊕ V₁` -/

theorem linearIndependent_rhoH : LinearIndependent ℂ_[p] (rhoH P φ ψ hε hεp hφψ hψφ) := by
  have h : restr P ψ ∘ rhoH P φ ψ hε hεp hφψ hψφ = P.rhoZp hε hεp :=
    funext fun l => rhoH_comp_iF P φ ψ hε hεp hφψ hψφ l
  have hli := P.linearIndependent_rhoZp hε hεp
  rw [← h] at hli
  exact LinearIndependent.of_comp _ hli

/-- `V₀ = ∑_l ℂ_p ρ_H(ω_l)`. -/
def V0H : Submodule ℂ_[p] (Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p]) :=
  Submodule.span ℂ_[p] (Set.range (rhoH P φ ψ hε hεp hφψ hψφ))

/-- `V₁ = {f | f ∘ ι ∈ V₁(F)}`. -/
def V1H : Submodule ℂ_[p] (Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p]) :=
  P.V1.comap (restr P ψ)

theorem restr_sum (c : Fin d → ℂ_[p]) :
    restr P ψ (∑ l, c l • rhoH P φ ψ hε hεp hφψ hψφ l) = ∑ l, c l • P.rhoZp hε hεp l := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, rhoH_comp_iF]

include hεp in
/-- **(FoInt)(b) for `H`**: `Hom_{ℤ_p}(T_p H, ℂ_p) = V₀ ⊕ V₁`. -/
theorem isCompl_V0H_V1H : IsCompl (V0H P φ ψ hε hεp hφψ hψφ) (V1H P ψ) := by
  have hc := P.isCompl_V0_V1 hε hεp
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro f hf0 hf1
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ_[p]).mp hf0
    have h1 : restr P ψ (∑ l, c l • rhoH P φ ψ hε hεp hφψ hψφ l) ∈ P.V0 hε hεp :=
      (restr_sum P φ ψ hε hεp hφψ hψφ c).symm ▸
        Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have h2 := Submodule.disjoint_def.mp hc.disjoint _ h1 hf1
    rw [restr_sum] at h2
    have hc0 : c = 0 := by
      have := (Fintype.linearIndependent_iff.mp (P.linearIndependent_rhoZp hε hεp)) c h2
      exact funext this
    simp [hc0]
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    have hf := hc.sup_eq_top ▸ (Submodule.mem_top : restr P ψ f ∈ ⊤)
    obtain ⟨v0, hv0, v1, hv1, hv⟩ := Submodule.mem_sup.mp hf
    obtain ⟨c, rfl⟩ := (P.mem_V0_iff hε hεp v0).mp hv0
    have hmem : f - ∑ l, c l • rhoH P φ ψ hε hεp hφψ hψφ l ∈ V1H P ψ := by
      change restr P ψ _ ∈ P.V1
      rw [map_sub, restr_sum, ← hv, add_sub_cancel_left]
      exact hv1
    have hmem0 : ∑ l, c l • rhoH P φ ψ hε hεp hφψ hψφ l ∈ V0H P φ ψ hε hεp hφψ hψφ :=
      Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have : f = ∑ l, c l • rhoH P φ ψ hε hεp hφψ hψφ l +
        (f - ∑ l, c l • rhoH P φ ψ hε hεp hφψ hψφ l) := by abel
    rw [this]
    exact Submodule.add_mem_sup hmem0 hmem

omit [FiniteDimensional ℚ_[p] L] in
variable (G) in
/-- `dim_{ℂ_p} Hom_{ℤ_p}(T_p H, ℂ_p) = h`. -/
theorem finrank_hom_tate :
    finrank ℂ_[p] (Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p]) = G.height := by
  rw [finrank_hom_cp]
  exact (G.baseChange L).finrank_tate

/-- `dim V₀ = d`. -/
theorem finrank_V0H : finrank ℂ_[p] (V0H P φ ψ hε hεp hφψ hψφ) = d := by
  rw [V0H, finrank_span_eq_card (linearIndependent_rhoH P φ ψ hε hεp hφψ hψφ), Fintype.card_fin]

include φ hε hεp hφψ hψφ in
/-- `dim V₁ = h - d`. -/
theorem finrank_V1H : finrank ℂ_[p] (V1H P ψ) = G.height - d := by
  have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_V0H_V1H P φ ψ hε hεp hφψ hψφ)
  have hW := finrank_hom_tate G
  have h0 := finrank_V0H P φ ψ hε hεp hφψ hψφ
  omega

/-- The `ℂ_p(1)`-isotypic part of `W` lies in `V₁`. -/
theorem isEquiv_mem_V1H (f : Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p])
    (hf : HomRep.IsEquiv (G.baseChange L).galRepZ f) : f ∈ V1H P ψ := by
  refine Submodule.subset_span (?_ : P.IsEquiv (restr P ψ f))
  intro σ x
  rw [restr_apply, restr_apply, iF_tpRep]
  exact hf _ _

/-- The étale classes `Hom(T / T⁰, ℂ_p)` lie in `V₁`. -/
theorem ker_restr_le_V1H : LinearMap.ker (restr P ψ) ≤ V1H P ψ := fun f hf => by
  change restr P ψ f ∈ P.V1
  rw [LinearMap.mem_ker.mp hf]
  exact zero_mem _

include φ hψφ in
/-- The étale classes are spanned by `G_L`-equivariant maps (`ℂ_p ⊗ V^{et}` is trivial). -/
theorem ker_restr_le_span_isEquiv :
    LinearMap.ker (restr P ψ) ≤
      Submodule.span ℂ_[p] {f | HomRep.IsEquiv (G.baseChange L).galRepZ f} := by
  intro g hg
  have hg0 : g ∘ₗ fP P ψ = 0 := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := P.tpLinEquiv.surjective y
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hg) x
  have hle : G.connTateOL ≤ LinearMap.ker g := by
    rw [← range_fP P φ ψ hψφ]
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun hg0 y
  set gb := G.connTateOL.liftQ g hle
  let C : HomRep.HomT G.etRepZ →ₗ[ℂ_[p]]
      (Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p]) :=
    { toFun := fun h => HomRep.toW _ h ∘ₗ G.connTateOL.mkQ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hgC : g = C (HomRep.ofW _ gb) := LinearMap.ext fun x => rfl
  have hmem : HomRep.ofW G.etRepZ gb ∈ Submodule.span ℂ_[p]
      {f : HomRep.HomT G.etRepZ | HomRep.IsEquiv G.etRepZ (HomRep.toW _ f)} := by
    rw [HomRep.span_isEquiv_eq_top G.etRepZ G.finrank_E_etRepZ_zero]
    exact Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := C) hmem
  rw [Submodule.map_span] at hmap
  rw [hgC]
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨h, hh, rfl⟩
  intro σ x
  change HomRep.toW _ h (G.connTateOL.mkQ ((G.baseChange L).galLin σ x)) =
    galCp L σ (HomRep.toW _ h (G.connTateOL.mkQ x))
  rw [← galQ_mkOL]
  exact hh σ _

/-! ### (a), (c): integrality and the lattice lemma -/

/-- **`p^N ρ_H` is integral** for some `N`. -/
theorem exists_pow_rhoH :
    ∃ N : ℕ, ∀ a : Fin d → ℂ_[p], (∀ l, ‖a l‖ ≤ 1) →
      ∀ x : Additive ((G.baseChange L).TateModule K),
        ‖(p : ℂ_[p]) ^ N * ∑ l, a l * rhoH P φ ψ hε hεp hφψ hψφ l x‖ ≤ 1 :=
  HomRep.exists_pow_norm_le _

include hεp in
/-- **(FoInt)(c) for `H`, the lattice lemma**: there are `N`, `c` such that `p^N ρ_H` is integral
and for every `f ∈ M = Hom_{ℤ_p}(T_p H, O_{ℂ_p})` there is `a ∈ O_{ℂ_p}^d` with
`p^c f - p^N ∑_l a_l ρ_H(ω_l) ∈ M ∩ V₁`. -/
theorem exists_lattice_H :
    ∃ N c : ℕ, (∀ a : Fin d → ℂ_[p], (∀ l, ‖a l‖ ≤ 1) →
      ∀ x : Additive ((G.baseChange L).TateModule K),
        ‖(p : ℂ_[p]) ^ N * ∑ l, a l * rhoH P φ ψ hε hεp hφψ hψφ l x‖ ≤ 1) ∧
      ∀ f : Additive ((G.baseChange L).TateModule K) →ₗ[ℤ_[p]] ℂ_[p], (∀ x, ‖f x‖ ≤ 1) →
        ∃ a : Fin d → ℂ_[p], (∀ l, ‖a l‖ ≤ 1) ∧
          (p : ℂ_[p]) ^ c • f - (p : ℂ_[p]) ^ N • ∑ l, a l • rhoH P φ ψ hε hεp hφψ hψφ l ∈
            V1H P ψ ∧
          ∀ x, ‖((p : ℂ_[p]) ^ c • f -
            (p : ℂ_[p]) ^ N • ∑ l, a l • rhoH P φ ψ hε hεp hφψ hψφ l) x‖ ≤ 1 := by
  obtain ⟨N, hN⟩ := exists_pow_rhoH P φ ψ hε hεp hφψ hψφ
  obtain ⟨c, hc⟩ := HomRep.exists_lattice _ (linearIndependent_rhoH P φ ψ hε hεp hφψ hψφ)
    (V1H P ψ) (isCompl_V0H_V1H P φ ψ hε hεp hφψ hψφ) N hN
  exact ⟨N, c, hN, hc⟩

end PDivGroup

end PadicHodge
