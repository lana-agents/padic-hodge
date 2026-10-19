/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.FoIntLin
import PadicHodge.FormalGroup.HodgeTateOL
import PadicHodge.HodgeTate.Dual

/-!
# (FoInt) (b): the rational Hodge–Tate decomposition of `Hom_{ℤ_p}(T_p F, ℂ_p)`

Let `W = Hom_{ℤ_p}(T_p F, ℂ_p)` (`T_p F` free of rank `h` over `ℤ_p`, so `dim_{ℂ_p} W = h`),
`V₀ = ∑_l ℂ_p ρ(ω_l)` (the image of `ρ ⊗ ℂ_p`) and `V₁ = ℂ_p · Hom_{ℤ_p[G_L]}(T_p F, ℂ_p)`.
Then `W = V₀ ⊕ V₁` (`PDivFGL.isCompl_V0_V1`), `dim V₀ = d`, `dim V₁ = h - d`
([Fo, §5.7 (i)]: `θ⁰_formel` is an isomorphism).

Proof: `G_L` acts semilinearly on `W` by `(τ f)(x) = τ(f(τ⁻¹ x))`; the `ρ(ω_l)` are
`χ^{-1}`-eigenvectors (weight `1`), the `G_L`-equivariant maps are the invariants (weight `0`).
The Serre–Tate lemma (`SerreTate.linearIndependent_of_eigen`) makes the `ρ(ω_l)` together with an
`L`-basis of the invariants `ℂ_p`-linearly independent; the invariants have `L`-dimension `≥ d'`
since `D_0(V_p^∨) = (ℂ_p ⊗ V_p^∨)^{G_L}` (of dimension `d'`, `hodgeTate_decompositionOL`) injects
into them, and `h = d + d'`.
-/

noncomputable section

open Module TensorProduct

namespace PadicHodge

section GenericDual

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
  [Module.Finite ℤ_[p] A]

theorem dualEquiv_qsmul {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
    (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] V) (q : ℚ_[p]) (y : ℂ_[p] ⊗[ℚ_[p]] V) :
    dualEquiv (V := V) w (q • y) = algebraMap ℚ_[p] ℂ_[p] q * dualEquiv (V := V) w y := by
  rw [← algebraMap_smul ℂ_[p] q y, map_smul, smul_eq_mul]

variable (p) in
/-- `a ↦ 1 ⊗ 1 ⊗ a ∈ ℂ_p ⊗ (ℚ_p ⊗ A)`. -/
def yA (a : A) : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] A) := (1 : ℂ_[p]) ⊗ₜ ((1 : ℚ_[p]) ⊗ₜ a)

omit [Module.Finite ℤ_[p] A] in
theorem yA_add (a b : A) : yA p (a + b) = yA p a + yA p b := by
  simp only [yA, tmul_add]

omit [Module.Finite ℤ_[p] A] in
theorem yA_smul (c : ℤ_[p]) (a : A) :
    yA p (c • a) = (algebraMap ℤ_[p] ℚ_[p] c) • yA p a := by
  rw [yA, yA, tmul_smul, ← algebraMap_smul ℚ_[p] c ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] a), tmul_smul]

/-- `w ↦ (a ↦ w(1 ⊗ 1 ⊗ a))`, `ℂ_p ⊗ (ℚ_p ⊗ A)^∨ → Hom_{ℤ_p}(A, ℂ_p)`. -/
def PhiA (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) : A →ₗ[ℤ_[p]] ℂ_[p] where
  toFun a := dualEquiv w (yA p a)
  map_add' a b := by rw [yA_add, map_add]
  map_smul' c a := by
    rw [yA_smul, dualEquiv_qsmul, RingHom.id_apply, Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] ℂ_[p]]

/-- `ℂ_p ⊗ (ℚ_p ⊗ A)^∨ → Hom_{ℤ_p}(A, ℂ_p)`, `ℂ_p`-linear. -/
def PhiAL : (ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) →ₗ[ℂ_[p]] (A →ₗ[ℤ_[p]] ℂ_[p]) where
  toFun := PhiA
  map_add' w w' := LinearMap.ext fun a => by
    change dualEquiv (w + w') _ = dualEquiv w _ + dualEquiv w' _
    rw [map_add, LinearMap.add_apply]
  map_smul' c w := LinearMap.ext fun a => by
    change dualEquiv (c • w) _ = c • dualEquiv w _
    rw [map_smul, LinearMap.smul_apply]

theorem PhiAL_apply (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) (a : A) :
    PhiAL w a = dualEquiv w (yA p a) := rfl

theorem PhiAL_injective :
    Function.Injective (PhiAL : (ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] A)) →ₗ[ℂ_[p]] _) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have h1 : ∀ a : A, dualEquiv w ((1 : ℂ_[p]) ⊗ₜ ((1 : ℚ_[p]) ⊗ₜ a)) = 0 := fun a =>
    LinearMap.congr_fun hw a
  have h2 : ∀ v : ℚ_[p] ⊗[ℤ_[p]] A, dualEquiv w ((1 : ℂ_[p]) ⊗ₜ v) = 0 := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => rw [tmul_zero, map_zero]
    | tmul q a =>
      have : (q ⊗ₜ[ℤ_[p]] a : ℚ_[p] ⊗[ℤ_[p]] A) = q • ((1 : ℚ_[p]) ⊗ₜ a) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this, tmul_smul, dualEquiv_qsmul, h1, mul_zero]
    | add v v' hv hv' => rw [tmul_add, map_add, hv, hv', add_zero]
  have h3 : dualEquiv w = 0 := by
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.zero_apply]
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul c v =>
      have : (c ⊗ₜ[ℚ_[p]] v : ℂ_[p] ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] A)) = c • ((1 : ℂ_[p]) ⊗ₜ v) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, h2, smul_zero]
    | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  exact (LinearEquiv.map_eq_zero_iff _).mp h3

end GenericDual

namespace PDivFGL

variable {p : ℕ} [hp : Fact p.Prime] {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] L] {d : ℕ} (P : PDivFGL (OL L) d p)

omit [FiniteDimensional ℚ_[p] L] in
/-- Shortcut instance (avoids a slow search through normed-space instances on `L`). -/
local instance (priority := high) instModuleDHT' {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) (q : ℤ) :
    Module L (DHT ρ q) :=
  (DHT ρ q).module

omit [FiniteDimensional ℚ_[p] L] in
/-- Shortcut instance. -/
local instance (priority := high) instAddCommGroupDHT' {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) V) (q : ℤ) :
    AddCommGroup (DHT ρ q) :=
  (DHT ρ q).addCommGroup

/-- `Hom_{ℤ_p}(T_p F, ℂ_p)`. -/
abbrev WT := Kummer.Tp (P.F.Pt p) p →ₗ[ℤ_[p]] ℂ_[p]

omit [FiniteDimensional ℚ_[p] L] in
theorem galCp_mul_apply (a b : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (z : ℂ_[p]) :
    galCp L (a * b) z = galCp L a (galCp L b z) := by
  rw [map_mul]; rfl

theorem tpRep_mul_apply (a b : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p) :
    Kummer.tpRep P.galRepOL p (a * b) x =
      Kummer.tpRep P.galRepOL p a (Kummer.tpRep P.galRepOL p b x) := by
  rw [map_mul]; rfl

theorem tpRep_inv_apply (a : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p) :
    Kummer.tpRep P.galRepOL p a⁻¹ (Kummer.tpRep P.galRepOL p a x) = x := by
  rw [← tpRep_mul_apply, inv_mul_cancel, map_one]; rfl

/-- `σ ∈ G_L` as a `ℤ_p`-linear map of `ℂ_p`. -/
def galCpZp (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) : ℂ_[p] →ₗ[ℤ_[p]] ℂ_[p] :=
  (galCpLin L τ).restrictScalars ℤ_[p]

/-- The semilinear action `(τ f)(x) = τ(f(τ⁻¹ x))` on `W`. -/
def gact (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (f : P.WT) : P.WT :=
  galCpZp τ ∘ₗ f ∘ₗ
    Kummer.tpRepZp p P.galRepOL ((IntermediateField.fixingSubgroupEquiv L).symm τ⁻¹)

theorem gact_apply (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (f : P.WT)
    (x : Kummer.Tp (P.F.Pt p) p) :
    P.gact τ f x = galCp L τ (f (Kummer.tpRep P.galRepOL p
      ((IntermediateField.fixingSubgroupEquiv L).symm τ⁻¹) x)) :=
  rfl

/-- `W` as a type carrying the semilinear `G_L`-action. -/
@[nolint unusedArguments]
def HomT (_P : PDivFGL (OL L) d p) : Type := Kummer.Tp (_P.F.Pt p) p →ₗ[ℤ_[p]] ℂ_[p]

instance : AddCommGroup P.HomT := inferInstanceAs (AddCommGroup P.WT)
instance : Module ℂ_[p] P.HomT := inferInstanceAs (Module ℂ_[p] P.WT)
instance : Module L P.HomT := Module.compHom P.HomT (algebraMap L ℂ_[p])

instance : IsScalarTower L ℂ_[p] P.HomT where
  smul_assoc a c w := by
    rw [Algebra.smul_def, mul_smul]
    rfl

/-- `HomT P = W`. -/
def toW : P.HomT → P.WT := id

/-- `W = HomT P`. -/
def ofW : P.WT → P.HomT := id

instance : DistribMulAction (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) P.HomT where
  smul τ f := P.ofW (P.gact τ (P.toW f))
  one_smul f := LinearMap.ext fun x => by
    change P.gact 1 (P.toW f) x = P.toW f x
    rw [gact_apply, inv_one, map_one, map_one, map_one]
    rfl
  mul_smul a b f := LinearMap.ext fun x => by
    change P.gact (a * b) (P.toW f) x = P.gact a (P.gact b (P.toW f)) x
    rw [gact_apply, gact_apply, gact_apply, mul_inv_rev,
      map_mul (IntermediateField.fixingSubgroupEquiv L).symm, tpRep_mul_apply,
      galCp_mul_apply]
  smul_zero τ := LinearMap.ext fun x => by
    change P.gact τ 0 x = 0
    rw [gact_apply, LinearMap.zero_apply, map_zero]
  smul_add τ f g := LinearMap.ext fun x => by
    change P.gact τ (P.toW f + P.toW g) x = P.gact τ (P.toW f) x + P.gact τ (P.toW g) x
    rw [gact_apply, gact_apply, gact_apply, LinearMap.add_apply, map_add]

theorem smul_homT_apply (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (f : P.HomT)
    (x : Kummer.Tp (P.F.Pt p) p) :
    P.toW (τ • f) x = galCp L τ (P.toW f (Kummer.tpRep P.galRepOL p
      ((IntermediateField.fixingSubgroupEquiv L).symm τ⁻¹) x)) := rfl

theorem smul_distrib_homT (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) (c : ℂ_[p]) (f : P.HomT) :
    τ • c • f = (τ • c) • (τ • f) := LinearMap.ext fun x => by
  change galCp L τ (c * _) = galCp L τ c * galCp L τ _
  rw [map_mul]
  rfl

/-- The `ψ_q`-eigenspaces of `W` (`ψ_q = χ^{-q}`). -/
def E (q : ℤ) : Submodule L P.HomT :=
  SerreTate.eigen (htSetup L) P.HomT P.smul_distrib_homT q

/-- `f : T_p F → ℂ_p` is `G_L`-equivariant. -/
def IsEquiv (f : P.WT) : Prop :=
  ∀ (σ : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p),
    f (Kummer.tpRep P.galRepOL p σ x) =
      galCp L (IntermediateField.fixingSubgroupEquiv L σ) (f x)

theorem mem_E_zero_iff (f : P.WT) : P.ofW f ∈ P.E 0 ↔ P.IsEquiv f := by
  change (∀ τ, τ • P.ofW f = (htSetup L).ψ 0 τ • P.ofW f) ↔ _
  simp only [(htSetup L).ψ_zero, one_smul]
  constructor
  · intro h σ x
    have := LinearMap.congr_fun (h (IntermediateField.fixingSubgroupEquiv L σ))
      (Kummer.tpRep P.galRepOL p σ x)
    change P.gact _ f _ = f _ at this
    rw [gact_apply, ← map_inv, MulEquiv.symm_apply_apply, tpRep_inv_apply] at this
    exact this.symm
  · intro h τ
    refine LinearMap.ext fun x => ?_
    change P.gact τ f x = f x
    rw [gact_apply, h, MulEquiv.apply_symm_apply, galCp_galCp_inv]

variable {ε : ℕ → PadicAlgCl p} (hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1)))
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

omit [FiniteDimensional ℚ_[p] L] in
theorem chi_inv_eq (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    (((chi ((τ⁻¹ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p).restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) :
      ℚ_[p]) = chiL L (-1) τ := by
  rw [chiL, chiPow_apply, zpow_neg_one, ← map_inv]
  rfl

include hεp in
theorem rhoZp_mem_E_one (l : Fin d) : P.ofW (P.rhoZp hε hεp l) ∈ P.E 1 := by
  intro τ
  refine LinearMap.ext fun x => ?_
  change P.gact τ (P.rhoZp hε hεp l) x =
    algebraMap L ℂ_[p] ((htSetup L).ψ 1 τ) * P.rhoZp hε hεp l x
  rw [gact_apply, rhoZp_apply, rhoZp_apply, P.rho_tpRep hεp, MulEquiv.apply_symm_apply, map_mul,
    galCp_galCp_inv, galCp_algebraMap]
  change _ = algebraMap L ℂ_[p] (algebraMap ℚ_[p] L (chiL L (-1) τ)) * _
  rw [algebraMap_L_cp_algebraMap, ← chi_inv_eq]


/-! ### `W` is finite-dimensional of dimension `h` -/

/-- `W ≅ ℂ_p^h` via a `ℤ_p`-basis of `T_p F`. -/
def wEquiv : (Fin (finrank ℤ_[p] (Kummer.Tp (P.F.Pt p) p)) → ℂ_[p]) ≃ₗ[ℂ_[p]] P.WT :=
  (Module.finBasis ℤ_[p] (Kummer.Tp (P.F.Pt p) p)).constr ℂ_[p]

instance : FiniteDimensional ℂ_[p] P.WT := Module.Finite.equiv P.wEquiv

instance : FiniteDimensional ℂ_[p] P.HomT := inferInstanceAs (FiniteDimensional ℂ_[p] P.WT)

/-- `dim_{ℂ_p} Hom_{ℤ_p}(T_p F, ℂ_p) = h`. -/
theorem finrank_WT : finrank ℂ_[p] P.WT = P.height := by
  rw [← P.wEquiv.finrank_eq, finrank_fin_fun, finrank_tp]

instance (q : ℤ) : FiniteDimensional L (P.E q) :=
  SerreTate.finiteDimensional_eigen (htSetup L) P.smul_distrib_homT q

/-! ### `ℂ_p ⊗ V_p^∨ ↪ W` -/

/-- `V = V_p(F[p^∞]_L) = ℚ_p ⊗ T_p(F[p^∞]_L)(ℚ̄_p)`. -/
abbrev VT := ℚ_[p] ⊗[ℤ_[p]] Additive (P.genericFibreOL.TateModule (PadicAlgCl p))

/-- `ℂ_p ⊗ V^∨ → Hom_{ℤ_p}(T_p F, ℂ_p)`, `w ↦ (x ↦ w(1 ⊗ x))`, `ℂ_p`-linear. -/
def Phi : (ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] P.VT) →ₗ[ℂ_[p]] P.WT where
  toFun w := PhiAL w ∘ₗ P.tpLinEquiv.toLinearMap
  map_add' w w' := by rw [map_add, LinearMap.add_comp]
  map_smul' c w := by rw [map_smul, LinearMap.smul_comp]; rfl

theorem Phi_apply (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] P.VT) (x : Kummer.Tp (P.F.Pt p) p) :
    P.Phi w x = dualEquiv w (yA p (P.tpLinEquiv x)) := rfl

theorem Phi_injective : Function.Injective P.Phi := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  refine (map_eq_zero_iff _ PhiAL_injective).mp (LinearMap.ext fun a => ?_)
  have := LinearMap.congr_fun hw (P.tpLinEquiv.symm a)
  rw [Phi_apply, LinearEquiv.apply_symm_apply] at this
  rw [PhiAL_apply, LinearMap.zero_apply]
  exact this

theorem tensorAct_yA (σ : L.fixingSubgroup) (x : Kummer.Tp (P.F.Pt p) p) :
    TensorProduct.map (galCpLin L (IntermediateField.fixingSubgroupEquiv L σ))
      (P.tateRepOL (IntermediateField.fixingSubgroupEquiv L σ)) (yA p (P.tpLinEquiv x)) =
      yA p (P.tpLinEquiv (Kummer.tpRep P.galRepOL p σ x)) := by
  rw [yA, yA, TensorProduct.map_tmul, galCpLin_apply, map_one, P.tpLinEquiv_tpRep]
  rfl

theorem dualEquiv_gal' (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] P.VT) (σ : L.fixingSubgroup)
    (y : ℂ_[p] ⊗[ℚ_[p]] P.VT) :
    dualEquiv (TensorProduct.map (galCpLin L (IntermediateField.fixingSubgroupEquiv L σ))
        (P.tateRepOL.dual (IntermediateField.fixingSubgroupEquiv L σ)) w)
      (TensorProduct.map (galCpLin L (IntermediateField.fixingSubgroupEquiv L σ))
        (P.tateRepOL (IntermediateField.fixingSubgroupEquiv L σ)) y) =
      galCp L (IntermediateField.fixingSubgroupEquiv L σ) (dualEquiv w y) :=
  dualEquiv_gal P.tateRepOL _ w y

set_option maxHeartbeats 400000 in
-- the instance paths of `ℂ_p ⊗ (ℚ_p ⊗ T)` coming from `dualEquiv_gal` and from instance search
-- only agree after unfolding the tensor-product instances
theorem Phi_isEquiv (w : ℂ_[p] ⊗[ℚ_[p]] Dual ℚ_[p] P.VT)
    (hw : ∀ τ, TensorProduct.map (galCpLin L τ) (P.tateRepOL.dual τ) w = w) :
    P.IsEquiv (P.Phi w) := by
  intro σ x
  have h := P.dualEquiv_gal' w σ (yA p (P.tpLinEquiv x))
  rw [hw, tensorAct_yA] at h
  rw [Phi_apply, Phi_apply]
  exact h

set_option maxHeartbeats 400000 in
-- the instance paths of `ℂ_p ⊗ (ℚ_p ⊗ T)` coming from `dualEquiv_gal` and from instance search
-- only agree after unfolding the tensor-product instances
theorem DHT_zero_fixed (w : CpTensor P.tateRepOL.dual) (hw : w ∈ DHT P.tateRepOL.dual 0)
    (τ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    TensorProduct.map (galCpLin L τ) (P.tateRepOL.dual τ) w = w := by
  have h := (mem_DHT _).mp hw τ
  rw [(htSetup L).ψ_zero, one_smul] at h
  exact h

/-- `D_0(V^∨) → W^{G_L}`, injective. -/
def PhiL : DHT P.tateRepOL.dual 0 →ₗ[L] P.E 0 where
  toFun w := ⟨P.ofW (P.Phi w.1), (P.mem_E_zero_iff _).mpr
    (P.Phi_isEquiv w.1 (P.DHT_zero_fixed w.1 w.2))⟩
  map_add' w w' := Subtype.ext (map_add P.Phi w.1 w'.1)
  map_smul' a w := Subtype.ext (map_smul P.Phi (algebraMap L ℂ_[p] a) w.1)

theorem PhiL_injective : Function.Injective P.PhiL := fun _ _ h =>
  Subtype.ext (P.Phi_injective (congrArg Subtype.val h))

/-- `dim_L W^{G_L} ≥ d' = h - d` (from the Hodge–Tate decomposition of `V_p^∨`). -/
theorem height_sub_le_finrank_E_zero : P.height - d ≤ finrank L (P.E 0) := by
  obtain ⟨d', P', ψ, -, -, h0, -, hh⟩ := P.hodgeTate_decompositionOL
  have := LinearMap.finrank_le_finrank_of_injective P.PhiL_injective
  omega

/-! ### The decomposition -/

/-- The family `ρ(ω_l)` (weight `1`) together with an `L`-basis of `W^{G_L}` (weight `0`). -/
def famF : Fin d ⊕ Fin (finrank L (P.E 0)) → P.HomT :=
  Sum.elim (fun l => P.ofW (P.rhoZp hε hεp l))
    (fun j => ((Module.finBasis L (P.E 0) j : P.E 0) : P.HomT))

/-- The weights. -/
def famQ : Fin d ⊕ Fin (finrank L (P.E 0)) → ℤ := Sum.elim (fun _ => 1) (fun _ => 0)

include hεp in
theorem linearIndependent_famF : LinearIndependent ℂ_[p] (P.famF hε hεp) := by
  refine SerreTate.linearIndependent_of_eigen (htSetup L) P.smul_distrib_homT P.famQ _ ?_ ?_
  · rintro (l | j)
    · exact P.rhoZp_mem_E_one hε hεp l
    · exact (Module.finBasis L (P.E 0) j).2
  · intro q0
    by_cases h1 : q0 = 1
    · subst h1
      let g : Fin d → {i // P.famQ i = 1} := fun l => ⟨Sum.inl l, rfl⟩
      have hg : Function.Bijective g := by
        refine ⟨fun l l' h => Sum.inl_injective (congrArg Subtype.val h), ?_⟩
        rintro ⟨(l | j), h⟩
        · exact ⟨l, rfl⟩
        · exact absurd h (by simp [famQ])
      rw [← linearIndependent_equiv (Equiv.ofBijective g hg)]
      have hli : LinearIndependent ℂ_[p] (fun l => P.ofW (P.rhoZp hε hεp l)) :=
        P.linearIndependent_rhoZp hε hεp
      exact hli.restrict_scalars' L
    · by_cases h0 : q0 = 0
      · subst h0
        let g : Fin (finrank L (P.E 0)) → {i // P.famQ i = 0} := fun j => ⟨Sum.inr j, rfl⟩
        have hg : Function.Bijective g := by
          refine ⟨fun j j' h => Sum.inr_injective (congrArg Subtype.val h), ?_⟩
          rintro ⟨(l | j), h⟩
          · exact absurd h (by simp [famQ])
          · exact ⟨j, rfl⟩
        rw [← linearIndependent_equiv (Equiv.ofBijective g hg)]
        exact (Module.finBasis L (P.E 0)).linearIndependent.map' (P.E 0).subtype
          (Submodule.ker_subtype _)
      · haveI : IsEmpty {i // P.famQ i = q0} := ⟨by
          rintro ⟨(l | j), h⟩
          · exact h1 h.symm
          · exact h0 h.symm⟩
        exact linearIndependent_empty_type

include hε hεp in
theorem card_famF : Fintype.card (Fin d ⊕ Fin (finrank L (P.E 0))) = finrank ℂ_[p] P.HomT := by
  have h1 := (P.linearIndependent_famF hε hεp).fintype_card_le_finrank
  have h2 := P.height_sub_le_finrank_E_zero
  have h3 : finrank ℂ_[p] P.HomT = P.height := P.finrank_WT
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1 ⊢
  omega

include hεp in
theorem span_famF : Submodule.span ℂ_[p] (Set.range (P.famF hε hεp)) = ⊤ := by
  have := (basisOfLinearIndependentOfCardEqFinrank' _ (P.linearIndependent_famF hε hεp)
    (P.card_famF hε hεp)).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank'] at this

theorem span_E_zero :
    Submodule.span ℂ_[p] (P.E 0 : Set P.HomT) =
      Submodule.span ℂ_[p]
        (Set.range fun j => ((Module.finBasis L (P.E 0) j : P.E 0) : P.HomT)) := by
  refine le_antisymm (Submodule.span_le.mpr fun e he => ?_)
    (Submodule.span_mono (Set.range_subset_iff.mpr fun j => (Module.finBasis L (P.E 0) j).2))
  have h1 := (Module.finBasis L (P.E 0)).mem_span ⟨e, he⟩
  have h2 := Submodule.apply_mem_span_image_of_mem_span (P.E 0).subtype h1
  rw [← Set.range_comp] at h2
  exact Submodule.span_le_restrictScalars L ℂ_[p] _ h2

/-- `V₀ = ∑_l ℂ_p ρ(ω_l)`: the image of `ρ ⊗ ℂ_p : ℂ_p^d → W`. -/
def V0 : Submodule ℂ_[p] P.WT := Submodule.span ℂ_[p] (Set.range (P.rhoZp hε hεp))

/-- `V₁ = ℂ_p · Hom_{ℤ_p[G_L]}(T_p F, ℂ_p)`. -/
def V1 : Submodule ℂ_[p] P.WT := Submodule.span ℂ_[p] {f : P.WT | P.IsEquiv f}

theorem mem_V0_iff (f : P.WT) :
    f ∈ P.V0 hε hεp ↔ ∃ c : Fin d → ℂ_[p], ∑ l, c l • P.rhoZp hε hεp l = f :=
  Submodule.mem_span_range_iff_exists_fun ℂ_[p]

include hεp in
/-- **(FoInt)(b), rational Hodge–Tate decomposition** ([Fo, §5.7 (i)]):
`Hom_{ℤ_p}(T_p F, ℂ_p) = V₀ ⊕ V₁`. -/
theorem isCompl_V0_V1 : IsCompl (P.V0 hε hεp) P.V1 := by
  have h := (P.linearIndependent_famF hε hεp).isCompl_span_image (P.span_famF hε hεp)
    Set.isCompl_range_inl_range_inr
  rw [← Set.range_comp, ← Set.range_comp] at h
  have hV1 : (P.V1 : Submodule ℂ_[p] P.WT) =
      Submodule.span ℂ_[p]
        (Set.range fun j => ((Module.finBasis L (P.E 0) j : P.E 0) : P.HomT)) := by
    rw [V1, ← span_E_zero]
    congr 1
    ext f
    exact (P.mem_E_zero_iff f).symm
  rw [hV1]
  exact h

include hεp in
/-- `dim V₀ = d`. -/
theorem finrank_V0 : finrank ℂ_[p] (P.V0 hε hεp) = d := by
  rw [V0, finrank_span_eq_card (P.linearIndependent_rhoZp hε hεp), Fintype.card_fin]

include hεp in
/-- `dim V₀ + dim V₁ = h`. -/
theorem finrank_V0_add_V1 : finrank ℂ_[p] (P.V0 hε hεp) + finrank ℂ_[p] P.V1 = P.height := by
  rw [← P.finrank_WT, ← Submodule.finrank_sup_add_finrank_inf_eq,
    (P.isCompl_V0_V1 hε hεp).sup_eq_top,
    (P.isCompl_V0_V1 hε hεp).inf_eq_bot, finrank_bot, add_zero, finrank_top]

include hε hεp in
/-- `dim V₁ = h - d = d'`. -/
theorem finrank_V1 : finrank ℂ_[p] P.V1 = P.height - d := by
  have h1 := P.finrank_V0_add_V1 hε hεp
  have h2 := P.finrank_V0 hε hεp
  omega

end PDivFGL

end PadicHodge
