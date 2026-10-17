/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Hilbert90.Residue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Hilbert 90 for `GL_h` modulo `p` over an unramified level

For `M` as in `Hilbert90/Residue.lean` (`IsUnrStable`) and a homomorphism
`B : Gal(ℚ̄_p/ℚ_p) → GL_h(ℤ_p)` which is `≡ 1 mod p` on `Gal(ℚ̄_p/M)`, there is
`X ∈ M_h(O_M)` with `|det X| = 1` and `B(σ) σ(X) ≡ X mod p` for all `σ`
(**`exists_GL_mod_p`**).

Proof (Speiser's descent over the residue field `κ = κ_M`, standard; written up here): the
twisted action `σ * x = B̄(σ) σ̄(x)` on `κ^h` factors through the finite set of embeddings
`e : M → ℚ̄_p`; the traces `Tr(x) = ∑_e σ_e * x` are invariant. They span `κ^h`: a linear form
`λ` vanishing on them satisfies `∑_e ē(m) λ(B̄(σ_e) e_i) = 0` for all `m ∈ κ`, so all
coefficients vanish by Dedekind (`linearIndependent_resAut`), and the coefficient of the
inclusion `M ⊆ ℚ̄_p` is `λ(e_i)`. An invariant basis of `κ^h` gives `X̄ ∈ GL_h(κ)` with
`B̄(σ) σ̄(X̄) = X̄`; any lift `X` works, since `|z| < 1` implies `|z| ≤ |p|` on `M`.
-/

noncomputable section

open IsLocalRing Matrix

namespace PadicHodge

namespace Hilbert90

variable {p : ℕ} [hp : Fact p.Prime] {M : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem algebraMap_padicInt_mem (a : ℤ_[p]) : algebraMap ℤ_[p] (PadicAlgCl p) a ∈ OM M := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
  refine ⟨M.algebraMap_mem _, ?_⟩
  rw [PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

theorem gal_algebraMap_padicInt (σ : GalQp p) (a : ℤ_[p]) :
    σ (algebraMap ℤ_[p] (PadicAlgCl p) a) = algebraMap ℤ_[p] (PadicAlgCl p) a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), AlgEquiv.commutes]

theorem norm_algebraMap_padicInt (a : ℤ_[p]) :
    ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends]
  rfl

variable (M) in
/-- `ℤ_p → O_M`. -/
def zO : ℤ_[p] →+* OM M :=
  (algebraMap ℤ_[p] (PadicAlgCl p)).codRestrict (OM M) algebraMap_padicInt_mem

@[simp] theorem zO_coe (a : ℤ_[p]) :
    (zO M a : PadicAlgCl p) = algebraMap ℤ_[p] (PadicAlgCl p) a := rfl

variable (hM : IsUnrStable M)

theorem sO_zO (σ : GalQp p) (a : ℤ_[p]) : sO hM σ (zO M a) = zO M a :=
  Subtype.ext (gal_algebraMap_padicInt σ a)

theorem sO_mul (σ τ : GalQp p) (x : OM M) : sO hM (σ * τ) x = sO hM σ (sO hM τ x) := rfl

theorem sO_fix (ν : GalQp p) (hν : ∀ z ∈ M, ν z = z) (x : OM M) : sO hM ν x = x :=
  Subtype.ext (hν x x.2.1)

theorem resAut_mul (σ τ : GalQp p) (x : ResidueField (OM M)) :
    resAut hM (σ * τ) x = resAut hM σ (resAut hM τ x) := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  simp only [resAut_residue, sO_mul]

theorem resAut_fix (ν : GalQp p) (hν : ∀ z ∈ M, ν z = z) (x : ResidueField (OM M)) :
    resAut hM ν x = x := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [resAut_residue, sO_fix hM ν hν]

variable (M) in
/-- `ℤ_p → κ_M`. -/
def rZ : ℤ_[p] →+* ResidueField (OM M) := (residue (OM M)).comp (zO M)

theorem resAut_rZ (σ : GalQp p) (a : ℤ_[p]) : resAut hM σ (rZ M a) = rZ M a := by
  simp only [rZ, RingHom.comp_apply, resAut_residue, sO_zO]

theorem rZ_eq_of_norm_lt {a b : ℤ_[p]} (h : ‖a - b‖ < 1) : rZ M a = rZ M b := by
  simp only [rZ, RingHom.comp_apply]
  rw [residue_eq_iff, zO_coe, zO_coe, ← map_sub, norm_algebraMap_padicInt]
  exact h

variable {h : ℕ} (B : GalQp p →* Matrix (Fin h) (Fin h) ℤ_[p])

/-- The twisted action `x ↦ B̄(σ) σ̄(x)` on `κ^h`. -/
def act (σ : GalQp p) : (Fin h → ResidueField (OM M)) →+ (Fin h → ResidueField (OM M)) where
  toFun x := (B σ).map (rZ M) *ᵥ fun i => resAut hM σ (x i)
  map_zero' := by simp only [Pi.zero_apply, map_zero]; exact mulVec_zero _
  map_add' x y := by
    rw [← mulVec_add]
    congr 1
    funext i
    simp

theorem act_apply (σ : GalQp p) (x : Fin h → ResidueField (OM M)) :
    act hM B σ x = (B σ).map (rZ M) *ᵥ fun i => resAut hM σ (x i) := rfl

theorem act_mul (σ τ : GalQp p) (x : Fin h → ResidueField (OM M)) :
    act hM B (σ * τ) x = act hM B σ (act hM B τ x) := by
  simp only [act_apply]
  have h1 : (fun i => resAut hM σ (((B τ).map (rZ M) *ᵥ fun i => resAut hM τ (x i)) i)) =
      (B τ).map (rZ M) *ᵥ fun i => resAut hM (σ * τ) (x i) := by
    funext i
    rw [RingHom.map_mulVec]
    congr 1
    · ext a b; simp [resAut_rZ]
    · funext j; simp [resAut_mul]
  rw [h1, mulVec_mulVec, ← Matrix.map_mul, ← map_mul]

theorem act_fix (ν : GalQp p) (hν : ∀ z ∈ M, ν z = z)
    (hB : ∀ i j, ‖B ν i j - (1 : Matrix (Fin h) (Fin h) ℤ_[p]) i j‖ < 1)
    (x : Fin h → ResidueField (OM M)) : act hM B ν x = x := by
  rw [act_apply]
  have h1 : (B ν).map (rZ M) = 1 := by
    ext i j
    rw [map_apply, rZ_eq_of_norm_lt (hB i j), Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1, one_mulVec]
  funext i
  exact resAut_fix hM ν hν (x i)

variable (hB : ∀ ν : GalQp p, (∀ z ∈ M, ν z = z) →
  ∀ i j, ‖B ν i j - (1 : Matrix (Fin h) (Fin h) ℤ_[p]) i j‖ < 1)

variable [FiniteDimensional ℚ_[p] M]

/-- The trace `∑_e σ_e * x`. -/
def trace (x : Fin h → ResidueField (OM M)) : Fin h → ResidueField (OM M) :=
  ∑ e : M →ₐ[ℚ_[p]] PadicAlgCl p, act hM B (liftE M e) x

include hB in
theorem act_trace (σ : GalQp p) (x : Fin h → ResidueField (OM M)) :
    act hM B σ (trace hM B x) = trace hM B x := by
  rw [trace, map_sum]
  conv_rhs => rw [← Equiv.sum_comp (reindex M σ)]
  refine Finset.sum_congr rfl fun e _ => ?_
  set ν := (liftE M (reindex M σ e))⁻¹ * σ * liftE M e
  have hσe : σ * liftE M e = liftE M (reindex M σ e) * ν := by
    simp only [ν, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [← act_mul, hσe, act_mul, act_fix hM B ν (fix_liftE_reindex σ e)
    (hB ν (fix_liftE_reindex σ e))]

include hB in
/-- **The traces span `κ^h`.** -/
theorem span_trace :
    Submodule.span (ResidueField (OM M)) (Set.range (trace hM B)) = ⊤ := by
  classical
  set κ := ResidueField (OM M)
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  apply hf0
  have hι : ∀ i, f (Pi.single i 1) = 0 := by
    intro i
    -- the coefficients `λ(B̄(σ_e) e_i)` vanish
    have hli := linearIndependent_resAut hM
    rw [Fintype.linearIndependent_iff] at hli
    have hzero := hli (fun e => f ((B (liftE M e)).map (rZ M) *ᵥ Pi.single i 1)) (by
      funext m
      have hm : f (trace hM B (Pi.single i m)) = 0 :=
        hle (Submodule.subset_span ⟨_, rfl⟩)
      rw [trace, map_sum] at hm
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [act_apply]
      have : (fun j => resAut hM (liftE M e) (Pi.single (M := fun _ => κ) i m j)) =
          Pi.single i (resAut hM (liftE M e) m) := by
        funext j
        rw [Pi.single_apply, Pi.single_apply]
        split_ifs <;> simp
      rw [this]
      have h2 : Pi.single (M := fun _ => κ) i (resAut hM (liftE M e) m) =
          resAut hM (liftE M e) m • Pi.single i 1 := by
        funext l
        rw [Pi.single_apply, Pi.smul_apply, Pi.single_apply]
        split_ifs <;> simp
      rw [h2, mulVec_smul, map_smul, smul_eq_mul, mul_comm]
      rfl) (IntermediateField.val M)
    have hfix : ∀ z ∈ M, liftE M (IntermediateField.val M) z = z := fun z hz => by
      rw [liftE_apply' _ hz]; rfl
    have h1 : (B (liftE M (IntermediateField.val M))).map (rZ M) = 1 := by
      ext a b
      rw [map_apply, rZ_eq_of_norm_lt (hB _ hfix a b), Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hz : f ((B (liftE M (IntermediateField.val M))).map (rZ M) *ᵥ Pi.single i 1) = 0 :=
      hzero
    rw [h1, Matrix.one_mulVec] at hz
    exact hz
  exact LinearMap.pi_ext' fun i => LinearMap.ext_ring (by simpa using hι i)

include hM hB in
/-- **Hilbert 90 for `GL_h` modulo `p`.** -/
theorem exists_GL_mod_p : ∃ X : Matrix (Fin h) (Fin h) (PadicAlgCl p),
    (∀ i j, X i j ∈ OM M) ∧ ‖X.det‖ = 1 ∧
      ∀ σ : GalQp p, ∀ i j,
        ‖((B σ).map (algebraMap ℤ_[p] (PadicAlgCl p)) * X.map σ - X) i j‖ ≤
          ‖(p : PadicAlgCl p)‖ := by
  classical
  set κ := ResidueField (OM M)
  -- an invariant basis of `κ^h`
  obtain ⟨ι, a, -, hsp, hli⟩ := exists_linearIndependent' κ (trace hM B)
  rw [span_trace hM B hB] at hsp
  let bb : Module.Basis ι κ (Fin h → κ) := Module.Basis.mk hli hsp.ge
  let eqv : Fin h ≃ ι := (Pi.basisFun κ (Fin h)).indexEquiv bb
  let y : Fin h → Fin h → κ := fun j => trace hM B (a (eqv j))
  have hyli : LinearIndependent κ y := hli.comp eqv eqv.injective
  let Xb : Matrix (Fin h) (Fin h) κ := Matrix.of fun i j => y j i
  have hXb : IsUnit Xb := by
    rw [← linearIndependent_cols_iff_isUnit]
    exact hyli
  have hXinv : ∀ σ : GalQp p, (B σ).map (rZ M) * Xb.map (resAut hM σ) = Xb := by
    intro σ
    ext i j
    have := congrFun (act_trace hM B hB σ (a (eqv j))) i
    rw [act_apply] at this
    simpa [Xb, y, mul_apply, mulVec, dotProduct] using this
  -- lift to `O_M`
  choose lift hlift using fun x : κ => residue_surjective x
  let X0 : Matrix (Fin h) (Fin h) (OM M) := Xb.map lift
  have hX0 : X0.map (residue (OM M)) = Xb := by ext i j; simp [X0, hlift]
  refine ⟨X0.map (OM M).subtype, fun i j => (X0 i j).2, ?_, ?_⟩
  · have hdet : IsUnit X0.det := by
      by_contra hn
      have h1 : residue (OM M) X0.det = 0 := by
        rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      have h2 : residue (OM M) X0.det = Xb.det := by
        rw [RingHom.map_det]; exact congrArg det hX0
      rw [h2] at h1
      exact ((isUnit_iff_isUnit_det Xb).mp hXb).ne_zero h1
    have h3 : (X0.map (OM M).subtype).det = (OM M).subtype X0.det := (RingHom.map_det _ _).symm
    rw [h3]
    exact (isUnit_OM_iff _).mp hdet
  · intro σ i j
    let Y0 : Matrix (Fin h) (Fin h) (OM M) := (B σ).map (zO M) * X0.map (sO hM σ) - X0
    have hY : ((B σ).map (algebraMap ℤ_[p] (PadicAlgCl p)) * (X0.map (OM M).subtype).map σ -
          X0.map (OM M).subtype) i j = (OM M).subtype (Y0 i j) := by
      simp only [Y0, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul,
        Matrix.map_apply]
      rfl
    have hYres : residue (OM M) (Y0 i j) = 0 := by
      have h1 := congrFun (congrFun (hXinv σ) i) j
      rw [Matrix.mul_apply] at h1
      simp only [Y0, X0, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul,
        Matrix.map_apply, ← resAut_residue, hlift]
      rw [sub_eq_zero, ← h1]
      rfl
    rw [hY]
    rw [residue_eq_zero_iff] at hYres
    exact hM.unr _ (Y0 i j).2.1 hYres

end Hilbert90

end PadicHodge
