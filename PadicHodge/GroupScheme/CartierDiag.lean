/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.GroupScheme.Cartier
import PadicHodge.GroupScheme.Constant

/-!
# The Cartier dual of a diagonalizable group scheme

For a finite commutative group `M`, the Cartier dual of the diagonalizable group scheme
`D(M) = Spec R[M]` is the constant group scheme `M_R = Spec R^M` ([BC, Exercise 12.5.3 (1)] is
the case `M = ℤ/n`, read backwards via double duality: `(ℤ/n)_R^∨ = μ_n`): the dual of the group
algebra `R[M]` is the algebra of functions `M → R` (the dual basis of `{m}` multiplies
pointwise because `Δ m = m ⊗ m`), and the transpose of the multiplication `m ⊗ m' ↦ m m'` of
`R[M]` is `Δ f = ∑_{m, n} f(mn) e_m ⊗ e_n`.

* `CartierDiag.psi : (M → R) →ₐc[R] R[M]^∨`, `φ ↦ (∑ a_m m ↦ ∑ a_m φ(m))`;
* `CartierDiag.dualDiagEquiv : (M → R) ≃ₐc[R] R[M]^∨`, i.e. `D(M)^∨ ≅ M_R`
  (`FFGroupScheme.dualDiagIso`).
-/

noncomputable section

open Coalgebra WithConv TensorProduct

namespace PadicHodge

universe u

namespace CartierDiag

variable {R : Type u} [CommRing R] {M : Type}

/-- The functional `∑ a_m m ↦ ∑ a_m φ(m)` on `R[M]`. -/
def psiFun (φ : M → R) : MonoidAlgebra R M →ₗ[R] R :=
  Finsupp.linearCombination R φ ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv (R := R) (S := R) (M := M)).toLinearMap

theorem psiFun_single (φ : M → R) (m : M) (r : R) :
    psiFun φ (MonoidAlgebra.single m r) = r * φ m := by
  change Finsupp.linearCombination R φ (MonoidAlgebra.single m r).coeff = _
  rw [MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, smul_eq_mul]

theorem single_eq_smul (m : M) (r : R) :
    MonoidAlgebra.single m r = r • MonoidAlgebra.single m (1 : R) := by
  rw [MonoidAlgebra.smul_single', mul_one]

/-- Linear functionals on `R[M]` are determined by their values on `M`. -/
theorem dual_ext {f g : MonoidAlgebra R M →ₗ[R] R}
    (h : ∀ m, f (MonoidAlgebra.single m 1) = g (MonoidAlgebra.single m 1)) : f = g := by
  refine LinearMap.ext fun x => ?_
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single m r => rw [single_eq_smul, map_smul, map_smul, h]

/-- Linear functionals on `R[M] ⊗ R[M]` are determined by their values on `M × M`. -/
theorem dual_ext₂ {f g : MonoidAlgebra R M ⊗[R] MonoidAlgebra R M →ₗ[R] R}
    (h : ∀ m n, f (MonoidAlgebra.single m 1 ⊗ₜ MonoidAlgebra.single n 1) =
      g (MonoidAlgebra.single m 1 ⊗ₜ MonoidAlgebra.single n 1)) : f = g := by
  refine TensorProduct.ext' fun x y => ?_
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [add_tmul, map_add, map_add, hx, hx']
  | single m r =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [tmul_add, map_add, map_add, hy, hy']
    | single n s =>
      rw [single_eq_smul m r, single_eq_smul n s, smul_tmul_smul, map_smul, map_smul, h]

variable [CommGroup M]

/-- `φ ↦ psiFun φ` as a linear map `R^M → R[M]^∨`. -/
def psiLin : (M → R) →ₗ[R] Cartier.Dual R (MonoidAlgebra R M) where
  toFun φ := toConv (psiFun φ)
  map_add' φ ψ := WithConv.ext <| dual_ext fun m => by
    simp only [ofConv_add, LinearMap.add_apply, psiFun_single, Pi.add_apply]
    ring
  map_smul' c φ := WithConv.ext <| dual_ext fun m => by
    simp only [ofConv_smul, LinearMap.smul_apply, psiFun_single, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem psiLin_single (φ : M → R) (m : M) (r : R) :
    psiLin φ (MonoidAlgebra.single m r) = r * φ m :=
  psiFun_single φ m r

variable [Fintype M] [DecidableEq M]

/-- `psiLin` as an algebra map (pointwise product ↦ convolution product). -/
def psiAlg' : (M → R) →ₐ[R] Cartier.Dual R (MonoidAlgebra R M) :=
  AlgHom.ofLinearMap psiLin
    (WithConv.ext <| dual_ext fun m => by
      rw [psiLin_single]
      simp [MonoidAlgebra.counit_single])
    (fun φ ψ => WithConv.ext <| dual_ext fun m => by
      rw [psiLin_single, LinearMap.convMul_apply, MonoidAlgebra.comul_single]
      simp)

/-- `psiAlg'` on the coordinate ring of the constant group scheme. -/
def psiAlg : (FFGroupScheme.const R M).A →ₐ[R] Cartier.Dual R (MonoidAlgebra R M) := psiAlg'

theorem psiAlg_apply (φ : M → R) : psiAlg (R := R) (M := M) φ = psiLin φ := rfl

/-- `psiAlg` is a bialgebra map. -/
def psi : (FFGroupScheme.const R M).A →ₐc[R] Cartier.Dual R (MonoidAlgebra R M) :=
  BialgHom.ofAlgHom psiAlg
    (AlgHom.ext fun (φ : M → R) => by
      change psiLin (R := R) (M := M) φ 1 = (φ : M → R) 1
      rw [MonoidAlgebra.one_def, psiLin_single, one_mul])
    (AlgHom.ext fun (φ : M → R) => by
      change TensorProduct.map (psiLin (R := R) (M := M)) psiLin (ConstGS.comul R M φ) =
        Cartier.comulD R _ (psiLin φ)
      apply Cartier.ev2_injective
      refine dual_ext₂ fun a b => ?_
      rw [Cartier.ev2_comulD_tmul, MonoidAlgebra.single_mul_single, mul_one, psiLin_single,
        one_mul, ConstGS.comul_apply]
      simp [ConstGS.e_apply, LinearMap.sum_apply])

theorem psi_apply (φ : M → R) : psi (R := R) (M := M) φ = psiLin φ := rfl

theorem psi_bijective : Function.Bijective (psi (R := R) (M := M)) := by
  refine ⟨fun φ ψ h => show (φ : M → R) = ψ from funext fun m => ?_,
     fun f => ⟨fun m => f (MonoidAlgebra.single m 1), ?_⟩⟩
  · have := congrArg (fun f : Cartier.Dual R (MonoidAlgebra R M) =>
      f (MonoidAlgebra.single m 1)) h
    simpa [psi_apply] using this
  · exact WithConv.ext <| dual_ext fun m => by simp [psi_apply]

/-- **`D(M)^∨ ≅ M_R`**: the dual of the group algebra `R[M]` is the Hopf algebra of functions
`M → R`. -/
def dualDiagEquiv : (FFGroupScheme.const R M).A ≃ₐc[R] Cartier.Dual R (MonoidAlgebra R M) :=
  BialgEquiv.ofBijective psi psi_bijective

end CartierDiag

namespace FFGroupScheme

variable (R : Type u) [CommRing R] (M : Type) [CommGroup M] [Fintype M] [DecidableEq M]

/-- The isomorphism `D(M)^∨ ≅ M_R` of finite flat group schemes (on coordinate rings). -/
def dualDiagIso : (const R M).A ≃ₐc[R] (diag R M).dual.A :=
  CartierDiag.dualDiagEquiv

end FFGroupScheme

end PadicHodge
