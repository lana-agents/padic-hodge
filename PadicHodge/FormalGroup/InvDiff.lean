/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.InvDeriv

/-!
# Invariant differentials of a formal group law

For a formal group law `F` of dimension `d` over a commutative ring `k`, let
`M_{lj}(T) = ∂_{U_j} Φ_l(T, 0)` (`invMat`, `FormalGroup/InvDeriv.lean`). Since `M(0) = 1`, `M` is
invertible; its inverse `N = M⁻¹` (`invDiff`) gives the `d` **invariant differentials**
`ω_l = ∑_j N_{lj}(T) dT_j`, with linear part `dT_l` (`constantCoeff_invDiff`).

* `invMat_subst_Φ`: differentiating associativity `Φ(Φ(T, U), V) = Φ(T, Φ(U, V))` with respect
  to `V_j` at `V = 0` gives the matrix identity `M(Φ(T, U)) = ∂_U Φ(T, U) · M(U)`.
* **Translation invariance** (`sum_invDiff_subst_Φ_mul_pderiv_one`,
  `sum_invDiff_subst_Φ_mul_pderiv_zero`): `∑_i N_{li}(Φ) ∂_{U_j} Φ_i = N_{lj}(U)` and
  `∑_i N_{li}(Φ) ∂_{T_j} Φ_i = N_{lj}(T)`, i.e. `Φ^* ω_l = pr_1^* ω_l + pr_2^* ω_l`.
* For families: `Φ(f, g)^* ω = f^* ω + g^* ω` (`sum_invDiff_subst_addPS`), hence
  **`[n]_F^* ω = n ω`** (`sum_invDiff_subst_mulPS`), as used in [Tate, §(2.2), p. 165].
-/

noncomputable section

open MvPowerSeries

namespace PadicHodge

namespace FGL

variable {k : Type*} [CommRing k] {d : ℕ} (F : FGL k d)

/-! ### Auxiliary substitution and chain-rule lemmas -/

/-- **Chain rule for `Φ(f, g)`.** -/
theorem pderiv_addPS {τ : Type*} {f g : Fin d → MvPowerSeries τ k} (hf : NoConst f)
    (hg : NoConst g) (t : τ) (i : Fin d) :
    pderiv k t (F.addPS f g i) =
      ∑ m, (pderiv k (0, m) (F.Φ i)).subst (pairFam f g) * pderiv k t (f m) +
        ∑ m, (pderiv k (1, m) (F.Φ i)).subst (pairFam f g) * pderiv k t (g m) := by
  rw [addPS, pderiv_subst (noConst_pairFam hf hg), Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

theorem subst_pairFam_subst {σ τ : Type*} {f g : Fin d → MvPowerSeries σ k} (hf : NoConst f)
    (hg : NoConst g) {h : σ → MvPowerSeries τ k} (hh : HasSubst h)
    (P : MvPowerSeries (Fin 2 × Fin d) k) :
    (P.subst (pairFam f g)).subst h =
      P.subst (pairFam (fun j => (f j).subst h) (fun j => (g j).subst h)) := by
  rw [subst_comp_subst_apply (hasSubst_pairFam hf hg) hh, pairFam_subst]

/-- `P(T, 0)` evaluated at `f` is `P(f, 0)`. -/
theorem subst_atZero_subst {τ : Type*} {f : Fin d → MvPowerSeries τ k} (hf : NoConst f)
    (P : MvPowerSeries (Fin 2 × Fin d) k) :
    (P.subst (atZero (k := k) (d := d))).subst f = P.subst (pairFam f 0) := by
  have hb := hasSubst_of_noConst hf
  rw [subst_pairFam_subst noConst_X noConst_zero hb]
  congr 2
  · funext m
    exact subst_X hb m
  · funext m
    exact subst_zero' hb

theorem pairFam_Xv : pairFam (Xv (R := k) (d := d) (n := 2) 0) (Xv 1) = X := by
  funext v
  obtain ⟨a, l⟩ := v
  fin_cases a <;> rfl

theorem invMat_apply (l j : Fin d) :
    F.invMat l j = (pderiv k (1, j) (F.Φ l)).subst (atZero (k := k) (d := d)) := rfl

/-! ### The invariant differentials -/

/-- The coefficient matrix `N = M⁻¹` of the invariant differentials `ω_l = ∑_j N_{lj} dT_j`. -/
def invDiff : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) k) := F.invMat⁻¹

theorem invMat_mul_invDiff : F.invMat * F.invDiff = 1 :=
  Matrix.mul_nonsing_inv _ F.isUnit_det_invMat

theorem invDiff_mul_invMat : F.invDiff * F.invMat = 1 :=
  Matrix.nonsing_inv_mul _ F.isUnit_det_invMat

/-- The linear part of `ω_l` is `dT_l`. -/
theorem constantCoeff_invDiff (l j : Fin d) :
    constantCoeff (F.invDiff l j) = if l = j then 1 else 0 := by
  have hM : (constantCoeff : MvPowerSeries (Fin d) k →+* k).mapMatrix F.invMat = 1 := by
    ext l j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, constantCoeff_invMat, Matrix.one_apply]
  have h := congrArg (constantCoeff : MvPowerSeries (Fin d) k →+* k).mapMatrix
    F.invMat_mul_invDiff
  rw [map_mul, map_one, hM, one_mul] at h
  have := congrFun (congrFun h l) j
  rwa [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply] at this

/-! ### Translation invariance -/

/-- **`M(Φ(T, U)) = ∂_U Φ(T, U) · M(U)`**: derivative of associativity in `V_j` at `V = 0`. -/
theorem invMat_subst_Φ (l j : Fin d) :
    (F.invMat l j).subst F.Φ =
      ∑ i, pderiv k (1, i) (F.Φ l) * (F.invMat i j).subst (Xv (R := k) (n := 2) 1) := by
  classical
  have hx : NoConst (Xv (R := k) (d := d) (n := 3) 0) := noConst_Xv 0
  have hy : NoConst (Xv (R := k) (d := d) (n := 3) 1) := noConst_Xv 1
  have hz : NoConst (Xv (R := k) (d := d) (n := 3) 2) := noConst_Xv 2
  have hh := hasSubst_tripleFam (noConst_Xv (R := k) (d := d) (n := 2) 0) (noConst_Xv 1)
    noConst_zero
  set h := tripleFam (Xv (R := k) (d := d) (n := 2) 0) (Xv 1) 0
  have hX : ∀ (a : Fin 3) (m : Fin d), (Xv (R := k) (n := 3) a m).subst h = h (a, m) :=
    fun a m => subst_X hh _
  have dx : ∀ m, pderiv k ((2 : Fin 3), j) (Xv (R := k) (d := d) (n := 3) 0 m) = 0 :=
    fun m => pderiv_X_of_ne (by simp)
  have dy : ∀ m, pderiv k ((2 : Fin 3), j) (Xv (R := k) (d := d) (n := 3) 1 m) = 0 :=
    fun m => pderiv_X_of_ne (by simp)
  have dz : ∀ m, pderiv k ((2 : Fin 3), j) (Xv (R := k) (d := d) (n := 3) 2 m) =
      if m = j then 1 else 0 := by
    intro m
    split_ifs with hm
    · subst hm
      exact pderiv_X_self _
    · exact pderiv_X_of_ne (by simp [hm])
  have dxy : ∀ m, pderiv k ((2 : Fin 3), j) (F.addPS (Xv (n := 3) 0) (Xv 1) m) = 0 := by
    intro m
    rw [F.pderiv_addPS hx hy]
    simp [dx, dy]
  have dyz : ∀ i, pderiv k ((2 : Fin 3), j) (F.addPS (Xv (n := 3) 1) (Xv 2) i) =
      (pderiv k (1, j) (F.Φ i)).subst (pairFam (Xv (R := k) (n := 3) 1) (Xv 2)) := by
    intro i
    rw [F.pderiv_addPS hy hz]
    simp [dy, dz]
  have exy : (fun m => (F.addPS (Xv (R := k) (n := 3) 0) (Xv 1) m).subst h) = F.Φ := by
    funext m
    rw [F.subst_addPS hx hy hh]
    simp only [hX]
    rw [F.Φ_eq_addPS]
    rfl
  have eyz : (fun m => (F.addPS (Xv (R := k) (n := 3) 1) (Xv 2) m).subst h) =
      Xv (R := k) (d := d) (n := 2) 1 := by
    funext m
    rw [F.subst_addPS hy hz hh]
    simp only [hX]
    exact congrFun (F.addPS_zero (noConst_Xv 1)) m
  calc (F.invMat l j).subst F.Φ
      = ((pderiv k (1, j) (F.Φ l)).subst
          (pairFam (F.addPS (Xv (n := 3) 0) (Xv 1)) (Xv 2))).subst h := by
        rw [invMat_apply, subst_atZero_subst F.constantCoeff_Φ,
          subst_pairFam_subst (F.noConst_addPS hx hy) hz hh, exy]
        simp only [hX]
        rfl
    _ = (pderiv k ((2 : Fin 3), j)
          (F.addPS (F.addPS (Xv (n := 3) 0) (Xv 1)) (Xv 2) l)).subst h := by
        rw [F.pderiv_addPS (F.noConst_addPS hx hy) hz]
        simp [dxy, dz]
    _ = (pderiv k ((2 : Fin 3), j)
          (F.addPS (Xv (n := 3) 0) (F.addPS (Xv 1) (Xv 2)) l)).subst h := by
        rw [F.addPS_assoc hx hy hz]
    _ = (∑ i, (pderiv k (1, i) (F.Φ l)).subst
          (pairFam (Xv (n := 3) 0) (F.addPS (Xv 1) (Xv 2))) *
          (pderiv k (1, j) (F.Φ i)).subst (pairFam (Xv (R := k) (n := 3) 1) (Xv 2))).subst h := by
        rw [F.pderiv_addPS hx (F.noConst_addPS hy hz)]
        simp [dx, dyz]
    _ = _ := by
        rw [← coe_substAlgHom hh, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, coe_substAlgHom,
          subst_pairFam_subst hx (F.noConst_addPS hy hz) hh, subst_pairFam_subst hy hz hh, eyz,
          invMat_apply, subst_atZero_subst (noConst_Xv 1)]
        simp only [hX]
        congr 1
        rw [show (pairFam (fun m => h (0, m)) (Xv (R := k) (d := d) (n := 2) 1)) = X from
          pairFam_Xv, subst_self]
        rfl

/-- **Translation invariance of the invariant differentials** (second variable):
`∑_i N_{li}(Φ(T, U)) ∂_{U_j} Φ_i(T, U) = N_{lj}(U)`. -/
theorem sum_invDiff_subst_Φ_mul_pderiv_one (l j : Fin d) :
    ∑ i, (F.invDiff l i).subst F.Φ * pderiv k (1, j) (F.Φ i) =
      (F.invDiff l j).subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × Fin d) k)) := by
  set φ := ((substAlgHom (hasSubst_of_constantCoeff_zero F.constantCoeff_Φ) :
    MvPowerSeries (Fin d) k →ₐ[k] MvPowerSeries (Fin 2 × Fin d) k) :
      MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin 2 × Fin d) k).mapMatrix (m := Fin d)
  set ψ := ((substAlgHom (hasSubst_of_noConst (noConst_Xv (R := k) (d := d) (n := 2) 1)) :
    MvPowerSeries (Fin d) k →ₐ[k] MvPowerSeries (Fin 2 × Fin d) k) :
      MvPowerSeries (Fin d) k →+* MvPowerSeries (Fin 2 × Fin d) k).mapMatrix (m := Fin d)
  let J : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin 2 × Fin d) k) :=
    fun i j => pderiv k (1, j) (F.Φ i)
  have hM : φ F.invMat = J * ψ F.invMat := by
    refine Matrix.ext fun l j => ?_
    simp only [φ, ψ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      RingHom.coe_coe, coe_substAlgHom]
    exact F.invMat_subst_Φ l j
  have h1 : φ F.invDiff * φ F.invMat = 1 := by
    rw [← map_mul, F.invDiff_mul_invMat, map_one]
  have h2 : ψ F.invMat * ψ F.invDiff = 1 := by
    rw [← map_mul, F.invMat_mul_invDiff, map_one]
  have key : φ F.invDiff * J = ψ F.invDiff := by
    calc φ F.invDiff * J = φ F.invDiff * J * (ψ F.invMat * ψ F.invDiff) := by
          rw [h2, Matrix.mul_one]
      _ = φ F.invDiff * φ F.invMat * ψ F.invDiff := by
          rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = ψ F.invDiff := by rw [h1, Matrix.one_mul]
  have := congrFun (congrFun key l) j
  simp only [φ, ψ, J, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingHom.coe_coe, coe_substAlgHom] at this
  exact this

/-- `∂_{T_j} Φ_i = (∂_{U_j} Φ_i)(U, T)` (commutativity). -/
theorem pderiv_zero_Φ (i j : Fin d) :
    pderiv k (0, j) (F.Φ i) =
      (pderiv k (1, j) (F.Φ i)).subst (pairFam (Xv (R := k) (d := d) (n := 2) 1) (Xv 0)) := by
  classical
  conv_lhs => rw [← F.comm i]
  rw [pderiv_subst (noConst_pairFam (noConst_Xv 1) (noConst_Xv 0)), Fintype.sum_prod_type,
    Fin.sum_univ_two]
  simp only [Fin.isValue, pairFam_zero, pairFam_one, Xv]
  have e0 : ∀ m : Fin d, pderiv k ((0 : Fin 2), j) (X ((1 : Fin 2), m) :
      MvPowerSeries (Fin 2 × Fin d) k) = 0 := fun m => pderiv_X_of_ne (by simp)
  simp only [e0, mul_zero, Finset.sum_const_zero, zero_add, pderiv_X, Pi.single_apply,
    Prod.mk.injEq, true_and, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Translation invariance of the invariant differentials** (first variable):
`∑_i N_{li}(Φ(T, U)) ∂_{T_j} Φ_i(T, U) = N_{lj}(T)`. -/
theorem sum_invDiff_subst_Φ_mul_pderiv_zero (l j : Fin d) :
    ∑ i, (F.invDiff l i).subst F.Φ * pderiv k (0, j) (F.Φ i) =
      (F.invDiff l j).subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × Fin d) k)) := by
  have hsw := hasSubst_pairFam (noConst_Xv (R := k) (d := d) (n := 2) 1) (noConst_Xv 0)
  have h := congrArg (MvPowerSeries.subst (pairFam (Xv (R := k) (d := d) (n := 2) 1) (Xv 0)))
    (F.sum_invDiff_subst_Φ_mul_pderiv_one l j)
  have hX1 : HasSubst (fun m => (X ((1 : Fin 2), m) : MvPowerSeries (Fin 2 × Fin d) k)) :=
    hasSubst_of_noConst (noConst_Xv 1)
  have hΦ := hasSubst_of_constantCoeff_zero F.constantCoeff_Φ
  have hc : (fun s => (F.Φ s).subst (pairFam (Xv (R := k) (d := d) (n := 2) 1) (Xv 0))) =
      F.Φ := funext F.comm
  rw [← coe_substAlgHom hsw, map_sum, coe_substAlgHom, subst_comp_subst_apply hX1 hsw] at h
  calc ∑ i, (F.invDiff l i).subst F.Φ * pderiv k (0, j) (F.Φ i)
      = ∑ i, ((F.invDiff l i).subst F.Φ * pderiv k (1, j) (F.Φ i)).subst
          (pairFam (Xv (R := k) (d := d) (n := 2) 1) (Xv 0)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← coe_substAlgHom hsw, map_mul, coe_substAlgHom, subst_comp_subst_apply hΦ hsw, hc,
          pderiv_zero_Φ]
    _ = _ := by
        rw [h]
        congr 1
        funext m
        exact subst_X hsw _

/-- **`Φ(f, g)^* ω = f^* ω + g^* ω`** for families `f`, `g` without constant term. -/
theorem sum_invDiff_subst_addPS {τ : Type*} {f g : Fin d → MvPowerSeries τ k} (hf : NoConst f)
    (hg : NoConst g) (t : τ) (l : Fin d) :
    ∑ i, (F.invDiff l i).subst (F.addPS f g) * pderiv k t (F.addPS f g i) =
      ∑ m, (F.invDiff l m).subst f * pderiv k t (f m) +
        ∑ m, (F.invDiff l m).subst g * pderiv k t (g m) := by
  have hb := hasSubst_pairFam hf hg
  have hΦ := hasSubst_of_constantCoeff_zero F.constantCoeff_Φ
  have e : ∀ i, (F.invDiff l i).subst (F.addPS f g) =
      ((F.invDiff l i).subst F.Φ).subst (pairFam f g) := fun i => by
    rw [subst_comp_subst_apply hΦ hb]
    rfl
  have e0 : ∀ m, ∑ i, ((F.invDiff l i).subst F.Φ).subst (pairFam f g) *
      (pderiv k (0, m) (F.Φ i)).subst (pairFam f g) = (F.invDiff l m).subst f := by
    intro m
    rw [← coe_substAlgHom hb]
    simp only [← map_mul, ← map_sum]
    have hXa : HasSubst (fun m => (X ((0 : Fin 2), m) : MvPowerSeries (Fin 2 × Fin d) k)) :=
      hasSubst_of_noConst (noConst_Xv 0)
    rw [F.sum_invDiff_subst_Φ_mul_pderiv_zero, coe_substAlgHom, subst_comp_subst_apply hXa hb]
    congr 1
    funext s
    exact subst_X hb _
  have e1 : ∀ m, ∑ i, ((F.invDiff l i).subst F.Φ).subst (pairFam f g) *
      (pderiv k (1, m) (F.Φ i)).subst (pairFam f g) = (F.invDiff l m).subst g := by
    intro m
    rw [← coe_substAlgHom hb]
    simp only [← map_mul, ← map_sum]
    have hXa : HasSubst (fun m => (X ((1 : Fin 2), m) : MvPowerSeries (Fin 2 × Fin d) k)) :=
      hasSubst_of_noConst (noConst_Xv 1)
    rw [F.sum_invDiff_subst_Φ_mul_pderiv_one, coe_substAlgHom, subst_comp_subst_apply hXa hb]
    congr 1
    funext s
    exact subst_X hb _
  simp only [e, F.pderiv_addPS hf hg, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← e0, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← e1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm

/-- **`[n]_F^* ω = n ω`** ([Tate, §(2.2), p. 165]). -/
theorem sum_invDiff_subst_mulPS (n : ℕ) (l j : Fin d) :
    ∑ i, (F.invDiff l i).subst (F.mulPS n) * pderiv k j (F.mulPS n i) = n • F.invDiff l j := by
  classical
  induction n with
  | zero => simp [mulPS_zero]
  | succ n ih =>
    rw [mulPS_succ, F.sum_invDiff_subst_addPS (F.noConst_mulPS n) noConst_X, ih, succ_nsmul,
      add_right_inj]
    simp only [pderiv_X, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [show (fun j => (X j : MvPowerSeries (Fin d) k)) = X from rfl, subst_self]
    rfl

end FGL

end PadicHodge
