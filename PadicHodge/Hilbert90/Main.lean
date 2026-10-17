/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Hilbert90.Matrix
import Mathlib.Topology.Instances.Matrix

/-!
# Hilbert 90 for the completion of an unramified tower

Let `A : Gal(ℚ̄_p/ℚ_p) → GL_h(ℤ_p)` be a homomorphism and `M_1 ⊆ M_2 ⊆ ⋯ ⊆ ℚ̄_p` finite,
Galois-stable, unramified and rigid extensions of `ℚ_p` (`IsUnrStable`) such that
`A(ν) ≡ 1 mod p^k` for `ν ∈ Gal(ℚ̄_p/M_k)`. Then (**`exists_hilbert90`**) there is
`X ∈ GL_h(ℂ_p)` (with entries in the closure of `⋃ O_{M_k}`) such that `A(σ) σ(X) = X` for all
`σ`: the semilinear representation `ℂ_p^h` with `σ * x = A(σ) σ(x)` is trivial.
(Hilbert 90 for `\hat{ℚ_p^{ur}}`; the `M_k` play the role of the finite unramified levels.)

Proof (successive approximation, standard; written up here):

1. `exists_good_zero`: `X_0 ∈ M_h(O_{M_1})`, `|det X_0| = 1`, `A(σ) σ(X_0) ≡ X_0 mod p`
   (`exists_GL_mod_p`, descent over the residue field of `M_1`);
2. `exists_good_succ`: given `X = X_k` with `A(σ) σ(X) ≡ X mod p^{k+1}`, put
   `U(σ) = X⁻¹ A(σ) σ(X) = 1 + p^{k+1} c(σ)`. Then `U(στ) = U(σ) σ(U(τ))`, so
   `c(στ) = c(σ) + σ(c(τ)) + p^{k+1} c(σ) σ(c(τ))` is a cocycle modulo `p`, `≡ 0 mod p` on
   `Gal(ℚ̄_p/M_{k+2})`; additive Hilbert 90 (`exists_additive`) gives `Z ∈ M_h(O_{M_{k+2}})` with
   `Z − σ(Z) ≡ c(σ) mod p`, and `X_{k+1} = X (1 + p^{k+1} Z)` solves the equation modulo
   `p^{k+2}`;
3. the `X_k` converge in `M_h(ℂ_p)` (`|X_{k+1} − X_k| ≤ |p|^{k+1}`); the limit is a solution with
   `|det X| = 1`.
-/

noncomputable section

open Matrix Filter Topology

namespace PadicHodge

namespace Hilbert90

variable {p : ℕ} [hp : Fact p.Prime] {h : ℕ}

local notation "K" => PadicAlgCl p

variable (A : GalQp p →* Matrix (Fin h) (Fin h) ℤ_[p])
  (Mk : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p))

/-- The matrix `A(σ)` over `ℚ̄_p`. -/
abbrev AK (σ : GalQp p) : Matrix (Fin h) (Fin h) K := (A σ).map (algebraMap ℤ_[p] K)

theorem AK_mul (σ τ : GalQp p) : AK A (σ * τ) = AK A σ * AK A τ := by
  simp only [AK, map_mul, Matrix.map_mul]

theorem AK_map (σ τ : GalQp p) : (AK A τ).map σ = AK A τ := by
  ext i j; simp [gal_algebraMap_padicInt]

theorem map_gal_mul (X : Matrix (Fin h) (Fin h) K) (σ τ : GalQp p) :
    X.map (σ * τ) = (X.map τ).map σ := by ext; rfl

theorem map_gal_one (σ : GalQp p) : (1 : Matrix (Fin h) (Fin h) K).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

theorem map_gal_add (X Y : Matrix (Fin h) (Fin h) K) (σ : GalQp p) :
    (X + Y).map σ = X.map σ + Y.map σ := by ext; simp

theorem map_gal_smul_natPow (X : Matrix (Fin h) (Fin h) K) (σ : GalQp p) (n : ℕ) :
    (((p : K) ^ n) • X).map σ = ((p : K) ^ n) • X.map σ := by ext; simp

/-- `X` solves `A(σ) σ(X) ≡ X mod p^{k+1}`, with entries in `O_{M_{k+1}}` and `|det X| = 1`. -/
structure Good (k : ℕ) (X : Matrix (Fin h) (Fin h) K) : Prop where
  inO : InO (Mk (k + 1)) X
  det : ‖X.det‖ = 1
  inv : ∀ σ : GalQp p, Bd (AK A σ * X.map σ - X) (‖(p : K)‖ ^ (k + 1))

variable {A Mk} [∀ k, FiniteDimensional ℚ_[p] (Mk k)]
variable (hM : ∀ k, IsUnrStable (Mk k)) (hmono : ∀ k, Mk k ≤ Mk (k + 1))
  (hA : ∀ k (ν : GalQp p), (∀ z ∈ Mk k, ν z = z) → Bd (AK A ν - 1) (‖(p : (PadicAlgCl p))‖ ^ k))

include hM hA in
theorem exists_good_zero : ∃ X, Good A Mk 0 X := by
  obtain ⟨X, hXO, hdet, hinv⟩ := exists_GL_mod_p (hM 1) A (fun ν hν i j => by
    have := hA 1 ν hν i j
    rw [pow_one, Matrix.sub_apply, AK, Matrix.map_apply] at this
    have h1 : ‖A ν i j - (1 : Matrix (Fin h) (Fin h) ℤ_[p]) i j‖ =
        ‖algebraMap ℤ_[p] K (A ν i j) - (1 : Matrix (Fin h) (Fin h) K) i j‖ := by
      rw [← norm_algebraMap_padicInt, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h1]
    exact this.trans_lt norm_p_lt_one)
  exact ⟨X, hXO, hdet, fun σ i j => by rw [zero_add, pow_one]; exact hinv σ i j⟩

theorem p_ne_zero : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero

include hM hmono hA in
theorem exists_good_succ {k : ℕ} {X : Matrix (Fin h) (Fin h) K} (hX : Good A Mk k X) :
    ∃ X', Good A Mk (k + 1) X' ∧ Bd (X' - X) (‖(p : K)‖ ^ (k + 1)) := by
  set P := ‖(p : K)‖ with hPdef
  have hP0 : 0 ≤ P := norm_nonneg _
  have hP1 : P < 1 := norm_p_lt_one
  set q : K := (p : K) ^ (k + 1) with hqdef
  have hq : ‖q‖ = P ^ (k + 1) := norm_pow _ _
  have hq0 : q ≠ 0 := pow_ne_zero _ p_ne_zero
  have hqP : P ^ (k + 1) ≤ P := by
    calc P ^ (k + 1) ≤ P ^ 1 := pow_le_pow_of_le_one hP0 hP1.le (by omega)
      _ = P := pow_one P
  have hqle : P ^ (k + 1) ≤ 1 := hqP.trans hP1.le
  set M' := Mk (k + 2)
  have hqO : q ∈ OM M' :=
    ⟨by have h1 : ((p ^ (k + 1) : ℕ) : K) ∈ M' := M'.natCast_mem _
        simpa [hqdef] using h1, hq.trans_le hqle⟩
  have hqinvM : q⁻¹ ∈ M' := M'.inv_mem hqO.1
  have hXO' : InO M' X := hX.inO.mono (hmono _)
  have hdet0 : IsUnit X.det := isUnit_iff_ne_zero.mpr fun h0 => by
    have h1 := hX.det
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  set Xi := X⁻¹
  have hXXi : X * Xi = 1 := Matrix.mul_nonsing_inv _ hdet0
  have hXiX : Xi * X = 1 := Matrix.nonsing_inv_mul _ hdet0
  have hXiO : InO M' Xi := (hX.inO.inv hX.det).mono (hmono _)
  let U : GalQp p → Matrix (Fin h) (Fin h) K := fun σ => Xi * (AK A σ * X.map σ)
  have hU1 : ∀ σ, U σ - 1 = Xi * (AK A σ * X.map σ - X) := by
    intro σ; simp only [U, Matrix.mul_sub, hXiX]
  have hUmul : ∀ σ τ, U (σ * τ) = U σ * (U τ).map σ := by
    intro σ τ
    have e1 : (X.map σ) * (Xi.map σ) = 1 := by
      rw [← Matrix.map_mul, hXXi, map_gal_one]
    simp only [U, Matrix.map_mul, AK_map, AK_mul, map_gal_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (X.map σ) (Xi.map σ), e1, Matrix.one_mul]
  let c : GalQp p → Matrix (Fin h) (Fin h) K := fun σ => q⁻¹ • (U σ - 1)
  have hUc : ∀ σ, U σ = 1 + q • c σ := by
    intro σ; simp only [c, smul_smul, mul_inv_cancel₀ hq0, one_smul, add_sub_cancel]
  have hUbd : ∀ σ, Bd (U σ - 1) (P ^ (k + 1)) := fun σ => by
    rw [hU1]; exact hXiO.bd.mul_left (hX.inv σ) (pow_nonneg hP0 _)
  have hUO : ∀ σ, InO M' (U σ - 1) := fun σ => by
    rw [hU1]
    exact hXiO.mul (((inO_padicInt _).mul (hXO'.map_gal (hM _) σ)).sub hXO')
  have hcO : ∀ σ, InO M' (c σ) := by
    intro σ i j
    refine ⟨M'.mul_mem hqinvM (hUO σ i j).1, ?_⟩
    change ‖q⁻¹ * (U σ - 1) i j‖ ≤ 1
    rw [norm_mul, norm_inv, hq]
    have hpos : 0 < P ^ (k + 1) := pow_pos norm_p_pos _
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hUbd σ i j
  have hcoc : ∀ σ τ, c (σ * τ) = c σ + (c τ).map σ + q • (c σ * (c τ).map σ) := by
    intro σ τ
    have h1 := hUmul σ τ
    rw [hUc, hUc, hUc, map_gal_add, map_gal_one, hqdef, map_gal_smul_natPow, ← hqdef] at h1
    have h2 : q • c (σ * τ) = q • (c σ + (c τ).map σ + q • (c σ * (c τ).map σ)) := by
      have h3 : (1 + q • c σ) * (1 + q • (c τ).map σ) =
          1 + q • (c σ + (c τ).map σ + q • (c σ * (c τ).map σ)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
        abel
      rw [h3] at h1
      exact add_left_cancel h1
    exact smul_right_injective _ hq0 h2
  have hcfix : ∀ ν : GalQp p, (∀ z ∈ M', ν z = z) → Bd (c ν) P := by
    intro ν hν
    have hXν : X.map ν = X := by ext i j; exact hν _ (hXO' i j).1
    have h1 : U ν - 1 = Xi * ((AK A ν - 1) * X) := by
      rw [hU1, hXν, Matrix.sub_mul, Matrix.one_mul]
    have h2 : Bd (U ν - 1) (P ^ (k + 2)) := by
      rw [h1]
      exact hXiO.bd.mul_left ((hA (k + 2) ν hν).mul_right hXO'.bd (pow_nonneg hP0 _))
        (pow_nonneg hP0 _)
    intro i j
    change ‖q⁻¹ * (U ν - 1) i j‖ ≤ P
    rw [norm_mul, norm_inv, hq]
    have hpos : 0 < P ^ (k + 1) := pow_pos norm_p_pos _
    rw [inv_mul_le_iff₀ hpos, ← pow_succ]
    exact h2 i j
  -- additive Hilbert 90, entrywise
  have hZ : ∀ i j, ∃ Z ∈ OM M', ∀ σ : GalQp p, ‖Z - σ Z - c σ i j‖ ≤ P := by
    intro i j
    refine exists_additive (hM (k + 2)) (fun σ => c σ i j) (fun σ => hcO σ i j)
      (fun σ τ => ?_) (fun ν hν => hcfix ν hν i j)
    rw [hcoc]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [show c σ i j + σ (c τ i j) + q * (c σ * (c τ).map σ) i j - c σ i j - σ (c τ i j) =
      q * (c σ * (c τ).map σ) i j by ring, norm_mul, hq]
    have : ‖(c σ * (c τ).map σ) i j‖ ≤ 1 :=
      ((hcO σ).bd.mul_left ((hcO τ).bd.map_gal σ) zero_le_one) i j
    calc P ^ (k + 1) * ‖(c σ * (c τ).map σ) i j‖ ≤ P ^ (k + 1) * 1 :=
          mul_le_mul_of_nonneg_left this (pow_nonneg hP0 _)
      _ ≤ P := by rw [mul_one]; exact hqP
  choose Z hZO hZ using hZ
  let Zm : Matrix (Fin h) (Fin h) K := Matrix.of Z
  have hZmO : InO M' Zm := hZO
  have hW : InO M' (1 + q • Zm) := inO_one.add (hZmO.smul hqO)
  have hWbd : Bd ((1 + q • Zm) - 1) (P ^ (k + 1)) := by
    rw [add_sub_cancel_left]
    have := hZmO.bd.smul q
    rwa [hq, mul_one] at this
  refine ⟨X * (1 + q • Zm), ⟨hXO'.mul hW, ?_, fun σ => ?_⟩, ?_⟩
  · rw [det_mul, norm_mul, hX.det, one_mul]
    exact norm_det_eq_one_of_bd (pow_nonneg hP0 _) (pow_lt_one₀ hP0 hP1 (by omega)) hW.bd hWbd
  · -- the new error term
    have hXU : AK A σ * X.map σ = X * (1 + q • c σ) := by
      rw [← hUc]
      simp only [U, ← Matrix.mul_assoc, hXXi, Matrix.one_mul]
    have hid : AK A σ * (X * (1 + q • Zm)).map σ - X * (1 + q • Zm) =
        q • (X * (c σ + Zm.map σ - Zm + q • (c σ * Zm.map σ))) := by
      rw [Matrix.map_mul, map_gal_add, map_gal_one, hqdef, map_gal_smul_natPow, ← hqdef,
        ← Matrix.mul_assoc, hXU, Matrix.mul_assoc, ← Matrix.mul_sub, ← Matrix.mul_smul]
      congr 1
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul]
      abel
    rw [hid]
    have hin : Bd (c σ + Zm.map σ - Zm + q • (c σ * Zm.map σ)) P := by
      refine Bd.add ?_ ?_
      · intro i j
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply]
        rw [show c σ i j + σ (Zm i j) - Zm i j = -(Z i j - σ (Z i j) - c σ i j) by
          simp only [Zm, of_apply]; ring, norm_neg]
        exact hZ i j σ
      · have := ((hcO σ).bd.mul_left (hZmO.bd.map_gal σ) zero_le_one).smul q
        rw [hq, mul_one] at this
        exact this.mono hqP
    have := (hXO'.bd.mul_left hin hP0).smul q
    rwa [hq, ← pow_succ] at this
  · have : X * (1 + q • Zm) - X = q • (X * Zm) := by
      rw [Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left, Matrix.mul_smul]
    rw [this]
    have := (hXO'.bd.mul_left hZmO.bd zero_le_one).smul q
    rwa [hq, mul_one] at this

/-- The completion map `ℚ̄_p → ℂ_p`. -/
abbrev toCp : K →+* ℂ_[p] := UniformSpace.Completion.coeRingHom

theorem norm_toCp (x : K) : ‖toCp x‖ = ‖x‖ := PadicComplex.norm_extends p x

include hM hmono hA in
/-- **Hilbert 90 for the completion of the unramified tower `⋃ M_k`.** -/
theorem exists_hilbert90 :
    ∃ X : Matrix (Fin h) (Fin h) ℂ_[p], IsUnit X.det ∧
      ∀ σ : GalQp p, (AK A σ).map toCp * X.map (autCp σ) = X := by
  set P := ‖(p : K)‖
  have hP0 : 0 ≤ P := norm_nonneg _
  have hP1 : P < 1 := norm_p_lt_one
  obtain ⟨X0, hX0⟩ := exists_good_zero hM hA
  choose f hf using fun k (X : Matrix (Fin h) (Fin h) K) (hX : Good A Mk k X) =>
    exists_good_succ hM hmono hA hX
  let seq : (k : ℕ) → {X // Good A Mk k X} := fun k =>
    Nat.rec ⟨X0, hX0⟩ (fun k Y => ⟨f k Y.1 Y.2, (hf k Y.1 Y.2).1⟩) k
  let Xs : ℕ → Matrix (Fin h) (Fin h) K := fun k => (seq k).1
  have hgood : ∀ k, Good A Mk k (Xs k) := fun k => (seq k).2
  have hstep : ∀ k, Bd (Xs (k + 1) - Xs k) (P ^ (k + 1)) := fun k => (hf k _ _).2
  -- convergence
  have hcauchy : ∀ i j, CauchySeq fun k => toCp (Xs k i j) := by
    intro i j
    refine cauchySeq_of_le_geometric P P hP1 fun k => ?_
    have h1 := hstep k i j
    rw [Matrix.sub_apply] at h1
    rw [dist_eq_norm, ← map_sub, norm_toCp, norm_sub_rev]
    calc _ ≤ P ^ (k + 1) := h1
      _ = P * P ^ k := pow_succ' P k
  choose L hL using fun i j => cauchySeq_tendsto_of_complete (hcauchy i j)
  let Xinf : Matrix (Fin h) (Fin h) ℂ_[p] := Matrix.of L
  have hT : Tendsto (fun k => (Xs k).map toCp) atTop (𝓝 Xinf) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hL i j
  refine ⟨Xinf, ?_, fun σ => ?_⟩
  · have hdetT : Tendsto (fun k => ((Xs k).map toCp).det) atTop (𝓝 Xinf.det) :=
      ((continuous_id.matrix_det).tendsto _).comp hT
    have hn : Tendsto (fun k => ‖((Xs k).map toCp).det‖) atTop (𝓝 ‖Xinf.det‖) :=
      (continuous_norm.tendsto _).comp hdetT
    have hconst : (fun k => ‖((Xs k).map toCp).det‖) = fun _ => (1 : ℝ) := by
      funext k
      rw [show ((Xs k).map toCp).det = toCp (Xs k).det from (RingHom.map_det _ _).symm,
        norm_toCp, (hgood k).det]
    rw [hconst] at hn
    have h1 : ‖Xinf.det‖ = 1 := tendsto_nhds_unique hn tendsto_const_nhds
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  · let F : Matrix (Fin h) (Fin h) ℂ_[p] → Matrix (Fin h) (Fin h) ℂ_[p] :=
      fun Y => (AK A σ).map toCp * Y.map (autCp σ) - Y
    have hF : Continuous F :=
      (continuous_const.matrix_mul (continuous_id.matrix_map (continuous_autCp σ))).sub
        continuous_id
    have h1 : Tendsto (fun k => F ((Xs k).map toCp)) atTop (𝓝 (F Xinf)) :=
      (hF.tendsto _).comp hT
    have hFk : ∀ k, F ((Xs k).map toCp) = (AK A σ * (Xs k).map σ - Xs k).map toCp := by
      intro k
      ext i j
      simp only [F, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, map_sub, map_sum,
        map_mul]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      exact autCp_coe σ _
    have h2 : Tendsto (fun k => F ((Xs k).map toCp)) atTop (𝓝 0) := by
      simp only [hFk]
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      refine squeeze_zero_norm (fun k => ?_) ((tendsto_pow_atTop_nhds_zero_of_lt_one hP0
        hP1).comp (tendsto_add_atTop_nat 1))
      rw [Matrix.map_apply, norm_toCp]
      exact (hgood k).inv σ i j
    have h3 : F Xinf = 0 := tendsto_nhds_unique h1 h2
    exact sub_eq_zero.mp h3

end Hilbert90

end PadicHodge
