/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Fontaine.Galois

/-!
# `V_p(Ω)` and `T_p(Ω)` via Fontaine's `ξ`

Let `L/ℚ_p` be finite inside `ℚ̄_p`, `Ω = Ω_{O_K̄/O_L}` and `ξ : ℚ̄_p → Ω` Fontaine's map
([Fo, Thm 1′], `OL.xi`), which is surjective, `O_K̄`-linear, with kernel the ball
`𝔞_L = {a | ‖a‖ ≤ R_L}`, `R_L = (‖𝔇_{L/ℚ_p}‖ · |ε_1 - 1|)⁻¹`.

A sequence `z : ℕ → Ω` with `p · z_{k+1} = z_k` (an element of `V_p(Ω) = lim_{×p} Ω`; it lies in
`T_p(Ω)` iff `z_0 = 0`) defines

* **`OL.tau`** `z = lim_k p^k a_k ∈ ℂ_p`, where `a_k ∈ ℚ̄_p` is any choice with `ξ(a_k) = z_k`:
  `ξ(p a_{k+1} - a_k) = 0`, so `p^{k+1} a_{k+1} - p^k a_k ∈ p^k 𝔞_L` and the sequence is Cauchy;
  two choices differ by `p^k 𝔞_L → 0`. The characterisation is **`OL.tendsto_tau`**.

Main results:

* `OL.tau_add`, `OL.tau_neg`, `OL.tau_sub`, `OL.tau_zero`, `OL.tau_smul` (`τ(y z) = y τ(z)` for
  `y ∈ O_K̄`);
* **`OL.norm_tau_le`**: on `T_p(Ω)`, `‖τ z‖ ≤ R_L`;
* **`OL.tau_eq_zero_iff`**, `OL.tau_injective`: `τ` is injective on `V_p(Ω)`
  (`z_k = ξ(p^m a_{k+m})` and `p^m a_{k+m} = p^{-k} (p^{k+m} a_{k+m}) → 0`);
* **`OL.tau_galΩ`**: `τ(σ z) = χ(σ) · σ(τ z)` for `σ ∈ G_L` (from `OL.galΩ_xi`);
* **`OL.map_xi`**, **`OL.tau_map`**: for `L ⊆ E`, `ξ_E = (Ω_{O_K̄/O_L} → Ω_{O_K̄/O_E}) ∘ ξ_L`,
  hence `τ_E` of the image of `z` is `τ_L z`.

So `τ` identifies `T_p(Ω)` with a `G_L`-stable `O_K̄`-submodule of the ball
`{‖x‖ ≤ R_L} ⊆ ℂ_p(1)`; surjectivity onto the ball is not proved here.

## References

* [Fo] J.-M. Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur
  les corps locaux*, Invent. Math. 65 (1982), §2.7–2.8, Thm 1′ (p. 383).
-/

noncomputable section

open Filter Topology KaehlerDifferential

namespace PadicHodge

variable {p : ℕ} [hp : Fact p.Prime]

namespace OL

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem norm_p_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_algebraMap', Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem norm_p_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.mpr (by exact_mod_cast hp.out.ne_zero)

theorem coe_cp_mul (a b : PadicAlgCl p) : ((a * b : PadicAlgCl p) : ℂ_[p]) = a * b := by
  simp only [PadicComplex.coe_eq, map_mul]

theorem coe_cp_add (a b : PadicAlgCl p) : ((a + b : PadicAlgCl p) : ℂ_[p]) = a + b := by
  simp only [PadicComplex.coe_eq, map_add]

theorem coe_cp_sub (a b : PadicAlgCl p) : ((a - b : PadicAlgCl p) : ℂ_[p]) = a - b := by
  simp only [PadicComplex.coe_eq, map_sub]

theorem coe_cp_neg (a : PadicAlgCl p) : ((-a : PadicAlgCl p) : ℂ_[p]) = -a := by
  simp only [PadicComplex.coe_eq, map_neg]

section Tau

variable {ε : ℕ → PadicAlgCl p} (hε : ∀ n, IsPrimitiveRoot (ε (n + 1)) (p ^ (n + 1)))
  (hεp : ∀ n, ε (n + 2) ^ p = ε (n + 1))

include hε in
theorem norm_eps_one_sub_one_pos : 0 < ‖ε 1 - 1‖ := by
  rcases (norm_nonneg (ε 1 - 1)).eq_or_lt with h0 | h0
  · have := norm_eps_one_sub_one_pow hε
    rw [← h0, zero_pow (by have := hp.out.two_le; omega)] at this
    exact absurd this.symm (inv_ne_zero (by exact_mod_cast hp.out.ne_zero))
  · exact h0

include hε in
theorem kerRadius_pos [FiniteDimensional ℚ_[p] L] : 0 < (dL L * ‖ε 1 - 1‖)⁻¹ :=
  inv_pos.mpr (mul_pos dnorm_pos (norm_eps_one_sub_one_pos hε))

include hεp in
theorem xi_zero : xi L hε 0 = 0 := by
  have h := xi_add hε hεp (L := L) 0 0
  rw [add_zero] at h
  exact (left_eq_add.mp h)

include hεp in
theorem xi_neg (a : PadicAlgCl p) : xi L hε (-a) = -xi L hε a := by
  rw [eq_neg_iff_add_eq_zero, ← xi_add hε hεp, neg_add_cancel, xi_zero hε hεp]

include hεp in
theorem xi_sub (a b : PadicAlgCl p) : xi L hε (a - b) = xi L hε a - xi L hε b := by
  rw [sub_eq_add_neg, xi_add hε hεp, xi_neg hε hεp, ← sub_eq_add_neg]

include hεp in
theorem xi_pow_mul (n : ℕ) (a : PadicAlgCl p) :
    xi L hε ((p : PadicAlgCl p) ^ n * a) = ((p : OKbar p) ^ n) • xi L hε a := by
  have h := xi_smul hε hεp (L := L) ((p : OKbar p) ^ n) a
  rwa [SubmonoidClass.coe_pow, Subring.coe_natCast] at h

include hεp in
/-- The kernel of `ξ` is the closed ball of radius `R_L = (‖𝔇_{L/ℚ_p}‖ · |ε_1 - 1|)⁻¹`. -/
theorem xi_eq_zero_iff_norm_le [FiniteDimensional ℚ_[p] L] (a : PadicAlgCl p) :
    xi L hε a = 0 ↔ ‖a‖ ≤ (dL L * ‖ε 1 - 1‖)⁻¹ := by
  have hpos : 0 < dL L * ‖ε 1 - 1‖ := mul_pos dnorm_pos (norm_eps_one_sub_one_pos hε)
  rw [xi_eq_zero_iff hε hεp, mul_assoc, ← le_div_iff₀ hpos, one_div]

include hεp in
theorem norm_sub_le_of_xi_eq [FiniteDimensional ℚ_[p] L] {a b : PadicAlgCl p}
    (h : xi L hε a = xi L hε b) : ‖a - b‖ ≤ (dL L * ‖ε 1 - 1‖)⁻¹ :=
  (xi_eq_zero_iff_norm_le hε hεp _).mp (by rw [xi_sub hε hεp, h, sub_self])

variable (L) in
/-- **`τ : V_p(Ω) → ℂ_p`**: for `z` with `p z_{k+1} = z_k`, `τ z = lim_k p^k a_k` for any
`a_k ∈ ℚ̄_p` with `ξ(a_k) = z_k` (`OL.tendsto_tau`). -/
def tau (z : ℕ → Ω[OKbar p⁄OL L]) : ℂ_[p] :=
  limUnder atTop fun k =>
    (((p : PadicAlgCl p) ^ k * Function.invFun (xi L hε) (z k) : PadicAlgCl p) : ℂ_[p])

variable {hε}

theorem pow_smul_eq_of_vp {z : ℕ → Ω[OKbar p⁄OL L]} (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k)
    (k N : ℕ) : ((p : OKbar p) ^ N) • z (k + N) = z k := by
  induction N with
  | zero => rw [pow_zero, one_smul, add_zero]
  | succ N ih => rw [pow_succ, mul_smul, ← add_assoc, hz, ih]

include hεp in
/-- Two choices of preimages under `ξ` of the same element differ by `p^k 𝔞_L` after
multiplication by `p^k`. -/
theorem norm_pow_mul_sub_le [FiniteDimensional ℚ_[p] L] {a b : PadicAlgCl p}
    (h : xi L hε a = xi L hε b) (k : ℕ) :
    ‖(p : PadicAlgCl p) ^ k * a - (p : PadicAlgCl p) ^ k * b‖ ≤
      ‖(p : PadicAlgCl p)‖ ^ k * (dL L * ‖ε 1 - 1‖)⁻¹ := by
  rw [← mul_sub, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (norm_sub_le_of_xi_eq hε hεp h) (by positivity)

include hεp in
theorem norm_step_le [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) {a : ℕ → PadicAlgCl p}
    (ha : ∀ k, xi L hε (a k) = z k) (k : ℕ) :
    ‖(p : PadicAlgCl p) ^ (k + 1) * a (k + 1) - (p : PadicAlgCl p) ^ k * a k‖ ≤
      ‖(p : PadicAlgCl p)‖ ^ k * (dL L * ‖ε 1 - 1‖)⁻¹ := by
  have h : xi L hε ((p : PadicAlgCl p) * a (k + 1)) = xi L hε (a k) := by
    have := xi_pow_mul hε hεp (L := L) 1 (a (k + 1))
    rw [pow_one, pow_one] at this
    rw [this, ha, ha, hz]
  have := norm_pow_mul_sub_le hεp h k
  rwa [← mul_assoc, ← pow_succ] at this

include hεp in
theorem cauchySeq_pow_mul [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) {a : ℕ → PadicAlgCl p}
    (ha : ∀ k, xi L hε (a k) = z k) :
    CauchySeq fun k => (((p : PadicAlgCl p) ^ k * a k : PadicAlgCl p) : ℂ_[p]) := by
  refine cauchySeq_of_le_geometric ‖(p : PadicAlgCl p)‖ (dL L * ‖ε 1 - 1‖)⁻¹ norm_p_lt_one
    fun k => ?_
  rw [dist_comm, dist_eq_norm, ← coe_cp_sub, PadicComplex.norm_extends, mul_comm _ (_ ^ k)]
  exact norm_step_le hεp hz ha k

include hεp in
/-- **Characterisation of `τ`**: if `ξ(a_k) = z_k` for all `k`, then `p^k a_k → τ z` in `ℂ_p`. -/
theorem tendsto_tau [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) {a : ℕ → PadicAlgCl p}
    (ha : ∀ k, xi L hε (a k) = z k) :
    Tendsto (fun k => (((p : PadicAlgCl p) ^ k * a k : PadicAlgCl p) : ℂ_[p])) atTop
      (𝓝 (tau L hε z)) := by
  set b : ℕ → PadicAlgCl p := fun k => Function.invFun (xi L hε) (z k) with hbdef
  have hb : ∀ k, xi L hε (b k) = z k := fun k =>
    Function.invFun_eq (xi_surjective hε hεp (z k))
  have hbt : Tendsto (fun k => (((p : PadicAlgCl p) ^ k * b k : PadicAlgCl p) : ℂ_[p])) atTop
      (𝓝 (tau L hε z)) :=
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_pow_mul hεp hz hb))
  have hdiff : Tendsto (fun k => (((p : PadicAlgCl p) ^ k * a k : PadicAlgCl p) : ℂ_[p]) -
      (((p : PadicAlgCl p) ^ k * b k : PadicAlgCl p) : ℂ_[p])) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k => ‖(p : PadicAlgCl p)‖ ^ k * (dL L * ‖ε 1 - 1‖)⁻¹)
      (fun k => ?_) ?_
    · rw [← coe_cp_sub, PadicComplex.norm_extends]
      exact norm_pow_mul_sub_le hεp ((ha k).trans (hb k).symm) k
    · simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_p_lt_one).mul_const
          (dL L * ‖ε 1 - 1‖)⁻¹
  simpa only [add_zero, add_sub_cancel] using hbt.add hdiff

include hεp in
theorem tau_eq_of_tendsto [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) {a : ℕ → PadicAlgCl p}
    (ha : ∀ k, xi L hε (a k) = z k) {x : ℂ_[p]}
    (hx : Tendsto (fun k => (((p : PadicAlgCl p) ^ k * a k : PadicAlgCl p) : ℂ_[p])) atTop
      (𝓝 x)) : tau L hε z = x :=
  tendsto_nhds_unique (tendsto_tau hεp hz ha) hx

/-! ### Linearity -/

include hεp in
theorem tau_zero [FiniteDimensional ℚ_[p] L] : tau L hε 0 = 0 := by
  refine tau_eq_of_tendsto hεp (a := 0) (fun k => smul_zero _) (fun k => xi_zero hε hεp) ?_
  simp only [Pi.zero_apply, mul_zero, PadicComplex.coe_zero]
  exact tendsto_const_nhds

include hεp in
theorem tau_add [FiniteDimensional ℚ_[p] L] {z w : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) (hw : ∀ k, (p : OKbar p) • w (k + 1) = w k) :
    tau L hε (z + w) = tau L hε z + tau L hε w := by
  choose a ha using fun k => xi_surjective hε hεp (L := L) (z k)
  choose b hb using fun k => xi_surjective hε hεp (L := L) (w k)
  refine tau_eq_of_tendsto hεp (a := a + b) (fun k => by simp only [Pi.add_apply, smul_add, hz, hw])
    (fun k => by rw [Pi.add_apply, xi_add hε hεp, ha, hb, Pi.add_apply]) ?_
  simpa only [Pi.add_apply, mul_add, coe_cp_add] using
    (tendsto_tau hεp hz ha).add (tendsto_tau hεp hw hb)

include hεp in
theorem tau_neg [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) :
    tau L hε (-z) = -tau L hε z := by
  choose a ha using fun k => xi_surjective hε hεp (L := L) (z k)
  refine tau_eq_of_tendsto hεp (a := -a) (fun k => by simp only [Pi.neg_apply, smul_neg, hz])
    (fun k => by rw [Pi.neg_apply, xi_neg hε hεp, ha, Pi.neg_apply]) ?_
  simpa only [Pi.neg_apply, mul_neg, coe_cp_neg] using (tendsto_tau hεp hz ha).neg

include hεp in
theorem tau_sub [FiniteDimensional ℚ_[p] L] {z w : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) (hw : ∀ k, (p : OKbar p) • w (k + 1) = w k) :
    tau L hε (z - w) = tau L hε z - tau L hε w := by
  have hw' : ∀ k, (p : OKbar p) • (-w) (k + 1) = (-w) k := fun k => by
    simp only [Pi.neg_apply, smul_neg, hw]
  rw [sub_eq_add_neg, tau_add hεp hz hw', tau_neg hεp hw, ← sub_eq_add_neg]

include hεp in
/-- `τ` is `O_K̄`-linear. -/
theorem tau_smul [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) (y : OKbar p) :
    tau L hε (y • z) = ((y : PadicAlgCl p) : ℂ_[p]) * tau L hε z := by
  choose a ha using fun k => xi_surjective hε hεp (L := L) (z k)
  refine tau_eq_of_tendsto hεp (a := fun k => (y : PadicAlgCl p) * a k)
    (fun k => by simp only [Pi.smul_apply, smul_comm (p : OKbar p) y, hz])
    (fun k => by rw [xi_smul hε hεp, ha, Pi.smul_apply]) ?_
  simpa only [mul_left_comm _ (y : PadicAlgCl p), coe_cp_mul] using
    (tendsto_tau hεp hz ha).const_mul ((y : PadicAlgCl p) : ℂ_[p])

/-! ### The image of `T_p(Ω)` and injectivity -/

include hεp in
/-- On `T_p(Ω)` (`z_0 = 0`), `‖τ z‖ ≤ R_L = (‖𝔇_{L/ℚ_p}‖ · |ε_1 - 1|)⁻¹`. -/
theorem norm_tau_le [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) (h0 : z 0 = 0) :
    ‖tau L hε z‖ ≤ (dL L * ‖ε 1 - 1‖)⁻¹ := by
  choose a ha using fun k => xi_surjective hε hεp (L := L) (z k)
  have hle : ∀ k, ‖(p : PadicAlgCl p) ^ k * a k‖ ≤ (dL L * ‖ε 1 - 1‖)⁻¹ := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, one_mul]
      exact (xi_eq_zero_iff_norm_le hε hεp _).mp ((ha 0).trans h0)
    | succ k ih =>
      have hs := norm_step_le hεp hz ha k
      have hpk : ‖(p : PadicAlgCl p)‖ ^ k * (dL L * ‖ε 1 - 1‖)⁻¹ ≤ (dL L * ‖ε 1 - 1‖)⁻¹ :=
        mul_le_of_le_one_left (kerRadius_pos hε).le
          (pow_le_one₀ (norm_nonneg _) norm_p_lt_one.le)
      calc ‖(p : PadicAlgCl p) ^ (k + 1) * a (k + 1)‖
          = ‖((p : PadicAlgCl p) ^ (k + 1) * a (k + 1) - (p : PadicAlgCl p) ^ k * a k) +
              (p : PadicAlgCl p) ^ k * a k‖ := by rw [sub_add_cancel]
        _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ _ := max_le (hs.trans hpk) ih
  refine le_of_tendsto' (tendsto_tau hεp hz ha).norm fun k => ?_
  rw [PadicComplex.norm_extends]
  exact hle k

include hεp in
/-- `τ` is injective on `V_p(Ω)`. -/
theorem eq_zero_of_tau_eq_zero [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) (h : tau L hε z = 0) (k : ℕ) : z k = 0 := by
  choose a ha using fun k => xi_surjective hε hεp (L := L) (z k)
  have ht := (tendsto_tau hεp hz ha).norm
  rw [h, norm_zero] at ht
  have hR : 0 < ‖(p : PadicAlgCl p)‖ ^ k * (dL L * ‖ε 1 - 1‖)⁻¹ :=
    mul_pos (pow_pos norm_p_pos k) (kerRadius_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hR))
  have hlt := hN (k + N) (Nat.le_add_left N k)
  rw [PadicComplex.norm_extends, pow_add, mul_assoc, norm_mul, norm_pow] at hlt
  have hsmall : ‖(p : PadicAlgCl p) ^ N * a (k + N)‖ ≤ (dL L * ‖ε 1 - 1‖)⁻¹ :=
    (lt_of_mul_lt_mul_left hlt (pow_nonneg (norm_nonneg _) k)).le
  rw [← pow_smul_eq_of_vp hz k N, ← ha, ← xi_pow_mul hε hεp]
  exact (xi_eq_zero_iff_norm_le hε hεp _).mpr hsmall

include hεp in
theorem tau_eq_zero_iff [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) : tau L hε z = 0 ↔ z = 0 := by
  refine ⟨fun h => funext (eq_zero_of_tau_eq_zero hεp hz h), ?_⟩
  rintro rfl
  exact tau_zero hεp

include hεp in
theorem tau_injective [FiniteDimensional ℚ_[p] L] {z w : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) (hw : ∀ k, (p : OKbar p) • w (k + 1) = w k)
    (h : tau L hε z = tau L hε w) : z = w := by
  have hzw : ∀ k, (p : OKbar p) • (z - w) (k + 1) = (z - w) k := fun k => by
    simp only [Pi.sub_apply, smul_sub, hz, hw]
  rw [← sub_eq_zero, ← tau_eq_zero_iff (hε := hε) hεp hzw, tau_sub hεp hz hw, h, sub_self]

/-! ### Galois equivariance -/

include hεp in
/-- **`G_L`-equivariance of `τ`**: `τ(σ z) = χ(σ) · σ(τ z)`, i.e. `τ` takes values in `ℂ_p(1)`. -/
theorem tau_galΩ [FiniteDimensional ℚ_[p] L] {z : ℕ → Ω[OKbar p⁄OL L]}
    (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) (σ : PadicAlgCl p ≃ₐ[L] PadicAlgCl p) :
    tau L hε (fun k => KaehlerUnion.galΩ (galOK σ) (z k)) =
      algebraMap ℚ_[p] ℂ_[p] ((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) *
        galCp L σ (tau L hε z) := by
  set c : ℚ_[p] := (((chi (σ.restrictScalars ℚ_[p]) : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])
  choose a ha using fun k => xi_surjective hε hεp (L := L) (z k)
  refine tau_eq_of_tendsto hεp (a := fun k => algebraMap ℚ_[p] (PadicAlgCl p) c * σ (a k))
    (fun k => by rw [← hz k, KaehlerUnion.galΩ_smul, map_natCast])
    (fun k => by rw [← galΩ_xi hε hεp, ha]) ?_
  have e : ∀ k, (((p : PadicAlgCl p) ^ k * (algebraMap ℚ_[p] (PadicAlgCl p) c * σ (a k)) :
      PadicAlgCl p) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] c *
        galCp L σ (((p : PadicAlgCl p) ^ k * a k : PadicAlgCl p) : ℂ_[p]) := fun k => by
    rw [galCp_coe, map_mul, map_pow, map_natCast, mul_left_comm, coe_cp_mul,
      IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
  simp only [e]
  exact (((continuous_galCp σ).tendsto _).comp (tendsto_tau hεp hz ha)).const_mul _

/-! ### Change of base field -/

section BaseChange

variable {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [Fact (L ≤ E)]

variable (hε) in
include hεp in
/-- `ξ_E = (Ω_{O_K̄/O_L} → Ω_{O_K̄/O_E}) ∘ ξ_L`. -/
theorem map_xi (a : PadicAlgCl p) :
    map (OL L) (OL E) (OKbar p) (OKbar p) (xi L hε a) = xi E hε a := by
  obtain ⟨n, h⟩ := exists_norm_pow_mul_le a
  rw [xi_eq hε hεp a h, xi_eq hε hεp a h, map_smul, dlogε, dlogε, map_smul, map_D,
    Algebra.algebraMap_self, RingHom.id_apply]

include hεp in
/-- `τ_E` of the image of `z` in `V_p(Ω_{O_K̄/O_E})` is `τ_L z`. -/
theorem tau_map [FiniteDimensional ℚ_[p] L] [FiniteDimensional ℚ_[p] E]
    {z : ℕ → Ω[OKbar p⁄OL L]} (hz : ∀ k, (p : OKbar p) • z (k + 1) = z k) :
    tau E hε (fun k => map (OL L) (OL E) (OKbar p) (OKbar p) (z k)) = tau L hε z := by
  choose a ha using fun k => xi_surjective hε hεp (L := L) (z k)
  exact tau_eq_of_tendsto hεp (a := a) (fun k => by rw [← map_smul, hz])
    (fun k => by rw [← map_xi (L := L) hε hεp, ha]) (tendsto_tau hεp hz ha)

end BaseChange

end Tau

end OL

end PadicHodge
