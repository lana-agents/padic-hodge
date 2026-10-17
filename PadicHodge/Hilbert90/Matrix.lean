/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.Hilbert90.Linear

/-!
# Entrywise estimates for matrices over `ℚ̄_p`

Bookkeeping for the successive approximation in `Hilbert90/Main.lean`:

* `InO M X`: all entries of `X` lie in `O_M`; stable under sums, products, `σ`, `det`,
  adjugates and inverses of matrices with `|det| = 1`;
* `Bd X r`: all entries have absolute value `≤ r`; `Bd.mul_left`, `Bd.mul_right` (ultrametric);
* `norm_det_sub_le`: `|det X − det Y| ≤ r` if the entries of `X`, `Y` are bounded by `1` and
  those of `X − Y` by `r`.
-/

noncomputable section

open Matrix

namespace PadicHodge

namespace Hilbert90

variable {p : ℕ} [hp : Fact p.Prime] {h : ℕ}

local notation "K" => PadicAlgCl p

/-- All entries lie in `O_M`. -/
def InO (M : IntermediateField ℚ_[p] K) (X : Matrix (Fin h) (Fin h) K) : Prop :=
  ∀ i j, X i j ∈ OM M

/-- All entries have absolute value `≤ r`. -/
def Bd (X : Matrix (Fin h) (Fin h) K) (r : ℝ) : Prop := ∀ i j, ‖X i j‖ ≤ r

variable {M M' : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- The matrix over the subring `O_M`. -/
def InO.toO {X : Matrix (Fin h) (Fin h) K} (hX : InO M X) : Matrix (Fin h) (Fin h) (OM M) :=
  fun i j => ⟨X i j, hX i j⟩

theorem InO.map_toO {X : Matrix (Fin h) (Fin h) K} (hX : InO M X) :
    hX.toO.map (OM M).subtype = X := rfl

theorem inO_of_map (Y : Matrix (Fin h) (Fin h) (OM M)) : InO M (Y.map (OM M).subtype) :=
  fun i j => (Y i j).2

theorem InO.mul {X Y : Matrix (Fin h) (Fin h) K} (hX : InO M X) (hY : InO M Y) :
    InO M (X * Y) := by
  rw [← hX.map_toO, ← hY.map_toO, ← Matrix.map_mul]; exact inO_of_map _

theorem InO.add {X Y : Matrix (Fin h) (Fin h) K} (hX : InO M X) (hY : InO M Y) :
    InO M (X + Y) := fun i j => (OM M).add_mem (hX i j) (hY i j)

theorem InO.sub {X Y : Matrix (Fin h) (Fin h) K} (hX : InO M X) (hY : InO M Y) :
    InO M (X - Y) := fun i j => (OM M).sub_mem (hX i j) (hY i j)

theorem inO_one : InO M (1 : Matrix (Fin h) (Fin h) K) := by
  intro i j
  rw [one_apply]
  split_ifs
  · exact (OM M).one_mem
  · exact (OM M).zero_mem

theorem InO.smul {X : Matrix (Fin h) (Fin h) K} (hX : InO M X) {c : K} (hc : c ∈ OM M) :
    InO M (c • X) := fun i j => (OM M).mul_mem hc (hX i j)

theorem InO.mono {X : Matrix (Fin h) (Fin h) K} (hX : InO M X) (hMM : M ≤ M') : InO M' X :=
  fun i j => ⟨hMM (hX i j).1, (hX i j).2⟩

theorem inO_padicInt (A : Matrix (Fin h) (Fin h) ℤ_[p]) :
    InO M (A.map (algebraMap ℤ_[p] K)) := fun i j => algebraMap_padicInt_mem (A i j)

theorem InO.map_gal (hM : IsUnrStable M) {X : Matrix (Fin h) (Fin h) K} (hX : InO M X)
    (σ : GalQp p) : InO M (X.map σ) := fun i j => mem_OM_gal hM σ (hX i j)

theorem InO.det {X : Matrix (Fin h) (Fin h) K} (hX : InO M X) : X.det ∈ OM M := by
  have h1 : X.det = (OM M).subtype hX.toO.det := by rw [RingHom.map_det]; rfl
  rw [h1]; exact (hX.toO.det).2

theorem InO.adjugate {X : Matrix (Fin h) (Fin h) K} (hX : InO M X) : InO M X.adjugate := by
  have h1 : X.adjugate = ((OM M).subtype.mapMatrix hX.toO).adjugate := rfl
  rw [h1, ← RingHom.map_adjugate]; exact inO_of_map _

theorem InO.inv {X : Matrix (Fin h) (Fin h) K} (hX : InO M X) (hdet : ‖X.det‖ = 1) :
    InO M X⁻¹ := by
  rw [Matrix.inv_def]
  refine hX.adjugate.smul ?_
  have hd := hX.det
  have h0 : X.det ≠ 0 := by intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  rw [Ring.inverse_eq_inv']
  exact ⟨M.inv_mem hd.1, by rw [norm_inv, hdet, inv_one]⟩

theorem InO.bd {X : Matrix (Fin h) (Fin h) K} (hX : InO M X) : Bd X 1 := fun i j => (hX i j).2

theorem Bd.mul_left {X Y : Matrix (Fin h) (Fin h) K} {r : ℝ} (hX : Bd X 1) (hY : Bd Y r)
    (hr : 0 ≤ r) : Bd (X * Y) r := by
  intro i j
  rw [mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun l _ => ?_
  rw [norm_mul]
  calc ‖X i l‖ * ‖Y l j‖ ≤ 1 * r := mul_le_mul (hX i l) (hY l j) (norm_nonneg _) zero_le_one
    _ = r := one_mul r

theorem Bd.mul_right {X Y : Matrix (Fin h) (Fin h) K} {r : ℝ} (hX : Bd X r) (hY : Bd Y 1)
    (hr : 0 ≤ r) : Bd (X * Y) r := by
  intro i j
  rw [mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun l _ => ?_
  rw [norm_mul]
  calc ‖X i l‖ * ‖Y l j‖ ≤ r * 1 := mul_le_mul (hX i l) (hY l j) (norm_nonneg _) hr
    _ = r := mul_one r

theorem Bd.add {X Y : Matrix (Fin h) (Fin h) K} {r : ℝ} (hX : Bd X r) (hY : Bd Y r) :
    Bd (X + Y) r := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))

theorem Bd.neg {X : Matrix (Fin h) (Fin h) K} {r : ℝ} (hX : Bd X r) : Bd (-X) r := fun i j => by
  rw [neg_apply, norm_neg]; exact hX i j

theorem Bd.sub {X Y : Matrix (Fin h) (Fin h) K} {r : ℝ} (hX : Bd X r) (hY : Bd Y r) :
    Bd (X - Y) r := by rw [sub_eq_add_neg]; exact hX.add hY.neg

theorem Bd.smul {X : Matrix (Fin h) (Fin h) K} {r : ℝ} (hX : Bd X r) (c : K) :
    Bd (c • X) (‖c‖ * r) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hX i j) (norm_nonneg _)

theorem Bd.mono {X : Matrix (Fin h) (Fin h) K} {r s : ℝ} (hX : Bd X r) (hrs : r ≤ s) : Bd X s :=
  fun i j => (hX i j).trans hrs

theorem Bd.map_gal {X : Matrix (Fin h) (Fin h) K} {r : ℝ} (hX : Bd X r) (σ : GalQp p) :
    Bd (X.map σ) r := fun i j => by rw [map_apply, norm_aut_apply]; exact hX i j

/-- Products of close families are close. -/
theorem norm_prod_sub_le {ι : Type*} (s : Finset ι) (a b : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) (hab : ∀ i, ‖a i - b i‖ ≤ r) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ 1 * r :=
            mul_le_mul (ha j) ih (norm_nonneg _) zero_le_one
        _ = r := one_mul r
    · rw [norm_mul]
      have hpb : ‖∏ i ∈ s, b i‖ ≤ 1 := by
        rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hb i
      calc ‖a j - b j‖ * ‖∏ i ∈ s, b i‖ ≤ r * 1 := mul_le_mul (hab j) hpb (norm_nonneg _) hr
        _ = r := mul_one r

/-- **Close matrices have close determinants.** -/
theorem norm_det_sub_le {X Y : Matrix (Fin h) (Fin h) K} {r : ℝ} (hr : 0 ≤ r) (hX : Bd X 1)
    (hY : Bd Y 1) (hXY : Bd (X - Y) r) : ‖X.det - Y.det‖ ≤ r := by
  rw [det_apply, det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun σ _ => ?_
  rw [← smul_sub]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rw [one_smul]
    exact norm_prod_sub_le _ _ _ hr (fun i => hX _ _) (fun i => hY _ _) fun i => hXY _ _
  · rw [Units.neg_smul, one_smul, norm_neg]
    exact norm_prod_sub_le _ _ _ hr (fun i => hX _ _) (fun i => hY _ _) fun i => hXY _ _

/-- A matrix `≡ 1` modulo something of absolute value `< 1` has determinant of absolute value
`1`. -/
theorem norm_det_eq_one_of_bd {X : Matrix (Fin h) (Fin h) K} {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hX : Bd X 1) (hX1 : Bd (X - 1) r) : ‖X.det‖ = 1 := by
  have h1 : Bd (1 : Matrix (Fin h) (Fin h) K) 1 := inO_one (M := ⊥).bd
  have hd := norm_det_sub_le hr0 hX h1 hX1
  rw [det_one] at hd
  have : X.det = 1 + (X.det - 1) := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
    rw [norm_one]; exact (hd.trans_lt hr).ne'), norm_one]
  exact max_eq_left (hd.trans hr.le)

end Hilbert90

end PadicHodge
