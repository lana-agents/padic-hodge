/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.LogProps
import PadicHodge.FormalGroup.Formal

/-!
# Multiplication by `n` and torsion points of a formal group law

For a formal group law `F` of dimension `d` (setting of `FormalGroup/Points.lean`):

* `ev_mulPS`: the power series `[n]_F(T)` (`FormalGroup/Formal.lean`) evaluated at a point
  `x` gives `n · x`;
* `eq_zero_of_nsmul_eq_zero`: `F(m_{ℂ_p})` has no torsion prime to `p` (if `p ∤ m` and
  `m · x = 0`, then `|x| ≤ |x|²`);
* `torsionBy F v = F(m_{ℂ_p})[p^v]`, the common zeros of `[p^v]_F` in the open polydisc
  (`mem_torsionBy_iff_ev`), and **`isOfFinAddOrder_iff`**: every torsion point is killed by a
  power of `p`; with `logF_eq_zero_iff`: `ker log_F = ⋃_v F(m_{ℂ_p})[p^v]` ([Hong, Prop. 3.2.3
  (2), Prop. 3.3.6 (3)] for formal groups).
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (F : FGL R d)

/-- **`[n]_F(x) = n · x`.** -/
theorem ev_mulPS (n : ℕ) (x : F.Pt p) (i : Fin d) : ev p (F.mulPS n i) x.1 = (n • x).1 i := by
  induction n generalizing i with
  | zero => rw [zero_nsmul, zero_val]; exact ev_zero x.2
  | succ n ih =>
    rw [mulPS_succ, addPS, ev_pairFam (F.constantCoeff_mulPS n) (fun j => constantCoeff_X j) x.2,
      succ_nsmul, add_val]
    congr 2
    · funext j; exact ih j
    · funext j; exact ev_X _ _

/-- **No torsion prime to `p`.** -/
theorem eq_zero_of_nsmul_eq_zero {x : F.Pt p} {m : ℕ} (hm : p.Coprime m) (h : m • x = 0) :
    x = 0 := by
  set r := F.rad x
  have hr0 : 0 ≤ r := F.rad_nonneg x
  have hr1 : r < 1 := F.rad_lt_one x
  have hm1 : ‖(m : ℂ_[p])‖ = 1 := by
    have : ((m : ℚ_[p]) : ℂ_[p]) = (m : ℂ_[p]) := by simp
    rw [← this, PadicComplex.norm_extends']
    exact Padic.norm_natCast_eq_one_iff.mpr hm
  have hb : F.Bnd x (r ^ 2) := fun i => by
    have h2 := (F.bnd_nsmul hr0 hr1.le (F.bnd_rad x) m).2 i
    rw [h, zero_val, ZeroMemClass.coe_zero, zero_sub, norm_neg, norm_mul, hm1, one_mul] at h2
    exact h2
  have hrr : r ≤ r ^ 2 := F.rad_le (sq_nonneg r) hb
  have hr : r = 0 := by
    by_contra hne
    have : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hne)
    nlinarith
  refine F.pt_ext fun j => Subtype.ext ?_
  have := F.bnd_rad x j
  rw [show F.rad x = 0 from hr] at this
  rw [zero_val, ZeroMemClass.coe_zero]
  exact norm_le_zero_iff.mp this

/-- `F(m_{ℂ_p})[p^v]`. -/
def torsionBy (v : ℕ) : AddSubgroup (F.Pt p) where
  carrier := {x | (p ^ v) • x = 0}
  zero_mem' := nsmul_zero _
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at *
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at *
    rw [smul_neg, hx, neg_zero]

theorem mem_torsionBy {v : ℕ} {x : F.Pt p} : x ∈ F.torsionBy v ↔ (p ^ v) • x = 0 := Iff.rfl

/-- `F(m_{ℂ_p})[p^v]` is the set of common zeros of `[p^v]_F` in the open polydisc. -/
theorem mem_torsionBy_iff_ev {v : ℕ} {x : F.Pt p} :
    x ∈ F.torsionBy v ↔ ∀ i, ev p (F.mulPS (p ^ v) i) x.1 = 0 := by
  rw [mem_torsionBy]
  constructor
  · intro h i; rw [ev_mulPS, h, zero_val]
  · intro h; exact F.pt_ext fun i => by rw [← ev_mulPS, h i, zero_val]

/-- **Every torsion point of `F(m_{ℂ_p})` is killed by a power of `p`.** -/
theorem isOfFinAddOrder_iff (x : F.Pt p) : IsOfFinAddOrder x ↔ ∃ v, x ∈ F.torsionBy v := by
  constructor
  · intro h
    obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
    obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p
      (Fact.out : p.Prime).ne_one
    refine ⟨v, F.eq_zero_of_nsmul_eq_zero ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm) ?_⟩
    rw [← mul_nsmul]
    exact hnx
  · rintro ⟨v, hv⟩
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p ^ v, pow_pos (Fact.out : p.Prime).pos _, hv⟩

/-- **`ker log_F = ⋃_v F(m_{ℂ_p})[p^v]`.** -/
theorem logF_eq_zero_iff_mem_torsionBy (x : F.Pt p) :
    (∀ i, F.logF x i = 0) ↔ ∃ v, x ∈ F.torsionBy v := by
  rw [logF_eq_zero_iff, isOfFinAddOrder_iff]

end FGL

end PadicHodge
