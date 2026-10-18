/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Anthropic)
-/
import PadicHodge.FormalGroup.Invariants

/-!
# The Tate module of a formal group law

For a formal group law `F` (setting of `FormalGroup/Points.lean`):

* `tate F = T_p F = lim_v F(m_{ℂ_p})[p^v]`, the compatible sequences `(x_v)` with `x_0 = 0` and
  `p · x_{v+1} = x_v`, as a subgroup of `ℕ → F(m_{ℂ_p})`; its terms are `p^v`-torsion
  (`tate_mem_torsionBy`) and have vanishing logarithm (`logF_tate`);
* `galPt_mem_tate`: `T_p F` is stable under `Gal(ℚ̄_p/ℚ_p)` (Galois-fixed coefficients);
* `exists_tate_of_divisible`: if `F(m_{ℂ_p})` is `p`-divisible, every `x ∈ F(m_{ℂ_p})[p^v]` is the
  `v`-th term of an element of `T_p F` (the transition maps `T_p F → F[p^v]` are surjective);
* for `Ĝ_m`: `gm_tate_iff` — the elements of `T_p Ĝ_m` are the sequences `1 + x_v` of
  compatible `p^v`-th roots of unity.
-/

noncomputable section

open MvPowerSeries Topology Filter

namespace PadicHodge

namespace FGL

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [DiscreteUniformity R] [Algebra R (OC p)] {d : ℕ} (F : FGL R d)

variable (p) in
/-- **The Tate module `T_p F = lim_v F(m_{ℂ_p})[p^v]`.** -/
def tate : AddSubgroup (ℕ → F.Pt p) where
  carrier := {x | x 0 = 0 ∧ ∀ v, p • x (v + 1) = x v}
  zero_mem' := ⟨rfl, fun v => nsmul_zero _⟩
  add_mem' := fun {x y} hx hy => ⟨by simp [hx.1, hy.1], fun v => by
    simp only [Pi.add_apply, nsmul_add, hx.2 v, hy.2 v]⟩
  neg_mem' := fun {x} hx => ⟨by simp [hx.1], fun v => by
    simp only [Pi.neg_apply, smul_neg, hx.2 v]⟩

theorem mem_tate {x : ℕ → F.Pt p} : x ∈ F.tate p ↔ x 0 = 0 ∧ ∀ v, p • x (v + 1) = x v :=
  Iff.rfl

theorem tate_mem_torsionBy {x : ℕ → F.Pt p} (hx : x ∈ F.tate p) (v : ℕ) :
    x v ∈ F.torsionBy v := by
  rw [mem_torsionBy]
  induction v with
  | zero => rw [pow_zero, one_nsmul]; exact hx.1
  | succ v ih => rw [pow_succ', mul_nsmul, hx.2 v, ih]

theorem logF_tate {x : ℕ → F.Pt p} (hx : x ∈ F.tate p) (v : ℕ) (i : Fin d) :
    F.logF (x v) i = 0 :=
  ((F.logF_eq_zero_iff_mem_torsionBy (x v)).mpr ⟨v, F.tate_mem_torsionBy hx v⟩) i

theorem galPt_mem_tate (hR : GalFixed p R) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    {x : ℕ → F.Pt p} (hx : x ∈ F.tate p) : (fun v => galPt σ (x v)) ∈ F.tate p := by
  refine ⟨?_, fun v => ?_⟩
  · change galPt σ (x 0) = 0
    rw [hx.1]
    refine F.pt_ext fun j => Subtype.ext ?_
    rw [galPt_val, zero_val, ZeroMemClass.coe_zero, map_zero]
  · rw [← galPt_nsmul hR, hx.2 v]

/-- **If `F(m_{ℂ_p})` is `p`-divisible, `T_p F → F(m_{ℂ_p})[p^v]` is surjective.** -/
theorem exists_tate_of_divisible (h : ∀ x : F.Pt p, ∃ y, p • y = x) {v : ℕ} {x : F.Pt p}
    (hx : x ∈ F.torsionBy v) : ∃ t ∈ F.tate p, t v = x := by
  classical
  -- choose `p`-th roots upwards and multiply downwards
  let up : ℕ → F.Pt p := fun n => Nat.rec x (fun _ y => (h y).choose) n
  have hup : ∀ n, p • up (n + 1) = up n := fun n => (h (up n)).choose_spec
  let t : ℕ → F.Pt p := fun w => if w ≤ v then (p ^ (v - w)) • x else up (w - v)
  have hup0 : up 0 = x := rfl
  refine ⟨t, ⟨?_, fun w => ?_⟩, ?_⟩
  · simp only [t, Nat.zero_le, if_true, Nat.sub_zero]
    exact (F.mem_torsionBy).mp hx
  · by_cases hw : w + 1 ≤ v
    · simp only [t, if_pos hw, if_pos (Nat.le_of_succ_le hw)]
      rw [← mul_nsmul', ← pow_succ']
      congr 2
      omega
    · by_cases hw' : w ≤ v
      · have hwv : w = v := by omega
        subst hwv
        simp only [t, if_neg hw, if_pos le_rfl, Nat.sub_self, pow_zero, one_nsmul,
          Nat.add_sub_cancel_left]
        exact hup 0
      · simp only [t, if_neg hw, if_neg hw']
        rw [show w + 1 - v = (w - v) + 1 by omega, hup]
  · simp only [t, le_rfl, if_true, Nat.sub_self, pow_zero, one_nsmul]

/-- **`T_p Ĝ_m`**: compatible systems of `p`-power roots of unity. -/
theorem gm_tate_iff (x : ℕ → (multiplicative R).Pt p) :
    x ∈ (multiplicative R).tate p ↔
      (1 + (((x 0).1 0 : OC p) : ℂ_[p])) = 1 ∧
      ∀ v, (1 + (((x (v + 1)).1 0 : OC p) : ℂ_[p])) ^ p = 1 + (((x v).1 0 : OC p) : ℂ_[p]) := by
  have key : ∀ y z : (multiplicative R).Pt p, p • y = z ↔
      (1 + ((y.1 0 : OC p) : ℂ_[p])) ^ p = 1 + ((z.1 0 : OC p) : ℂ_[p]) := fun y z => by
    constructor
    · rintro rfl; rw [gm_nsmul_val]; ring
    · intro h
      refine (multiplicative R).pt_ext fun j => Subtype.ext ?_
      rw [Subsingleton.elim j 0, gm_nsmul_val, h]
      ring
  have key0 : ∀ y : (multiplicative R).Pt p, y = 0 ↔ 1 + ((y.1 0 : OC p) : ℂ_[p]) = 1 :=
    fun y => by
      constructor
      · rintro rfl; rw [zero_val, ZeroMemClass.coe_zero, add_zero]
      · intro h
        refine (multiplicative R).pt_ext fun j => Subtype.ext ?_
        rw [Subsingleton.elim j 0, zero_val, ZeroMemClass.coe_zero]
        linear_combination h
  rw [mem_tate, key0]
  simp only [key]

end FGL

end PadicHodge
