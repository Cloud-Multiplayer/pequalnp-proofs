import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3771

def D : Finset (Fin 13) := {0, 1, 3, 9}

def A (y : Fin 13) : Finset (Fin 13) := Finset.univ.filter (fun x => x + y ∈ D)

theorem card_A : ∀ y : Fin 13, (A y).card = 4 := by decide

theorem inter_A : ∀ a y : Fin 13, a ≠ y → (A a ∩ A y).card ≤ 1 := by decide

theorem grow (Y : Finset (Fin 13)) :
    9 * Y.card ≤ 2 * (Y.biUnion A).card + Y.card * Y.card := by
  induction Y using Finset.induction_on with
  | empty => simp
  | insert a Y ha ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem ha]
    have hu := Finset.card_union_add_card_inter (A a) (Y.biUnion A)
    have hi : (A a ∩ Y.biUnion A).card ≤ Y.card := by
      rw [Finset.inter_biUnion]
      calc (Y.biUnion fun y => A a ∩ A y).card ≤ ∑ y ∈ Y, (A a ∩ A y).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _y ∈ Y, 1 :=
            Finset.sum_le_sum (fun y hy => inter_A a y (fun h => ha (h ▸ hy)))
        _ = Y.card := by simp
    have h4 := card_A a
    nlinarith [ih, hu, hi, h4]

end PEqualNP.Outside.L_meta_3771

theorem PEqualNP.Outside.L_meta_3771 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  intro x1 x2 x3 h
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨Y, hY, hYc⟩ := Finset.exists_subset_card_eq (show 4 ≤ x3.card by omega)
  have hg := PEqualNP.Outside.L_meta_3771.grow Y
  rw [hYc] at hg
  have hsub : x2 ⊆ Finset.univ \ Y.biUnion PEqualNP.Outside.L_meta_3771.A := by
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hU
    obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.1 hU
    exact h x hx y (hY hy) (Finset.mem_filter.1 hxy).2
  have hle := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin] at hle
  omega
