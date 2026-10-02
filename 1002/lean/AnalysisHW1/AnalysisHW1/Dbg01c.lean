import Mathlib

namespace Dbg01c

def R (a b : ℤ) : Prop := a ^ 2 = b ^ 2

theorem dbg_equiv : Equivalence R :=
  ⟨fun _ => rfl, fun h => h.symm, fun hab hbc => hab.trans hbc⟩

theorem sq_eq_sq_iff (a b : ℤ) : a ^ 2 = b ^ 2 ↔ (a = b ∨ a = -b) := by
  have hfac : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [← sub_eq_zero, hfac, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  tauto

theorem dbg_class (a : ℤ) : {b | R a b} = ({a, -a} : Set ℤ) := by
  ext b
  simp only [R, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [sq_eq_sq_iff b a]
  constructor <;> intro h
  · rcases h with h | h <;> tauto
  · rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h]; ring)

theorem dbg_add_wd : ∀ a b c d : ℤ, R a b → R c d → R (a + c) (b + d) := by
  intro a b c d hab hcd
  rw [R] at hab hcd ⊢
  obtain h | h := (sq_eq_sq_iff a b).mp hab
  · obtain h' | h' := (sq_eq_sq_iff c d).mp hcd
    · rw [h, h']
    · rw [h, h']; ring
  · obtain h' | h' := (sq_eq_sq_iff c d).mp hcd
    · rw [h, h']; ring
    · rw [h, h']; ring

theorem dbg_mul_not_wd : ¬ (∀ a b c d : ℤ, R a b → R c d → R (a * c) (b * d)) := by
  intro h
  have h5 : R (5 * 5) (5 * (-5)) :=
    h 5 5 5 (-5) (by norm_num [R]) (by norm_num [R])
  rw [R] at h5
  norm_num at h5

end Dbg01c
