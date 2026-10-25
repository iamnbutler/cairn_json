import CairnJson.Core

/-! # Fuel

`decode` is total by construction: `value`, `members` and `elements` are structural recursion on
a fuel argument, and nothing in `CairnJson` is a `partial def` (`make lint`). These theorems say
the fuel can only cut a parse short, never change it: an answer found with some fuel is the
answer with any more. The round-trip theorems (`CairnJsonProofs.RoundTrip`) show the fuel
`decode` gives, the input's length plus one, is enough for every encoded value. -/

namespace CairnJson

mutual
theorem value_mono (limit : Nat) : (f d : Nat) → (cs : List Char) → (r : Json × List Char) →
    value limit f d cs = some r → value limit (f + 1) d cs = some r
  | 0, _, _, _, h => by simp [value] at h
  | f + 1, d, cs, r, h => by
    simp only [value] at h ⊢
    revert h
    split
    · split
      · intro h; exact members_mono limit f _ _ _ _ _ h
      · simp
    · split
      · intro h; exact elements_mono limit f _ _ _ _ _ h
      · simp
    all_goals exact id

theorem members_mono (limit : Nat) : (f d : Nat) → (acc : List (String × Json)) → (cs : List Char) →
    (first : Bool) → (r : Json × List Char) →
    members limit f d acc cs first = some r → members limit (f + 1) d acc cs first = some r
  | 0, _, _, _, _, _, h => by simp [members] at h
  | f + 1, d, acc, cs, first, r, h => by
    simp only [members] at h ⊢
    revert h
    split
    · exact id
    · split
      · exact id
      · split
        · cases hv : value limit f d _ with
          | none => simp
          | some p =>
            rw [value_mono limit f d _ p hv]
            simp only
            split
            · intro h; exact members_mono limit f _ _ _ _ _ h
            · exact id
            · exact id
        · exact id
    · exact id

theorem elements_mono (limit : Nat) : (f d : Nat) → (acc : List Json) → (cs : List Char) →
    (first : Bool) → (r : Json × List Char) →
    elements limit f d acc cs first = some r → elements limit (f + 1) d acc cs first = some r
  | 0, _, _, _, _, _, h => by simp [elements] at h
  | f + 1, d, acc, cs, first, r, h => by
    simp only [elements] at h ⊢
    revert h
    split
    · exact id
    · cases hv : value limit f d cs with
      | none => simp
      | some p =>
        rw [value_mono limit f d cs p hv]
        simp only
        split
        · intro h; exact elements_mono limit f _ _ _ _ _ h
        · exact id
        · exact id
end

/-- More fuel never changes an answer. -/
theorem value_mono_le (limit : Nat) {f g : Nat} (d : Nat) (cs : List Char) (r : Json × List Char)
    (hfg : f ≤ g) (h : value limit f d cs = some r) : value limit g d cs = some r := by
  obtain ⟨k, rfl⟩ : ∃ k, g = f + k := ⟨g - f, by omega⟩
  induction k with
  | zero => exact h
  | succ k ih => exact value_mono limit (f + k) d cs r (ih (by omega))

/-- A document `decodeChars` accepts is accepted, as the same value, with any more fuel. -/
theorem decodeChars_fuel (limit : Nat) (cs : List Char) (v : Json) (k : Nat)
    (h : decodeChars limit cs = some v) :
    ∃ rest, value limit (cs.length + 1 + k) 0 cs = some (v, rest) ∧ skipWs rest = [] := by
  unfold decodeChars at h
  split at h
  · rename_i v' rest hv
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨rest, value_mono_le limit 0 cs _ (by omega) hv, by assumption⟩
    · simp at h
  · simp at h

end CairnJson
