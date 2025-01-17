
import Mathlib.Tactic


#check Rat.instEncodable
#check Rat.instDenumerable


example : Encodable ℚ := by
  exact Rat.instEncodable

example : Denumerable ℚ := by
  exact Rat.instDenumerable


/-
REMINDERS

class Encodable (α : Type*) where
  encode : α → ℕ
  decode : ℕ → Option α
  encodek : ∀ a, decode (encode a) = some a


class Denumerable (α : Type*) extends Encodable α where
  decode_inv : ∀ n, ∃ a ∈ decode n, encode a = n
-/


lemma EncodableRat : ∃ f : ℚ → ℕ, ∃ g : ℕ → Option ℚ, ∀ q : ℚ, g (f q) = q := by

  have h : Encodable ℚ
  exact Rat.instEncodable

  use h.encode
  use h.decode
  exact h.encodek

lemma DenumerableRat : ∃ f : ℚ → ℕ, ∃ g : ℕ → Option ℚ, ((∀ q : ℚ, g (f q) = q)
    ∧ (∀ n : ℕ, ∃ q, f q = n)) := by

  have h : Denumerable ℚ
  exact Rat.instDenumerable

  use h.encode
  use h.decode
  constructor
  · exact h.encodek
  · intro n
    let h' := h.decode_inv
    specialize h' n
    cases' h' with q hq
    use q
    exact hq.right

def encodeRat : ℚ → ℕ := (Rat.instDenumerable).encode
def decodeRat : ℕ → Option ℚ := (Rat.instDenumerable).decode

lemma EncodableRat' : ∀ a : ℚ, decodeRat (encodeRat a) = a := by
  have h := (Rat.instDenumerable).encodek
  rw [decodeRat]
  rw [encodeRat]
  exact fun a ↦ h a

def encodeRatProp := EncodableRat'

lemma DenumerableRat' : ∀ n : ℕ, ∃ q : ℚ, encodeRat q = n := by
  intro n
  let h := (Rat.instDenumerable).decode_inv
  rcases h n with ⟨q, hq⟩
  use q
  rw [encodeRat]
  exact hq.right

def decodeRatProp := DenumerableRat'

lemma some_eq_imp_eq {p q : ℚ} (h : some p = some q) : p = q := by
  rw [← Option.mem_some_iff]
  rw [h]
  rfl

lemma injective_encodeRat : Function.Injective encodeRat := by
  intro p q h

  have h' : ∀ a b : ℕ, a = b → decodeRat a = decodeRat b
  exact fun a b a_1 ↦ congrArg decodeRat a_1

  apply h' at h

  rw [encodeRatProp] at h
  rw [encodeRatProp] at h

  exact some_eq_imp_eq h


lemma injective_decodeRat : Function.Injective decodeRat := by
  intro n m h

  rcases decodeRatProp n with ⟨q, hq⟩
  rcases decodeRatProp m with ⟨p, hp⟩

  rw [← hq, ← hp] at h

  rw [encodeRatProp] at h
  rw [encodeRatProp] at h

  apply some_eq_imp_eq at h
  rw [← hq, ← hp]
  rw [h]
