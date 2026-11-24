/-
  False.lean: the same decorative machinery as Toy.lean, now aimed at FALSE statements.
  Every attempt below is rejected. Empty pieces carry no information, so they cannot
  produce a false conclusion. (Definitions are copied so the file is self-contained.)
-/
def sumOdd : Nat → Nat
  | 0     => 0
  | n + 1 => sumOdd n + (2 * n + 1)
def trueLen (n : Nat) : Nat := n * n
def DeepArithmeticGeometry (_n : Nat) : Prop := True
theorem carry_geometry (G : Nat → Prop) (hG : ∀ n, G n)
    (P : Nat → Prop) (hP : ∀ n, P n) : ∀ n, G n ∧ P n := fun n => ⟨hG n, hP n⟩
structure LengthRecord (n : Nat) where
  len    : Nat
  len_eq : len = trueLen n
structure RiemannStyleCertificate : Prop where
  content : 1 + 1 = 2
theorem certificate_holds : RiemannStyleCertificate := ⟨rfl⟩

-- Attempt 1: 2 + 2 = 5, from the `True` geometry predicate.
-- The predicate only ever gives back `True`, which is not `2 + 2 = 5`.
theorem bad_two_plus_two : 2 + 2 = 5 :=
  (carry_geometry DeepArithmeticGeometry (fun _ => trivial)
    (fun _ => True) (fun _ => trivial) 0).1

-- Attempt 2: a record whose "computed" length is wrong (5 instead of 2*2 = 4).
-- `rfl` only works when the two sides really are the same value.
def bad_record : LengthRecord 2 where
  len    := 5
  len_eq := rfl

-- Attempt 3: "every number is prime" (toy definition), from the grand certificate.
def IsPrimeToy (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d ∣ n → d = 1 ∨ d = n
theorem bad_all_prime : ∀ n, IsPrimeToy n :=
  fun _ => certificate_holds.content

-- Attempt 4: a false value for the honest quantity (the true sum is 9, not 10).
theorem bad_sum : sumOdd 3 = 10 := by decide
