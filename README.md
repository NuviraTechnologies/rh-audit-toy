# The Toy: four decorative patterns from the Alpöge RH audit, in miniature

Two small Lean 4 files (plain Lean core, no Mathlib) that model the four
decorative patterns documented in the audit paper:

*Vigslist, R. "An Audit of the Claimed Lean Proof of the Riemann Hypothesis:
Eight Findings, with Addresses." Zenodo, 2026.
https://doi.org/10.5281/zenodo.24489395*

The toy does not reproduce the release. It models the patterns. The paper is
what traces the patterns inside the actual release, at file and line.

## Toy.lean — the patterns ride along, and a true theorem still proves

Patterns modelled:

- **(a)** `DeepArithmeticGeometry` — an impressively named predicate defined
  as `True` (compare `anyGeometry`, OverIx.lean:19 in the release), carried
  through the framework by a generic lemma that never looks inside it.
- **(b)** `LengthRecord.len_eq` — a field tying a stored length to the genuine
  value (compare the `sha_eq` field of `NData`, DataN.lean:66). The
  construction `adaptRecord` simply assigns the genuine value, so the equality
  is closed by `rfl`. Set equal, then proved equal. No computation happens.
- **(c)** `record_nonempty` — an example record discharging a nonemptiness
  requirement (compare the example package on the release's dependency path).
- **(d)** `RiemannStyleCertificate` — a grand name whose only field is
  `1 + 1 = 2` (compare `OpenImageCondition`, whose only field is another
  package).

The one honest lemma, `sumOdd_eq`, proves by induction that the sum of the
first n odd numbers is n². The framework theorem consumes every decorative
input plus the honest lemma. The decorative inputs contribute nothing.

Verified run (Lean 4.36.0):

```
$ lean Toy.lean
'GrandOddSquareTheorem' depends on axioms: [propext, Quot.sound]
25
```

- Exit code 0. No errors, no `sorry`.
- `#print axioms` shows only standard axioms — no `sorryAx`, nothing added.
- `#eval sumOdd 5` prints `25` (1+3+5+7+9).

## False.lean — the same machinery cannot prove anything false

The identical decorative pieces aimed at false statements. The file is
supposed to fail. Verified run:

```
$ lean False.lean
False.lean:23:2: error: Type mismatch ... DeepArithmeticGeometry 0
  but is expected to have type 2 + 2 = 5
False.lean:30:12: error: Type mismatch ... rfl ... 5 = trueLen 2
False.lean:35:11: error: Type mismatch ... 1 + 1 = 2
  but is expected to have type IsPrimeToy x
False.lean:38:38: error: Tactic `decide` proved that the proposition
  sumOdd 3 = 10 is false
```

Exit code 1, four errors, one per attempt:

1. The `True` predicate cannot produce `2 + 2 = 5`.
2. `rfl` refuses a record whose stored length is set to the wrong value.
3. The grand certificate cannot prove every number is prime.
4. `decide` reports the false sum is false.

## What this shows

Both directions at once:

- The decorative patterns cannot manufacture a false proof. The kernel is
  doing its job, and the audit has never claimed otherwise.
- The same patterns add nothing to a true proof either. They are packaging:
  names and structures that describe work which is not done at those points.

Whether a claimed proof *is* the argument its names describe is a question
about the content at specific addresses — which is what the paper checks,
finding by finding, with a stated refutation condition for each.

## Run it yourself

Install Lean 4 via elan (https://elan.lean-lang.org), then:

```
lean Toy.lean    # succeeds; prints the axiom list and 25
lean False.lean  # fails with the four errors above
```
