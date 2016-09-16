# Proof refactoring

## Adding bullets

Bullets help structure the proof script but some intelligence is useful to choose between classic bullets `-` `+` `*`
(which put all sub-goals on the same level) or brackets `{` `}` which encapsulate the proof of intermediate results.

The most obvious way to decide would be to depend on the tactic used to create such goals:

- `induction`, `destruct`, `elim`, `apply` generate sub-goals which are of equal value and should be on the same level;

- `enough`, `assert`, `absurd` generate one intermediate goal, and one main goal (with the first two the main goal is unchanged);

- `rewrite`, `apply in` and `rewrite in` may generate several intermediate goals corresponding to the additional conditions to satisfy but unfortunately these conditions are put *after* the main goal (thus preventing proving them between brackets).
One solution is to add some `assert` to tackle the conditions before-hand.
Then this new hypothesis can be used explicitely, or through `; trivial` or `; [| assumption]`.

## Initial changes to the goal to prove

Many times, a lemma statement is written in a form that is easy to use but harder to prove,
or the lemma needs to be generalized before being proved by induction.
Then the proof may start by a series of changes to the goal to prove with `intros` `rewrite` `revert` or other tactics.

If not already the case, such beginning must be refactored to use `enough` so as to make obvious what will be the real goal to prove.

### Unfolding definitions in the lemma statement

Using `enough` could also be useful for clarification when the lemma statement contains a definition that is (possibly silently) unfolded.
But `now_show` is more than enough in such cases.

#### Example

    Theorem Nat_divides_l : ∀ a b, (∃ c, a = (b * c)%nat) ↔ (b | a)%nat.
    Proof.
      now_show (∀ a b, (∃ c, a = (b * c)%nat) ↔ (∃ c, a = (c * b)%nat)).

## Simple automation

Use of simple automation such as `auto with arith` might be helpful to clarify which steps are easy and which are more important.
It also makes the proof shorter without removing any of the real content.

Some different considerations may apply when the proof is designed to be shown to students.

## Sequence of `rewrite`

It is clear that chaining calls to `rewrite` is not the clearest way to show what's going on to the reader.
Using a sequence of `assert` or `enough` would be too heavy and not robust to minor changes.

Instead, a sequence of `rewrite` can be refactored to use `replace`, thus making the part that is transformed very explicit,
without having to write anything else.

#### Example

    Theorem Nat_sub_sub_comm : ∀ m n p, (m - n - p)%nat = (m - p - n)%nat.
    Proof.
      intros.
      replace (m - n - p)   % nat with (m - (n + p)) % nat by auto using Nat.sub_add_distr.
      replace (n + p)       % nat with (p + n)       % nat by auto using Nat.add_comm.
      replace (m - (p + n)) % nat with (m - p - n)   % nat by auto using Nat.sub_add_distr.
      reflexivity.
    Qed.

Here, the lemma allowing the rewrite step is mentionned after `by auto using`.
`auto using` instead of `apply` avoids having to explicitely call `symmetry`.

The same technique with `replace` could be used for important reduction or unfolding steps (TODO: check this).

## Similar sub-goals

In case several sub-goals are solved in a very similar way, it might read better to factorize the proofs,
provided that it still allows to see what is going on.
Using `all:` instead of `;` can help distinguish a few logical steps.
Using `replace` and such can help make these steps sufficiently explicit.
