# Proof refactoring

## Adding bullets

Bullets help structure the proof script but some intelligence is useful to choose between classic bullets `-` `+` `*`
(which put all sub-goals on the same level) or brackets `{` `}` which encapsulate the proof of intermediate results.

The most obvious way to decide would be to depend on the tactic used to create such goals:

- `induction`, `destruct`, `elim`, `apply` generate sub-goals which are of equal value and should be on the same level;

- `enough`, `assert`, `absurd` generate one intermediate goal, and one main goal (with the first two the main goal is unchanged);

- `rewrite` may generate several intermediate goals, and one main goal which is last (TODO: check that).

## Initial changes to the goal to prove

Many times, a lemma statement is written in a form that is easy to use but harder to prove,
or the lemma needs to be generalized before being proved by induction.
Then the proof may start by a series of changes to the goal to prove with `intros` `rewrite` `revert` or other tactics.

If not already the case, such beginning must be refactored to use `enough` so as to make obvious what will be the real goal to prove.

Using `enough` might also be useful for clarification when the lemma statement contains a definition that is silently unfolded.

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


