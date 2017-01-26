# Proof refactoring

## Adding bullets

Bullets help structure the proof script but some intelligence is useful to choose between classic bullets `-` `+` `*`
(which put all sub-goals on the same level) or brackets `{` `}` which encapsulate the proof of intermediate results.

The most obvious way to decide would be to depend on the tactic used to create such goals:

- `induction`, `destruct`, `elim`, `apply` generate sub-goals which are of equal value and should be on the same level (for `apply` it is not necessarily true, it is often used as a backward-chaining mechanism);

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
But `now_show` is simpler and probably better in such cases.

#### Example

    Theorem Nat_divides_l : ∀ a b, (∃ c, a = (b * c)%nat) ↔ (b | a)%nat.
    Proof.
      now_show (∀ a b, (∃ c, a = (b * c)%nat) ↔ (∃ c, a = (c * b)%nat)).

## Simple automation

Use of simple automation such as `auto with arith` might be helpful to clarify which steps are easy and which are more important.
It also makes the proof shorter without removing any of the real content.

Some different considerations may apply when the proof is designed to be shown to students.

Use of `autorewrite` can be also quite useful for easy steps.
However the tactic is very inefficient as soon as the database gets big.
Maybe the database to use in a proof should be defined on the spot.

## Expliciting an existential statement to be destructurated

Instead of using `destruct`, we can use `assert` to remind the hypothesis with an `as` clause to destruct it immediately.

    assert (∃ k₁, m = k₁ * (k' * g)) as (k₁, ?) by assumption.

This will be translated in English into:

> Take k₁ such that m = k₁ · (k' · g).

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

I still have one example where an explicit call to `symmetry` is necessary:

    replace (l' * g / g) with l' by (symmetry; auto using Nat.div_mul).

So does `auto` try `symmetry` or not?

The same technique with `replace` can be used for important reduction or unfolding steps:

    replace (Nat.lcm (k' * g) (l' * g)) with (k' * g * (l' * g / Nat.gcd (k' * g) (l' * g))) by reflexivity.

### When `replace` needs quite some justification

Then this is not the right tactic because the justification is postponed.
Instead we can introduce the rewriting lemma with an `assert` and use it immediately with `as ->`.

Note that this is an example of inconsistency in the semantics of the `by` keyword.

Another limitation of `replace` is that it does not fail when there is nothing to replace.
It can be corrected with the use of the tactical `progress`.

## Similar sub-goals

In case several sub-goals are solved in a very similar way, it might read better to factorize the proofs,
provided that it still allows to see what is going on.
Using `all:` instead of `;` can help distinguish a few logical steps.
Using `replace` and such can help make these steps sufficiently explicit.

### Similar intermediate steps

When it can be identified that intermediate steps (introduced with `assert`) share a similar proof,
they can be grouped together with a conjunction only to be introduced again as distinct assumptions.
Then the proof can be factorized.

#### Example

    assert (g ≠ 0 ∧ l' ≠ 0) % nat as []. {
      split; intro.
      all: absurd ((l' * g) = 0) % nat; [ assumption |].
      - now subst g.
      - now subst l'.
    }

## Putting the proof back in order (deductive style)

### Prefer `absurd` to `exfalso`

Use of `exfalso` is generally followed by the application of a lemma ending with a negation.
This is hard to follow.
Instead, we can make explicit what is the contradiction we're going to get with `absurd`.
Ideally the reason why it is absurd is not hard to get (with automation).

### Negations can be proved by contradiction

It suffices to start the proof with `intro`.
To make it more explicit, it would be enough to be able to repeat what is the hypothesis introduced.

### Group by reasoning block

A series of manipulation of an hypothesis can be singled out in an intermediate step.
Then the sub-proof can be refactored independently.

### Expliciting the reasonning behind `apply`

When it makes sense to use keep a justificative style (proof by `apply`) for some steps,
we can make these steps more explicit with the use of `enough`

#### Example

Replace:

    apply Nat.gauss with (m := l'); trivial.

with:

    enough (k' | l' * l₁) by (eapply Nat.gauss; eauto).

### Deductive style

It is a series of `assert` replacing a series of `apply`. The order is reversed.
The `assert` explicit what is the intermediate step to prove and the use of `by now apply` allows to replace one line with just one line.

It gets more complicated to replace `eapply` or if we don't want to provide explicit arguments to our theorem:
`eauto using` does not seem to work; `eapply; eassumption` can fail depending on the order of generated subgoals.

