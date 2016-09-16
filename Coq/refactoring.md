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
