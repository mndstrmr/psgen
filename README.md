# PSGen
PSGen is a theorem proving type language which generates SystemVerilog and TCL. It dramatically simplifies case splitting, inductive proofs and similar strategies often found in formal verification.

## `have`
Directly produces a SystemVerilog assertion of the same content, potentially with additional preconditions based on scope conditions (see `cond` and `on`).
```
lemma have_example
  have (p)
```
Produces simply an assertion for `p`.

`have`, among with many commands, can be labeled to produce more readable outputs:
```
lemma have_labelled_example
  Hello: have(p)
```
Produces an assertion for `p` who's name starts with `Hello_`.

## `cond`
Conditions allow for a precondition to be attached to every statement in the block.
```
lemma cond_example
  cond (p)
  cond (r)
  have (q)
```
Will produce an assertion that `p & r |-> q`.

## `on`
Is a local version of cond which starts a new scope.
```
lemma on_example
  on (p)
    have (q)
```
Will produce an assertion that `p |-> q`.

```
lemma on_example_with_states
  state example_state (p)

  on example_state
    have (q)
```
Will also produce an assertion that `p |-> q`.

Note that most places where SystemVerilog expressions are expected (e.g. `have` and `graph_induction` nodes) can also take state names, `on` is not special in this way.

`on` can have multiple conditions:
```
lemma on_multiple
  on (p) (q)
    have (r)
```
Will produce two assertions: `p |-> r` and `q |-> r`.

## `block`
Blocks simply introduce fresh scopes, they are equivalent to `on (1)`
```
lemma block_example
  block
    cond (p)
    have (q)
  have (r)
```
Will produce two assertions: `p |-> q` and `r`.

## Lemmas
One lemma can be imported into another via the `lemma` command. Lemmas cannot be helped and do not inherit any conditions or any other scope.
```
lemma abc
  have (p)

lemma lemmas_example
  cond (q)
  lemma abc
  /
  have (r)
```
Will produce two assertions: `p` and  `q |-> r` sequenced in that order.

Lemmas are intended to be imported once, they are intended to neaten code.

## Defs
Defs are similar to lemmas but do inherit scope and can have helpers, they are intended to reduce size.
```
def abc
  have (p)

lemma defs_example
  cond (q)
  use abc
    split_bool (r)
```
Produces two assertions: `q & r |-> p` and `q & ~r |-> p`.

## Proof Sequencing
Proof sequencing is a way to 'order' proofs, so that useful properties are proved 'first' so that they can be used to help later properties. We use assume-guarantee reasoning, i.e.  if `p` comes before `q` then `p` and `p -> q` (or more specifically `p` is assumed for `q`) can be proved independently of one another. PSGen orders proofs based on seperations with `/`:
```
lemma sequencing_example
  have (p)
  have (q)
  /
  have (r)
```
Will generate a property for each of `p`, `q`, `r`, and will configure the TCL with assume-guarantee type reasoning, where `r` will be proved using the assumptions of `p` and `q`, which will themselves each be individually verified, though neither will assume the other.

## Case Splitting
`split` is a proof helper which case splits the given property into the cases given. `split` sequences the case proofs before the proof that is being helped. Any number of cases may be given. For example:
```
lemma case_splitting_example
  have (p)
    split (q) (r)
```
Will generate three properties (`q |-> p`, `r |-> p`, `p`) where `q |-> p` and `r |-> p` are sequenced before `p`.

Individual cases of a case split can also be written out of line and have additional proof helpers attached to them.
```
lemma case_splitting_example
  have (p)
    split (q)
      case (r)
        split (a) (b)
```
Will generate the following properties `p & q`, `p & r & a`, `p & r & b`, which sequenced before `p & r` which is sequenced before `p`.

Case booleans can be case split directly with `split_bool`. `split_bool` can take any number of arguments.
```
lemma bool_case_splitting_example
  have (p)
    split_bool (q) (r)
```
Will generate four properties: `p & q & r`, `p & q & ~r`, `p & ~q & r`, `p & ~q & ~r`. Hence this is equivalent to
```
lemma bool_case_splitting_as_split_example
  have (p)
    split
      case (q)
        split (r) (~r)
      case (~q)
        split (r) (~r)
```

## Graph Induction
Sometimes we want to prove that an automaton maintains an invariant through every step of its execution. We can do this by induction, where we consider every edge of a graph and verify the invariant specified is maintained. Regular induction is a special case of graph induction with one node which loops forever.

What follows is an example to help verify that the BTYPE instructions in Ibex set the correct PC, since this is difficult for k-induction to do alone.
```
Induction:
graph_induction +rev
  cond (`CR.instr_valid_id & idex_iss_btype & ~ex_err & ~ex_kill)
  inv nobranch (~ex_has_branched_d)
  inv eq (ex_has_branched_d == `CR.branch_decision)

  entry (`CR.instr_new_id) -> stall oma progress

  node stall nobranch (`ID.stall_ld_hz) => stall progress
  node oma eq (`IDG.outstanding_memory_access) => oma progress
    split_bool (`CR.branch_decision)
  node progress eq (instr_will_progress)
```
- `graph_induction` starts a nested scope and `cond` can be used in the same way it is otherwise
- `inv <name> <condition>` specifies an invariant in the graph. There may be several invariants, each node will have one invariant (FIXME: several?)
- `entry <condition> -> <nodes>` optionally specifies a set of entry points of the graph, with the given entry condition. When present checks are added to ensure that when the entry condition is satisfied one of the entry nodes are selected and that nodes invariant is true.
- `node <name> <invariant> <condition> => <nodes>` defines a node with the given name, for which the given invariant must be true. The node is recognised by the condition being true. The nodes given are the set of allowable next states in the next cycle. Note that nodes can have proof helpers (e.g. `split` or `split_bool`). These helpers are applied to assertion 4 in the below.
- `+rev` indicates that we should also that the only reach to reach any node is to walk through the graph

Assertions are emit to check that:
1. If an entry is given, when the entry condition is true the condition of one of the entry nodes is true.
2. If an entry is given, when the entry condition is true the invariant is true for any entry node who's condition is true.
3. For each node, if the node's condition is true in this cycle then one of the given next nodes's condition's must be true in the next cycle. Note that if there are no next nodes this is vacuously true (and is not checked).
4. For each transition from `a` to `b`, if the condition for a is true this cycle, and the invariant for `a` is true this cycle, then if we transition to `b` in the next cycle, the invariant for `b` will be true next cycle.
5. If `+rev` is given, for each node, if the node's condition is true then either the node is an entry node and entry condition is met, or one of the nodes which transitions to this node had it's condition true in the last cycle.

Now (assuming an entry was given and `+rev`) we can derive that if the condition for some node is satisfied, then it's invariant is satisfied also:
1. At some point in the past the entry condition was met, and the graph has not been left since, by induction using 5.
2. Every state in the graph reachable from the entry condition satisfies the invariant of that state, by induction using 1-4.

## K-Induction Debug
When attempting to determine why a property cannot be proved with k-induction it is useful to have a trace to explain why a given k does not suffice. We can obtain such a property using `k_induction`:
```
lemma k_induction_example
  have (p)
    k_induction 3
```
Will produce 4 properties sequenced together. Those properties are `$past(p) |-> p`, `$past(p, 2) & $past(p, 1) |-> p`, `$past(p, 3) & $past(p, 2) & $past(p, 1) |-> p`.
