import Veil

veil module ReliableBroadcast

/-
  Reliable Broadcast is a Byzantine fault-tolerant broadcast protocol
  that ensures that all honest nodes deliver the same message, as long
  as the `originator` (the node that initiated the broadcast) is honest.

  It proceeds in three phases:
    - an initial phase, where the originator broadcasts `initial_msg`
    - an echo phase, where nodes broadcast an `echo` of the value they
      received
    - a vote phase, where nodes broadcast a `vote` for the value they've
      seen echoed by a `2f + 1` quorum of nodes; alternatively, a node
      votes if it sees `f + 1` votes for the same value

  The `deliver` action is triggered when a node sees `2f + 1` votes for
  the same value, and outputs (delivers) that value.

  The protocol has three separate quorum thresholds:
    - `echo4vote` -- `2f + 1` nodes that have echoed the same value to vote
    - `vote4vote` -- `f + 1` nodes that have voted for the same value to vote
    - `vote4output` -- `2f + 1` nodes that have voted for the same value to output/deliver
-/

/- SabNote:
Recall that the `type` command in Veil defines a Lean type that is sound to use
as an SMT sort, i.e. one that comes with an instance of the `Nonempty` typeclass.

nodeset: the set of nodes (of course.)
address: node identifier
round: what round we are currently in
value: output sent/received from nodes
-/
type nodeset
type address
type round
type value

/-SabNote:
Recall that Byzantine faults in a system may present differently to
different observers.
-/
variable (is_byz : address → Prop)

instantiate nset : NodeSet address is_byz nodeset
open NodeSet

-- Messages over the network
/-SabNote:
Recall that relations are predicates over types.
We just defined the address, round, and value types.

initial_msg: has `originator` sent `value` to a `dst` in round `r`?

echo_msg: has `src` echoed a message from `originator` containing `value` to
`dst` in round `r`?

vote_msg: has `vote` voted on a message from `originator` containing `value` to
`dst` in round `r`?
-/
relation initial_msg (originator : address) (dst : address) (r : round) (v : value)
relation echo_msg (src : address) (dst : address) (originator : address) (r : round) (v : value)
relation vote_msg (src : address) (dst : address) (originator : address) (r : round) (v : value)

-- State of the nodes
/- SabNote:
The primary difference between these relations and the initial_msg, echo_msg,
and vote_msg relations are that these do not include the destination.
As the developer's note says, these relations define the state of the nodes,
while the above defines the state of messages in the network.

sent (n, r) : has the node `n` initiated round `r`?

echoed(n, originator, in_round, value) : has `n` echoed `value` in round
`in_round` from origin `originator`?

voted (n, originator, in_round, v) : has `n` at voted in round `in_round` for
`value` from origin `originator`?

delivered (n, originator, in_round, v) : has the node `n` delivered a message
from `originator` in round `in_round` fro value `v`?
-/
relation sent (n : address) (r : round)
relation echoed (n : address) (originator : address) (in_round : round) (v : value)
relation voted (n : address) (originator : address) (in_round : round) (v : value)
relation delivered (n : address) (originator : address) (in_round : round) (v : value)

#gen_state
/- SabNote:
Recall, gen_state calls assemble_state, which packages all relation predicates
into a single `State` type.
-/

-- Ghost relations
/-SabNote: These are just used in specification.-/
ghost relation initial_value (n : address) (r : round) (v : value) := ∀ dst, initial_msg n dst r v

/-
SabNote:
In the initial state:
no nodes should have sent, echoed, voted, or delivered any messages, and
no messages should be in the process of being sent, echoed, or voted on.
-/
after_init {
  initial_msg O D R V := False;
  echo_msg S D O R V  := False;
  vote_msg S D O R V  := False;

  sent N R            := False;
  echoed N O R V      := False;
  voted N O R V       := False;
  delivered N O R V   := False
}

/-
SabNote:
First condition:
For all src and dst nodes in any round and any message value,
  The src is not byzantine and the initial msg states are the same before and after the transition, OR
  The src is byzantine and the initial msg state implies the initial message state after transition.
  (Note: since we also have the condition `st.sent = st'.sent`, I am guessing
  that if the initial msg state is false before the internal transition, it must
  also be false after transition since no nodes' sent states can change.
  However, if the initial msg state is true, it must remain true.)

Second condition:
For all src and dst nodes in any round and any message value,
  The src is not byzantine and the echo msg states are the same before and after the transition, OR
  The src is byzantine and the echo msg state implies the echo message state after transition.
  (Note: since we also have the condition `st.echoed = st'.echoed`, I am guessing
  that if the echo msg state is false before the internal transition, it must
  also be false after transition since no nodes' sent states can change.
  However, if the echo msg state is true, it must remain true.)

Third condition:
For all src and dst nodes in any round and any message value,
  The src is not byzantine and the vote msg states are the same before and after the transition, OR
  The src is byzantine and the vote msg state implies the vote message state after transition.
  (Note: since we also have the condition `st.voted = st'.voted`, I am guessing
  that if the vote msg state is false before the internal transition, it must
  also be false after transition since no nodes' vote states can change.
  However, if the vote msg state is true, it must remain true.)
-/
internal transition byz = fun st st' =>
  (∀ (src dst : address) (r : round) (v : value),
    (¬ is_byz src ∧ (st.initial_msg src dst r v ↔ st'.initial_msg src dst r v)) ∨
    (is_byz src ∧ (st.initial_msg src dst r v → st'.initial_msg src dst r v))) ∧
  (∀ (src dst originator : address) (r : round) (v : value),
    (¬ is_byz src ∧ (st.echo_msg src dst originator r v ↔ st'.echo_msg src dst originator r v)) ∨
    (is_byz src ∧ (st.echo_msg src dst originator r v → st'.echo_msg src dst originator r v))) ∧
  (∀ (src dst originator : address) (r : round) (v : value),
    (¬ is_byz src ∧ (st.vote_msg src dst originator r v ↔ st'.vote_msg src dst originator r v)) ∨
    (is_byz src ∧ (st.vote_msg src dst originator r v → st'.vote_msg src dst originator r v)))
  /-SabNote:
  Internal transition should not affect if the node has sent, echoed, voted, or
  delivered in this round.
  -/
  ∧ (st.sent = st'.sent)
  ∧ (st.echoed = st'.echoed)
  ∧ (st.voted = st'.voted)
  ∧ (st.delivered = st'.delivered)


/-
SabNote:
In order to broadcast, a node must not have sent a message this round.
If it has not yet sent a message, initialize a message and mark the node
as having sent a message this round.
-/
action broadcast (n : address) (r : round) (v : value) = {
  require ¬ sent n r;
  initial_msg n N r v := True;
  sent n r := True
}

/-
SabNote:
Conditions:
To echo a message, the originator must have sent an initial message to this node
during this round. Also, the current node must not have already echoed any message
from the originator this round,

If met:
  Mark the node as having echoed a value in this round
  Mark the echoed message as true.
-/
action echo (n : address) (originator : address) (r : round) (v : value) = {
  require initial_msg originator n r v;
  require ∀ V, ¬ echoed n originator r V;
  echoed n originator r v := True;
  echo_msg n DST originator r v := True
}

/-
SabNote:
Conditions:
To vote on a message...
  A supermajority of nodes must have echoed the message, AND
  if the source node of the message is a member of the nodeset, then the message
  from the source node to n must have already been echoed,

  OR

  More than a third of nodes must have voted on the message, AND
  if the source node of the message is a member of the nodeset, then the message
  from the source node to n must have already been voted on.

If met:
  Mark the node as having voted on a value from the originator in this round
  Mark the voted message as true.
-/
action vote (n : address) (originator : address) (r : round) (v : value) = {
  -- received 2f + 1 echo messages OR f + 1 vote messages
  require (∃ (q : nodeset), nset.supermajority q ∧
              ∀ (src : address), nset.member src q → echo_msg src n originator r v) ∨
          (∃ (q : nodeset), nset.greater_than_third q ∧
              ∀ (src : address), nset.member src q → vote_msg src n originator r v);
  require ∀ V, ¬ voted n originator r V;
  voted n originator r v := True;
  vote_msg n DST originator r v := True
}

/-
SabNote:
Conditions:
To deliver a message...
  A supermajority of nodes must have voted for the the message, AND
  if the source node of the message is a member of the nodeset, then the
  message from the source node to n must have already been voted on.

If met:
  Mark the node as having delivered a message.
-/
action deliver (n : address) (originator : address) (r : round) (v : value) = {
  -- received 2f + 1 votes
  require (∃ (q : nodeset), nset.supermajority q ∧
              ∀ (src : address), nset.member src q → vote_msg src n originator r v);
  delivered n originator r v := True
}

/-
SabNote:
The safety conditions here are checking for consistency of message contents.
-/
/- If a value is voted for, it is the value that was initially proposed by the originator. -/
safety [vote_integrity]
  ∀ (src dst : address) (r : round) (v : value),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v → (sent src r ∧ initial_value src r v)

/- If a value is delivered, it is the value that was initially proposed by the originator. -/
safety [deliver_integrity]
  ∀ (src dst : address) (r : round) (v : value),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ delivered dst src r v → (sent src r ∧ initial_value src r v)

/- Also known as "delivered uniqueness". -/
safety [agreement]
  ∀ (src dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    ¬ is_byz dst₁ ∧ ¬ is_byz dst₂ ∧ delivered dst₁ src r v₁ ∧ delivered dst₂ src r v₂ → v₁ = v₂

-- These invariants are discovered in the order given, by inspecting the code
-- of the actions one by one.
/-
SabNote:
By "discovered," I think the authors are implying that they used Veil to
generate the invariants below rather than specifying them manually.

These invariants check for consistency between node states and message states.
-/

-- broadcast
/-
SabNote:
If the source node is not byzantine, then for all nodes that have sent a
message in the current round, there exists a corresponding initial message
value.
-/
invariant [sent_iff_initial]
  ∀ (src : address) (r : round),
    ¬ is_byz src → (sent src r ↔ ∃ (v : value), initial_value src r v)

-- echo

/-
SabNote:
If the source node is not byzantine, then for all nodes that have echoed a
message in the current round, there exists a corresponding message that has been
echoed.
-/
invariant [echoed_iff_echo]
  ∀ (n dst originator : address) (r : round) (v : value),
    ¬ is_byz n → (echoed n originator r v ↔ echo_msg n dst originator r v)

/-
SabNote:
If the source node is not byzantine, then for all nodes that have echoed a
message in the current round, there exists a corresponding initial message.
-/
invariant [echoed_requires_initial]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (echoed n originator r v → initial_msg originator n r v)

-- vote
/-
SabNote:
If the source node is not byzantine, then for all nodes that have voted on a
message in the current round, there exists a corresponding message that has
been voted on.
-/
invariant [voted_iff_vote]
  ∀ (n dst originator : address) (r : round) (v : value),
    ¬ is_byz n → (voted n originator r v ↔ vote_msg n dst originator r v)


/-
SabNote: skipping these invariants since checking them is undecidable.
Worth noting that Veil can generate invariants that cannot be checked.
-/
-- not in the decidable fragment due to edge from `address` to `nodeset`:
invariant [voted_requires_echo_quorum_or_vote_quorum]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (voted n originator r v →
      (∃ (q : nodeset), nset.supermajority q ∧
        ∀ (src : address), member src q → echo_msg src n originator r v) ∨
      (∃ (q : nodeset), nset.greater_than_third q ∧
        ∀ (src : address), member src q → vote_msg src n originator r v))

-- deliver
-- not in the decidable fragment due to edge from `address` to `nodeset`
invariant [delivered_requires_vote_quorum]
  ∀ (n originator : address) (r : round) (v : value),
    ¬ is_byz n → (delivered n originator r v →
      ∃ (q : nodeset), nset.supermajority q ∧
        ∀ (src : address), member src q → vote_msg src n originator r v)

-- these invariants are discovered in the order given, by eliminating CTIs

-- vote_vote_integrity
-- this version is not in the decidable fragment:
-- invariant [sent_iff_initial]
--   ∀ (src : address) (r : round),
--     sent src r ↔ ∃ (dst : address) (v : value), initial_msg src dst r v

-- So instead we use the following:

/-
SabNote:
If the source node is not byzantine, then for all nodes that have an initial
message value in the current round, there exists a corresponding initial
message.
-/
invariant [initial_value_iff_initial_msg]
  ∀ (src dst : address) (r : round) (v : value),
    ¬ is_byz src → (initial_value src r v ↔ initial_msg src dst r v)

-- deliver_agreement
/-
SabNote:
Assume the source node is not byzantine. If we have two initial messages from
the source to (possibly different) destination nodes in the same round, these
messages must contain the same value.
-/
invariant [honest_non_conflicting_initial_msg]
  ∀ (src dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (initial_msg src dst₁ r v₁ ∧ initial_msg src dst₂ r v₂ → v₁ = v₂)

/-
SabNote:
Assume the source node is not byzantine. If we have two initial messages from
the source to (possibly different) destination nodes in the same round, these
messages must contain the same value.
-/
invariant [honest_non_conflicting_echoes]
  ∀ (src originator dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (echo_msg src dst₁ originator r v₁ ∧ echo_msg src dst₂ originator r v₂ → v₁ = v₂)

/-
SabNote:
Assume the source node is not byzantine. If we have two voted-on messages from
the source to (possibly different) destination nodes in the same round, these
messages must contain the same value.
-/
invariant [honest_non_conflicting_votes]
  ∀ (src originator dst₁ dst₂ : address) (r : round) (v₁ v₂ : value),
    (¬ is_byz src) → (vote_msg src dst₁ originator r v₁ ∧ vote_msg src dst₂ originator r v₂ → v₁ = v₂)

#gen_spec

#time #check_invariants

end ReliableBroadcast
