import Veil

veil module Cykas

/-
  Cykas is a protocol for sender-side enforcement of causal message delivery.
  If a process receives a causally out-of-order message, the sender puts the
  receiver in "secret mode," so the receiver cannot send any messages. Once the
  sender receives an ACK signalling that the message has been delivered, the
  sender then releases the receiver from secret mode.

  For more details, see the paper "Can You Keep A Secret? A new protocol for
  sender-side enforcement of causal message delivery" by Tong et al.
  https://arxiv.org/pdf/2603.14690
-/

-- process: independent participant in a distributed system
-- message: output sent/received from processes in a system
type process
type message

/-
The state of messages over the network
Recall that relations are predicates over types.

eager_msg: has `sender` sent `m` to a `receiver` out of causal order?

normal_msg:  has `sender` sent `m` to a `receiver` in causal order?

ack_msg: has the message `m` from `sender` to `receiver` been acknowledged?

youcantell_msg: has `sender` told `secret_receiver` to send the message `m`
to `msg_receiver`?
-/
relation eager_msg (sender : process) (receiver : process) (m : message)
relation normal_msg (sender : process) (receiver : process) (m : message)
relation ack_msg (sender : process) (receiver : process) (m : message)
relation youcantell_msg (sender : process) (secret_receiver : process) (msg_receiver : process) (m : message)

/-
State of the nodes
secret: is `p` in secret mode?

sending: is `p` currently sending a message?

delivered: did `p` deliver the message `m` to `receiver`?
-/
relation secret (p : process)
relation sending (p : process)
relation delivered (p : process) (receiver : process) (m : message)

/-
Recall, gen_state calls assemble_state, which packages all relation predicates
into a single `State` type.
-/
#gen_state


/-
SabNote:
In the initial state:
No processes should be in secret mode or sending any messages
No process should have delivered any messages.
There should be no eager, normal, ACK, or YouCanTell messages.
-/
after_init {
  secret P := False;
  sending P := False;
  delivered P R M := False;

  eager_msg S R M := False
  normal_msg S R M := False
  ack_msg S R M := False
  youcantell_msg S R M V := False
}

/-
SabNote:
First condition:
For all src and dst nodes in any round and any message message,
  The src is not byzantine and the initial msg states are the same before and after the transition, OR
  The src is byzantine and the initial msg state implies the initial message state after transition.
  (Note: since we also have the condition `st.sent = st'.sent`, I am guessing
  that if the initial msg state is false before the internal transition, it must
  also be false after transition since no nodes' sent states can change.
  However, if the initial msg state is true, it must remain true.)

Second condition:
For all src and dst nodes in any round and any message message,
  The src is not byzantine and the echo msg states are the same before and after the transition, OR
  The src is byzantine and the echo msg state implies the echo message state after transition.
  (Note: since we also have the condition `st.echoed = st'.echoed`, I am guessing
  that if the echo msg state is false before the internal transition, it must
  also be false after transition since no nodes' sent states can change.
  However, if the echo msg state is true, it must remain true.)

Third condition:
For all src and dst nodes in any round and any message message,
  The src is not byzantine and the vote msg states are the same before and after the transition, OR
  The src is byzantine and the vote msg state implies the vote message state after transition.
  (Note: since we also have the condition `st.voted = st'.voted`, I am guessing
  that if the vote msg state is false before the internal transition, it must
  also be false after transition since no nodes' vote states can change.
  However, if the vote msg state is true, it must remain true.)
-/
internal transition byz = fun st st' =>
  (∀ (src dst : address) (r : round) (v : message),
    (¬ is_byz src ∧ (st.initial_msg src dst r v ↔ st'.initial_msg src dst r v)) ∨
    (is_byz src ∧ (st.initial_msg src dst r v → st'.initial_msg src dst r v))) ∧
  (∀ (src dst originator : address) (r : round) (v : message),
    (¬ is_byz src ∧ (st.echo_msg src dst originator r v ↔ st'.echo_msg src dst originator r v)) ∨
    (is_byz src ∧ (st.echo_msg src dst originator r v → st'.echo_msg src dst originator r v))) ∧
  (∀ (src dst originator : address) (r : round) (v : message),
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
action broadcast (n : address) (r : round) (v : message) = {
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
  Mark the node as having echoed a message in this round
  Mark the echoed message as true.
-/
action echo (n : address) (originator : address) (r : round) (v : message) = {
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
  Mark the node as having voted on a message from the originator in this round
  Mark the voted message as true.
-/
action vote (n : address) (originator : address) (r : round) (v : message) = {
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
action deliver (n : address) (originator : address) (r : round) (v : message) = {
  -- received 2f + 1 votes
  require (∃ (q : nodeset), nset.supermajority q ∧
              ∀ (src : address), nset.member src q → vote_msg src n originator r v);
  delivered n originator r v := True
}

/-
SabNote:
The safety conditions here are checking for consistency of message contents.
-/
/- If a message is voted for, it is the message that was initially proposed by the originator. -/
safety [vote_integrity]
  ∀ (src dst : address) (r : round) (v : message),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ voted dst src r v → (sent src r ∧ initial_message src r v)

/- If a message is delivered, it is the message that was initially proposed by the originator. -/
safety [deliver_integrity]
  ∀ (src dst : address) (r : round) (v : message),
     ¬ is_byz src ∧ ¬ is_byz dst ∧ delivered dst src r v → (sent src r ∧ initial_message src r v)

/- Also known as "delivered uniqueness". -/
safety [agreement]
  ∀ (src dst₁ dst₂ : address) (r : round) (v₁ v₂ : message),
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
message.
-/
invariant [sent_iff_initial]
  ∀ (src : address) (r : round),
    ¬ is_byz src → (sent src r ↔ ∃ (v : message), initial_message src r v)

-- echo

/-
SabNote:
If the source node is not byzantine, then for all nodes that have echoed a
message in the current round, there exists a corresponding message that has been
echoed.
-/
invariant [echoed_iff_echo]
  ∀ (n dst originator : address) (r : round) (v : message),
    ¬ is_byz n → (echoed n originator r v ↔ echo_msg n dst originator r v)

/-
SabNote:
If the source node is not byzantine, then for all nodes that have echoed a
message in the current round, there exists a corresponding initial message.
-/
invariant [echoed_requires_initial]
  ∀ (n originator : address) (r : round) (v : message),
    ¬ is_byz n → (echoed n originator r v → initial_msg originator n r v)

-- vote
/-
SabNote:
If the source node is not byzantine, then for all nodes that have voted on a
message in the current round, there exists a corresponding message that has
been voted on.
-/
invariant [voted_iff_vote]
  ∀ (n dst originator : address) (r : round) (v : message),
    ¬ is_byz n → (voted n originator r v ↔ vote_msg n dst originator r v)


/-
SabNote: skipping these invariants since checking them is undecidable.
Worth noting that Veil can generate invariants that cannot be checked.
-/
-- not in the decidable fragment due to edge from `address` to `nodeset`:
invariant [voted_requires_echo_quorum_or_vote_quorum]
  ∀ (n originator : address) (r : round) (v : message),
    ¬ is_byz n → (voted n originator r v →
      (∃ (q : nodeset), nset.supermajority q ∧
        ∀ (src : address), member src q → echo_msg src n originator r v) ∨
      (∃ (q : nodeset), nset.greater_than_third q ∧
        ∀ (src : address), member src q → vote_msg src n originator r v))

-- deliver
-- not in the decidable fragment due to edge from `address` to `nodeset`
invariant [delivered_requires_vote_quorum]
  ∀ (n originator : address) (r : round) (v : message),
    ¬ is_byz n → (delivered n originator r v →
      ∃ (q : nodeset), nset.supermajority q ∧
        ∀ (src : address), member src q → vote_msg src n originator r v)

-- these invariants are discovered in the order given, by eliminating CTIs

-- vote_vote_integrity
-- this version is not in the decidable fragment:
-- invariant [sent_iff_initial]
--   ∀ (src : address) (r : round),
--     sent src r ↔ ∃ (dst : address) (v : message), initial_msg src dst r v

-- So instead we use the following:

/-
SabNote:
If the source node is not byzantine, then for all nodes that have an initial
message message in the current round, there exists a corresponding initial
message.
-/
invariant [initial_message_iff_initial_msg]
  ∀ (src dst : address) (r : round) (v : message),
    ¬ is_byz src → (initial_message src r v ↔ initial_msg src dst r v)

-- deliver_agreement
/-
SabNote:
Assume the source node is not byzantine. If we have two initial messages from
the source to (possibly different) destination nodes in the same round, these
messages must contain the same message.
-/
invariant [honest_non_conflicting_initial_msg]
  ∀ (src dst₁ dst₂ : address) (r : round) (v₁ v₂ : message),
    (¬ is_byz src) → (initial_msg src dst₁ r v₁ ∧ initial_msg src dst₂ r v₂ → v₁ = v₂)

/-
SabNote:
Assume the source node is not byzantine. If we have two initial messages from
the source to (possibly different) destination nodes in the same round, these
messages must contain the same message.
-/
invariant [honest_non_conflicting_echoes]
  ∀ (src originator dst₁ dst₂ : address) (r : round) (v₁ v₂ : message),
    (¬ is_byz src) → (echo_msg src dst₁ originator r v₁ ∧ echo_msg src dst₂ originator r v₂ → v₁ = v₂)

/-
SabNote:
Assume the source node is not byzantine. If we have two voted-on messages from
the source to (possibly different) destination nodes in the same round, these
messages must contain the same message.
-/
invariant [honest_non_conflicting_votes]
  ∀ (src originator dst₁ dst₂ : address) (r : round) (v₁ v₂ : message),
    (¬ is_byz src) → (vote_msg src dst₁ originator r v₁ ∧ vote_msg src dst₂ originator r v₂ → v₁ = v₂)

#gen_spec

#time #check_invariants

end ReliableBroadcast
