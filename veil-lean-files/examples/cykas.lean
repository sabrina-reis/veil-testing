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
State of the processes
secret: is `p` in secret mode?

sending: is `p` currently sending a message?

delivered: did `p` deliver the message `m` to `receiver`?
-/
relation secret (p : process)
relation sending (p : process) (receiver : process) (m : message)
relation delivered (p : process) (receiver : process) (m : message)

/-
Recall, gen_state calls assemble_state, which packages all relation predicates
into a single `State` type.
-/
#gen_state


/-
In the initial state:
No processes should be in secret mode or sending any messages
No process should have delivered any messages.
There should be no eager, normal, ACK, or YouCanTell messages.
-/
after_init {
  secret P := False;
  sending P R M := False;
  delivered P R M := False;

  eager_msg S R M := False;
  normal_msg S R M := False;
  ack_msg S R M := False;
  youcantell_msg S R M V := False;
}

/-
Conditions:
To normally send a message, the receiver must not be in secret mode and the
sender must not be sending any another message.

If met:
Update the message state to reflect the normal message and update the
process state to indicate that the sender is currently sending a message.
-/
action normal_send (sender : process) (receiver : process) (m : message) = {
  require ¬ secret receiver ∧ ∀ R M, ¬ sending sender R M;
  normal_msg sender receiver m := True;
  sending sender receiver m := True;
}

/-
Conditions:
To eagerly send a message, the sender must already be sending a message.

If met:
Initialize an eager message and put the receiver into secret mode.
-/
action eager_send (sender : process) (receiver : process) (m : message) = {
  require ∃ R M, sending sender R M;
  eager_msg sender receiver m := True;
  secret receiver := True;
  -- receiver could already be in secret mode; is that a problem?

}

/-
Conditions:
To deliver a normal message, a corresponding normal message must already exist.

If met:
  Mark the message as delivered e as having echoed a message in this round
  Mark the echoed message as true.
-/
action normal_delivery (sender : process) (receiver : process) (m : message) = {
  sorry
}

/-
SabNote:
From reliable_broadcast

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

action eager_delivery (sender : process) (receiver : process) (m : message) = {
  sorry
}

action ack (sender : process) (receiver : process) (m : message) = {
  sorry
}

action you_can_tell (sender : process) (receiver : process) (m : message) = {
  sorry
}

/-
From reliable_broadcast
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

#gen_spec

#time #check_invariants

end Cykas
