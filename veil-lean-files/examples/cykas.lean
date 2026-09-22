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


/-
State of the processes

secret: is `p` in secret mode until the message `m` from `sender` to `receiver`
is ACKed?
sent: is `p` currently sending a message?
delivered: did `p` deliver the message `m` to `receiver`?
sent_before : was `m1` sent before `m2`?
delivered_before : was `m1` delivered before `m2`?
-/
relation secret (p : process) (sender : process) (receiver : process) (m : message)
relation sent (p : process) (receiver : process) (m : message)
relation delivered (p : process) (receiver : process) (m : message)
relation sent_before (sender : process) (receiver : process) (m1 : message) (m2 : message)
relation delivered_before (sender : process) (receiver : process) (m1 : message) (m2 : message)

/-
Recall, gen_state calls assemble_state, which packages all relation predicates
into a single `State` type.
-/
#gen_state


/-
In the initial state:
No processes should be in secret mode.
No process should have sent or delivered any messages.
All sent_before and delivered_before relations are False.
There should be no eager, normal, ACK, or YouCanTell messages.
-/
after_init {
  secret P S R M := False;
  sent P R M := False;
  delivered P R M := False;
  sent_before S R M N := False; -- TODO: we actually don't need sender info for causal ordering
  delivered_before S R M N := False; -- TODO: we actually don't need sender info for causal ordering

  eager_msg S R M := False;
  normal_msg S R M := False;
  ack_msg S R M := False;
}

/-
Conditions:
  sender must not be in secret mode
  if another message from this sender exists, it must already have been ACKed.
  If another from this sender exists and has not been ACKed, we would need to send
  an eager message.

If met:
  Instantiate the normal message.
  Mark the normal message as sent.
  Update the sent_before relation to track every message M from this sender
  and receiver that was sent before m.
  Update the delivered_before relation to track every message M from this sender
  and receiver that was delivered before m.
-/
action normal_send (sender : process) (receiver : process) (m : message) = {
  require ¬ (∃ S R M, secret sender S R M);
  -- if we are sending a normal message, no other messages from this sender
  -- should be in progress
  require ¬ (∃ R M, normal_msg sender R M ∧ ¬ delivered sender R M);
  require ¬ (∃ R M, normal_msg sender R M ∧ ¬ ack_msg sender R M);
  require ¬ (∃ R M, eager_msg sender R M ∧ ¬ ack_msg sender R M);
  require ¬ (∃ R M, eager_msg sender R M ∧ ¬ delivered sender R M);
  require ¬ sent sender receiver m;
  require (∀ S R, (S != sender ∨ R != receiver) → (¬ normal_msg S R m ∧ ¬ eager_msg S R m))
  require sender != receiver;

  normal_msg sender receiver m := True;

  -- have to update sent_before first, otherwise we mark m as being delivered
  -- before itself.
  sent_before sender receiver M m := sent sender receiver M;
  sent sender receiver m := True;
  -- why is this neccessary for causal delivery if false by default? still needed?
  delivered sender receiver m := False;
  ack_msg sender receiver m := False;
}

/-
Conditions:
  A corresponding normal message must already exist.
  This message must be sent and not delivered.

If met:
  Mark the message as delivered.
  Update the delivered_before relation to track every message M from this sender
  and receiver that was delivered before m.
-/
action normal_delivery (sender : process) (receiver : process) (m : message) = {
  require normal_msg sender receiver m;
  require sent sender receiver m;
  require ¬ delivered sender receiver m;
  require ¬ (∃ S R M, secret sender S R M);
  require ¬ (∃ R M, normal_msg sender R M ∧ ¬ delivered sender R M);
  require ¬ (∃ R M, normal_msg sender R M ∧ ¬ ack_msg sender R M);
  require ¬ (∃ R M, eager_msg sender R M ∧ ¬ ack_msg sender R M);
  require ¬ (∃ R M, eager_msg sender R M ∧ ¬ delivered sender R M);
  require sender != receiver;

  delivered sender receiver m := True;
  delivered_before sender receiver M m := delivered sender receiver M;
}

/-
Conditions:
To ACK a message,
  A corresponding message must already exist.
  The message must have been delivered.

If met:
  Mark the message as acknowledged.
-/
action ack (sender : process) (receiver : process) (m : message) = {
  require eager_msg sender receiver m ∨ normal_msg sender receiver m;
  require delivered sender receiver m;

  ack_msg sender receiver m := True;
}

/-
Conditions:
To eagerly send a message:
  The sender must already have sent a normal message which has not yet been ACKed.
  The sender must not be in secret mode.

If met:
  Initialize an eager message and send it.
  If any other messages have been sent from this sender to the receiver, ensure
  that they are causually sent.
-/
action eager_send (sender : process) (receiver : process) (m : message) = {
  require ¬ ∃ S R M, secret sender S R M;
  require ∃ R M, normal_msg sender R M ∧ ¬ ack_msg sender R M;
   /- without this condition, we send the same message
   multiple times. This is a problem since both messages are mapped to the same
   proposition in the state relations, and we end up overwriting the relations when
   we send again to make the state inconsistent with causal message delivery.
    -/
  require ¬ sent sender receiver m;
  -- must require message uniqueness or else ordering issues
  require (∀ S R, (S != sender ∨ R != receiver) → (¬ normal_msg S R m ∧ ¬ eager_msg S R m))
  require sender != receiver

  eager_msg sender receiver m := True;

  -- have to update sent_before first, otherwise we mark m as being delivered
  -- before itself.
  sent_before sender receiver M m := sent sender receiver M;
  sent sender receiver m := True;

}

/-
Conditions:
To deliver an eager message, a corresponding eager message must already exist.
There must also be a normal message sent from the same sender.
The normal message must already be sent and delivered.

If met:
  Mark the message as delivered.
-/
action eager_delivery (sender : process) (secret_receiver : process) (msg_receiver : process) (em : message) (nm : message) = {
  require eager_msg sender secret_receiver em;
  require normal_msg sender msg_receiver nm;
  require sent sender secret_receiver em;
  require sent sender msg_receiver nm;
  require ¬ delivered sender secret_receiver em;
  require (∀ S R, (S != sender ∨ R != secret_receiver) → (¬ normal_msg S R em ∧ ¬ eager_msg S R em))
  require (∀ S R, (S != sender ∨ R != msg_receiver) → (¬ normal_msg S R nm ∧ ¬ eager_msg S R nm))
  require sender != secret_receiver;
  require sender != msg_receiver;
  -- assume no causal delivery violations so far
  require ∀ M, sent_before sender secret_receiver M em → delivered sender secret_receiver M;

  if secret_receiver == msg_receiver
    then require sent_before sender msg_receiver nm em ∧ nm != em;
  -- sent_before sender receiver M m := sent sender receiver M
  -- require sent_before sender msg_receiver nm em;
  -- do we need to require that the normal msg has been delivered?

  -- have to update delivered_before first, otherwise we mark em as being delivered
  -- before itself.
  delivered_before sender secret_receiver M em := delivered sender secret_receiver M;
  delivered sender secret_receiver em := True;

  -- if normal msg has not been delivered, put into secret mode
  secret secret_receiver sender msg_receiver nm := True

  -- delivered_before sender receiver M m := delivered sender receiver M
  -- maintain causal ordering tracking for eager message
}


/-
Conditions:
To tell a process in secret mode that they can tell,
  The message that put the process in secret mode must have been ACKed.
  The process must have been in secret mode for the message.

If met:
  Take the secret receiver out of secret mode.
-/
action you_can_tell (secret_receiver : process) (msg_sender : process) (msg_receiver : process) (m : message) = {
  require ack_msg msg_sender msg_receiver m;
  require secret secret_receiver msg_sender msg_receiver m;
  secret secret_receiver msg_sender msg_receiver m := False;
}

/-
From Cykas paper:
"The safety property we wish to ensure is causal delivery, i.e., messages are
never delivered in an order that violates the causal order.
That is, if m is sent before m′ and m and m′ are received and delivered at
the same process, then the delivery of m precedes the delivery of m′."

Assumptions:
Two messages to the same receiver exist (can be normal or eager.)
The message contents are not the same (needed to prevent edge case counterexamples, possibly overconstrained.)
Both messages were sent.
Both messages were delivered.
One message was sent before the other.

Conclusion:
The message that was sent first is delivered before the other message.
-/
safety [causal_delivery]
∀ S (receiver : process) (m1 m2 : message),
  m1 != m2 ∧
  ((normal_msg S receiver m1) ∨ (eager_msg S receiver m1)) ∧
  ((normal_msg S receiver m2) ∨ (eager_msg S receiver m2)) ∧
  (sent S receiver m1) ∧ (sent S receiver m2) ∧
  (delivered S receiver m1) ∧ (delivered S receiver m2) ∧
  (sent_before S receiver m1 m2) →
  delivered_before S receiver m1 m2


invariant [ack_implies_delivered] ack_msg S R M → delivered S R M

invariant [delivered_implies_send] delivered S R M → sent S R M

invariant [sent_before_implies_sent] sent_before S R M1 M2 → sent S R M1 ∧ sent S R M2

invariant [sent_before_ordering] sent_before S R M1 M2 → ¬ sent_before S R M2 M1

invariant [delivered_before_implies_delivered] delivered_before S R M1 M2 → delivered S R M1 ∧ delivered S R M2

invariant [delivered_before_ordering] delivered_before S R M1 M2 → ¬ delivered_before S R M2 M1

invariant [delivery_respects_send_order] sent_before S R M1 M2 → delivered S R M2 → delivered S R M1

-- each msg must have unique id otherwise ordering issues
invariant [unique_msg_owner] (normal_msg S R M ∨ eager_msg S R M) →
  (∀ S2 R2, (S2 != S ∨ R2 != R) →
  (¬ normal_msg S2 R2 M ∧ ¬ eager_msg S2 R2 M))


#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"
#time #check_invariants


end Cykas
