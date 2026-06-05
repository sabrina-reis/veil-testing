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

sent: is `p` currently sent a message?

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
No processes should be in secret mode or sent any messages
No process should have delivered any messages.
There should be no eager, normal, ACK, or YouCanTell messages.
-/
after_init {
  secret P S R M := False;
  sent P R M := False;
  delivered P R M := False;

  eager_msg S R M := False;
  normal_msg S R M := False;
  ack_msg S R M := False;
  sent_before S R M N := False
  delivered_before S R M N := False
}

/-
Conditions:
  sender must not be in secret mode
  if another message from this sender exists, it must already have been ACKed.
  If another from this sender exists and has not been ACKed, we would need to send
  an eager message.

If met:
  Initialize the normal message
  Mark message as sent.
  If any other messages have been sent from this sender and receiver, ensure
  that they are causally ordered.
-/
action normal_send (sender : process) (receiver : process) (m : message) = {
  require ¬ ∃ S R M, secret sender S R M
  require ¬ ∃ R M, normal_msg sender R M ∧ ¬ ack_msg sender R M
  require ¬ ∃ R M, eager_msg sender R M ∧ ¬ ack_msg sender R M

  normal_msg sender receiver m := True;
  sent sender receiver m := True;
  ∀ M, sent sender receiver M → sent_before sender receiver M m := True
}

/-
Conditions:
  A corresponding normal message must already exist.
  This message must be sent and not delivered.
  (TODO: does it have to not be delivered?)

If met:
  Mark the message as delivered.
-/
action normal_delivery (sender : process) (receiver : process) (m: message) = {
  require normal_msg sender receiver m;
  require sent sender receiver m;
  require ¬ delivered sender receiver m;


  delivered sender receiver m := True;
  ∀ M, delivered sender receiver M → delivered_before sender receiver M m := True
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
  require ¬ ∃ S R M secret sender S R M;
  require ∃ R M, normal_msg sender R M ∧ ¬ ack_msg sender R M

  eager_msg sender receiver m := True;
  sent sender receiver m := True;
  ∀ M, sent sender receiver M → sent_before sender receiver M m := True
}

/-
Conditions:
To deliver an eager message, a corresponding eager message must already exist.
There must also be a normal message sent from the same sender.
The normal message must no longer be sent and must already be delivered.

If met:
  Mark the message as delivered.
  Mark the sender as no longer sent this message.
-/
action eager_delivery (sender : process) (secret_receiver : process) (msg_receiver) (em : message) (nm : message) = {
  require eager_msg sender secret_receiver em;
  require sent sender secret_receiver em;
  require ¬delivered sender secret_receiver em;
  require ∃ R, normal_msg msg_sender R nm

  delivered sender secret_receiver em := True;
  secret receiver sender msg_receiver nm := True;
  ∀ M, delivered sender secret_receiver M → delivered sender secret_receiver M m := True
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
The safety property we wish to ensure is causal delivery, i.e., messages are
never delivered in an order that violates the causal order.
That is, if m is sent before m′ and m and m′ are received and delivered at
the same process, then the delivery of m precedes the delivery of m′.
-/

safety [causal_delivery]
∀ (sender receiver : process) (m1 m2 : message),
  (normal_msg sender receiver m1) ∧ (eager_msg sender receiver m2) ∧
  (sent sender receiver m1) ∧ (sent sender receiver m2) ∧
  (delivered sender receiver m1) ∧ (delivered sender receiver m2) →
  sent_before sender receiver m1 m2 ∧
  delivered_before sender receiver m1 m2

#gen_spec

set_option veil.printCounterexamples true
set_option veil.smt.model.minimize true
set_option veil.vc_gen "transition"
#time #check_invariants


end Cykas
