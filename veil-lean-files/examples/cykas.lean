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
}

/-
Conditions:
To normally send a message, the sender must not be in secret mode and the
sender must not be sending any another message.

If met:
Update the message state to reflect the normal message and update the
process state to indicate that the sender is currently sending a message.
-/
action normal_send (sender : process) (receiver : process) (m : message) = {
  require ¬ secret sender
  require ∀ R M, ¬ sending sender R M
  require ∀ S R M, ¬ normal_msg S R M
  require ∀ S R M, ¬ eager_msg S R M

  normal_msg sender receiver m := True;
  delivered sender receiver m := False;
  sending sender receiver m := True;
}

/-
Conditions:
To deliver a normal message, a corresponding normal message must already exist.

If met:
  Mark the message as delivered.
  Mark the sender as no longer sending this message.
-/
action normal_delivery (sender : process) (receiver : process) (m: message) = {
  require normal_msg sender receiver m;
  require sending sender receiver m;
  require ∀ M, ¬ sending sender receiver M;
  require ¬ delivered sender receiver m;

  sending sender receiver m := False;
  delivered sender receiver m := True;
}

/-
Conditions:
To eagerly send a message, the sender must already be sending a normal message.

If met:
Initialize an eager message and put the receiver into secret mode.
-/
action eager_send (sender : process) (receiver : process) (m : message) = {
  require ¬ secret sender;
  require ∃ R M, normal_msg sender R M;
  require ∃ R M, sending sender R M;
  require ∃ R M, ¬ delivered sender R M;

  eager_msg sender receiver m := True;
  sending sender receiver m := True;
  delivered sender receiver m := False;
  -- receiver could already be in secret mode; is that a problem?

}

/-
Conditions:
To deliver an eager message, a corresponding eager message must already exist.
There must also be a normal message sent from the same sender.
The normal message must no longer be sending and must already be delivered.

If met:
  Mark the message as delivered.
  Mark the sender as no longer sending this message.
-/
action eager_delivery (sender : process) (receiver : process) (m : message) = {
  require ¬ secret sender;
  require ∃ R M, normal_msg sender R M;
  require ∃ R M, ¬ sending sender R M;
  require ∃ R M, delivered sender R M;
  require eager_msg sender receiver m;
  require sending sender receiver m;
  require ¬ delivered sender receiver m;

  sending sender receiver m := False;
  delivered sender receiver m := True;
  secret receiver := True; -- should I put this in the send or deliver?
}

/-
Conditions:
To ACK an eager message,
  A corresponding eager message must already exist.
  The sender must no longer be sending the eager message.
  This eager message must already have been delivered.

If met:
  Mark the message as delivered.
  Mark the sender as no longer sending this message.
-/
action ack (sender : process) (receiver : process) (m : message) = {
  require eager_msg sender receiver m;
  require ¬ sending sender receiver m;
  require delivered sender receiver m;

  ack_msg sender receiver m := True;
}

-- ack_msg: has the message `m` from `sender` to `receiver` been acknowledged?

/-
Conditions:
To tell a process in secret mode that they can tell,
  The eager message that put the process in secret mode must have been ACKed.

If met:
  Take the secret receiver out of secret mode.
  (TODO: I think this is enough to allow them to perform their send transition?)
-/
action you_can_tell (sender : process) (secret_receiver : process) (msg_receiver : process) (m : message) = {
  require ack_msg sender msg_receiver m;
  secret secret_receiver := False;
}

/-
From Cykas paper:
The safety property we wish to ensure is causal delivery, i.e., messages are
never delivered in an order that violates the causal order.
That is, if m is sent before m′ and m and m′ are received and delivered at
the same process, then the delivery of m precedes the delivery of m′.

In other words, if we are sending our normal message, then we are not sending
our eager message. Additionally, if our normal message has not been delivered,
then our eager message has not been delivered.
-/

safety [causal_delivery]
∀ (sender receiver1 receiver2 : process) (m1 m2 : message),
  (normal_msg sender receiver1 m1) ∧ (eager_msg sender receiver2 m2) →
    (sending sender receiver1 m1 → ¬ sending sender receiver2 m2) ∧
    (¬ delivered sender receiver1 m1) → (¬ delivered sender receiver2 m2)


/- From Cykas paper:
The liveness property we wish to ensure is that, assuming a reliable network,
all messages will eventually be delivered.

I don't know that we have a way to verify liveness in Veil yet?
-/

-- invariant[reliable_delivery]
--   ∀ (sender receiver : process) (m: message),
--     (normal_msg sender receiver m) ∨ (eager_msg sender receiver m) →
--     (eventually) delivered sender receiver m

#gen_spec
set_option veil.printCounterexamples true
#time #check_invariants

end Cykas
