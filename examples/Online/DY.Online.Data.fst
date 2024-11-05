module DY.Online.Data

open Comparse
open DY.Core
open DY.Lib

/// Here, we define the abstract types for the "Online?" Protocol:
///
/// A -> B: enc{Ping (A, n_A)}_B
/// B -> A: enc{Ack n_A}_A
///
/// (They are the same as for the simple 2 message protocol)



(*** Message Type ***)

/// for each of the two messages we define an abstract message type

[@@ with_bytes bytes] // ignore this line for now
type ping_t = {
  p_alice: principal;
  p_n_a : bytes;
}

[@@ with_bytes bytes] // ignore this line for now
type ack = {
  a_n_a : bytes;
}

/// the overall abstract message type
/// (consisting of constructors for the two messages
/// and using the above abstract types for each of them)

[@@ with_bytes bytes] // ignore this line for now
type message =
  | Ping: (ping:ping_t) -> message
  | Ack: (ack:ack) -> message


/// We use Comparse to generate the corresponding message formats.
/// I.e., we don't need to write parsing and serializing by hand
///
/// for this we need the `[@@ with_bytes bytes]` annotation for the message types above
///
/// We are not going into the details of how Comparse works.


/// We let Comparse generate a parser `ps_ping` for the abstract `ping` type
%splice [ps_ping_t] (gen_parser (`ping_t))

%splice [ps_ack] (gen_parser (`ack))

%splice [ps_message] (gen_parser (`message))

/// With the above parsers, we can make our `message` type an instance of
/// Comparse's `parseable_serializeable` class.
/// Again, the details are not important here,
/// but this is the step that enables us to call
/// `parse message buff` and `serialize message msg`
/// to translate between bytes and our abstract message type.
instance parseable_serializeable_bytes_message: parseable_serializeable bytes message = mk_parseable_serializeable ps_message


(*** State Type ***)

/// As for the messages we define abstract state types
/// for the three states stored by Alice and Bob after each step of the protocol.

[@@ with_bytes bytes]
type sent_ping = {
  sp_bob : principal;
  sp_n_a : bytes;
}

[@@ with_bytes bytes]
type sent_ack = {
  sa_alice: principal;
  sa_n_a : bytes;
}

[@@ with_bytes bytes]
type received_ack = {
  ra_bob : principal;
  ra_n_a : bytes;
}

[@@ with_bytes bytes]
type state = 
  | SentPing: (ping:sent_ping) -> state
  | SentAck: (ack:sent_ack) -> state
  | ReceivedAck: (rack:received_ack) -> state

/// As for messages, we use Comparse to generate
/// a parser and serializer for our abstract state type.

%splice [ps_sent_ping] (gen_parser (`sent_ping))
%splice [ps_sent_ack] (gen_parser (`sent_ack))
%splice [ps_received_ack] (gen_parser (`received_ack))
%splice [ps_state] (gen_parser (`state))

/// Now, we can call
/// `parse state buff` and `serialize state st`
/// to translate between bytes and the abstract state type.
instance parseable_serializeable_bytes_state: parseable_serializeable bytes state = mk_parseable_serializeable ps_state

/// We tag our protocol level states,
/// so that they are distinguishable from any internal DY* states. 

instance local_state_state: local_state state = {
  tag = "P.State";
  format = parseable_serializeable_bytes_state;
}


(*** PKI ***)

/// For en-/de-cryption we assume some PKI.
/// I.e., every participant has some private decryption keys
/// and some public encryption keys from other participants.
/// All private keys of a participant will be stored in one session
/// and all public keys that the participant knows will be stored in another session.
/// For each participant, we collect both these session IDs in a global record.

type global_sess_ids = {
  pki: state_id;
  private_keys: state_id;
}

/// Similarly as for states,
/// we tag the keys that are used on the protocol level,
/// so that they can not be confused with other keys.
/// (TODO: rephrase this)

let key_tag = "P.Key"
