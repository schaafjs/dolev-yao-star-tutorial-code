module DY.TwoMessage.Protocol

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

/// A simple 2 message protocol
///
/// A -> B: Ping (A, n_A)
/// B -> A: Ack n_A

(*** Message Type ***)

/// for each of the two messages we define an abstract message type

[@@ with_bytes bytes] // ignore this line for now
type ping_t = {
  alice: principal;
  n_a : bytes;
}

[@@ with_bytes bytes] // ignore this line for now
type ack_t = {
  n_a : bytes;
}

/// the overall abstract message type
/// (consisting of constructors for the two messages
/// and using the above abstract types for each of them)

[@@ with_bytes bytes] // ignore this line for now
type message_t =
  | Ping: ping_t -> message_t
  | Ack: ack_t -> message_t


/// We use Comparse to generate the corresponding message formats.
/// I.e., we don't need to write parsing and serializing by hand
///
/// for this we need the `[@@ with_bytes bytes]` annotation for the message types above
///
/// We are not going into the details of how Comparse works.


/// We let Comparse generate a parser `ps_ping_t` for the abstract `ping_t` type

%splice [ps_ping_t] (gen_parser (`ping_t))

/// ... and the same for the other abstract message types

%splice [ps_ack_t] (gen_parser (`ack_t))

%splice [ps_message_t] (gen_parser (`message_t))

/// With the above parsers, we can make our `message` type an instance of
/// Comparse's `parseable_serializeable` class.
/// Again, the details are not important here,
/// but this is the step that enables us to call
/// `parse message buff` and `serialize message msg`
/// to translate between bytes and our abstract message type.

instance parseable_serializeable_bytes_message_t: parseable_serializeable bytes message_t = mk_parseable_serializeable ps_message_t


(*** State Type ***)

/// As for the messages we define abstract state types
/// for the three states stored by Alice and Bob after each step of the protocol.

[@@ with_bytes bytes]
type sent_ping_t = {
  bob : principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type sent_ack_t = {
  alice: principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type received_ack_t = {
  bob : principal;
  n_a : bytes;
}

[@@ with_bytes bytes]
type state_t = 
  | SentPing: (ping:sent_ping_t) -> state_t
  | SentAck: (ack:sent_ack_t) -> state_t
  | ReceivedAck: (rack:received_ack_t) -> state_t

/// As for messages, we use Comparse to generate
/// a parser and serializer for our abstract state types.

%splice [ps_sent_ping_t] (gen_parser (`sent_ping_t))
%splice [ps_sent_ack_t] (gen_parser (`sent_ack_t))
%splice [ps_received_ack_t] (gen_parser (`received_ack_t))
%splice [ps_state_t] (gen_parser (`state_t))

/// Now, we can call
/// `parse state buff` and `serialize state st`
/// to translate between bytes and the abstract state type.

instance parseable_serializeable_bytes_state_t: parseable_serializeable bytes state_t = mk_parseable_serializeable ps_state_t

/// We tag our protocol level states,
/// so that they are distinguishable from any internal DY* states. 

instance local_state_state: local_state state_t = {
  tag = "P.State";
  format = parseable_serializeable_bytes_state_t;
}

(*** The Protocol ***)

/// Alice sends the first message to Bob:
/// * Alice generates a new nonce [n_a]
/// * sends the message (Alice, n_a) (intended for Bob)
/// * stores n_a and Bob in a state (in a new session)
/// The step returns the ID of the new state
/// and the timestamp of the message on the trace

val send_ping: principal -> principal -> traceful (state_id & timestamp)
let send_ping alice bob =
  // generate a new nonce
  let* n_a = gen_rand in

  // the abstract message (alice, n_a)
  let ping = Ping {alice = alice; n_a = n_a} in 
  // send the message (serialize abstract to bytes first!)
  let* msg_ts = send_msg (serialize message_t ping) in

  // the abstract new state (bob, n_a)
  let ping_state = SentPing {bob = bob; n_a = n_a} in
  // start a new session with this new state
  let* sid = start_new_session alice ping_state in

  // return the ID of the new session and the timestamp of the message
  return (sid, msg_ts)


/// Bob receives the first messages and replies:
/// * read the message (Alice, n_a) from the trace
/// * send the reply (n_a) (intended for Alice)
/// * store n_a and Alice in a state in a new session
/// The step returns the ID of the new state
/// and the timestamp of the reply on the trace.
/// The step fails, if
/// the message is not of the right type, i.e., not a first message.

val receive_ping_and_send_ack: principal -> timestamp -> traceful (option (state_id & timestamp))
let receive_ping_and_send_ack bob msg_ts =
  // receive the message
  let*? msg = recv_msg msg_ts in 
  // this returns bytes, so we need to translate to our abstract type:
  let*? png_ = return (parse message_t msg) in
  // check that the received message is of the right type
  // (the whole step fails, if the message is not a Ping)
  guard_tr (Ping? png_);*?

  // read the data (alice and n_a) from the received message
  let Ping png = png_ in // this "removes" the Ping constructor from png_
  let alice = png.alice in
  let n_a = png.n_a in

  // the abstract reply (n_a)
  let ack = Ack { n_a} in
  // send the reply (serialize abstract to bytes first!)
  let* ack_ts = send_msg (serialize message_t ack) in

  // the abstract new state storing alice and n_a from the message
  let ack_state = SentAck {alice; n_a} in
  // start a new session wit this new state
  let* sess_id = start_new_session bob ack_state in

  // return the ID of the new session and the timestamp of the message
  return (Some (sess_id, ack_ts))


/// Alice receives the reply from Bob:
/// * read the message (n_a) from the trace
/// * check if Alice previously sent n_a in some session
/// * store completion of this session in a new state
/// Returns the ID of the session that is marked as completed.
/// The step fails, if
/// * the message is not of the right type, i.e., not a reply
/// * there is no prior session related to n_a

val receive_ack: principal -> timestamp -> traceful (option state_id)
let receive_ack alice ack_ts =
  // receive the message and translate to abstract message type
  let*? ack = recv_msg ack_ts in
  let*? ack = return (parse message_t ack) in
  // check that the message is a reply
  // (otherwise this step fails)
  guard_tr (Ack? ack);*?

  // read the data (n_a) from the message
  let Ack ack = ack in
  let n_a = ack.n_a in

  // check if alice has a previous session where
  // * she startet a run
  // * with the nonce n_a (the one received from Bob)
  // (the step fails, if no such session exists)
  let*? (st, sid) = lookup_state #state_t alice
    (fun st -> 
          SentPing? st // st is a state of type SentPing 
      && (SentPing?.ping st).n_a = n_a // the nonce stored in st is n_a
    ) in
  guard_tr(SentPing? st);*?
  // access the name of Bob in the stored state
  let bob = (SentPing?.ping st).bob in

  // mark this session as completed by
  // setting a new state
  set_state alice sid (ReceivedAck {bob; n_a});*

  // return the ID of the completed session
  return (Some sid)
