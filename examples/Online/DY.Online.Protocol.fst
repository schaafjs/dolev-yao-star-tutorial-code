module DY.Online.Protocol

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
  | Ping: (msg:ping_t) -> message
  | Ack: (msg:ack) -> message


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
  | SentAck: sent_ack -> state
  | ReceivedAck: received_ack -> state

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

(** TODO **)

instance local_state_state: local_state state = {
  tag = "P.State";
  format = parseable_serializeable_bytes_state;
}

(*** The Protocol ***)

val send_ping: principal -> principal -> traceful (state_id & timestamp)
let send_ping alice bob =
  // TODO: use public/secret for this label? 
  // or already explain high-level idea of "intended readers"?
  let* n_a = mk_rand NoUsage (join (principal_label alice) (principal_label bob)) 32 in
  let ping = Ping {p_alice = alice; p_n_a = n_a} in 
  let* msg_ts = send_msg (serialize message ping) in
  // TODO: add `start_new_session` to API
  // hiding `new_session_id`
  let* sess_id = new_session_id alice in
  set_state alice sess_id (SentPing {sp_bob = bob; sp_n_a = n_a} <: state);*
  return (sess_id, msg_ts)


val decode_ping : bytes -> option ping_t
let decode_ping msg =
  let? png = parse message msg in
  guard (Ping? png);?
  assert(Ping? png);
  Some (Ping?.msg png)

val receive_ping_and_send_ack: principal -> timestamp -> traceful (option state_id)
let receive_ping_and_send_ack bob msg_ts =
  let*? msg = recv_msg msg_ts in
  let*? png = return (decode_ping msg) in
  let* sess_id = new_session_id bob in
  set_state bob sess_id (SentAck {sa_alice = png.p_alice; sa_n_a = png.p_n_a});*
  return (Some sess_id)


val receive_ping_and_send_ack_: principal -> timestamp -> traceful (option state_id)
let receive_ping_and_send_ack_ bob msg_ts =
  let*? msg = recv_msg msg_ts in
  match*? return (parse message msg) with
  | Ping png -> (
      let* sess_id = new_session_id bob in
      set_state bob sess_id (SentAck {sa_alice = png.p_alice; sa_n_a = png.p_n_a});*
      return (Some sess_id)
  )
  | _ -> return None



val receive_ping_and_send_ack___: principal -> timestamp -> traceful (option (state_id & timestamp))
let receive_ping_and_send_ack___ bob msg_ts =
  let*? msg = recv_msg msg_ts in
  let*? png_ = return (parse message msg) in
  guard_tr (Ping? png_);*?
  let Ping png = png_ in
  let n_a = png.p_n_a in
  let ack = Ack {a_n_a = n_a} in
  let* ack_ts = send_msg (serialize message ack) in
  let* sess_id = new_session_id bob in
  set_state bob sess_id (SentAck {sa_alice = png.p_alice; sa_n_a = png.p_n_a});*
  return (Some (sess_id, ack_ts))


val receive_ack: principal -> timestamp -> traceful (option state_id)
let receive_ack alice ack_ts =
  let*? ack = recv_msg ack_ts in
  let*? ack = return (parse message ack) in
  guard_tr (Ack? ack);*?
  let Ack ack = ack in

  let*? (st, sid) = lookup_state #state alice
    (fun st -> SentPing? st && (SentPing?.ping st).sp_n_a = ack.a_n_a)
    in
  guard_tr(SentPing? st);*?
  let SentPing ping = st in

  set_state alice sid (ReceivedAck {ra_bob=ping.sp_bob; ra_n_a = ack.a_n_a});*

  return (Some sid)
