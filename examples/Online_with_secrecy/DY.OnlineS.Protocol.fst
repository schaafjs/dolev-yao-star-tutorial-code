module DY.OnlineS.Protocol

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

/// The "Online?" protocol
/// 
/// An extension of the simple Two Message protocol:
/// the two messages are now (asymmetrically) encrypted
///
/// A -> B: enc{Ping (A, n_A)}_B
/// B -> A: enc{Ack n_A}_A

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

let key_tag = "P.Key"

(*** The Protocol ***)

let nonce_label alice bob = join (principal_label alice) (principal_label bob)

/// Alice sends the first message to Bob:
/// * Alice generates a new nonce [n_a]
/// * encrypts the message (Alice, n_a) for Bob
/// * sends the encrypted message
/// * stores n_a and Bob in a state (in a new session)
/// The step returns the ID of the new state
/// and the timestamp of the message on the trace
/// The step fails (returns None), if
/// encryption was not successful, i.e.,
/// Alice does not have a public key of Bob.

val send_ping: principal -> principal -> state_id -> traceful (option (state_id & timestamp))
let send_ping alice bob keys_sid =
  // TODO: explain high-level idea of "intended readers"
  let* n_a = gen_rand_labeled (nonce_label alice bob) in
  
  let ping = Ping {p_alice = alice; p_n_a = n_a} in 

  // encrypt the message for bob
  let*? ping_encrypted = pk_enc_for alice bob keys_sid key_tag ping in
  let* msg_ts = send_msg ping_encrypted in

  let ping_state = SentPing {sp_bob = bob; sp_n_a = n_a} in
  let* sid = start_new_session alice ping_state in

  return (Some (sid, msg_ts))


/// Bob receives the first messages and replies:
/// * read the message from the trace
/// * decrypt the message to (Alice, n_a)
/// * encrypt the reply (n_a) for Alice
/// * send the encrypted reply
/// * store n_a and Alice in a state in a new session
/// The step returns the ID of the new state
/// and the timestamp of the reply on the trace.
/// The step fails, if one of
/// * decryption fails
/// * the message is not of the right type, i.e., not a first message
/// * encryption fails

/// Decrypting the message (Step 2 from above) is pulled out to a separate function.
/// The function
/// * decrypts the message
/// * checks that the message is of the right type (a Ping)
/// * returns the content of the message
/// The function fails if decryption fails.

val decode_ping : principal -> state_id -> bytes -> traceful (option ping_t)
let decode_ping bob keys_sid msg =
  // try to decrypt the message with
  // a private key of bob with the protocol key tag
  // (fails, if no such key exists)
  let*? png = pk_dec_with_key_lookup #message bob keys_sid key_tag msg in
  
  // check that the decrypted message is of the right type
  // (otherwise fail)
  guard_tr (Ping? png);*?

  // return the content of the message 
  // (i.e., strip the Ping constructor)
  return (Some (Ping?.ping png))

/// Now the actual receive and reply step
/// using the decode function
val receive_ping_and_send_ack: principal -> global_sess_ids -> timestamp -> traceful (option (state_id & timestamp))
let receive_ping_and_send_ack bob global_sids msg_ts =
  let*? msg = recv_msg msg_ts in
  // decode the received expected ping
  let*? png = decode_ping bob global_sids.private_keys msg in

  let n_a = png.p_n_a in
  let alice = png.p_alice in

  let ack = Ack {a_n_a = n_a} in
  // encrypt the reply for alice
  let*? ack_encrypted = pk_enc_for bob alice global_sids.pki key_tag ack in
  let* ack_ts = send_msg ack_encrypted in
  
  let* sess_id = start_new_session bob (SentAck {sa_alice = alice; sa_n_a = n_a}) in
  
  return (Some (sess_id, ack_ts))


/// Alice receives the reply from Bob:
/// * read the message from the trace
/// * decrypt the message to (n_a)
/// * check if Alice previously sent n_a in some session
/// * store completion of this session in a new state
/// Returns the ID of the session that is marked as completed.
/// The step fails, if one of
/// * decryption fails
/// * the message is not of the right type, i.e., not a reply
/// * there is no prior session related to n_a


/// Again, we pull out decryption of the message (Step 2):
/// * decrypt the message
/// * check that the message is of the Ack type
/// Returns the content of the reply.
/// Fails if decryption fails.

val decode_ack : principal -> state_id -> bytes -> traceful (option ack)
let decode_ack alice keys_sid cipher =
  // try to decrypt the message with
  // a private key of alice with the protocol tag
  let*? ack = pk_dec_with_key_lookup #message alice keys_sid key_tag cipher in

  // check that the decrypted message is of the Ack type
  guard_tr (Ack? ack);*?

  // return the content of the message
  return (Some (Ack?.ack ack))

/// The actual protocol step using the decode function
val receive_ack: principal -> state_id -> timestamp -> traceful (option state_id)
let receive_ack alice keys_sid ack_ts =
  let*? msg = recv_msg ack_ts in
  // decode the received expected ack
  let*? ack = decode_ack alice keys_sid msg in

  let n_a = ack.a_n_a in
  // try to find a previous session of alice that
  // * is in a SentPing state and
  // * the stored nonce is the received nonce
  let*? (st, sid) = lookup_state #state alice
    (fun st -> SentPing? st && (SentPing?.ping st).sp_n_a = n_a)
    in
  guard_tr(SentPing? st);*?
  let bob = (SentPing?.ping st).sp_bob in

  set_state alice sid (ReceivedAck {ra_bob=bob; ra_n_a = n_a});*

  return (Some sid)
