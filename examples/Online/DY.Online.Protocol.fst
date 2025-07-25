module DY.Online.Protocol

open Comparse
open DY.Core
open DY.Lib

// Manually copied from tutorial-code repo to `utils/` for now
open DY.Simplified
open DY.Extend

open DY.Online.Data

// Sending the ping msg
val send_ping:
  (alice: principal) -> state_id -> (bob: principal) ->
  traceful (option (state_id & timestamp))

let send_ping alice alice_public_keys_sid bob =
  // Generate nonce
  let* n_a = gen_rand in

  // Assemble, encrypt and then send ping
  let ping = Ping {alice = alice; n_a = n_a} in
  let*? ping_encrypted = pke_enc_for alice bob alice_public_keys_sid key_tag ping in
  let* msg_ts = send_msg ping_encrypted in

  // Store the local state and start new session (traceful, serializing happens internally)
  let ping_state = SentPing {bob = bob; n_a = n_a} in
  let* sid = start_new_session alice ping_state in

  return (Some (sid, msg_ts))

// Receiving the ping msg and responding w/ an ACK
val receive_ping_and_send_ack:
  (bob:principal) -> state_id -> state_id -> (ping_ts:timestamp) ->
  traceful (option (state_id & timestamp))

let receive_ping_and_send_ack bob bob_private_keys_sid bob_public_keys_sid msg_ts=
  // Receive, parse and verify that it is actually a ping msg 
  let*? msg = recv_msg msg_ts in
  let*? png = pke_dec_with_key_lookup #message_t bob bob_private_keys_sid key_tag msg in
  
  // Ensures that png is of type Ping, fails otherwise (causing the whole function to fail)
  guard_tr (Ping? png);*?

  // Msg is actually a ping, access it
  let Ping png = png in // removes Ping constructor to allow access to the field values
  let alice = png.alice in
  let n_a = png.n_a in

  // Sending the ACK
  let ack = Ack {n_a} in
  let*? ack_encrypted = pke_enc_for bob alice bob_public_keys_sid key_tag ack in
  let* ack_ts = send_msg ack_encrypted in

  let ack_state = SentAck {alice; n_a} in
  let* sess_id = start_new_session bob ack_state in

  return (Some (sess_id, ack_ts))

// Receiving an ACK
val receive_ack:
  (alice: principal) -> state_id -> (ack_ts: timestamp) ->
  traceful (option state_id)

let receive_ack alice alice_private_keys_sid ack_ts =
  let*? msg = recv_msg ack_ts in
  let*? ack = pke_dec_with_key_lookup #message_t alice alice_private_keys_sid key_tag msg in
  guard_tr (Ack? ack);*?

  let Ack ack = ack in
  let n_a = ack.n_a in

  let*? (sid, st) = lookup_state #state_t alice
    (fun st ->
          SentPing? st
      && (SentPing?.ping st).n_a = n_a
    ) in
  guard_tr(SentPing? st);*?
  let bob = (SentPing?.ping st).bob in

  set_state alice sid (ReceivedAck {bob; n_a});*

  return (Some sid)
