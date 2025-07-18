module DY.TwoMessage.Protocol

open Comparse
open DY.Core
open DY.Lib

// Manually copied from tutorial-code repo to utils/ for now
open DY.Simplified
open DY.Extend

open DY.TwoMessage.Data

// Sending the ping msg
val send_ping:
  (alice: principal) -> (bob: principal) ->
  traceful (state_id & timestamp)

let send_ping alice bob =
  // Generate nonce
  let* n_a = gen_rand in

  // Assemble, serialize and then send ping
  let ping = Ping {alice = alice; n_a = n_a} in
  let ping_wire = serialize message_t ping in
  let* msg_ts = send_msg ping_wire in

  // Store the local state and start new session (traceful, serializing happens internally)
  let ping_state = SentPing {bob = bob; n_a = n_a} in
  let* sid = start_new_session alice ping_state in

  return (sid, msg_ts)

// Receiving the ping msg and responding w/ an ACK
val receive_ping_and_send_ack:
  (bob:principal) -> (ping_ts:timestamp) ->
  traceful (option (state_id & timestamp))

let receive_ping_and_send_ack bob msg_ts=
  // Receive, parse and verify that it is actually a ping msg 
  let*? msg = recv_msg msg_ts in
  let*? png = return (parse message_t msg) in
  guard_tr (Ping? png);*?

  // Msg is actually a ping, access it
  let Ping png = png in // removes Ping constructor to allow access to the field values
  let alice = png.alice in
  let n_a = png.n_a in

  // Sending the ACK
  let ack = Ack {n_a} in
  let* ack_ts = send_msg (serialize message_t ack) in

  let ack_state = SentAck {alice; n_a} in
  let* sess_id = start_new_session bob ack_state in

  return (Some (sess_id, ack_ts))

// Receiving an ACK
val receive_ack:
  (alice: principal) -> (ack_ts: timestamp) ->
  traceful (option state_id)

let receive_ack alice ack_ts =
  let*? ack = recv_msg ack_ts in
  let*? ack = return (parse message_t ack) in
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
