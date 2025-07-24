module DY.NSL.Protocol

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.NSL.Data

val send_msg1:
  (alice: principal) -> state_id -> (bob: principal) -> traceful(option(state_id & timestamp))

let send_msg1 alice alice_public_keys_sid bob =
  // Generate nonce
  let* n_a = gen_rand_labeled (nonce_label alice bob) in

  let init_event = Initiating{alice; bob; n_a} in
  trigger_event alice init_event;*  

  // Assemble, encrypt and finally send initial message
  let msg1 = Msg1 {alice; n_a} in
  let*? msg1_encrypted = pke_enc_for alice bob alice_public_keys_sid key_tag msg1 in
  let* msg1_ts = send_msg msg1_encrypted in

  // Store local state, logging that sending worked successfully
  let msg1_state = SentMsg1 {bob; n_a} in
  // traceful as it starts a new session (that is logged on the trace)
  let* sid = start_new_session alice msg1_state in

  return (Some (sid, msg1_ts))

val receive_msg1_and_send_msg2:
  (bob: principal) -> state_id -> state_id -> (msg1_ts: timestamp) -> traceful (option (state_id & timestamp))

let receive_msg1_and_send_msg2 bob bob_private_keys_sid bob_public_keys_sid msg1_ts=
  let*? msg1_encrypted = recv_msg msg1_ts in
  let*? msg1 = pke_dec_with_key_lookup #message_t bob bob_private_keys_sid key_tag msg1_encrypted in
  guard_tr (Msg1? msg1);*?

  let Msg1 msg1 = msg1 in
  let alice = msg1.alice in
  let n_a = msg1.n_a in

  let* n_b = gen_rand_labeled (nonce_label alice bob) in

  trigger_event bob (Responding1{alice; bob; n_a; n_b});*

  let msg2 = Msg2 {bob; n_a; n_b} in
  let*? msg2_encrypted = pke_enc_for bob alice bob_public_keys_sid key_tag msg2 in
  let* msg2_ts = send_msg msg2_encrypted in

  let msg2_state = SentMsg2 {alice; n_a; n_b} in
  let* sid_ = start_new_session bob msg2_state in

  return (Some (sid_, msg2_ts))

val receive_msg2_and_send_msg3:
  (alice: principal) -> state_id -> state_id -> (msg2_ts: timestamp) -> traceful (option (state_id & timestamp))

let receive_msg2_and_send_msg3 alice alice_private_keys_sid alice_public_keys_sid msg2_ts=
  let*? msg2_encrypted = recv_msg msg2_ts in
  let*? msg2 = pke_dec_with_key_lookup #message_t alice alice_private_keys_sid key_tag msg2_encrypted in
  guard_tr (Msg2? msg2);*?

  let Msg2 msg2 = msg2 in
  let bob = msg2.bob in
  let n_a = msg2.n_a in
  let n_b = msg2.n_b in

  // Check whether Alice has inited a session w/ principal bob and nonce n_a
  let*? (sid, current_state_alice) = lookup_state #state_t alice
    (fun current_state_alice -> 
          SentMsg1? current_state_alice
      && (SentMsg1?.sentmsg1 current_state_alice).n_a = n_a
      && (SentMsg1?.sentmsg1 current_state_alice).bob = bob
    ) in
  guard_tr(SentMsg1? current_state_alice);*?

  let msg3 = Msg3 {n_b} in
  let*? msg3_encrypted = pke_enc_for alice bob alice_public_keys_sid key_tag msg3 in
  let* msg3_ts = send_msg msg3_encrypted in

  // IMPORTANT: the state shall *always* contain all knowledge up until that point as set_state overwrites and does not append
  let msg3_state = SentMsg3 {bob; n_a; n_b} in
  set_state alice sid msg3_state;*

  return (Some (sid, msg3_ts))

val receive_msg3:
  (bob: principal) -> state_id -> (msg3_ts: timestamp) -> traceful (option state_id)

let receive_msg3 bob bob_private_keys_sid msg3_ts=
  let*? msg3_encrypted = recv_msg msg3_ts in
  let*? msg3 = pke_dec_with_key_lookup #message_t bob bob_private_keys_sid key_tag msg3_encrypted in
  guard_tr (Msg3? msg3);*?

  (*let alice = (RcvdMsg3?.receivedmsg3 current_state_bob).alice in
  let n_b = (RcvdMsg3?.receivedmsg3 current_state_bob).n_b in*)

  let Msg3 msg3 = msg3 in
  let n_b = msg3.n_b in
  //let alice = msg3.alice in

  let*? (sid_, current_state_bob) = lookup_state #state_t bob
    (fun current_state_bob ->
          SentMsg2? current_state_bob
      && (SentMsg2?.sentmsg2 current_state_bob).n_b = n_b
      //&& (SentMsg2?.sentmsg2 current_state_bob).alice = alice
    ) in
  guard_tr (SentMsg2? current_state_bob);*?

  let*? (sid, msg2) = lookup_state #state_t bob
    (fun msg2 -> 
          SentMsg2? msg2
      && (SentMsg2?.sentmsg2 msg2).n_b = n_b
    ) in
  guard_tr(SentMsg2? msg2);*?
  let n_a = (SentMsg2?.sentmsg2 msg2).n_a in
  let alice = (SentMsg2?.sentmsg2 msg2).alice in

  set_state bob sid_ (RcvdMsg3 {alice; n_a; n_b});*

  return (Some sid_)

// Helper function needed for the proofs
let nonce_label alice bob = join (principal_label alice) (principal_label bob)
