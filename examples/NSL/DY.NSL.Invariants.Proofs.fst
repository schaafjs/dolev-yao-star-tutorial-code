module DY.NSL.Invariants.Proofs

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.NSL.Data
open DY.NSL.Protocol
open DY.NSL.Invariants

// Taken from OnlineS
#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100' --query_stats"


val send_msg1_invariant:
  alice:principal -> bob:principal -> alice_public_keys_sid:state_id -> tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = send_msg1 alice alice_public_keys_sid bob tr in
    trace_invariant tr_out
  ))

let send_msg1_invariant alice bob alice_public_keys_sid tr =
  let (n_a, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
  let msg1 = Msg1 {alice; n_a} in
  serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_rand) msg1;
  match pke_enc_for_is_publishable tr_rand alice bob alice_public_keys_sid key_tag msg1 with
  | (None, tr_enc) -> (
    assert(trace_invariant tr_rand);
    assert(tr == tr_rand)
  )
  | (Some msg1_encrypted, tr_enc) -> (
    assert(trace_invariant tr_enc);
    let (msg_ts, tr_msg) = send_msg msg1_encrypted tr_enc in
    
  )

val receive_msg1_and_send_msg2:
  alice:principal -> bob:principal -> bob_public_keys_sid:state_id -> bob_private_keys_sid:state_id -> msg1_ts:timestamp -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = receive_msg1_and_send_msg2 bob bob_private_keys_sid bob_public_keys_sid msg1_ts in
    trace_invariant tr_out
  ))

  let receive_msg1_and_send_msg2 alice bob bob_public_keys_sid bob_private_keys_sid msg1_ts tr = (admit())

  val receive_msg2_and_send_msg3:
    alice:principal -> bob:principal -> alice_public_keys_sid:state_id -> alice_private_keys_sid:state_id -> msg2_ts:timestamp -> tr:trace ->
    Lemma
    (requires trace_invariant tr)
    (ensures (
      let (_, tr_out) = receive_msg2_and_send_msg3 alice bob alice_private_keys_sid alice_public_keys_sid msg2_ts in
      trace_invariant tr_out
    ))

  let receive_msg2_and_send_msg3 alice bob alice_public_keys_sid alice_private_keys_sid msg2_ts tr = (admit())

  val receive_msg3:
    alice:principal -> bob:principal -> bob_public_keys_sid:state_id -> bob_private_keys_sid:state_id -> msg3_ts:timestamp -> tr:trace ->
    Lemma
    (requires trace_invariant tr)
    (ensures (
      let (_, tr_out) = receive_msg3 alice bob bob_public_keys_sid bob_private_keys_sid msg3_ts in
      trace_invariant tr_out
    ))

  let receive_msg3 alice bob bob_public_keys_sid bob_private_keys_sid msg3_ts tr = (admit())
