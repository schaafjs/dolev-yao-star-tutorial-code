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

#push-options "--fuel 3 --ifuel 3 --z3rlimit 50"
let send_msg1_invariant alice bob alice_public_keys_sid tr = (
  let (msg_ts, tr_out) = send_msg1 alice alice_public_keys_sid bob tr in
  match msg_ts with
  | None -> admit()
  | Some(_) -> (
    let (n_a, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr in
    assert(is_secret (nonce_label alice bob) tr_rand n_a);
    let init_event = Initiating{alice; bob; n_a} in
    let (_, tr_event) = trigger_event alice init_event tr_rand in
    assert(trace_invariant tr_event);
    let msg1 = Msg1 {alice; n_a} in
    let (Some(msg1_encrypted), tr_enc) = pke_enc_for alice bob alice_public_keys_sid key_tag msg1 tr_event in
    assert(trace_invariant tr_enc);
    assert(is_well_formed _ (bytes_invariant tr_event) msg1);
    assert(is_well_formed _ (is_knowable_by (long_term_key_label bob) tr_event) msg1);
    assert(is_well_formed _ (is_knowable_by (long_term_key_label alice) tr_event) msg1);
    assert(has_pki_invariant);
    assume(is_publishable tr msg1_encrypted);
    let (msg1_ts, tr_send) = send_msg msg1_encrypted tr_enc in
    assert(trace_invariant tr_send);
    let msg1_state = SentMsg1 {bob; n_a} in
    let (sid, tr_st) = start_new_session alice msg1_state tr_send in
    assert(is_secret (nonce_label alice bob) tr_send n_a);
    assert(trace_invariant tr_st);
    assert(tr_st == tr_out);
    ()
  )
)

val receive_msg1_and_send_msg2:
  alice:principal -> bob:principal -> bob_public_keys_sid:state_id -> bob_private_keys_sid:state_id -> msg1_ts:timestamp -> tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (_, tr_out) = receive_msg1_and_send_msg2 bob bob_private_keys_sid bob_public_keys_sid msg1_ts tr in
    trace_invariant tr_out
  ))

  let receive_msg1_and_send_msg2 alice bob bob_public_keys_sid bob_private_keys_sid msg1_ts tr = admit()

  val receive_msg2_and_send_msg3:
    alice:principal -> bob:principal -> alice_public_keys_sid:state_id -> alice_private_keys_sid:state_id -> msg2_ts:timestamp -> tr:trace ->
    Lemma
    (requires trace_invariant tr)
    (ensures (
      let (_, tr_out) = receive_msg2_and_send_msg3 alice alice_private_keys_sid alice_public_keys_sid msg2_ts tr in
      trace_invariant tr_out
    ))

  let receive_msg2_and_send_msg3 alice bob alice_public_keys_sid alice_private_keys_sid msg2_ts tr = (
    let (msg_ts, tr_out) = receive_msg2_and_send_msg3 alice alice_private_keys_sid alice_public_keys_sid msg2_ts tr in
    assert(trace_invariant tr);
    match msg_ts with
    | None -> admit()
    | Some(_) -> (
      let (Some(msg2_encrypted), tr_rec) = recv_msg msg2_ts tr in
      assert(trace_invariant tr_rec);
      let (Some(msg2), tr_dec) = pke_dec_with_key_lookup #message_t alice alice_private_keys_sid key_tag msg2_encrypted tr_rec in
      assert(trace_invariant tr_dec);
      // Should succeed since we are in the Some case
      assert(Msg2? msg2);
      let Msg2 msg2 = msg2 in
      let bob = msg2.bob in
      let n_a = msg2.n_a in
      let n_b = msg2.n_b in
      assert(is_knowable_by (nonce_label alice bob) tr_dec n_b);
      let (Some(sid, current_state_alice), tr_lookup) = lookup_state #state_t alice
        (fun current_state_alice -> 
              SentMsg1? current_state_alice
          && (SentMsg1?.sentmsg1 current_state_alice).n_a = n_a
          && (SentMsg1?.sentmsg1 current_state_alice).bob = bob
        ) tr_rec in
      assert(trace_invariant tr_lookup);
      assert(SentMsg1? current_state_alice);
      let msg3 = Msg3 {n_b} in
      let (Some(msg3_encrypted), tr_enc) = pke_enc_for alice bob alice_public_keys_sid key_tag msg3 tr_rec in
      assert(trace_invariant tr_enc);
      let (msg3_ts, tr_send) = send_msg msg3_encrypted tr_enc in
      assume(is_publishable tr_enc msg3_encrypted);
      assert(trace_invariant tr_send);
      let msg3_state = SentMsg3 {bob; n_a; n_b} in
      let (_, tr_st) = set_state alice sid msg3_state tr_send in
      assert(is_knowable_by (nonce_label alice bob) tr n_b);
      assert(trace_invariant tr_st);
      ()
    )
  )

  val receive_msg3:
    alice:principal -> bob:principal -> bob_public_keys_sid:state_id -> bob_private_keys_sid:state_id -> msg3_ts:timestamp -> tr:trace ->
    Lemma
    (requires trace_invariant tr)
    (ensures (
      let (_, tr_out) = receive_msg3 alice bob bob_public_keys_sid bob_private_keys_sid msg3_ts in
      trace_invariant tr_out
    ))

  let receive_msg3 alice bob bob_public_keys_sid bob_private_keys_sid msg3_ts tr = ()
