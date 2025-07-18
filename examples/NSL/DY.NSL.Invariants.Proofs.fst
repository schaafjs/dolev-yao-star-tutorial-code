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
//#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

// Customized options
#set-options "--fuel 30 --ifuel 5 --z3rlimit 100  --z3cliopt 'smt.qi.eager_threshold=100'"

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
  let (_, tr_out) = send_msg1 alice alice_public_keys_sid bob tr_rand in
  assert(trace_invariant tr_rand);
  //assert(trace_invariant tr_out);
  // TODO: may mismatch with gen_rand
  
  //assert(trace_invariant tr_rand);
  // The following line does not change the trace
  let msg1 = Msg1 {alice; n_a} in
  match pke_enc_for alice bob alice_public_keys_sid key_tag msg1 tr_rand with
  | (None, tr_enc) -> (
    assert(trace_invariant tr_rand);
    assert(trace_invariant tr_enc);
    assert(has_pki_invariant);
    serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_enc) msg1;
    serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_rand) msg1;
    assume(tr_enc == tr_rand);
    // This is the final goal for this case. Given that the encryption fails, tr_enc == tr_rand should also hold. Maybe we can use this to our advantage somehow. We cannot prove it as is however...
    // TODO: get rid of the assumes
    assume(tr == tr_enc);
    admit()
  )
    // encryption failed, trace not interacted with
  | (Some msg1_encrypted, tr_enc) -> (
    assert(trace_invariant tr_enc);
    let (msg_ts, tr_msg) = send_msg msg1_encrypted tr_enc in
    assert(has_pki_invariant);
    serialize_wf_lemma message_t (is_knowable_by (nonce_label alice bob) tr_rand) msg1;
    let (pk_bob_opt, _) = get_public_key alice alice_public_keys_sid (LongTermPkeKey key_tag) bob tr_rand in
    assert(None? pk_bob_opt \/
      pke_pred.pred tr_rand (long_term_key_type_to_usage (LongTermPkeKey key_tag) bob) (Some?.v pk_bob_opt) (serialize message_t msg1)
    );
    pke_enc_for_is_publishable tr_rand alice bob alice_public_keys_sid key_tag msg1;
    assert(trace_invariant tr_msg);

    let st = SentMsg1 {bob; n_a} in
    let (sid, tr_sess) = start_new_session alice st tr_msg in

    assert(state_predicate_nsl.pred tr_msg alice sid st);
    assert(trace_invariant tr_sess);
    admit()
  )

  val receive_msg1_and_send_msg2:
    alice:principal -> bob:principal -> bob_public_keys_sid:state_id -> bob_private_keys_sid:state_id -> msg1_ts:timestamp -> tr:trace ->
    Lemma
    (requires trace_invariant tr)
    (ensures (
      let (_, tr_out) = receive_msg1_and_send_msg2 bob bob_private_keys_sid bob_public_keys_sid msg1_ts in
      trace_invariant tr_out
    ))


  let receive_msg1_and_send_msg2 alice bob bob_public_keys_sid bob_private_keys_sid msg1_ts tr = (
    // receive msg1
    let*? msg1 = recv_msg msg1_ts in
    // decrypt ...
    let*? msg1_d = pke_dec_with_key_lookup #message_t bob bob_private_keys_sid key_tag msg1 in
    // ... check welformedness of msg1 ...
    guard_tr (Msg1? msg1);*?
    // ... and deconstruct
    let Msg1 msg1 = msg1 in
    let alice = msg1.alice in
    let n_a = msg1.n_a in
    // prepare  msg2
    let (n_b, tr_rand) = gen_rand_labeled (nonce_label alice bob) tr_dec in
    let (_, tr_out) = send_msg1 alice alice_public_keys_sid bob tr_rand in
    // create msg2
    let msg2 = Msg2 {bob; n_a; n_b} in
    // encrypt msg2
    // send msg2
    admit()
    )

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
