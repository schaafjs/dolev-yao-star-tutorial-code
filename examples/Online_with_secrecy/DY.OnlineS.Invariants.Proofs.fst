module DY.OnlineS.Invariants.Proofs

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified
open DY.Extend

open DY.OnlineS.Protocol
open DY.OnlineS.Invariants

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

val send_ping_invariant:
  alice:principal -> bob:principal -> keys_sid:state_id ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = send_ping alice bob keys_sid tr in
    trace_invariant tr_out
  ))
let send_ping_invariant alice bob keys_sid  tr =
  let (n_a, tr_rand) = mk_rand NoUsage (nonce_label alice bob) 32 tr in
  assert(trace_invariant tr_rand);

  let ping = Ping {p_alice = alice; p_n_a = n_a} in 
  match pk_enc_for alice bob keys_sid key_tag ping tr_rand with
  | (None, _) -> ()
  | (Some ping_encrypted, tr_enc) -> (
      assert(trace_invariant tr_enc);
      let (msg_ts, tr_msg) = send_msg ping_encrypted tr_enc in
      serialize_wf_lemma message (is_knowable_by (nonce_label alice bob) tr_rand) ping;
      bytes_invariant_pk_enc_for tr_rand alice bob keys_sid key_tag ping;
      assert(trace_invariant tr_msg);
      let st = SentPing {sp_bob = bob; sp_n_a = n_a} in
      let (sid, tr_sess) = start_new_session alice st tr_msg in
      assert(trace_invariant tr_sess)
  )

val decode_ping_proof:
  tr:trace ->
  bob:principal -> keys_sid:state_id ->
  msg:bytes ->
  Lemma
  (requires (
    trace_invariant tr
    /\ bytes_invariant tr msg
  ))
  (ensures (
    match decode_ping bob keys_sid msg tr with
    | (None, _) -> True
    | (Some png, _) -> (
        let n_a = png.p_n_a in
        bytes_invariant tr n_a /\
        is_knowable_by (nonce_label png.p_alice bob) tr n_a /\
        ( is_publishable tr n_a
        \/ (pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob) (serialize message (Ping png)))
        )
    )
  ))
let decode_ping_proof tr bob keys_sid msg =
    match decode_ping bob keys_sid msg tr with
    | (None, _) -> ()
    | (Some png, _) -> (
        bytes_invariant_pk_dec_with_key_lookup tr #message #parseable_serializeable_bytes_message bob keys_sid key_tag msg;
        let plain = serialize message (Ping png) in
        parse_wf_lemma message (bytes_invariant tr) plain;
        FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) plain
    )
  

val receive_ping_and_send_ack_invariant:
  bob:principal -> keys_sid:global_sess_ids -> ts:timestamp ->
  tr:trace ->
  Lemma
  ( requires trace_invariant tr
  )
  (ensures (
    let (_ , tr_out) = receive_ping_and_send_ack bob keys_sid ts tr in
    trace_invariant tr_out
  ))
let receive_ping_and_send_ack_invariant bob bob_keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _ ) -> ()
  | (Some msg, _) -> (
      match decode_ping bob bob_keys_sid.private_keys msg tr with
      | (None, _) -> ()
      | (Some png, _) -> (
           let n_a = png.p_n_a in
           let alice = png.p_alice in
          decode_ping_proof tr bob bob_keys_sid.private_keys msg;
          assert(is_knowable_by (nonce_label alice bob) tr n_a);
           let ack = Ack {a_n_a = n_a} in
           match pk_enc_for bob alice bob_keys_sid.pki key_tag ack tr with
           | (None, _) -> ()
           | (Some ack_encrypted, tr_ack) ->(
                assert(trace_invariant tr_ack);
                
                serialize_wf_lemma message (bytes_invariant tr) (Ping png);
                assert(bytes_invariant tr (serialize message (Ping png)));
                serialize_wf_lemma message (bytes_invariant tr) (ack);
                assert(bytes_invariant tr (serialize message ack));

                serialize_wf_lemma message (is_knowable_by (nonce_label alice bob) tr) (ack);
                bytes_invariant_pk_enc_for tr bob alice bob_keys_sid.pki key_tag ack;
                let (ack_ts, tr_msg) = send_msg ack_encrypted tr_ack in
                assert(trace_invariant tr_msg);
                let st = (SentAck {sa_alice = png.p_alice; sa_n_a = png.p_n_a}) in
                let (sess_id, tr_sess) = start_new_session bob st tr_msg in
                assert(trace_invariant tr_sess)
           )
      )
  )

val receive_ack_invariant:
  alice:principal -> keys_sid:state_id -> msg_ts:timestamp ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = receive_ack alice keys_sid msg_ts tr in
    trace_invariant tr_out
  ))
let receive_ack_invariant alice keys_sid msg_ts tr =
  match recv_msg msg_ts tr with
  | (None, _ ) -> ()
  | (Some msg, _) -> (
      match decode_ack alice keys_sid msg tr with
      | (None, _) -> ()
      | (Some ack, tr_ack) -> (
          let n_a = ack.a_n_a in
          assert(trace_invariant tr_ack);
          match lookup_state #state alice
    (fun st -> SentPing? st && (SentPing?.ping st).sp_n_a = n_a) tr with
          | (None, _) -> ()
          | (Some (SentPing st, sid), _) -> ()
  ))
