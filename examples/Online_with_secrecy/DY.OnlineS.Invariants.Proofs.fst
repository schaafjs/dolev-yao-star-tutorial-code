module DY.OnlineS.Invariants.Proofs

open Comparse
open DY.Core
open DY.Lib

open DY.Simplified

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
