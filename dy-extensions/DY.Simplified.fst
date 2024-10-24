module DY.Simplified

open Comparse
open DY.Core
open DY.Lib

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

val start_new_session:
  #a:Type -> {| local_state a |} ->
  principal -> a ->
  traceful state_id
let start_new_session prin cont =
  let* sid = new_session_id prin in
  set_state prin sid cont;*
  return sid

val pk_enc_for:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> principal ->
  state_id -> string -> 
  a -> 
  traceful (option bytes)
let pk_enc_for #a alice bob key_sid key_tag plaintext =
  let*? pk_bob = get_public_key alice key_sid (LongTermPkEncKey key_tag) bob in
  let* nonce = mk_rand PkNonce (principal_label alice) 32 in
  return ( Some (pk_enc pk_bob nonce (serialize a plaintext)))

val bytes_invariant_pk_enc_for:
  {|protocol_invariants|}->
  tr:trace ->
  #a:Type -> {|parseable_serializeable bytes a|} ->
  alice:principal -> bob:principal ->
  alice_pki_sid:state_id ->
  key_tag:string ->
  msg:a ->
  Lemma
  (requires
      trace_invariant tr
    /\ has_pki_invariant
    /\ is_knowable_by ( principal_label alice `join` principal_label bob ) tr (serialize a msg)
    /\ pkenc_pred.pred tr (long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob) (serialize a msg)
  )
  (ensures (
    match pk_enc_for alice bob alice_pki_sid key_tag msg tr with
    | (None, _) -> True
    | (Some cipher, tr_out) -> 
        is_publishable tr_out cipher
  ))
let bytes_invariant_pk_enc_for #pinvs tr #a alice bob alice_pki_sid key_tag msg =
  match pk_enc_for alice bob alice_pki_sid key_tag msg tr with
  | (None, _) -> ()
  | (Some cipher, tr_out) -> (
      let pk_type = LongTermPkEncKey key_tag in
      let (Some pk_bob, _) = get_public_key alice alice_pki_sid pk_type bob tr in
      let (nonce, tr_nonce) = mk_rand PkNonce (principal_label alice) 32 tr in
      let msg = serialize #bytes a msg in
      assert(is_public_key_for tr_out pk_bob pk_type bob);
      let sk_usg = long_term_key_type_to_usage (LongTermPkEncKey key_tag) bob in
      pkenc_pred.pred_later tr tr_out sk_usg msg
)  

val pk_dec_with_key_lookup:
  #a:Type -> {| parseable_serializeable bytes a |} ->
  principal -> 
  state_id -> string ->
  bytes ->
  traceful (option a)
let pk_dec_with_key_lookup #a prin keys_sid key_tag cipher =
  let*? sk_a = get_private_key prin keys_sid (LongTermPkEncKey key_tag) in
  let*? plaintext = return (pk_dec sk_a cipher) in 
  // guard_tr ( Some? (parse a plaintext));*?
  return (parse a plaintext)
