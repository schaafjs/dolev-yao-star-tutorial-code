module DY.Simplified

open Comparse
open DY.Core
open DY.Lib

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
  let* nonce = mk_rand PkNonce (principal_label bob) 32 in
  return ( Some (pk_enc pk_bob nonce (serialize a plaintext)))

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
