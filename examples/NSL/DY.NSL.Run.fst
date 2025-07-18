module DY.NSL.Run

open DY.Core
open DY.Lib

open DY.Simplified

open DY.NSL.Data
open DY.NSL.Protocol

open DY.NSL.Run.Printing

let run () : traceful (option unit) = 
  let _ = IO.debug_print_string "************* Trace *************\n" in

  let alice = "Alice" in
  let bob = "Bob" in

  // Keys
  let* alice_private_keys_sid = initialize_private_keys alice in
  let* alice_public_keys_sid = initialize_pki alice in
  let* bob_private_keys_sid = initialize_private_keys bob in
  let* bob_public_keys_sid = initialize_pki bob in
  generate_private_pke_key alice alice_private_keys_sid key_tag;*
  generate_private_pke_key bob bob_private_keys_sid key_tag;*
  install_public_pke_key alice alice_public_keys_sid key_tag bob bob_private_keys_sid;*
  install_public_pke_key bob bob_public_keys_sid key_tag alice alice_private_keys_sid;*
  let*? (alice_sid, msg1_ts) = send_msg1 alice alice_public_keys_sid bob in
  let*? (bob_sid, msg2_ts) = receive_msg1_and_send_msg2 bob bob_private_keys_sid bob_public_keys_sid msg1_ts in
  let*? (alice_sid_, msg3_ts) = receive_msg2_and_send_msg3 alice alice_public_keys_sid alice_public_keys_sid msg2_ts in
  receive_msg3 bob bob_private_keys_sid msg3_ts;*?

  // Printing the trace
  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string get_trace_to_string_printers tr
    ) in

  return (Some ())

let _ = run () empty_trace
